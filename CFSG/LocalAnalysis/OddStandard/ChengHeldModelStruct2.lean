module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelFacts
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelSimple
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelClosure
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelEA

public section

namespace CFSG.OddStandard.ChengHeld.Model

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.RegModel Subgroup
open CFSG.OddStandard.ChengHeld.M1b (evalE)

variable {H : Type} [Group H]

namespace Struct2Aux

variable {M : RegModel}

theorem size_replicate_true (M : RegModel) : (Array.replicate M.N true).size = M.N := by
  simp

theorem set_replicate_true (R : Rep M H) : R.set (Array.replicate M.N true) = Set.univ := by
  ext h
  simp only [Rep.mem_set, Set.mem_univ, iff_true]
  rw [getElem!_pos _ _ (by simpa using R.pt_lt h)]
  simp

theorem size3 (R : Rep M H) (a b c : H) : (M.closure [R.pt a, R.pt b, R.pt c]).size = M.N :=
  R.closure_size (by simp [R.pt_lt])

theorem size5 (R : Rep M H) (a b c d e : H) :
    (M.closure [R.pt a, R.pt b, R.pt c, R.pt d, R.pt e]).size = M.N :=
  R.closure_size (by simp [R.pt_lt])

theorem set3 (R : Rep M H) (a b c : H) :
    R.set (M.closure [R.pt a, R.pt b, R.pt c]) = (closure {a, b, c} : Set H) := by
  have e : {h : H | R.pt h ∈ [R.pt a, R.pt b, R.pt c]} = {a, b, c} := by
    ext h
    simp [R.pt_inj.eq_iff]
  rw [R.set_closure (by simp [R.pt_lt]), e]

theorem set5 (R : Rep M H) (a b c d e : H) :
    R.set (M.closure [R.pt a, R.pt b, R.pt c, R.pt d, R.pt e]) =
      (closure {a, b, c, d, e} : Set H) := by
  have e' : {h : H | R.pt h ∈ [R.pt a, R.pt b, R.pt c, R.pt d, R.pt e]} = {a, b, c, d, e} := by
    ext h
    simp [R.pt_inj.eq_iff]
  rw [R.set_closure (by simp [R.pt_lt]), e']

theorem natCard_eq (R : Rep M H) {B : Array Bool} (hB : B.size = M.N) (K : Subgroup H)
    (hK : R.set B = K) : Nat.card K = card B := by
  rw [R.card_eq_ncard hB, hK, ← SetLike.coe_sort_coe, Nat.card_coe_set_eq]

theorem commutator_top_eq :
    ⁅(⊤ : Subgroup H), ⊤⁆ = closure {c : H | ∃ a ∈ (Set.univ : Set H),
      ∃ b ∈ (Set.univ : Set H), c = a⁻¹ * b⁻¹ * a * b} := by
  rw [Subgroup.commutator_def]
  congr 1
  ext c
  simp only [Subgroup.mem_top, Set.mem_univ, true_and, Set.mem_ofPred_eq, commutatorElement_def]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a⁻¹, b⁻¹, by simp⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨a⁻¹, b⁻¹, by simp⟩

theorem invols_length_eq (R : Rep M H) {B : Array Bool} (hB : B.size = M.N) :
    (M.invols B).length = {h : H | h ∈ R.set B ∧ h ≠ 1 ∧ h * h = 1}.ncard := by
  refine R.length_eq_ncard (Rep.invols_nodup B) (R.invols_lt hB) (fun h => ?_)
  rw [R.mem_invols hB]
  constructor
  · rintro ⟨h', hpt, hh⟩
    rw [R.pt_inj hpt] at hh
    exact hh
  · intro hh
    exact ⟨h, rfl, hh⟩

theorem hasRoot_iff (R : Rep M H) (a : H) :
    ((List.range M.N).any fun s => M.pw s 2 == R.pt a) = true ↔ ∃ s : H, s ^ 2 = a := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨s, hs, hsa⟩
    obtain ⟨t, rfl⟩ := R.pt_surj s (List.mem_range.1 hs)
    rw [beq_iff_eq, ← R.pt_pow] at hsa
    exact ⟨t, R.pt_inj hsa⟩
  · rintro ⟨s, rfl⟩
    exact ⟨R.pt s, List.mem_range.2 (R.pt_lt s), by rw [beq_iff_eq, R.pt_pow]⟩

theorem isPGroup_two (E : Subgroup H) (h2 : ∀ a ∈ E, a * a = 1) : IsPGroup 2 E := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, pow_two, h2 g g.2]
  rfl

theorem elemAb_le (R : Rep M H) (h6 : (eaL M 6).size = 0) (E : Subgroup H)
    (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (h2 : ∀ a ∈ E, a * a = 1) : Nat.card E ≤ 32 := by
  have := R.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (isPGroup_two E h2).exists_card_eq
  rw [hn]
  by_cases hn5 : n ≤ 5
  · calc 2 ^ n ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hn5
      _ = 32 := by norm_num
  · exfalso
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 2 (n := 6)
      (by rw [hn]; exact pow_dvd_pow 2 (by omega))
    have hFE : K.map E.subtype ≤ E := Subgroup.map_subtype_le K
    have hFc : Nat.card (K.map E.subtype) = 2 ^ 6 := by
      rw [Subgroup.card_map_of_injective E.subtype_injective, hK]
    obtain ⟨l, hl, -⟩ := R.eaL_complete 6 (by norm_num) (K.map E.subtype)
      (fun a ha b hb => hab a (hFE ha) b (hFE hb)) (fun a ha => h2 a (hFE ha)) hFc
    have hpos := List.length_pos_of_mem (Array.mem_def.1 hl)
    rw [Array.length_toList, h6] at hpos
    omega

theorem eq_or_eq_of_pair {α : Type} {u v a b c : α} (ha : a = u ∨ a = v) (hb : b = u ∨ b = v)
    (hc : c = u ∨ c = v) (hab : a ≠ b) : c = a ∨ c = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    simp_all

theorem elemAb_32 (R : Rep M H) (h5 : (eaL M 5).size = 2) {A B : Subgroup H}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a * a = 1) (hcA : Nat.card A = 32)
    (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ a ∈ B, a * a = 1) (hcB : Nat.card B = 32)
    (hAB : A ≠ B) (E : Subgroup H) (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE2 : ∀ a ∈ E, a * a = 1) (hcE : Nat.card E = 32) : E = A ∨ E = B := by
  obtain ⟨lA, hlA, hA'⟩ := R.eaL_complete 5 (by norm_num) A hA hA2 (by rw [hcA]; norm_num)
  obtain ⟨lB, hlB, hB'⟩ := R.eaL_complete 5 (by norm_num) B hB hB2 (by rw [hcB]; norm_num)
  obtain ⟨lE, hlE, hE'⟩ := R.eaL_complete 5 (by norm_num) E hE hE2 (by rw [hcE]; norm_num)
  have hne : lA ≠ lB := by
    rintro rfl
    exact hAB (Subgroup.ext fun h => (hA' h).trans (hB' h).symm)
  obtain ⟨u, v, huv⟩ := List.length_eq_two.1
    (by rw [Array.length_toList, h5] : (eaL M 5).toList.length = 2)
  rw [Array.mem_def, huv] at hlA hlB hlE
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hlA hlB hlE
  rcases eq_or_eq_of_pair hlA hlB hlE hne with rfl | rfl
  · exact Or.inl (Subgroup.ext fun h => (hE' h).trans (hA' h).symm)
  · exact Or.inr (Subgroup.ext fun h => (hE' h).trans (hB' h).symm)

theorem center_eq (R : Rep M H) (x : Fin 7 → H)
    (h : M.center = M.closure [R.pt (x 0), R.pt (x 1), R.pt (x 2)]) : center H = sD x := by
  apply SetLike.coe_injective
  rw [← R.set_center, h, set3]
  rfl

theorem commutator_eq (R : Rep M H) (x : Fin 7 → H)
    (h : M.commSub (Array.replicate M.N true) (Array.replicate M.N true) =
      M.closure [R.pt (x 0), R.pt (x 1), R.pt (x 2)]) : ⁅(⊤ : Subgroup H), ⊤⁆ = sD x := by
  have e := R.set_commSub (size_replicate_true M) (size_replicate_true M)
  rw [h, set3, set_replicate_true] at e
  rw [commutator_top_eq]
  exact SetLike.coe_injective e.symm

theorem inf_eq (R : Rep M H) (x : Fin 7 → H)
    (h : bInter (M.closure [R.pt (x 0), R.pt (x 1), R.pt (x 2), R.pt (x 3), R.pt (x 4)])
      (M.closure [R.pt (x 0), R.pt (x 1), R.pt (x 2), R.pt (x 5), R.pt (x 6)]) =
      M.closure [R.pt (x 0), R.pt (x 1), R.pt (x 2)]) : sR1 x ⊓ sR2 x = sD x := by
  have e := R.set_bInter
    (B := M.closure [R.pt (x 0), R.pt (x 1), R.pt (x 2), R.pt (x 5), R.pt (x 6)])
    (size5 R (x 0) (x 1) (x 2) (x 3) (x 4))
  rw [h, set3, set5, set5] at e
  apply SetLike.coe_injective
  rw [Subgroup.coe_inf]
  exact e.symm

theorem involutions_eq (R : Rep M H) (h : (M.invols (Array.replicate M.N true)).length = 55) :
    {a : H | a ≠ 1 ∧ a * a = 1}.ncard = 55 := by
  rw [invols_length_eq R (size_replicate_true M), set_replicate_true] at h
  simpa only [Set.mem_univ, true_and] using h

theorem involutions_mem (R : Rep M H) (x : Fin 7 → H)
    (h1 : (M.invols (Array.replicate M.N true)).length = 55)
    (h2 : (M.invols
      (bUnion (M.closure [R.pt (x 0), R.pt (x 1), R.pt (x 2), R.pt (x 3), R.pt (x 4)])
        (M.closure [R.pt (x 0), R.pt (x 1), R.pt (x 2), R.pt (x 5), R.pt (x 6)]))).length = 55) :
    ∀ a : H, a * a = 1 → a ∈ sR1 x ∨ a ∈ sR2 x := by
  have := R.finite
  rw [invols_length_eq R (size_replicate_true M), set_replicate_true] at h1
  rw [invols_length_eq R (by rw [Rep.bUnion_size, size5]), R.set_bUnion (size5 R _ _ _ _ _),
    set5, set5] at h2
  have hsub : {h : H | h ∈ ((sR1 x : Set H) ∪ sR2 x) ∧ h ≠ 1 ∧ h * h = 1} ⊆
      {h : H | h ∈ Set.univ ∧ h ≠ 1 ∧ h * h = 1} := fun h hh => ⟨Set.mem_univ _, hh.2⟩
  have heq := Set.eq_of_subset_of_ncard_le hsub (h1.trans h2.symm).le (Set.toFinite _)
  intro a ha
  by_cases ha1 : a = 1
  · exact Or.inl (ha1 ▸ one_mem _)
  · have hmem : a ∈ {h : H | h ∈ Set.univ ∧ h ≠ 1 ∧ h * h = 1} := ⟨Set.mem_univ _, ha1, ha⟩
    rw [← heq] at hmem
    exact hmem.1

end Struct2Aux

open Struct2Aux in
theorem struct2_facts (h : struct2OK = true) (x : Fin 7 → H) (R : Rep (mkReg 2) H)
    (hx : ∀ j : Fin 7, R.pt (x j) = (mkReg 2).g j.val) : Struct2Facts H x := by
  unfold struct2OK at h
  generalize mkReg 2 = M at h R hx
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  have g0 : M.g 0 = R.pt (x 0) := (hx 0).symm
  have g1 : M.g 1 = R.pt (x 1) := (hx 1).symm
  have g2 : M.g 2 = R.pt (x 2) := (hx 2).symm
  have g3 : M.g 3 = R.pt (x 3) := (hx 3).symm
  have g4 : M.g 4 = R.pt (x 4) := (hx 4).symm
  have g5 : M.g 5 = R.pt (x 5) := (hx 5).symm
  have g6 : M.g 6 = R.pt (x 6) := (hx 6).symm
  rw [g0, g1, g2, g3, g4, g5, g6] at h
  obtain ⟨-, hord, hcen, hcD, hcomm, hc1, hc2, he1, he2, hint, hinv, hinvU, hea, hq, hpi, hqpi,
    htau, hqtau, hmlx, hmz⟩ := h
  rw [eaCounts_eq] at hea
  simp only [List.cons.injEq] at hea
  have hD := natCard_eq R (size3 R _ _ _) (sD x) (set3 R _ _ _)
  have hR1 := natCard_eq R (size5 R _ _ _ _ _) (sR1 x) (set5 R _ _ _ _ _)
  have hR2 := natCard_eq R (size5 R _ _ _ _ _) (sR2 x) (set5 R _ _ _ _ _)
  rw [hcD] at hD
  rw [hc1] at hR1
  rw [hc2] at hR2
  have e1 := (R.isElemAb_iff (size5 R _ _ _ _ _)).1 he1
  have e2 := (R.isElemAb_iff (size5 R _ _ _ _ _)).1 he2
  rw [set5] at e1 e2
  have hi := inf_eq R x hint
  have hne : sR1 x ≠ sR2 x := by
    intro heq
    rw [← heq, inf_idem] at hi
    rw [hi] at hR1
    omega
  rw [← R.pt_mul] at hqpi hqtau hmz
  rw [← R.pt_mul] at hmlx hmz
  rw [← R.pt_mul, ← R.pt_pow] at hmlx
  rw [← R.pt_pow] at hmz
  exact
    { ord_q := (R.ord_eq _).symm.trans hord
      center := center_eq R x hcen
      commutator := commutator_eq R x hcomm
      card_D := hD
      card_R1 := hR1
      card_R2 := hR2
      R1_comm := e1.1
      R1_sq := e1.2
      R2_comm := e2.1
      R2_sq := e2.2
      inf_R := hi
      involutions := involutions_eq R hinv
      involutions_mem := involutions_mem R x hinv hinvU
      elemAb_le := elemAb_le R hea.2.2.2.2.2.1
      elemAb_32 := elemAb_32 R hea.2.2.2.2.1 e1.1 e1.2 hR1 e2.1 e2.2 hR2 hne
      no_root_q := fun s hs => by
        rw [(hasRoot_iff R (x 0)).2 ⟨s, hs⟩] at hq
        exact absurd hq (by decide)
      root_pi := (hasRoot_iff R _).1 hpi
      root_qpi := (hasRoot_iff R _).1 hqpi
      root_tau := (hasRoot_iff R _).1 htau
      root_qtau := (hasRoot_iff R _).1 hqtau
      sq_mlx := R.pt_inj hmlx
      sq_mz := R.pt_inj hmz }

end CFSG.OddStandard.ChengHeld.Model
