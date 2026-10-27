module

public import CFSG.LieType.Ree.SmallReeThreePerm
public import CFSG.LieType.Ree.SmallReeBorelCosetAction

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps Equiv
open scoped commutatorElement

section Vectors

variable {τ : Tag} {R : Type*} [CommRing R]

theorem vecOf_normModVec
    {n : ℕ} (hn : (n : R) = 0) (v : List (ℕ × ℤ)) :
    vecOf τ R (normModVec n v) = vecOf τ R v := by
  rw [normModVec, vecOf_filter_ne_zero, ← vecOf_normalize v]
  generalize normalize v = w
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [List.map_cons, vecOf_cons, vecOf_cons, ih]
    congr 2
    conv_rhs => rw [← Int.emod_add_mul_ediv x.2 n]
    rw [Int.cast_add, Int.cast_mul, Int.cast_natCast, hn, zero_mul, add_zero]

theorem posCoord_vecOf
    {v : List (ℕ × ℤ)} (hv : ValidVec τ v) (p : ℕ) :
    posCoord τ R p (vecOf τ R v) = (coeffAtPos v p : R) := by
  induction v with
  | nil => simp [coeffAtPos]
  | cons x v ih =>
    rw [vecOf_cons, map_add, map_smul, posCoord_posVec (hv x List.mem_cons_self),
      ih fun y hy => hv y (List.mem_cons_of_mem _ hy)]
    simp only [coeffAtPos, List.filter_cons, beq_iff_eq]
    split_ifs with h₁ h₂ h₂
    · simp
    · exact absurd h₁.symm h₂
    · exact absurd h₂.symm h₁
    · simp

end Vectors

section Orbit

variable (K : Type) [Field K] [CharP K ReeTag.G2.prime]

theorem three_eq_zero_K : ((3 : ℕ) : K) = 0 :=
  CharP.cast_eq_zero K ReeTag.G2.prime

@[expose] def srVec (i : Fin 56) : RootModule ReeTag.G2.tag K :=
  vecOf ReeTag.G2.tag K (srOrbit.getD i [])

theorem srOrbit_valid {i : ℕ} : ValidVec ReeTag.G2.tag (srOrbit.getD i []) := by
  have h := srValidCheck_eq
  simp only [srValidCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Nat.blt_eq] at h
  intro x hx
  by_cases hi : i < srOrbit.length
  · rw [List.getD_eq_getElem _ _ hi] at hx
    exact h.2 _ (List.getElem_mem hi) x hx
  · rw [List.getD_eq_default _ _ (not_lt.1 hi)] at hx
    exact absurd hx List.not_mem_nil

theorem srVec_injective
    : Function.Injective (srVec K) := by
  have : CharP K 3 := ‹CharP K ReeTag.G2.prime›
  intro i j h
  by_contra hne
  have hsep := srSepCheck_eq
  simp only [srSepCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true, bne_iff_ne, ne_eq] at hsep
  rcases hsep i i.2 j j.2 with hij | ⟨p, hp, hne'⟩
  · exact hne (Fin.ext hij)
  · apply hne'
    have hc := congrArg (posCoord ReeTag.G2.tag K p) h
    rw [srVec, srVec, posCoord_vecOf srOrbit_valid, posCoord_vecOf srOrbit_valid] at hc
    exact (CharP.intCast_eq_intCast K 3).1 hc

theorem eq_of_eq_on_srVec
    {f g : Module.End K (RootModule ReeTag.G2.tag K)}
    (h : ∀ i, f (srVec K i) = g (srVec K i)) : f = g := by
  have hspan := srSpanCheck_eq
  simp only [srSpanCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at hspan
  have hk : ∀ k : ℕ, f (vecOf ReeTag.G2.tag K (srOrbit.getD k [])) =
      g (vecOf ReeTag.G2.tag K (srOrbit.getD k [])) := by
    intro k
    by_cases hk : k < 56
    · exact h ⟨k, hk⟩
    · have hlen : srOrbit.length = 56 := by
        have hv := srValidCheck_eq
        simp only [srValidCheck, Bool.and_eq_true, beq_iff_eq] at hv
        exact hv.1
      rw [List.getD_eq_default _ _ (by omega), vecOf_nil, map_zero, map_zero]
  refine ext_posVec fun p hp => ?_
  have hp' : p < 14 := hp
  have e : posVec ReeTag.G2.tag K p = vecOf ReeTag.G2.tag K (srCombo (srSpan.getD p [])) := by
    rw [← vecOf_normModVec (three_eq_zero_K K), hspan p hp']
    simp
  have hsum : ∀ cs : List (ℕ × ℤ), vecOf ReeTag.G2.tag K (srCombo cs) =
      (cs.map fun x => (x.2 : K) • vecOf ReeTag.G2.tag K (srOrbit.getD x.1 [])).sum := by
    intro cs
    rw [srCombo, vecOf_flatMap]
    congr 1
    refine List.map_congr_left fun x _ => ?_
    exact vecOf_map_mul x.2 _
  rw [e, hsum, map_list_sum, map_list_sum, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp only [Function.comp_apply, map_smul, hk]

theorem one_add_entriesOp_srVec
    {E : List Entry} {σ : List ℕ} (hE : srActCheck E σ = true)
    (i : Fin 56) : (1 + entriesOp ReeTag.G2.tag K E) (srVec K i) =
      vecOf ReeTag.G2.tag K (srOrbit.getD (σ.getD i 0) []) := by
  simp only [srActCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at hE
  rw [srVec, LinearMap.add_apply, Module.End.one_apply, entriesOp_vecOf E srOrbit_valid,
    ← vecOf_append, ← vecOf_normModVec (three_eq_zero_K K), hE i i.2]

theorem constP_constProd (n : ℕ) :
    ∀ (fs : List (ℕ × ℤ)) (acc : List RootOps.PEntry), ConstP acc →
      ConstP (constProd ReeTag.G2.tag n acc fs)
  | [], _, h => h
  | _ :: fs, _, _ => constP_constProd n fs _ (constP_normC n _)

theorem constPinned_eq_one_add
    {L : List (ℕ × ℤ)}
    (hL : ∀ f ∈ L, f.1 < ReeTag.G2.tag.rootCertificate.roots.length) :
    (constPinned ReeTag.G2.tag K L : Module.End K (RootModule ReeTag.G2.tag K)) =
      1 + entriesOp ReeTag.G2.tag K ((constProd ReeTag.G2.tag 3 [] L).map Prod.snd) := by
  have hnil : ConstP ([] : List RootOps.PEntry) := fun x hx => absurd hx List.not_mem_nil
  have h := one_add_pOp_constProd (three_eq_zero_K K) L [] hnil hL 0 0
  rw [pOp_nil, add_zero, one_mul, pOp_eq_of_constP (constP_constProd 3 L [] hnil)] at h
  exact h.symm

end Orbit

section Graph

variable (K : Type) [Field K] [CharP K ReeTag.G2.prime]

@[expose] def srGraph : Subgroup (ModGL ReeTag.G2.tag K × Perm (Fin 56)) where
  carrier := {p | ∀ i, (p.1 : Module.End K (RootModule ReeTag.G2.tag K)) (srVec K i) =
    srVec K (p.2 i)}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro p q hp hq i
    change (p.1 * q.1 : ModGL ReeTag.G2.tag K).val (srVec K i) = srVec K ((p.2 * q.2) i)
    rw [Units.val_mul, Module.End.mul_apply, hq, hp, Perm.mul_apply]
  inv_mem' := by
    intro p hp i
    change (p.1⁻¹ : ModGL ReeTag.G2.tag K).val (srVec K i) = srVec K (p.2⁻¹ i)
    have h := hp (p.2⁻¹ i)
    rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply] at h
    rw [← h, ← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]

@[expose] def srFst : srGraph K →* ModGL ReeTag.G2.tag K :=
  (MonoidHom.fst _ _).comp (srGraph K).subtype

@[expose] def srSnd : srGraph K →* Perm (Fin 56) :=
  (MonoidHom.snd _ _).comp (srGraph K).subtype

theorem srFst_injective
    : Function.Injective (srFst K) := by
  intro p q h
  have h' : p.1.1 = q.1.1 := h
  refine Subtype.ext (Prod.ext h' (Equiv.ext fun i => srVec_injective K ?_))
  rw [← p.2 i, ← q.2 i, h']

theorem srSnd_injective
    : Function.Injective (srSnd K) := by
  intro p q h
  have h' : p.1.2 = q.1.2 := h
  refine Subtype.ext (Prod.ext (Units.ext (eq_of_eq_on_srVec K fun i => ?_)) h')
  rw [p.2 i, q.2 i, h']

end Graph

section Generators

variable (K : Type) [Field K] [CharP K ReeTag.G2.prime]

theorem srGraph_mem_of
    {g : ModGL ReeTag.G2.tag K} {L : List (ℕ × ℤ)} {E : List Entry}
    {l l' : List ℕ} (hpair : srPermPairCheck l l' = true) (hg : g = constPinned ReeTag.G2.tag K L)
    (hL : ∀ f ∈ L, f.1 < ReeTag.G2.tag.rootCertificate.roots.length)
    (hE : (constProd ReeTag.G2.tag 3 [] L).map Prod.snd = E) (hact : srActCheck E l = true) :
    (g, listPerm l l' hpair) ∈ srGraph K := by
  intro i
  simp only
  rw [hg, constPinned_eq_one_add K hL, hE, one_add_entriesOp_srVec K hact i, srVec]
  have h := hpair
  simp only [srPermPairCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Nat.blt_eq] at h
  congr 2
  exact (Nat.mod_eq_of_lt (h.2 i i.2).1.1.1).symm

theorem g2UWord_lt (k : Fin 3) :
    ∀ f ∈ ReeTag.g2UWord k, f.1 < ReeTag.G2.tag.rootCertificate.roots.length := by
  revert k
  decide

theorem g2LongWord_lt :
    ∀ f ∈ ReeTag.g2LongWord, f.1 < ReeTag.G2.tag.rootCertificate.roots.length := by
  decide

theorem srGraph_u0 :
    (ReeTag.g2U₀ K, srSigma0) ∈ srGraph K :=
  srGraph_mem_of K srPermPairCheck_u0 (ReeTag.g2U_eq_constPinned K).1 (g2UWord_lt 0)
    srEntriesU0_eq srActCheck_u0

theorem srGraph_u1 :
    (ReeTag.g2U₁ K, srSigma1) ∈ srGraph K :=
  srGraph_mem_of K srPermPairCheck_u1 (ReeTag.g2U_eq_constPinned K).2.1 (g2UWord_lt 1)
    srEntriesU1_eq srActCheck_u1

theorem srGraph_n
    {w₀ : WeylGroup ReeTag.G2.tag}
    (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤
      (coxeterSystem ReeTag.G2.tag).length w₀) :
    (canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀, srSigmaN) ∈ srGraph K :=
  srGraph_mem_of K srPermPairCheck_n (ReeTag.canonicalRep_longest hw₀) g2LongWord_lt
    srEntriesN_eq srActCheck_n

end Generators

section Iso

variable
    {K : Type} [Field K] [CharP K ReeTag.G2.prime] {w₀ : WeylGroup ReeTag.G2.tag}
  (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤ (coxeterSystem ReeTag.G2.tag).length w₀)

include hw₀ in
theorem srGraph_closure_map :
    (Subgroup.closure {(⟨_, srGraph_u0 K⟩ : srGraph K), ⟨_, srGraph_n K hw₀⟩}).map (srFst K) =
        Subgroup.closure {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀} ∧
      (Subgroup.closure {(⟨_, srGraph_u0 K⟩ : srGraph K), ⟨_, srGraph_n K hw₀⟩}).map (srSnd K) =
        srP := by
  rw [MonoidHom.map_closure, MonoidHom.map_closure, Set.image_pair, Set.image_pair]
  exact ⟨rfl, rfl⟩

include hw₀ in
theorem nonempty_srD_mulEquiv :
    Nonempty
    (Subgroup.closure {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀} ≃* srP) := by
  obtain ⟨h1, h2⟩ := srGraph_closure_map (K := K) hw₀
  set C := Subgroup.closure {(⟨_, srGraph_u0 K⟩ : srGraph K), ⟨_, srGraph_n K hw₀⟩}
  exact ⟨(MulEquiv.subgroupCongr h1.symm).trans
    ((C.equivMapOfInjective _ (srFst_injective K)).symm.trans
      ((C.equivMapOfInjective _ (srSnd_injective K)).trans (MulEquiv.subgroupCongr h2)))⟩

include hw₀ in
theorem srD_u1 :
    ReeTag.g2U₁ K * ReeTag.g2U₀ K * (ReeTag.g2U₁ K)⁻¹ ∈
        Subgroup.closure {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀} ∧
      ReeTag.g2U₁ K * canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀ * (ReeTag.g2U₁ K)⁻¹ ∈
        Subgroup.closure {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀} ∧
      ReeTag.g2U₁ K ∉
        Subgroup.closure {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀} := by
  obtain ⟨h1, h2⟩ := srGraph_closure_map (K := K) hw₀
  set C := Subgroup.closure {(⟨_, srGraph_u0 K⟩ : srGraph K), ⟨_, srGraph_n K hw₀⟩}
  set q0 : srGraph K := ⟨_, srGraph_u0 K⟩
  set qn : srGraph K := ⟨_, srGraph_n K hw₀⟩
  set q1 : srGraph K := ⟨_, srGraph_u1 K⟩
  have hconj : ∀ q ∈ ({q0, qn} : Set (srGraph K)), srSnd K (q1 * q * q1⁻¹) ∈ srP →
      srFst K (q1 * q * q1⁻¹) ∈ C.map (srFst K) := by
    intro q _ hq
    rw [← h2] at hq
    obtain ⟨c, hc, hce⟩ := hq
    have := srSnd_injective K hce
    rw [← this]
    exact ⟨c, hc, rfl⟩
  obtain ⟨hP0, hPn⟩ := srSigma1_conj_mem
  refine ⟨?_, ?_, ?_⟩
  · rw [← h1]
    exact hconj q0 (Set.mem_insert _ _) hP0
  · rw [← h1]
    exact hconj qn (Set.mem_insert_of_mem _ rfl) hPn
  · intro hu
    rw [← h1] at hu
    obtain ⟨c, hc, hce⟩ := hu
    have hcq : c = q1 := srFst_injective K hce
    apply srSigma1_not_mem
    rw [← h2]
    exact ⟨c, hc, by rw [hcq]; rfl⟩

end Iso

theorem small_Ree_three_derived_simple
    (K : Type) [Field K] [Finite K] [CharP K ReeTag.G2.prime]
    (hK : Nat.card K = 3) (w₀ : WeylGroup ReeTag.G2.tag)
    (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤
      (coxeterSystem ReeTag.G2.tag).length w₀) :
    Nat.card (ReeTag.G2.reeGamma K 0) = 1512 ∧
      Subgroup.closure {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀} ≤
        ReeTag.G2.reeGamma K 0 ∧
      ((Subgroup.closure
        {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀}).subgroupOf
          (ReeTag.G2.reeGamma K 0)).Normal ∧
      Nat.card (Subgroup.closure
        {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀}) = 504 ∧
      ((Subgroup.closure
        {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀}).subgroupOf
          (ReeTag.G2.reeGamma K 0)).index = 3 ∧
      IsSimpleGroup (Subgroup.closure
        {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀}) ∧
      (∃ a b : Subgroup.closure
        {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀}, a * b ≠ b * a) ∧
      ⁅ReeTag.G2.reeGamma K 0, ReeTag.G2.reeGamma K 0⁆ =
        Subgroup.closure {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀} := by
  set Γ := ReeTag.G2.reeGamma K 0 with hΓ
  set D := Subgroup.closure {ReeTag.g2U₀ K, canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀}
    with hD
  have hcardΓ : Nat.card Γ = 1512 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ :=
      small_Ree_Borel_coset_Sylow_action 0 K (by rw [hK]; norm_num) w₀ hw₀
    rw [h]
    norm_num
  have hu0 : ReeTag.g2U₀ K ∈ Γ := ReeTag.g2U₀_mem_reeGamma K 0
  have hn : canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀ ∈ Γ :=
    ReeTag.canonicalRep_longest_mem_reeGamma (K := K) (a := 0) hw₀
  have hu1 : ReeTag.g2U₁ K ∈ Γ := ReeTag.g2U₁_mem_reeGamma K 0
  have hDΓ : D ≤ Γ := by
    rw [hD, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hu0
    · exact hn
  obtain ⟨e⟩ := nonempty_srD_mulEquiv (K := K) hw₀
  have hcardD : Nat.card D = 504 := (Nat.card_congr e.toEquiv).trans card_srP
  have hsimple : IsSimpleGroup D := (e.isSimpleGroup_congr).2 isSimpleGroup_srP
  have hnonab : ∃ a b : D, a * b ≠ b * a := by
    refine ⟨e.symm ⟨srSigma0, srSigma0_mem⟩, e.symm ⟨srSigmaN, srSigmaN_mem⟩, fun h => ?_⟩
    apply srSigma0_mul_srSigmaN_ne
    have := congrArg (fun x => ((e x : srP) : Perm (Fin 56))) h
    simpa using this
  obtain ⟨hc0, hcn, hu1D⟩ := srD_u1 (K := K) hw₀
  have hmap : D.map (MulAut.conj (ReeTag.g2U₁ K)).toMonoidHom = D := by
    have hle : D.map (MulAut.conj (ReeTag.g2U₁ K)).toMonoidHom ≤ D := by
      rw [Subgroup.map_le_iff_le_comap, hD, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact hc0
      · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact hcn
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj (ReeTag.g2U₁ K)).injective]
  set D' := D.subgroupOf Γ with hD'
  have hcardD' : Nat.card D' = 504 := by
    rw [hD', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDΓ).toEquiv, hcardD]
  set u₁ : Γ := ⟨ReeTag.g2U₁ K, hu1⟩
  have hu₁N : u₁ ∈ Subgroup.normalizer (D' : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [hD', Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · intro hh
      have : (MulAut.conj (ReeTag.g2U₁ K)).toMonoidHom (h : ModGL ReeTag.G2.tag K) ∈
          D.map (MulAut.conj (ReeTag.g2U₁ K)).toMonoidHom := Subgroup.mem_map_of_mem _ hh
      rw [hmap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      exact this
    · intro hh
      rw [← hmap] at hh
      obtain ⟨x, hx, hxe⟩ := hh
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxe
      have : x = (h : ModGL ReeTag.G2.tag K) := mul_left_cancel (mul_right_cancel hxe)
      rw [← this]
      exact hx
  have hu₁D' : u₁ ∉ D' := fun h => hu1D (Subgroup.mem_subgroupOf.1 h)
  have hnorm : D'.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    set N := Subgroup.normalizer (D' : Set Γ)
    have hle : D' ≤ N := Subgroup.le_normalizer
    have hdvd₁ : Nat.card D' ∣ Nat.card N := Subgroup.card_dvd_of_le hle
    have hdvd₂ : Nat.card N ∣ Nat.card Γ := Subgroup.card_subgroup_dvd_card N
    rw [hcardD'] at hdvd₁
    rw [hcardΓ] at hdvd₂
    obtain ⟨m, hm⟩ := hdvd₁
    have hm3 : m ∣ 3 := by
      rw [hm, show (1512 : ℕ) = 504 * 3 by norm_num] at hdvd₂
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd₂
    rcases (Nat.dvd_prime Nat.prime_three).1 hm3 with rfl | rfl
    · have : D' = N := Subgroup.eq_of_le_of_card_ge hle (by rw [hm, hcardD'])
      exact absurd (this ▸ hu₁N) hu₁D'
    · exact Subgroup.eq_top_of_card_eq N (by rw [hm, hcardΓ])
  have hindex : D'.index = 3 := by
    have h := Subgroup.card_mul_index D'
    rw [hcardD', hcardΓ] at h
    omega
  refine ⟨hcardΓ, hDΓ, hnorm, hcardD, hindex, hsimple, hnonab, le_antisymm ?_ ?_⟩
  ·
    have hq : Nat.card (Γ ⧸ D') = 3 := by rw [← Subgroup.index_eq_card, hindex]
    have : Fact (Nat.card (Γ ⧸ D')).Prime := ⟨hq ▸ Nat.prime_three⟩
    have hcyc : IsCyclic (Γ ⧸ D') := isCyclic_of_prime_card rfl
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Γ ⧸ D')
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hcomm : Commute (QuotientGroup.mk (⟨x, hx⟩ : Γ) : Γ ⧸ D')
        (QuotientGroup.mk (⟨y, hy⟩ : Γ)) := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hg (QuotientGroup.mk (⟨x, hx⟩ : Γ)))
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hg (QuotientGroup.mk (⟨y, hy⟩ : Γ)))
      rw [← hi, ← hj]
      exact (Commute.refl g).zpow_zpow i j
    have h1 : (QuotientGroup.mk ⁅(⟨x, hx⟩ : Γ), ⟨y, hy⟩⁆ : Γ ⧸ D') = 1 := by
      change (QuotientGroup.mk' D') ⁅(⟨x, hx⟩ : Γ), ⟨y, hy⟩⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.2 hcomm
    rw [QuotientGroup.eq_one_iff, hD', Subgroup.mem_subgroupOf] at h1
    exact h1
  ·
    have hperf : _root_.commutator D = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (G := D) (_root_.commutator D) with h | h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnonab
        have hc := (commutator_eq_bot_iff (G := D)).1 h
        exact hab (hc.is_comm.comm a b)
      · exact h
    have hDD : ⁅D, D⁆ = D := by
      rw [← Subgroup.map_subtype_commutator, hperf, Subgroup.map_top, Subgroup.range_subtype]
    rw [← hDD]
    exact Subgroup.commutator_mono hDΓ hDΓ

end CFSG.LieType.Ree
