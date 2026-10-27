module

public import CFSG.CGT.A8S.N0Sem
public import CFSG.CGT.A8S.Interfaces

public section

namespace CFSG.CGT.A8S

open CFSG.CGT.T75JM CFSG.CGT.Timmesfeld75 CFSG.CosetTable

namespace N0

variable {G : Type} [Group G] {T : Subgroup G}

theorem card_quot_of_naturalSL (hN : NaturalSL T (Subgroup.normalizer (T : Set G)) 3 1) :
    Nat.card (↥(Subgroup.normalizer (T : Set G)) ⧸
      T.subgroupOf (Subgroup.normalizer (T : Set G))) = 168 := by
  obtain ⟨_, e, -, -⟩ := hN
  let : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField 2 1) = 2 := by
    have := GaloisField.card 2 1 one_ne_zero
    rw [Nat.card_eq_fintype_card] at this
    simpa using this
  rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field 3]
  simp [hF, Fin.prod_univ_three]

theorem card_T_of_naturalSL {H : Subgroup G} (hN : NaturalSL T H 3 1) : Nat.card T = 8 := by
  obtain ⟨-, -, φ, -⟩ := hN
  have hF : Nat.card (GaloisField 2 1) = 2 := by
    have := GaloisField.card 2 1 one_ne_zero
    simpa using this
  rw [Nat.card_congr φ.toEquiv,
    Nat.card_congr (Multiplicative.ofAdd (α := Fin 3 → GaloisField 2 1)).symm, Nat.card_pi]
  simp [hF]

theorem card_normalizer3 (h8 : Nat.card T = 8)
    (hq : Nat.card (↥(Subgroup.normalizer (T : Set G)) ⧸
      T.subgroupOf (Subgroup.normalizer (T : Set G))) = 168) :
    Nat.card (Subgroup.normalizer (T : Set G)) = 1344 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (T.subgroupOf (Subgroup.normalizer (T : Set G)))]
  have ht : Nat.card (T.subgroupOf (Subgroup.normalizer (T : Set G))) = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv).trans h8
  rw [hq, ht]

theorem card_complement3
    (hq : Nat.card (↥(Subgroup.normalizer (T : Set G)) ⧸
      T.subgroupOf (Subgroup.normalizer (T : Set G))) = 168)
    {L : Subgroup G} (hLT : L ⊓ T = ⊥) (hTL : T ⊔ L = Subgroup.normalizer (T : Set G)) :
    Nat.card L = 168 := by
  have : (T.subgroupOf (Subgroup.normalizer (T : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).2 le_rfl
  have hLN : L ≤ Subgroup.normalizer (T : Set G) := by rw [← hTL]; exact le_sup_right
  let π : L →* ↥(Subgroup.normalizer (T : Set G)) ⧸
      T.subgroupOf (Subgroup.normalizer (T : Set G)) :=
    (QuotientGroup.mk' (T.subgroupOf (Subgroup.normalizer (T : Set G)))).comp
      (Subgroup.inclusion hLN)
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have hT : Subgroup.inclusion hLN l ∈ T.subgroupOf (Subgroup.normalizer (T : Set G)) :=
      (QuotientGroup.eq_one_iff (Subgroup.inclusion hLN l)).1 hl
    have hbot : (l : G) ∈ L ⊓ T := ⟨l.2, hT⟩
    rw [hLT] at hbot
    exact Subtype.ext (Subgroup.mem_bot.1 hbot)
  have hsurj : Function.Surjective π := by
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
    have hn : n ∈ T.subgroupOf (Subgroup.normalizer (T : Set G)) ⊔
        L.subgroupOf (Subgroup.normalizer (T : Set G)) := by
      rw [← Subgroup.subgroupOf_sup Subgroup.le_normalizer hLN, hTL, Subgroup.subgroupOf_self]
      exact Subgroup.mem_top n
    obtain ⟨t, ht, l, hl, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hn
    refine ⟨⟨l, hl⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion hLN ⟨(l : G), hl⟩) :
        ↥(Subgroup.normalizer (T : Set G)) ⧸ T.subgroupOf (Subgroup.normalizer (T : Set G))) =
      QuotientGroup.mk (t * l)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff t).2 ht, one_mul]
    rfl
  rw [Nat.card_congr (Equiv.ofBijective π ⟨hinj, hsurj⟩), hq]

theorem isGL3_colsOf3 (c : Coords3 T) (g : Subgroup.normalizer (T : Set G)) :
    isGL3 (colsOf3 c g) = true := by
  have hinv : ∀ v, v < 8 → applyC3 (colsOf3 c g⁻¹) (applyC3 (colsOf3 c g) v) = v := by
    intro v hv
    rw [← applyC3_compC3, ← colsOf3_mul, inv_mul_cancel, colsOf3_one, applyC3_idC3 hv]
  unfold isGL3
  rw [List.all_eq_true]
  intro v hv
  rw [List.mem_range] at hv
  rw [bne_iff_ne]
  intro h0
  have h1 := hinv (v + 1) (by omega)
  rw [h0, applyC3_zero] at h1
  omega

theorem exists_mem_complement_colsOf3 (c : Coords3 T)
    (hC : Subgroup.centralizer (T : Set G) = T) {L : Subgroup G} (hLT : L ⊓ T = ⊥)
    (hLN : L ≤ Subgroup.normalizer (T : Set G)) (hL : Nat.card L = 168) {A : Cols3}
    (hA : ∀ j, A.col j < 8) (hAg : isGL3 A = true) :
    ∃ l : Subgroup.normalizer (T : Set G), (l : G) ∈ L ∧ colsOf3 c l = A := by
  classical
  have : Finite L := Nat.finite_of_card_ne_zero (by rw [hL]; norm_num)
  have : Fintype L := Fintype.ofFinite L
  let ρ : L → Cols3 := fun x => colsOf3 c ⟨x, hLN x.2⟩
  have hρ : Function.Injective ρ := by
    intro x y hxy
    have h1 : colsOf3 c ((⟨x, hLN x.2⟩ : Subgroup.normalizer (T : Set G))⁻¹ * ⟨y, hLN y.2⟩) =
        idC3 := by
      rw [colsOf3_mul]
      change compC3 _ (ρ y) = idC3
      rw [← hxy]
      change compC3 _ (colsOf3 c ⟨x, hLN x.2⟩) = idC3
      rw [← colsOf3_mul, inv_mul_cancel, colsOf3_one]
    have h2 := eq_one_of_colsOf3_eq_idC3 c L hC hLT (L.mul_mem (L.inv_mem x.2) y.2) h1
    rw [inv_mul_eq_one] at h2
    exact Subtype.ext (congrArg (fun z : Subgroup.normalizer (T : Set G) => (z : G)) h2)
  have hsub : Finset.univ.image ρ ⊆ (allCols3.filter isGL3).toFinset := by
    intro C hC'
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hC'
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨mem_allCols3 (colsOf3_lt c _), isGL3_colsOf3 c _⟩
  have hcard : (allCols3.filter isGL3).toFinset.card ≤ (Finset.univ.image ρ).card := by
    rw [Finset.card_image_of_injective _ hρ, Finset.card_univ, ← Nat.card_eq_fintype_card, hL]
    exact (List.toFinset_card_le _).trans length_filter_isGL3.le
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hAS : A ∈ (allCols3.filter isGL3).toFinset := by
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨mem_allCols3 hA, hAg⟩
  rw [← heq] at hAS
  obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hAS
  exact ⟨⟨x, hLN x.2⟩, x.2, hx⟩


theorem exists_mulEquiv_normalizerA8 (hN : NaturalSL T (Subgroup.normalizer (T : Set G)) 3 1)
    (hC : Subgroup.centralizer (T : Set G) = T) {L : Subgroup G} (hLT : L ⊓ T = ⊥)
    (hTL : T ⊔ L = Subgroup.normalizer (T : Set G)) [Finite (PG 5 relsN0A8)]
    (hcard : Nat.card (PG 5 relsN0A8) ≤ 1344) :
    ∃ ψ : PG 5 relsN0A8 ≃* ↥(Subgroup.normalizer (T : Set G)),
      Subgroup.map ψ.toMonoidHom (Subgroup.closure (Set.range tGenA8)) =
        T.subgroupOf (Subgroup.normalizer (T : Set G)) := by
  classical
  have hq := card_quot_of_naturalSL hN
  have h8 := card_T_of_naturalSL hN
  obtain ⟨-, -, φ, -⟩ := hN
  obtain ⟨c⟩ := nonempty_coords3 φ
  have hLN : L ≤ Subgroup.normalizer (T : Set G) := by rw [← hTL]; exact le_sup_right
  have hL := card_complement3 hq hLT hTL
  choose l hlL hlc using fun i : Fin 2 =>
    exists_mem_complement_colsOf3 c hC hLT hLN hL (modelCols3_lt i.val i.isLt)
      (isGL3_modelCols3 i.val i.isLt)
  let Φ : PG 5 relsN0A8 →* Subgroup.normalizer (T : Set G) :=
    PresentedGroup.toGroup (f := gens3 c l) fun r hr => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
      exact lift_relsN0A8_eq_one c L hC hLT hlL hlc w hw
  have hΦ : ∀ k, Φ (PresentedGroup.of k) = gens3 c l k := fun k => PresentedGroup.toGroup.of _
  have hΦmk : ∀ w, Φ (PresentedGroup.mk _ (FreeGroup.mk w)) =
      FreeGroup.lift (gens3 c l) (FreeGroup.mk w) := by
    intro w
    have hcomp : Φ.comp (PresentedGroup.mk _) = FreeGroup.lift (gens3 c l) := by
      apply FreeGroup.ext_hom
      intro i
      simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
      exact hΦ i
    exact congrArg (fun g => g (FreeGroup.mk w)) hcomp
  have hinj : Function.Injective Φ := by
    intro x y hxy
    obtain ⟨i, rfl⟩ := n0_forall_of_card_le hcard x
    obtain ⟨j, rfl⟩ := n0_forall_of_card_le hcard y
    have hi := rep3_lift c L hlL hlc (n0Word i)
    have hj := rep3_lift c L hlL hlc (n0Word j)
    rw [← hΦmk, hxy] at hi
    rw [← hΦmk] at hj
    rw [affEval_n0Word_injective (rep3_unique c L hLT hi hj)]
  have hPG : Nat.card (PG 5 relsN0A8) = 1344 :=
    (Nat.card_congr (Equiv.ofBijective _ (mk_n0Word_bijective hcard))).symm.trans
      (Nat.card_fin 1344)
  have hNc := card_normalizer3 h8 hq
  have : Finite (Subgroup.normalizer (T : Set G)) :=
    Nat.finite_of_card_ne_zero (by rw [hNc]; norm_num)
  have hbij : Function.Bijective Φ := hinj.bijective_of_nat_card_le (by rw [hNc, hPG])
  have hΦt : ∀ j : Fin 3, Φ (tGenA8 j) = inN3 (tOf3 c (2 ^ j.val)) := by
    intro j
    have h2 : ¬ (2 + j.val < 2) := by omega
    show Φ (PresentedGroup.of _) = _
    rw [hΦ]
    simp [gens3, h2]
  set S := Subgroup.map Φ (Subgroup.closure (Set.range tGenA8)) with hS
  have hSt : ∀ j : Fin 3, inN3 (tOf3 c (2 ^ j.val)) ∈ S := fun j =>
    ⟨tGenA8 j, Subgroup.subset_closure ⟨j, rfl⟩, hΦt j⟩
  have hpart : ∀ (b : Bool) (n : ℕ), (n = 1 ∨ n = 2 ∨ n = 4) →
      inN3 (tOf3 c (if b then n else 0)) ∈ S := by
    intro b n hn
    cases b
    · simp only [Bool.false_eq_true, ite_false, tOf3_zero c]
      exact S.one_mem
    · simp only [ite_true]
      rcases hn with rfl | rfl | rfl
      · exact hSt 0
      · exact hSt 1
      · exact hSt 2
  have hT : ∀ t : T, inN3 t ∈ S := by
    intro t
    rw [decomp3 c t]
    simp only [← inN3_mul]
    exact S.mul_mem (S.mul_mem (hpart _ _ (by simp)) (hpart _ _ (by simp)))
      (hpart _ _ (by simp))
  refine ⟨MulEquiv.ofBijective Φ hbij, ?_⟩
  show S = T.subgroupOf (Subgroup.normalizer (T : Set G))
  refine le_antisymm ?_ fun x hx => ?_
  · rw [hS, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    show Φ (tGenA8 j) ∈ T.subgroupOf (Subgroup.normalizer (T : Set G))
    rw [hΦt]
    exact (tOf3 c (2 ^ j.val)).2
  · have hx' : x = inN3 (⟨(x : G), hx⟩ : T) := Subtype.ext rfl
    rw [hx']
    exact hT _

end N0

theorem n0StatementA8 : N0StatementA8 := by
  intro G _ _ T T₁ hyp
  have := finite_pg_relsN0A8
  obtain ⟨L, hLT, hTL⟩ := hyp.compl
  exact N0.exists_mulEquiv_normalizerA8 hyp.nat hyp.cent_eq hLT hTL card_pg_relsN0A8.le

end CFSG.CGT.A8S
