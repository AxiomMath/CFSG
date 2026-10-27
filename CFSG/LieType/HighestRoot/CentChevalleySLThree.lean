module

public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall

public section

namespace CFSG.LieType.HighestRoot

open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

section SL23

abbrev SL23 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

theorem card_SL23 : Nat.card SL23 = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem mem_center_SL23_iff (x : SL23) : x ∈ Subgroup.center SL23 ↔ x = 1 ∨ x = -1 := by
  rw [Subgroup.mem_center_iff]
  revert x
  decide

theorem eq_one_or_neg_one_of_commute_SL23 :
    ∀ j : SL23, (∀ g : SL23, g * j = j * g ∨ g * j = -(j * g)) → j = 1 ∨ j = -1 := by
  decide

theorem eight_le_card_conj_SL23 :
    ∀ x : SL23, x ≠ 1 → x ≠ -1 →
      8 ≤ (Finset.univ.filter fun y : SL23 =>
        (∃ g : SL23, y * g = g * x ∨ y * g * x = g) ∨ y = 1 ∨ y = x * x).card := by
  decide +kernel

theorem orderOf_neg_one_SL23 : orderOf (-1 : SL23) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by decide) (by decide)

end SL23

section Unitriangular

variable {K : Type} [Field K]

@[expose] noncomputable def slMapEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Matrix.SpecialLinearGroup (Fin 2) R ≃* Matrix.SpecialLinearGroup (Fin 2) S where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by
    ext i j
    simp
  right_inv A := by
    ext i j
    simp
  map_mul' := map_mul _

theorem sl2Upper_mul (a b : K) : sl2Upper K a * sl2Upper K b = sl2Upper K (a + b) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [sl2Upper, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem sl2Lower_mul (a b : K) : sl2Lower K a * sl2Lower K b = sl2Lower K (a + b) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [sl2Lower, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2Upper_zero : sl2Upper K 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Upper]

theorem sl2Lower_zero : sl2Lower K 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Lower]

variable [Finite K]

theorem three_eq_zero (hK : Nat.card K = 3) : (3 : K) = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.cast_card_eq_zero K
  rw [← Nat.card_eq_fintype_card, hK] at h
  exact_mod_cast h

theorem orderOf_eq_three_of_hom (hK : Nat.card K = 3) {G : Type*} [Group G] (f : K → G)
    (hf : ∀ a b, f a * f b = f (a + b)) {c : K} (hc : f c ≠ 1) (h0 : f 0 = 1) :
    orderOf (f c) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ hc
  rw [pow_three, hf, hf, ← h0]
  congr 1
  linear_combination c * three_eq_zero hK

theorem closure_orderOf_three_eq_top (hK : Nat.card K = 3) :
    Subgroup.closure {x : Matrix.SpecialLinearGroup (Fin 2) K | orderOf x = 3} = ⊤ := by
  rw [eq_top_iff, ← sl2_closure_upper_lower, Subgroup.closure_le]
  have key : ∀ (f : K → Matrix.SpecialLinearGroup (Fin 2) K), (∀ a b, f a * f b = f (a + b)) →
      f 0 = 1 → ∀ c, f c ∈ Subgroup.closure {x : Matrix.SpecialLinearGroup (Fin 2) K |
        orderOf x = 3} := by
    intro f hf h0 c
    by_cases hc : f c = 1
    · rw [hc]
      exact one_mem _
    · exact Subgroup.subset_closure (orderOf_eq_three_of_hom hK f hf hc h0)
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact key _ sl2Upper_mul sl2Upper_zero c
  · exact key _ sl2Lower_mul sl2Lower_zero c

end Unitriangular

section Transfer

variable {K : Type} [Field K] [Finite K]

@[expose] noncomputable def slEquivSL23 (hK : Nat.card K = 3) :
    Matrix.SpecialLinearGroup (Fin 2) K ≃* SL23 :=
  have : Fintype K := Fintype.ofFinite K
  slMapEquiv (ZMod.ringEquivOfPrime K Nat.prime_three
    (by rw [← Nat.card_eq_fintype_card, hK])).symm

theorem card_eq_24 (hK : Nat.card K = 3) {J : Type*} [Group J]
    (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) K) : Nat.card J = 24 := by
  rw [Nat.card_congr (e.trans (slEquivSL23 hK)).toEquiv, card_SL23]

theorem isSolvable_of_mulEquiv (hK : Nat.card K = 3) {J : Type*} [Group J]
    (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) K) : Group.IsSolvable J := by
  have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) K) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable K
      (Or.inr hK)
  have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Group.isSolvable_of_isSolvable_injective Matrix.SpecialLinearGroup.toGL_injective
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem closure_orderOf_three_eq_top_of_mulEquiv (hK : Nat.card K = 3) {J : Type*} [Group J]
    (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    Subgroup.closure {x : J | orderOf x = 3} = ⊤ := by
  have hmap := congrArg (Subgroup.map e.symm.toMonoidHom) (closure_orderOf_three_eq_top hK)
  rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ e.symm.surjective] at hmap
  rw [← hmap]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, MulEquiv.coe_toMonoidHom]
  constructor
  · intro hx
    refine ⟨e x, ?_, e.symm_apply_apply x⟩
    rw [← orderOf_injective e.toMonoidHom e.injective x] at hx
    exact hx
  · rintro ⟨y, hy, rfl⟩
    rw [← orderOf_injective e.symm.toMonoidHom e.symm.injective y] at hy
    exact hy

theorem mem_center_iff_of_mulEquiv (hK : Nat.card K = 3) {J : Type*} [Group J]
    (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) K) (x : J) :
    x ∈ Subgroup.center J ↔
      (e.trans (slEquivSL23 hK)) x = 1 ∨ (e.trans (slEquivSL23 hK)) x = -1 := by
  set φ := e.trans (slEquivSL23 hK)
  rw [← mem_center_SL23_iff, Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h g
    obtain ⟨g, rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul, h g]
  · intro h g
    exact φ.injective (by rw [map_mul, map_mul, h])

theorem mem_center_of_forall_commutator_mem_center (hK : Nat.card K = 3) {J : Type*} [Group J]
    (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) K) {j : J}
    (h : ∀ g : J, g * j * g⁻¹ * j⁻¹ ∈ Subgroup.center J) : j ∈ Subgroup.center J := by
  set φ := e.trans (slEquivSL23 hK)
  rw [mem_center_iff_of_mulEquiv hK e]
  refine eq_one_or_neg_one_of_commute_SL23 (φ j) fun g => ?_
  obtain ⟨g, rfl⟩ := φ.surjective g
  rcases (mem_center_iff_of_mulEquiv hK e _).1 (h g) with h1 | h1 <;>
    simp only [map_mul, map_inv] at h1
  · exact Or.inl (by
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1)
  · refine Or.inr ?_
    have h1' : φ g * φ j * (φ g)⁻¹ * (φ j)⁻¹ = -1 := h1
    have h2 : φ g * φ j = -1 * (φ j * φ g) := by
      calc φ g * φ j = (φ g * φ j * (φ g)⁻¹ * (φ j)⁻¹) * (φ j * φ g) := by group
        _ = -1 * (φ j * φ g) := by rw [h1']
    rw [h2, neg_one_mul]

theorem eight_le_card_of_normal (hK : Nat.card K = 3) {J : Type*} [Group J]
    (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) K) (N : Subgroup J) [hN : N.Normal]
    (hNZ : ¬ N ≤ Subgroup.center J) : 8 ≤ Nat.card N := by
  classical
  set φ := e.trans (slEquivSL23 hK)
  obtain ⟨x, hxN, hxZ⟩ := Set.not_subset.1 hNZ
  rw [SetLike.mem_coe, mem_center_iff_of_mulEquiv hK e, not_or] at hxZ
  have h8 := eight_le_card_conj_SL23 (φ x) hxZ.1 hxZ.2
  set F := Finset.univ.filter fun y : SL23 =>
    (∃ g : SL23, y * g = g * φ x ∨ y * g * φ x = g) ∨ y = 1 ∨ y = φ x * φ x
  have hsub : (F : Set SL23) ⊆ (N.map φ.toMonoidHom : Set SL23) := by
    intro y hy
    simp only [F, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy
    rcases hy with ⟨g, hg | hg⟩ | rfl | rfl
    · obtain ⟨g, rfl⟩ := φ.surjective g
      refine ⟨g * x * g⁻¹, hN.conj_mem x hxN g, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
      rw [mul_inv_eq_iff_eq_mul, hg]
    · obtain ⟨g, rfl⟩ := φ.surjective g
      refine ⟨g * x⁻¹ * g⁻¹, hN.conj_mem _ (inv_mem hxN) g, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
      rw [mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul, hg]
    · exact one_mem _
    · exact ⟨x * x, mul_mem hxN hxN, by simp [map_mul]⟩
  have hcard : F.card ≤ Nat.card (N.map φ.toMonoidHom) := by
    rw [← Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
    exact Nat.card_mono (Set.toFinite _) hsub
  rw [Subgroup.card_map_of_injective φ.injective] at hcard
  omega

theorem orderOf_ne_three_of_mem_center (hK : Nat.card K = 3) {J : Type*} [Group J]
    (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) K) {y : J} (hy : y ∈ Subgroup.center J) :
    orderOf y ≠ 3 := by
  rw [mem_center_iff_of_mulEquiv hK e] at hy
  rw [← orderOf_injective (e.trans (slEquivSL23 hK)).toMonoidHom
    (e.trans (slEquivSL23 hK)).injective y]
  simp only [MulEquiv.coe_toMonoidHom]
  rcases hy with h | h <;> rw [h]
  · rw [orderOf_one]
    decide
  · rw [orderOf_neg_one_SL23]
    decide

end Transfer

section CentralProduct

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup_of_commute {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        rw [mul_assoc, ← mul_assoc b, ← hAB a' ha' b hb]
        group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by rw [mul_one]⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        rw [mul_inv_rev, ← hAB a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)] }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, one_mem _, by rw [mul_one]⟩)
    (fun b hb => ⟨1, one_mem _, b, hb, by rw [one_mul]⟩)
  exact hle hx

theorem conj_mul_commutator {g j l : G} (hgl : g * l = l * g) :
    g * (j * l) * g⁻¹ * (j * l)⁻¹ = g * j * g⁻¹ * j⁻¹ := by
  have h1 : l * g⁻¹ = g⁻¹ * l := ((Commute.inv_left (hgl : Commute g l))).eq.symm
  calc g * (j * l) * g⁻¹ * (j * l)⁻¹ = g * j * (l * g⁻¹) * l⁻¹ * j⁻¹ := by group
    _ = g * j * (g⁻¹ * l) * l⁻¹ * j⁻¹ := by rw [h1]
    _ = g * j * g⁻¹ * j⁻¹ := by group

theorem three_le_card_inf {L : Subgroup G} (hL : Nat.card L = 24) {N₁ N₂ : Subgroup G}
    (h₁ : N₁ ≤ L) (h₂ : N₂ ≤ L) (h8₁ : 8 ≤ Nat.card N₁) (h8₂ : 8 ≤ Nat.card N₂) :
    3 ≤ Nat.card (N₁ ⊓ N₂ : Subgroup G) := by
  set M₁ := N₁.subgroupOf L
  set M₂ := N₂.subgroupOf L
  have hc₁ : Nat.card M₁ = Nat.card N₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₁).toEquiv
  have hc₂ : Nat.card M₂ = Nat.card N₂ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₂).toEquiv
  have hM : (N₁ ⊓ N₂).subgroupOf L = M₁ ⊓ M₂ := by
    ext x
    simp [M₁, M₂, Subgroup.mem_subgroupOf]
  have hc : Nat.card (M₁ ⊓ M₂ : Subgroup L) = Nat.card (N₁ ⊓ N₂ : Subgroup G) := by
    rw [← hM]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans h₁)).toEquiv
  have hi₁ := Subgroup.card_mul_index M₁
  have hi₂ := Subgroup.card_mul_index M₂
  have hi := Subgroup.card_mul_index (M₁ ⊓ M₂)
  rw [hL] at hi₁ hi₂ hi
  have hle := Subgroup.index_inf_le (H := M₁) (K := M₂)
  have hx₁ : M₁.index ≤ 3 := by
    by_contra h
    have := Nat.mul_le_mul (hc₁ ▸ h8₁ : 8 ≤ Nat.card M₁) (not_le.1 h)
    omega
  have hx₂ : M₂.index ≤ 3 := by
    by_contra h
    have := Nat.mul_le_mul (hc₂ ▸ h8₂ : 8 ≤ Nat.card M₂) (not_le.1 h)
    omega
  have h9 : (M₁ ⊓ M₂).index ≤ 9 := hle.trans (Nat.mul_le_mul hx₁ hx₂)
  rw [← hc]
  by_contra h
  have := Nat.mul_le_mul (Nat.le_of_lt_succ (not_le.1 h)) h9
  omega

variable [Finite G] {K : Type} [Field K] [Finite K]

theorem eq_or_eq_of_le_sup (hK : Nat.card K = 3) {J L₀ L : Subgroup G}
    (eJ : J ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (eL₀ : L₀ ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (eL : L ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (hcomm : ∀ a ∈ J, ∀ b ∈ L₀, a * b = b * a) (hint : Nat.card (J ⊓ L₀ : Subgroup G) ≤ 2)
    (hZJ : ∀ x : J, x ∈ Subgroup.center J → (x : G) ∈ L₀)
    (hZL₀ : ∀ x : L₀, x ∈ Subgroup.center L₀ → (x : G) ∈ J)
    (hLS : L ≤ J ⊔ L₀) (hJ : J ≤ Subgroup.normalizer (L : Set G))
    (hL₀ : L₀ ≤ Subgroup.normalizer (L : Set G)) : L = J ∨ L = L₀ := by
  have hcL := card_eq_24 hK eL
  have hnorm : ∀ {A : Subgroup G}, A ≤ Subgroup.normalizer (L : Set G) →
      ((L ⊓ A).subgroupOf A).Normal := fun {A} hA => by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnL, hnA⟩ := Subgroup.mem_inf.1 hn
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.1 (hA g.2) n).1 hnL
    · simpa using mul_mem (mul_mem g.2 hnA) (inv_mem g.2)
  have hcardA : ∀ {A : Subgroup G},
      Nat.card ((L ⊓ A).subgroupOf A) = Nat.card (L ⊓ A : Subgroup G) :=
    fun {A} => Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have h8 : ∀ {A : Subgroup G} (_ : A ≃* Matrix.SpecialLinearGroup (Fin 2) K),
      A ≤ Subgroup.normalizer (L : Set G) → ∀ y : A, y ∉ Subgroup.center A → (y : G) ∈ L →
        8 ≤ Nat.card (L ⊓ A : Subgroup G) := fun {A} eA hA y hyZ hyL => by
    have := hnorm hA
    rw [← hcardA]
    refine eight_le_card_of_normal hK eA _ fun hle => hyZ (hle ?_)
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hyL, y.2⟩)
  have hboth : ¬ (8 ≤ Nat.card (L ⊓ J : Subgroup G) ∧ 8 ≤ Nat.card (L ⊓ L₀ : Subgroup G)) := by
    rintro ⟨h1, h2⟩
    have h3 := three_le_card_inf hcL inf_le_left inf_le_left h1 h2
    have hle : (L ⊓ J) ⊓ (L ⊓ L₀) ≤ J ⊓ L₀ := fun x hx => ⟨hx.1.2, hx.2.2⟩
    have := Subgroup.card_le_of_le hle
    omega
  have hcomm_ex : ∀ {A : Subgroup G} (_ : A ≃* Matrix.SpecialLinearGroup (Fin 2) K) (y : A),
      y ∉ Subgroup.center A → ∃ g : A, g * y * g⁻¹ * y⁻¹ ∉ Subgroup.center A :=
    fun {A} eA y hyZ => by
      by_contra hc
      simp only [not_exists, not_not] at hc
      exact hyZ (mem_center_of_forall_commutator_mem_center hK eA hc)
  have hJL : ∀ x ∈ L, orderOf x = 3 → x ∈ J ∨ x ∈ L₀ := by
    intro x hxL hx3
    obtain ⟨j, hj, l, hl, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm (hLS hxL)
    by_cases hjZ : (⟨j, hj⟩ : J) ∈ Subgroup.center J
    · exact Or.inr (mul_mem (hZJ _ hjZ) hl)
    by_cases hlZ : (⟨l, hl⟩ : L₀) ∈ Subgroup.center L₀
    · exact Or.inl (mul_mem hj (hZL₀ _ hlZ))
    exfalso
    refine hboth ⟨?_, ?_⟩
    · obtain ⟨g, hg⟩ := hcomm_ex eJ _ hjZ
      refine h8 eJ hJ _ hg ?_
      have e1 : ((g * ⟨j, hj⟩ * g⁻¹ * (⟨j, hj⟩ : J)⁻¹ : J) : G) =
          (g : G) * (j * l) * (g : G)⁻¹ * (j * l)⁻¹ := by
        rw [conj_mul_commutator (hcomm _ g.2 _ hl)]
        rfl
      rw [e1]
      exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hJ g.2) _).1 hxL) (inv_mem hxL)
    · obtain ⟨g, hg⟩ := hcomm_ex eL₀ _ hlZ
      refine h8 eL₀ hL₀ _ hg ?_
      have hjl : j * l = l * j := hcomm _ hj _ hl
      have e1 : ((g * ⟨l, hl⟩ * g⁻¹ * (⟨l, hl⟩ : L₀)⁻¹ : L₀) : G) =
          (g : G) * (j * l) * (g : G)⁻¹ * (j * l)⁻¹ := by
        rw [hjl, conj_mul_commutator (hcomm _ hj _ g.2).symm]
        rfl
      rw [e1]
      exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hL₀ g.2) _).1 hxL) (inv_mem hxL)
  have hnZ : ∀ {A : Subgroup G} (_ : A ≃* Matrix.SpecialLinearGroup (Fin 2) K) (y : A),
      orderOf (y : G) = 3 → y ∉ Subgroup.center A := fun {A} eA y hy hyZ =>
    orderOf_ne_three_of_mem_center hK eA hyZ (by rwa [← Subgroup.orderOf_coe])
  have hgen := closure_orderOf_three_eq_top_of_mulEquiv hK eL
  have hle_of : ∀ {A : Subgroup G}, (∀ x ∈ L, orderOf x = 3 → x ∈ A) → L ≤ A := by
    intro A hA x hx
    have hle : Subgroup.closure {y : L | orderOf y = 3} ≤ A.subgroupOf L :=
      (Subgroup.closure_le _).2 fun y hy => Subgroup.mem_subgroupOf.2
        (hA y.1 y.2 (by rw [Subgroup.orderOf_coe]; exact hy))
    have h := hle (hgen ▸ Subgroup.mem_top (⟨x, hx⟩ : L))
    exact Subgroup.mem_subgroupOf.1 h
  by_cases hall : ∀ x ∈ L, orderOf x = 3 → x ∈ J
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge (hle_of hall)
      (by rw [card_eq_24 hK eJ, hcL]))
  · right
    simp only [not_forall] at hall
    obtain ⟨x₁, hx₁L, hx₁3, hx₁J⟩ := hall
    have hx₁L₀ : x₁ ∈ L₀ := (hJL x₁ hx₁L hx₁3).resolve_left hx₁J
    have h2 : 8 ≤ Nat.card (L ⊓ L₀ : Subgroup G) :=
      h8 eL₀ hL₀ ⟨x₁, hx₁L₀⟩ (hnZ eL₀ _ hx₁3) hx₁L
    refine Subgroup.eq_of_le_of_card_ge (hle_of fun x hx hx3 => ?_)
      (by rw [card_eq_24 hK eL₀, hcL])
    by_contra hxL₀
    have hxJ : x ∈ J := (hJL x hx hx3).resolve_right hxL₀
    exact hboth ⟨h8 eJ hJ ⟨x, hxJ⟩ (hnZ eJ _ hx3) hx, h2⟩

end CentralProduct

end CFSG.LieType.HighestRoot
