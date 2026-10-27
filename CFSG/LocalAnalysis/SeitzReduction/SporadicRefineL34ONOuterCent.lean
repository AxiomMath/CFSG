module

import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint Matrix
open CFSG.ComponentClassification.PSL3Four

@[expose] def lowTriMul (a b : F4 × F4 × F4) : F4 × F4 × F4 :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2 + a.2.1 * b.1)

@[expose] def lowTriInv (a : F4 × F4 × F4) : F4 × F4 × F4 := (a.1, a.2.1, a.2.2 + a.2.1 * a.1)

@[expose] def lowTriMat (a : F4 × F4 × F4) : Matrix (Fin 3) (Fin 3) F4 :=
  !![1, 0, 0; a.1, 1, 0; a.2.2, a.2.1, 1]

theorem det_lowTriMat (a : F4 × F4 × F4) : (lowTriMat a).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [lowTriMat]

theorem lowTriMat_mul (a b : F4 × F4 × F4) :
    lowTriMat a * lowTriMat b = lowTriMat (lowTriMul a b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowTriMat, lowTriMul, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals ring

@[expose] def lowTriSL (a : F4 × F4 × F4) : SpecialLinearGroup (Fin 3) F4 :=
  ⟨lowTriMat a, det_lowTriMat a⟩

theorem lowTriSL_mul (a b : F4 × F4 × F4) : lowTriSL a * lowTriSL b = lowTriSL (lowTriMul a b) :=
  Subtype.ext (lowTriMat_mul a b)

theorem lowTriSL_zero : lowTriSL 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def lowTriPerm (a : F4 × F4 × F4) : Equiv.Perm (Fin 42) := rhoSL (lowTriSL a)

theorem lowTriPerm_mul (a b : F4 × F4 × F4) :
    lowTriPerm a * lowTriPerm b = lowTriPerm (lowTriMul a b) := by
  rw [lowTriPerm, lowTriPerm, lowTriPerm, ← map_mul, lowTriSL_mul]

theorem lowTriPerm_zero : lowTriPerm 0 = 1 := by
  rw [lowTriPerm, lowTriSL_zero, map_one]

theorem lowTriMul_lowTriInv : ∀ a : F4 × F4 × F4, lowTriMul a (lowTriInv a) = 0 := by decide +kernel

theorem eq_of_lowTriMul_lowTriInv : ∀ a b : F4 × F4 × F4, (lowTriMul a (lowTriInv b)).1 = 0 →
    (lowTriMul a (lowTriInv b)).2.1 = 0 → (lowTriMul a (lowTriInv b)).2.2 = 0 → a = b := by
  decide +kernel

theorem lowTriMul_self_eq_zero : ∀ a : F4 × F4 × F4, a.1 * a.2.1 = 0 → lowTriMul a a = 0 := by
  decide +kernel

theorem card_lowTriComm : ∀ a : F4 × F4 × F4, a.1 * a.2.1 ≠ 0 →
    (Finset.univ.filter fun b : F4 × F4 × F4 => lowTriMul b a = lowTriMul a b).card = 16 := by
  decide +kernel

section Model


theorem lowTriPerm_mem (a : F4 × F4 × F4) : lowTriPerm a ∈ S :=
  range_rhoSL.1 ▸ ⟨lowTriSL a, rfl⟩

theorem r₁_eq_lowTriPerm : r₁ = lowTriPerm (0, 0, 1) := by
  rw [r₁, g₁, g₂, lowTriPerm, rhoSL_apply, pow_two, ← map_mul, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  show aMat * aMat * bMat * aMat = lowTriMat (0, 0, 1)
  decide +kernel

theorem lowTriPerm_mem_C₁ (a : F4 × F4 × F4) : lowTriPerm a ∈ C₁ := by
  refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, lowTriPerm_mem a⟩
  rw [r₁_eq_lowTriPerm, lowTriPerm_mul, lowTriPerm_mul]
  congr 1
  simp only [lowTriMul, Prod.mk.injEq]
  exact ⟨by ring, by ring, by ring⟩

theorem lowTriPerm_injective : Function.Injective lowTriPerm := by
  intro a b hab
  have h1 : lowTriSL (lowTriMul a (lowTriInv b)) ∈ rhoSL.ker := by
    rw [MonoidHom.mem_ker, ← lowTriSL_mul, map_mul]
    change lowTriPerm a * lowTriPerm (lowTriInv b) = 1
    rw [hab, lowTriPerm_mul, lowTriMul_lowTriInv, lowTriPerm_zero]
  rw [range_rhoSL.2, mem_scalars_iff] at h1
  obtain ⟨c, hc⟩ := h1
  have e10 := congrFun (congrFun hc 1) 0
  have e21 := congrFun (congrFun hc 2) 1
  have e20 := congrFun (congrFun hc 2) 0
  simp [lowTriSL, lowTriMat] at e10 e21 e20
  exact eq_of_lowTriMul_lowTriInv a b e10 e21 e20

theorem exists_lowTriPerm_of_mem_C₁ {t : Equiv.Perm (Fin 42)} (ht : t ∈ C₁) :
    ∃ a, lowTriPerm a = t := by
  have hsub : Set.range lowTriPerm ⊆ (C₁ : Set (Equiv.Perm (Fin 42))) := by
    rintro _ ⟨a, rfl⟩
    exact lowTriPerm_mem_C₁ a
  have hcard : Nat.card (Set.range lowTriPerm) = 64 := by
    rw [Nat.card_range_of_injective lowTriPerm_injective, Nat.card_eq_fintype_card]
    simp [Fintype.card_prod, F4.card_eq]
  have heq : Set.range lowTriPerm = (C₁ : Set (Equiv.Perm (Fin 42))) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hcard]
    exact card_C₁.le
  rw [← SetLike.mem_coe, ← heq] at ht
  exact ht

theorem card_centralizer_le_of_sq_eq_r₁ {s' : Equiv.Perm (Fin 42)} (hs'S : s' ∈ S)
    (hs'o : orderOf s' = 4) (hs'2 : s' ^ 2 = r₁) : Nat.card ↥(centralizer {s'} ⊓ S) ≤ 16 := by
  have hC : ∀ t ∈ centralizer {s'} ⊓ S, t ∈ C₁ := by
    intro t ht
    obtain ⟨htc, htS⟩ := mem_inf.mp ht
    refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, htS⟩
    rw [← hs'2]
    exact ((show Commute t s' from mem_centralizer_singleton_iff.mp htc).pow_right 2).eq
  obtain ⟨a, ha⟩ := exists_lowTriPerm_of_mem_C₁
    (hC s' (mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl, hs'S⟩))
  have ha0 : a.1 * a.2.1 ≠ 0 := by
    intro h0
    have h1 : s' ^ 2 = 1 := by
      rw [← ha, pow_two, lowTriPerm_mul, lowTriMul_self_eq_zero a h0, lowTriPerm_zero]
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hs'o] at h2
    norm_num at h2
  set F : Finset (F4 × F4 × F4) :=
    Finset.univ.filter fun b : F4 × F4 × F4 => lowTriMul b a = lowTriMul a b with hF
  have hsub : ((centralizer {s'} ⊓ S : Subgroup (Equiv.Perm (Fin 42))) :
      Set (Equiv.Perm (Fin 42))) ⊆ ((F.image lowTriPerm : Finset (Equiv.Perm (Fin 42))) :
        Set (Equiv.Perm (Fin 42))) := by
    intro t ht
    obtain ⟨b, rfl⟩ := exists_lowTriPerm_of_mem_C₁ (hC t ht)
    have hcomm : lowTriPerm b * s' = s' * lowTriPerm b :=
      mem_centralizer_singleton_iff.mp (mem_inf.mp ht).1
    rw [← ha, lowTriPerm_mul, lowTriPerm_mul] at hcomm
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr
      ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, lowTriPerm_injective hcomm⟩, rfl⟩)
  calc Nat.card ↥(centralizer {s'} ⊓ S)
      = ((centralizer {s'} ⊓ S : Subgroup (Equiv.Perm (Fin 42))) :
          Set (Equiv.Perm (Fin 42))).ncard := Nat.card_coe_set_eq _
    _ ≤ ((F.image lowTriPerm : Finset (Equiv.Perm (Fin 42))) : Set (Equiv.Perm (Fin 42))).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (F.image lowTriPerm).card := Set.ncard_coe_finset _
    _ ≤ F.card := Finset.card_image_le
    _ = 16 := card_lowTriComm a ha0

end Model

theorem card_centralizer_le_of_orderOf_four {X : Type} [Group X]
    (h : LieModel X .PSL 3 2 2) {x : X} (hx : orderOf x = 4) :
    Nat.card (centralizer ({x} : Set X)) ≤ 16 := by
  obtain ⟨θ⟩ := nonempty_equiv_of_stated X
    (ComponentClassification.CatLeaf.statedClassicalModel_of_lieModel_psl h)
  rw [card_centralizer_of_equiv θ x, card_centralizer_S]
  set s : Equiv.Perm (Fin 42) := ((θ x : S) : Equiv.Perm (Fin 42)) with hs
  have hsS : s ∈ S := (θ x).2
  have hso : orderOf s = 4 := by rw [hs, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx]
  have hs2S : s ^ 2 ∈ S := pow_mem hsS 2
  set tR : R := ⟨s ^ 2, S_le_R hs2S⟩ with htR
  have ht1 : tR ≠ 1 := by
    intro h1
    have h2 : s ^ 2 = 1 := congrArg Subtype.val h1
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hso] at h3
    norm_num at h3
  have ht2 : tR * tR = 1 := by
    apply Subtype.ext
    show s ^ 2 * s ^ 2 = 1
    rw [← pow_add, show 2 + 2 = orderOf s by rw [hso], pow_orderOf_eq_one]
  obtain ⟨c, hcR, hc⟩ := eq_conj_of_isConj (isConj_r₁_of_inner (x := tR) hs2S ht1 ht2)
  have hc' : s ^ 2 = c * r₁ * c⁻¹ := hc
  set s' : Equiv.Perm (Fin 42) := c⁻¹ * s * c with hs'
  have hss' : s = c * s' * c⁻¹ := by
    rw [hs']
    group
  rw [hss', Nat.card_congr (centConjEquiv hcR).toEquiv]
  refine card_centralizer_le_of_sq_eq_r₁ ?_ ?_ ?_
  · have := conj_mem_S (R.inv_mem hcR) hsS
    rwa [inv_inv] at this
  · rw [hs', show c⁻¹ * s * c = MulAut.conj c⁻¹ s by rw [MulAut.conj_apply, inv_inv],
      MulEquiv.orderOf_eq, hso]
  · rw [hs', show (c⁻¹ * s * c) ^ 2 = c⁻¹ * s ^ 2 * c by rw [pow_two, pow_two]; group, hc']
    group

end CFSG.SeitzReduction.SporadicRefine
