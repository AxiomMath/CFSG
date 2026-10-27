module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Model.Faithful
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Hmod

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup SemidirectProduct CFSG.Sporadic.Recognition.HSMultiplier
  CFSG.EvenSporadicStandard.TwoHS

@[expose] noncomputable def P1408 : Subgroup (Equiv.Perm (Fin 1408)) :=
  closure (Set.range h1408GenPerm)

theorem h1408GenPerm_mem_P1408 (j : Fin 7) : h1408GenPerm j ∈ P1408 :=
  subset_closure ⟨j, rfl⟩

theorem h1408XPerm_mem_P1408 (i : Fin 6) : h1408XPerm i ∈ P1408 :=
  h1408GenPerm_mem_P1408 (Fin.castSucc i)

theorem h1408VPerm_mem_P1408 : h1408VPerm ∈ P1408 :=
  h1408GenPerm_mem_P1408 6

section VHom


@[expose] noncomputable def h1408VHom : Multiplicative (ZMod 2) →* Equiv.Perm (Fin 1408) where
  toFun a := if a = 1 then 1 else h1408VPerm
  map_one' := by simp
  map_mul' a b := by
    by_cases ha : a = 1
    · simp [ha]
    · by_cases hb : b = 1
      · simp [hb]
      · have hab : a * b = 1 := by
          have h2 : ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a * b = 1 := by decide
          exact h2 a b ha hb
        rw [if_neg ha, if_neg hb, if_pos hab]
        exact h1408VPerm_mul_self.symm

theorem h1408VHom_one2 : h1408VHom one2 = h1408VPerm := by
  change (if one2 = 1 then (1 : Equiv.Perm (Fin 1408)) else h1408VPerm) = h1408VPerm
  rw [if_neg (show one2 ≠ 1 by decide)]

end VHom

section Model


theorem rho1408_sigma (hΛ : HSCtx) (x : HSCover) :
    rho1408 (hΛ.sigma x) = h1408VPerm * rho1408 x * h1408VPerm⁻¹ := by
  have hcomp : rho1408.comp hΛ.sigma =
      (MulAut.conj h1408VPerm).toMonoidHom.comp rho1408 := by
    apply PresentedGroup.ext
    intro i
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, rho1408_of]
    rw [hΛ.sigma_of]
    simp only [sigmaGen]
    rw [map_wordVal]
    have hmap : hsGens.map rho1408 = (List.finRange 6).map h1408XPerm := by
      rw [hsGens, List.map_map]
      apply List.map_congr_left
      intro j _
      simpa only [Function.comp_apply] using rho1408_of j
    rw [hmap]
    exact (h1408VPerm_conj i).symm
  exact DFunLike.congr_fun hcomp x

theorem hmod1408_compat (hΛ : HSCtx) (g : Multiplicative (ZMod 2)) :
    rho1408.comp (hΛ.sigmaHom g).toMonoidHom =
      (MulAut.conj (h1408VHom g)).toMonoidHom.comp rho1408 := by
  by_cases hg : g = 1
  · subst hg
    apply MonoidHom.ext
    intro x
    simp [h1408VHom, HSCtx.sigmaHom]
  · have hg2 : g = one2 := by
      revert g
      decide
    subst hg2
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, HSCtx.sigmaHom_one2,
      h1408VHom_one2, MulAut.conj_apply]
    exact rho1408_sigma hΛ x

noncomputable def hmod1408 (hΛ : HSCtx) : hΛ.Hmod →* Equiv.Perm (Fin 1408) :=
  SemidirectProduct.lift rho1408 h1408VHom (hmod1408_compat hΛ)

theorem hmod1408_inl (hΛ : HSCtx) (x : HSCover) : hmod1408 hΛ (inl x) = rho1408 x := by
  change SemidirectProduct.lift rho1408 h1408VHom (hmod1408_compat hΛ) (inl x) = rho1408 x
  simp

theorem hmod1408_inr (hΛ : HSCtx) (a : Multiplicative (ZMod 2)) :
    hmod1408 hΛ (inr a) = h1408VHom a := by
  change SemidirectProduct.lift rho1408 h1408VHom (hmod1408_compat hΛ) (inr a) = h1408VHom a
  simp

private theorem mul_h1408VPerm_not_mem_blocks (l : HSCover) :
    rho1408 l * h1408VPerm ∉ blocks1408 := by
  intro hmem
  have h1 : ¬ (rho1408 l (h1408VPerm h1408Pt0)).val < 704 := by
    have h := rho1408_mem_blocks l (h1408VPerm h1408Pt0)
    rw [h1408VPerm_zero] at h
    intro hp
    exact absurd (h.mp hp) (by decide)
  apply h1
  have h0 := hmem h1408Pt0
  rw [Equiv.Perm.mul_apply] at h0
  exact h0.mpr (by decide)

theorem hmod1408_mem_blocks_iff (hΛ : HSCtx) (x : hΛ.Hmod) :
    hmod1408 hΛ x ∈ blocks1408 ↔ x ∈ hΛ.Emod := by
  have hx : hmod1408 hΛ x = rho1408 x.left * h1408VHom x.right := by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
    rw [map_mul, hmod1408_inl, hmod1408_inr]
  rw [hx, hΛ.mem_Emod_iff x]
  constructor
  · intro h
    by_contra hr
    have hV : h1408VHom x.right = h1408VPerm := by
      change (if x.right = 1 then (1 : Equiv.Perm (Fin 1408)) else h1408VPerm) = h1408VPerm
      rw [if_neg hr]
    rw [hV] at h
    exact mul_h1408VPerm_not_mem_blocks x.left h
  · intro hr
    rw [hr]
    simp only [map_one, mul_one]
    exact rho1408_mem_blocks x.left

theorem hmod1408_injective (hΛ : HSCtx) : Function.Injective (hmod1408 hΛ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hmem : hmod1408 hΛ x ∈ blocks1408 := by
    rw [hx]
    exact blocks1408.one_mem
  have hE : x ∈ hΛ.Emod := (hmod1408_mem_blocks_iff hΛ x).1 hmem
  have hr : x.right = 1 := (hΛ.mem_Emod_iff x).1 hE
  have hx1 : x = inl x.left := by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
    rw [hr, map_one, mul_one]
  rw [hx1] at hx
  rw [hmod1408_inl] at hx
  have hl : x.left = 1 := HSCtx.rho1408_injective hΛ (hx.trans (map_one rho1408).symm)
  rw [hx1, hl]
  simp

theorem hmod1408_range (hΛ : HSCtx) : (hmod1408 hΛ).range = P1408 := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have hl : ∀ l : HSCover, rho1408 l ∈ P1408 := by
      intro l
      exact PresentedGroup.generated_by _ (P1408.comap rho1408) (fun i => by
        rw [Subgroup.mem_comap, rho1408_of]
        exact h1408XPerm_mem_P1408 i) l
    have hv : ∀ a : Multiplicative (ZMod 2), h1408VHom a ∈ P1408 := by
      intro a
      by_cases ha : a = 1
      · rw [ha, map_one]; exact P1408.one_mem
      · have hV : h1408VHom a = h1408VPerm := by
          change (if a = 1 then (1 : Equiv.Perm (Fin 1408)) else h1408VPerm) = h1408VPerm
          rw [if_neg ha]
        rw [hV]; exact h1408VPerm_mem_P1408
    rw [← SemidirectProduct.inl_left_mul_inr_right x, map_mul, hmod1408_inl, hmod1408_inr]
    exact P1408.mul_mem (hl x.left) (hv x.right)
  · rw [P1408, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    rcases lt_or_eq_of_le (show j.val ≤ 6 by omega) with hlt | heq
    · refine ⟨inl (PresentedGroup.of ⟨j.val, hlt⟩), ?_⟩
      have hj : j = Fin.castSucc (⟨j.val, hlt⟩ : Fin 6) := Fin.ext rfl
      conv_rhs => rw [hj]
      rw [h1408GenPerm_castSucc, hmod1408_inl, rho1408_of]
    · refine ⟨inr one2, ?_⟩
      have hj : j = 6 := Fin.ext (by simpa using heq)
      rw [hj, h1408GenPerm_last, hmod1408_inr, h1408VHom_one2]

noncomputable def hmod1408Equiv (hΛ : HSCtx) : hΛ.Hmod ≃* P1408 :=
  (MonoidHom.ofInjective (hmod1408_injective hΛ)).trans
    (MulEquiv.subgroupCongr (hmod1408_range hΛ))

theorem coe_hmod1408Equiv (hΛ : HSCtx) (x : hΛ.Hmod) :
    ((hmod1408Equiv hΛ x : P1408) : Equiv.Perm (Fin 1408)) = hmod1408 hΛ x := by
  rfl

theorem hmod1408Equiv_mem_Emod_iff (hΛ : HSCtx) (x : hΛ.Hmod) :
    x ∈ hΛ.Emod ↔ ((hmod1408Equiv hΛ x : P1408) : Equiv.Perm (Fin 1408)) ∈ blocks1408 := by
  rw [coe_hmod1408Equiv]
  exact (hmod1408_mem_blocks_iff hΛ x).symm

theorem card_P1408 (hΛ : HSCtx) : Nat.card P1408 = 177408000 := by
  have h1 : Nat.card P1408 = Nat.card hΛ.Hmod :=
    Nat.card_congr (hmod1408Equiv hΛ).symm.toEquiv
  have h2 : Nat.card hΛ.Hmod = Nat.card hΛ.Emod * hΛ.Emod.index :=
    (Subgroup.card_mul_index hΛ.Emod).symm
  have h3 : Nat.card hΛ.Emod = Nat.card HSCover :=
    (Nat.card_congr hΛ.eEmod.toEquiv).symm
  calc Nat.card P1408 = Nat.card hΛ.Hmod := h1
    _ = Nat.card hΛ.Emod * hΛ.Emod.index := h2
    _ = 88704000 * 2 := by rw [h3, hΛ.card_eq, hΛ.Emod_index]
    _ = 177408000 := by norm_num

end Model

end CFSG.EvenSporadicStandard.HNRecog
