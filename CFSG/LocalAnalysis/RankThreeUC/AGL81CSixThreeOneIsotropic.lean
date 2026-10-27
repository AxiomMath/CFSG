module

import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneReducible
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneDickson
import CFSG.LinearAlgebra.LinearGroups.QuadraticActions
import CFSG.GroupTheory.WeirSylow.Symplectic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PCoreQuotient
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open Subgroup
open CFSG.LinearGroups
open scoped Matrix

section Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem orthogonal_invariant (B : LinearMap.BilinForm K V) {T : Submodule K V}
    {H : Subgroup (Module.End K V)ˣ}
    (hiso : ∀ x ∈ H, ∀ u v : V, B ((x : Module.End K V) u) ((x : Module.End K V) v) = B u v)
    (hTH : ∀ x ∈ H, ∀ u ∈ T, (x : Module.End K V) u ∈ T) :
    ∀ x ∈ H, ∀ u ∈ B.orthogonal T, (x : Module.End K V) u ∈ B.orthogonal T := by
  intro x hx u hu
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hu ⊢
  intro t ht
  have h1 : (x : Module.End K V) (((x⁻¹ : (Module.End K V)ˣ) : Module.End K V) t) = t := by
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  rw [← h1, hiso x hx, hu]
  exact hTH x⁻¹ (H.inv_mem hx) t ht

theorem sub_mem_orthogonal_of_isometry (B : LinearMap.BilinForm K V) {x : (Module.End K V)ˣ}
    (hx : ∀ u v : V, B ((x : Module.End K V) u) ((x : Module.End K V) v) = B u v)
    {T : Submodule K V} (hfix : ∀ t ∈ T, (x : Module.End K V) t = t)
    (hfixinv : ∀ t ∈ T, (((x⁻¹ : (Module.End K V)ˣ) : Module.End K V)) t = t) (w : V) :
    (x : Module.End K V) w - w ∈ B.orthogonal T := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro t ht
  have h1 : (x : Module.End K V) (((x⁻¹ : (Module.End K V)ˣ) : Module.End K V) t) = t := by
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  have h2 : B t ((x : Module.End K V) w) = B t w := by
    conv_lhs => rw [← h1]
    rw [hx, hfixinv t ht]
  rw [map_sub, h2, sub_self]

theorem le_orthogonal_of_totallyIsotropic {B : LinearMap.BilinForm K V} {T : Submodule K V}
    (hTB : ∀ u ∈ T, ∀ v ∈ T, B u v = 0) : T ≤ B.orthogonal T := by
  intro t ht
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro s hs
  exact hTB s hs t ht

theorem totallyIsotropic_of_finrank_le_one [Module.Finite K V] {B : LinearMap.BilinForm K V}
    (hAlt : B.IsAlt) {T : Submodule K V} (hT : Module.finrank K T ≤ 1) :
    ∀ u ∈ T, ∀ v ∈ T, B u v = 0 := by
  intro u hu v hv
  obtain ⟨w, hw⟩ := finrank_le_one_iff.mp hT
  obtain ⟨c, hc⟩ := hw ⟨u, hu⟩
  obtain ⟨d, hd⟩ := hw ⟨v, hv⟩
  have hcu : u = c • (w : V) := by
    simpa using (congrArg Subtype.val hc).symm
  have hdv : v = d • (w : V) := by
    simpa using (congrArg Subtype.val hd).symm
  rw [hcu, hdv]
  simp [hAlt w]

end Orthogonal

section Nilpotent

private theorem one_add_pow_eq_one_of_pow_eq_zero {R : Type*} [Ring R] {p k : ℕ} {n : R}
    (hp : (p : R) = 0) (hprime : p.Prime) (hp2 : p ≠ 2) (hk : n ^ k = 0) (hkp : k ≤ p) :
    (1 + n) ^ p = 1 := by
  rw [(Commute.one_left n).add_pow]
  refine (Finset.sum_eq_single p ?_ ?_).trans ?_
  · intro m hm hmp
    have hmle : m ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · simp [pow_eq_zero_of_le hkp hk]
    · have hmlt : m < p := lt_of_le_of_ne hmle hmp
      obtain ⟨d, hd⟩ := hprime.dvd_choose_self hmpos.ne' hmlt
      rw [hd, Nat.cast_mul, hp, zero_mul, mul_zero]
  · intro hnot
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self p)) hnot
  · simp

private theorem units_pow_eq_one_of_pow_eq_zero {R : Type*} [Ring R] {p k : ℕ}
    (hp : (p : R) = 0) (hprime : p.Prime) (hp2 : p ≠ 2) {x : Rˣ}
    (hk : ((x : R) - 1) ^ k = 0) (hkp : k ≤ p) : x ^ p = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  have h1 : (x : R) = 1 + ((x : R) - 1) := by abel
  rw [h1]
  exact one_add_pow_eq_one_of_pow_eq_zero hp hprime hp2 hk hkp

end Nilpotent

private theorem three_le_of_prime_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : 3 ≤ p := by
  have := hp.two_le
  omega

private theorem natCast_end_eq_zero (p : ℕ) (W : Type) [AddCommGroup W] [Module (ZMod p) W] :
    (p : Module.End (ZMod p) W) = 0 := by
  rw [← map_natCast (algebraMap (ZMod p) (Module.End (ZMod p) W)),
    CharP.cast_eq_zero, map_zero]

theorem isPGroup_ker_of_pow_eq_one {p : ℕ} [Fact p.Prime] {G H : Type*} [Group G] [Group H]
    (ρ : G →* H) (h : ∀ g : G, ρ g = 1 → g ^ p = 1) : IsPGroup p ρ.ker := by
  rw [IsPGroup.iff_orderOf]
  intro g
  have hg : (g : G) ^ p = 1 := h g.1 (MonoidHom.mem_ker.mp g.2)
  have hdvd : orderOf g ∣ p := by
    rw [← Subgroup.orderOf_coe g]
    exact orderOf_dvd_of_pow_eq_one hg
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h1 | hp
  · exact ⟨0, by rw [h1, pow_zero]⟩
  · exact ⟨1, by rw [hp, pow_one]⟩

theorem isSLType_or_trivial_of_ker_isPGroup {p : ℕ} [Fact p.Prime] {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (hU : Module.finrank (ZMod p) U = 2) {G : Type} [Group G] [Finite G]
    (hG : oPPrimeHull p (⊤ : Subgroup G) = ⊤) (ρ : G →* (Module.End (ZMod p) U)ˣ)
    (hker : IsPGroup p ρ.ker) :
    IsSLType 2 (ZMod p) (G ⧸ CFSG.pCore p G) ∨ Nat.card (G ⧸ CFSG.pCore p G) = 1 := by
  have hrange : oPPrimeHull p ρ.range = ρ.range := by
    rw [MonoidHom.range_eq_map]
    exact oPPrimeHull_map_eq ρ hG
  have key :=
    sLTwoOrTrivial_of_finrank_eq_two (p := p) (sLTwoOrTrivialAt p) hU (H := ρ.range) hrange
  obtain ⟨E⟩ := nonempty_quot_pCore_mulEquiv_of_surjective (p := p) ρ.rangeRestrict
    ρ.rangeRestrict_surjective (by rwa [MonoidHom.ker_rangeRestrict])
  rcases key with h | h
  · obtain ⟨ψ⟩ := h
    exact Or.inl ⟨E.trans ψ⟩
  · exact Or.inr (by rw [Nat.card_congr E.toEquiv]; exact h)

private theorem fixes_of_finrank_eq_one {p : ℕ} [Fact p.Prime] {W : Type}
    [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    {H : Subgroup (Module.End (ZMod p) W)ˣ} {T : Submodule (ZMod p) W}
    (hH : oPPrimeHull p H = H)
    (hTH : ∀ x ∈ H, ∀ u ∈ T, (x : Module.End (ZMod p) W) u ∈ T)
    (hT1 : Module.finrank (ZMod p) T = 1) :
    ∀ x ∈ H, ∀ t ∈ T, (x : Module.End (ZMod p) W) t = t := by
  let ρT : H →* LinearMap.GeneralLinearGroup (ZMod p) T := invariantRestrict H T hTH
  have hρT : ρT = 1 :=
    monoidHom_eq_one_of_finrank_eq_one hT1 (oPPrimeHull_top_of_eq hH) ρT
  intro x hx t ht
  have h1 : ((ρT ⟨x, hx⟩ : LinearMap.GeneralLinearGroup (ZMod p) T) :
      T →ₗ[ZMod p] T) ⟨t, ht⟩ = ⟨t, ht⟩ := by
    rw [hρT]
    rfl
  have h2 := congrArg Subtype.val h1
  rwa [coe_invariantRestrict_apply] at h2

private theorem mapsTo_submoduleOf_of_fixes {p : ℕ} [Fact p.Prime] {W : Type}
    [AddCommGroup W] [Module (ZMod p) W] {U T : Submodule (ZMod p) W}
    {H : Subgroup (Module.End (ZMod p) W)ˣ}
    (hUH : ∀ x ∈ H, ∀ u ∈ U, (x : Module.End (ZMod p) W) u ∈ U)
    (hfixT : ∀ x ∈ H, ∀ t ∈ T, (x : Module.End (ZMod p) W) t = t) :
    ∀ g ∈ (invariantRestrict H U hUH).range,
      ∀ t ∈ T.submoduleOf U, (g : Module.End (ZMod p) U) t ∈ T.submoduleOf U := by
  intro g hg t ht
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hg
  have htW : (t : W) ∈ T := ht
  have hxt : (x.1 : Module.End (ZMod p) W) (t : W) = t := hfixT x x.2 (t : W) htW
  let gx : Module.End (ZMod p) U := invariantRestrict H U hUH x
  have hgx : (↑(gx t) : W) = (t : W) := by
    change (((invariantRestrict H U hUH x : LinearMap.GeneralLinearGroup (ZMod p) U)) :
      U →ₗ[ZMod p] U) t = (t : W)
    rw [coe_invariantRestrict_apply, hxt]
  change (↑(gx t) : W) ∈ T
  rw [hgx]
  exact htW

private theorem finrank_quotient_orthogonal {p : ℕ} [Fact p.Prime] {W : Type}
    [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    (hW : Module.finrank (ZMod p) W = 4) (B : LinearMap.BilinForm (ZMod p) W)
    (hBnd : ∀ u : W, (∀ v : W, B u v = 0) → u = 0) (hBalt : ∀ w : W, B w w = 0)
    {T : Submodule (ZMod p) W} (hTB : ∀ u ∈ T, ∀ v ∈ T, B u v = 0)
    (hT1 : Module.finrank (ZMod p) T = 1) :
    Module.finrank (ZMod p) (B.orthogonal T ⧸ T.submoduleOf (B.orthogonal T)) = 2 := by
  have hAlt : B.IsAlt := hBalt
  have hNd : B.Nondegenerate := CFSG.GroupTheory.WeirSylow.nondegenerate_of_isAlt hAlt hBnd
  have hdim : Module.finrank (ZMod p) (B.orthogonal T) = 3 := by
    have h := LinearMap.BilinForm.finrank_orthogonal hNd T
    rw [hW, hT1] at h
    omega
  have h := Submodule.finrank_quotient_add_finrank (T.submoduleOf (B.orthogonal T))
  have hc : Module.finrank (ZMod p) (T.submoduleOf (B.orthogonal T)) = 1 := by
    rw [← hT1]
    exact LinearEquiv.finrank_eq
      (Submodule.comapSubtypeEquivOfLe (le_orthogonal_of_totallyIsotropic hTB))
  omega

private theorem units_pow_eq_one_of_cube_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    {T U : Submodule (ZMod p) W} {xu : (Module.End (ZMod p) W)ˣ}
    (hfixT : ∀ t ∈ T, (xu : Module.End (ZMod p) W) t = t)
    (himgW : ∀ w : W, ((xu : Module.End (ZMod p) W) - 1) w ∈ U)
    (himgU : ∀ u ∈ U, ((xu : Module.End (ZMod p) W) - 1) u ∈ T) :
    xu ^ p = 1 := by
  have hkill : ∀ t ∈ T, ((xu : Module.End (ZMod p) W) - 1) t = 0 := by
    intro t ht
    rw [LinearMap.sub_apply, hfixT t ht, Module.End.one_apply, sub_self]
  have hcube : ((xu : Module.End (ZMod p) W) - 1) ^ 3 = 0 := by
    rw [pow_three]
    ext w
    rw [Module.End.mul_apply, Module.End.mul_apply, LinearMap.zero_apply]
    exact hkill _ (himgU _ (himgW w))
  exact units_pow_eq_one_of_pow_eq_zero (natCast_end_eq_zero p W) (Fact.out) hp2 hcube
    (three_le_of_prime_ne_two Fact.out hp2)

private theorem exists_quotient_action_of_finrank_eq_one {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    [Module.Finite (ZMod p) W] (B : LinearMap.BilinForm (ZMod p) W)
    {H : Subgroup (Module.End (ZMod p) W)ˣ}
    (hiso : ∀ x ∈ H, ∀ u v : W,
      B ((x : Module.End (ZMod p) W) u) ((x : Module.End (ZMod p) W) v) = B u v)
    {T : Submodule (ZMod p) W}
    (hTH : ∀ x ∈ H, ∀ u ∈ T, (x : Module.End (ZMod p) W) u ∈ T)
    (hfixT : ∀ x ∈ H, ∀ t ∈ T, (x : Module.End (ZMod p) W) t = t) :
    ∃ ρ : H →* (Module.End (ZMod p) (B.orthogonal T ⧸ T.submoduleOf
      (B.orthogonal T)))ˣ, IsPGroup p ρ.ker := by
  classical
  let U := B.orthogonal T
  have hUH : ∀ x ∈ H, ∀ u ∈ U, (x : Module.End (ZMod p) W) u ∈ U :=
    orthogonal_invariant B hiso hTH
  let ρU : H →* LinearMap.GeneralLinearGroup (ZMod p) U := invariantRestrict H U hUH
  have hTUfix : ∀ g ∈ ρU.range, ∀ t ∈ T.submoduleOf U,
      (g : Module.End (ZMod p) U) t ∈ T.submoduleOf U :=
    mapsTo_submoduleOf_of_fixes hUH hfixT
  let ρ : H →* LinearMap.GeneralLinearGroup (ZMod p) (U ⧸ T.submoduleOf U) :=
    (invariantQuotient ρU.range (T.submoduleOf U) hTUfix).comp ρU.rangeRestrict
  refine ⟨ρ, ?_⟩
  refine isPGroup_ker_of_pow_eq_one ρ ?_
  intro x hx
  let xu : (Module.End (ZMod p) W)ˣ := x
  have hfixT' : ∀ t ∈ T, (xu : Module.End (ZMod p) W) t = t := hfixT x x.2
  have himgW : ∀ w : W, ((xu : Module.End (ZMod p) W) - 1) w ∈ U := fun w =>
    sub_mem_orthogonal_of_isometry B (hiso x x.2) hfixT'
      (fun t ht => hfixT x⁻¹ (H.inv_mem x.2) t ht) w
  have himgU : ∀ u ∈ U, ((xu : Module.End (ZMod p) W) - 1) u ∈ T := by
    intro u hu
    have h1 : (((invariantQuotient ρU.range (T.submoduleOf U) hTUfix)
        (ρU.rangeRestrict x) : LinearMap.GeneralLinearGroup
          (ZMod p) (U ⧸ T.submoduleOf U)) :
        (U ⧸ T.submoduleOf U) →ₗ[ZMod p] U ⧸ T.submoduleOf U)
        (Submodule.Quotient.mk ⟨u, hu⟩) = Submodule.Quotient.mk ⟨u, hu⟩ := by
      change ((ρ x : LinearMap.GeneralLinearGroup (ZMod p)
        (U ⧸ T.submoduleOf U)) : (U ⧸ T.submoduleOf U) →ₗ[ZMod p]
          U ⧸ T.submoduleOf U) (Submodule.Quotient.mk ⟨u, hu⟩) =
        Submodule.Quotient.mk ⟨u, hu⟩
      rw [hx]
      rfl
    rw [invariantQuotient_apply_mk] at h1
    have hmem : ((((ρU x : Module.End (ZMod p) U) ⟨u, hu⟩ - ⟨u, hu⟩ : U)) : W) ∈ T :=
      (Submodule.Quotient.eq (T.submoduleOf U)).mp h1
    have hval : ((((ρU x : Module.End (ZMod p) U) ⟨u, hu⟩ - ⟨u, hu⟩ : U)) : W) =
        (xu : Module.End (ZMod p) W) u - u := by
      rw [Submodule.coe_sub, coe_invariantRestrict_apply]
    change (xu : Module.End (ZMod p) W) u - u ∈ T
    rw [← hval]
    exact hmem
  have hxpow : xu ^ p = 1 := units_pow_eq_one_of_cube_zero hp2 hfixT' himgW himgU
  apply Subtype.ext
  simpa [xu] using hxpow

private theorem isSLType_or_trivial_of_finrank_eq_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {W : Type} [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    (hW : Module.finrank (ZMod p) W = 4) (B : LinearMap.BilinForm (ZMod p) W)
    (hBnd : ∀ u : W, (∀ v : W, B u v = 0) → u = 0) (hBalt : ∀ w : W, B w w = 0)
    {H : Subgroup (Module.End (ZMod p) W)ˣ} (hH : oPPrimeHull p H = H)
    (hiso : ∀ x ∈ H, ∀ u v : W,
      B ((x : Module.End (ZMod p) W) u) ((x : Module.End (ZMod p) W) v) = B u v)
    {T : Submodule (ZMod p) W} (hTB : ∀ u ∈ T, ∀ v ∈ T, B u v = 0)
    (hTH : ∀ x ∈ H, ∀ u ∈ T, (x : Module.End (ZMod p) W) u ∈ T)
    (hT1 : Module.finrank (ZMod p) T = 1) :
    IsSLType 2 (ZMod p) (↥H ⧸ CFSG.pCore p ↥H) ∨ Nat.card (↥H ⧸ CFSG.pCore p ↥H) = 1 := by
  have hfixT : ∀ x ∈ H, ∀ t ∈ T, (x : Module.End (ZMod p) W) t = t :=
    fixes_of_finrank_eq_one hH hTH hT1
  obtain ⟨ρ, hker⟩ := exists_quotient_action_of_finrank_eq_one hp2 B hiso hTH hfixT
  have hdim := finrank_quotient_orthogonal hW B hBnd hBalt hTB hT1
  exact isSLType_or_trivial_of_ker_isPGroup (p := p) hdim (oPPrimeHull_top_of_eq hH) ρ hker

private theorem orthogonal_eq_self_of_finrank_eq_two {p : ℕ} [Fact p.Prime] {W : Type}
    [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    (hW : Module.finrank (ZMod p) W = 4) (B : LinearMap.BilinForm (ZMod p) W)
    (hBnd : ∀ u : W, (∀ v : W, B u v = 0) → u = 0) (hBalt : ∀ w : W, B w w = 0)
    {T : Submodule (ZMod p) W} (hTB : ∀ u ∈ T, ∀ v ∈ T, B u v = 0)
    (hT2 : Module.finrank (ZMod p) T = 2) : B.orthogonal T = T := by
  have hAlt : B.IsAlt := hBalt
  have hNd : B.Nondegenerate := CFSG.GroupTheory.WeirSylow.nondegenerate_of_isAlt hAlt hBnd
  have hTle : T ≤ B.orthogonal T := le_orthogonal_of_totallyIsotropic hTB
  refine (Submodule.eq_of_le_of_finrank_eq hTle ?_).symm
  have h := LinearMap.BilinForm.finrank_orthogonal hNd T
  rw [hW, hT2] at h
  omega

private theorem isSLType_or_trivial_of_finrank_eq_two {p : ℕ} [Fact p.Prime] {W : Type}
    [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    (hW : Module.finrank (ZMod p) W = 4) (B : LinearMap.BilinForm (ZMod p) W)
    (hBnd : ∀ u : W, (∀ v : W, B u v = 0) → u = 0) (hBalt : ∀ w : W, B w w = 0)
    {H : Subgroup (Module.End (ZMod p) W)ˣ} (hH : oPPrimeHull p H = H)
    (hiso : ∀ x ∈ H, ∀ u v : W,
      B ((x : Module.End (ZMod p) W) u) ((x : Module.End (ZMod p) W) v) = B u v)
    {T : Submodule (ZMod p) W} (hTB : ∀ u ∈ T, ∀ v ∈ T, B u v = 0)
    (hTH : ∀ x ∈ H, ∀ u ∈ T, (x : Module.End (ZMod p) W) u ∈ T)
    (hT2 : Module.finrank (ZMod p) T = 2) :
    IsSLType 2 (ZMod p) (↥H ⧸ CFSG.pCore p ↥H) ∨ Nat.card (↥H ⧸ CFSG.pCore p ↥H) = 1 := by
  classical
  have hTeq : B.orthogonal T = T := orthogonal_eq_self_of_finrank_eq_two hW B hBnd hBalt hTB hT2
  let ρ : H →* LinearMap.GeneralLinearGroup (ZMod p) T := invariantRestrict H T hTH
  have hker : IsPGroup p ρ.ker := by
    refine isPGroup_ker_of_pow_eq_one ρ ?_
    intro x hx
    let xu : (Module.End (ZMod p) W)ˣ := x
    have hfix : ∀ t ∈ T, (xu : Module.End (ZMod p) W) t = t := by
      intro t ht
      have h1 : ((ρ x : LinearMap.GeneralLinearGroup (ZMod p) T) : T →ₗ[ZMod p] T)
          ⟨t, ht⟩ = ⟨t, ht⟩ := by
        rw [hx]
        rfl
      have h2 := congrArg Subtype.val h1
      rwa [coe_invariantRestrict_apply] at h2
    have hxinv : ρ (x⁻¹ : H) = 1 := by rw [map_inv, hx, inv_one]
    have hfixinv : ∀ t ∈ T,
        (((x⁻¹ : H) : (Module.End (ZMod p) W)ˣ) : Module.End (ZMod p) W) t = t := by
      intro t ht
      have h1 : ((ρ (x⁻¹ : H) : LinearMap.GeneralLinearGroup (ZMod p) T) :
          T →ₗ[ZMod p] T) ⟨t, ht⟩ = ⟨t, ht⟩ := by
        rw [hxinv]
        rfl
      have h2 := congrArg Subtype.val h1
      rwa [coe_invariantRestrict_apply] at h2
    have himg : ∀ w : W, ((xu : Module.End (ZMod p) W) - 1) w ∈ T := by
      intro w
      have h := sub_mem_orthogonal_of_isometry B (hiso x x.2) hfix hfixinv w
      rwa [hTeq] at h
    have hkill : ∀ t ∈ T, ((xu : Module.End (ZMod p) W) - 1) t = 0 := by
      intro t ht
      rw [LinearMap.sub_apply, hfix t ht, Module.End.one_apply, sub_self]
    have hsq : ((xu : Module.End (ZMod p) W) - 1) ^ 2 = 0 := by
      rw [pow_two]
      ext w
      rw [Module.End.mul_apply, LinearMap.zero_apply]
      exact hkill _ (himg w)
    have hxpow : xu ^ p = 1 := (quadratic_linear_p_elements p xu hsq).1
    apply Subtype.ext
    simpa [xu] using hxpow
  exact isSLType_or_trivial_of_ker_isPGroup (p := p) hT2 (oPPrimeHull_top_of_eq hH) ρ hker

theorem sl2_or_trivial_of_isotropic_invariant {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {W : Type}
    [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    (hW : Module.finrank (ZMod p) W = 4) (B : LinearMap.BilinForm (ZMod p) W)
    (hBnd : ∀ u : W, (∀ v : W, B u v = 0) → u = 0) (hBalt : ∀ w : W, B w w = 0)
    {H : Subgroup (Module.End (ZMod p) W)ˣ} (hH : oPPrimeHull p H = H)
    (hiso : ∀ x ∈ H, ∀ u v : W,
      B ((x : Module.End (ZMod p) W) u) ((x : Module.End (ZMod p) W) v) = B u v)
    {T : Submodule (ZMod p) W} (hT0 : T ≠ ⊥) (hTB : ∀ u ∈ T, ∀ v ∈ T, B u v = 0)
    (hTH : ∀ x ∈ H, ∀ u ∈ T, (x : Module.End (ZMod p) W) u ∈ T) :
    IsSLType 2 (ZMod p) (↥H ⧸ CFSG.pCore p ↥H) ∨ Nat.card (↥H ⧸ CFSG.pCore p ↥H) = 1 := by
  have hAlt : B.IsAlt := hBalt
  have hNd : B.Nondegenerate := CFSG.GroupTheory.WeirSylow.nondegenerate_of_isAlt hAlt hBnd
  have hTle : T ≤ B.orthogonal T := le_orthogonal_of_totallyIsotropic hTB
  have hdim : Module.finrank (ZMod p) T + Module.finrank (ZMod p) (B.orthogonal T) = 4 := by
    have h := LinearMap.BilinForm.finrank_orthogonal hNd T
    rw [hW] at h
    have hle : Module.finrank (ZMod p) T ≤ 4 := by
      simpa [hW] using Submodule.finrank_le (R := ZMod p) (M := W) T
    omega
  have hTpos : 1 ≤ Module.finrank (ZMod p) T := by
    rw [Submodule.one_le_finrank_iff]
    exact hT0
  have hTdimle : Module.finrank (ZMod p) T ≤ 2 := by
    have := Submodule.finrank_mono hTle
    omega
  rcases lt_or_eq_of_le hTdimle with hlt | hT2
  · have hT1 : Module.finrank (ZMod p) T = 1 := by omega
    exact isSLType_or_trivial_of_finrank_eq_one hp2 hW B hBnd hBalt hH hiso hTB hTH hT1
  · exact isSLType_or_trivial_of_finrank_eq_two hW B hBnd hBalt hH hiso hTB hTH hT2

theorem exists_orthogonal_planes_of_reducible {p : ℕ} [Fact p.Prime] {W : Type}
    [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    (hW : Module.finrank (ZMod p) W = 4) (B : LinearMap.BilinForm (ZMod p) W)
    (hBnd : ∀ u : W, (∀ v : W, B u v = 0) → u = 0) (hBalt : ∀ w : W, B w w = 0)
    {H : Subgroup (Module.End (ZMod p) W)ˣ}
    (hiso : ∀ x ∈ H, ∀ u v : W,
      B ((x : Module.End (ZMod p) W) u) ((x : Module.End (ZMod p) W) v) = B u v)
    {U : Submodule (ZMod p) W} (hU0 : U ≠ ⊥) (hU1 : U ≠ ⊤)
    (hUH : ∀ x ∈ H, ∀ u ∈ U, (x : Module.End (ZMod p) W) u ∈ U)
    (hno : ∀ T : Submodule (ZMod p) W, T ≠ ⊥ → (∀ u ∈ T, ∀ v ∈ T, B u v = 0) →
      ¬ ∀ x ∈ H, ∀ u ∈ T, (x : Module.End (ZMod p) W) u ∈ T) :
    ∃ U₁ U₂ : Submodule (ZMod p) W, IsCompl U₁ U₂ ∧ Module.finrank (ZMod p) U₁ = 2 ∧
      Module.finrank (ZMod p) U₂ = 2 ∧ (∀ u ∈ U₁, ∀ v ∈ U₂, B u v = 0) ∧
      (∀ x ∈ H, ∀ u ∈ U₁, (x : Module.End (ZMod p) W) u ∈ U₁) ∧
      (∀ x ∈ H, ∀ u ∈ U₂, (x : Module.End (ZMod p) W) u ∈ U₂) := by
  classical
  have hAlt : B.IsAlt := hBalt
  have hNd : B.Nondegenerate := CFSG.GroupTheory.WeirSylow.nondegenerate_of_isAlt hAlt hBnd
  set U₂ := B.orthogonal U with hU₂def
  have hU₂H : ∀ x ∈ H, ∀ u ∈ U₂, (x : Module.End (ZMod p) W) u ∈ U₂ :=
    orthogonal_invariant B hiso hUH
  have hdim : Module.finrank (ZMod p) U + Module.finrank (ZMod p) U₂ = 4 := by
    have h := LinearMap.BilinForm.finrank_orthogonal hNd U
    rw [hW, ← hU₂def] at h
    have hle : Module.finrank (ZMod p) U ≤ 4 := by
      simpa [hW] using Submodule.finrank_le (R := ZMod p) (M := W) U
    omega
  have hUpos : 1 ≤ Module.finrank (ZMod p) U := by
    rw [Submodule.one_le_finrank_iff]
    exact hU0
  have hUle : Module.finrank (ZMod p) U ≤ 3 := by
    have hlt : Module.finrank (ZMod p) U < Module.finrank (ZMod p) W := by
      simpa [hW] using Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne le_top hU1)
    omega
  have hUinf : U ⊓ U₂ = ⊥ := by
    by_contra hne
    exact hno (U ⊓ U₂) hne
      (fun u hu v hv => (LinearMap.BilinForm.mem_orthogonal_iff.mp hv.2) u hu.1)
      (fun x hx u hu => ⟨hUH x hx u hu.1, hU₂H x hx u hu.2⟩)
  have hUnot1 : Module.finrank (ZMod p) U ≠ 1 := by
    intro h1
    exact hno U hU0 (totallyIsotropic_of_finrank_le_one hAlt (by omega)) hUH
  have hUnot3 : Module.finrank (ZMod p) U ≠ 3 := by
    intro h3
    have hU₂dim1 : Module.finrank (ZMod p) U₂ = 1 := by omega
    refine hno U₂ ?_ (totallyIsotropic_of_finrank_le_one hAlt (by omega)) hU₂H
    intro hbot
    have h0 : Module.finrank (ZMod p) U₂ = 0 :=
      (Submodule.finrank_eq_zero (R := ZMod p) (M := W) (S := U₂)).mpr hbot
    omega
  have hUdim2 : Module.finrank (ZMod p) U = 2 := by omega
  have hU₂dim2 : Module.finrank (ZMod p) U₂ = 2 := by omega
  have hcompl : IsCompl U U₂ := by
    refine ⟨disjoint_iff.mpr hUinf, codisjoint_iff.mpr ?_⟩
    have hsup : Module.finrank (ZMod p) ↥(U ⊔ U₂) = 4 := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq U U₂
      have h0 : Module.finrank (ZMod p) (⊥ : Submodule (ZMod p) W) = 0 :=
        finrank_bot (ZMod p) W
      rw [hUinf, h0, hdim] at h
      omega
    exact Submodule.eq_top_of_finrank_eq (by rw [hsup, hW])
  exact ⟨U, U₂, hcompl, hUdim2, hU₂dim2,
    (fun u hu v hv => (LinearMap.BilinForm.mem_orthogonal_iff.mp hv) u hu), hUH, hU₂H⟩

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
