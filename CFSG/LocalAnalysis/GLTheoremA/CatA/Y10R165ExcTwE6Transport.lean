module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.E6HeisScBase
public import CFSG.LieType.SeitzGeneration.ExcWideThree.G2
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6Transport

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LieType.Steinberg.Exceptional


variable {n : ℕ} {k k₁ k₂ : Type} [Field k] [Field k₁] [Field k₂]

private theorem scPhi_xm (ι : k →+* k₁) {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    (c : k) :
    scPhi ι (e6Data_valid.xm k γ c) = e6Data_valid.xm k₁ γ (ι c) :=
  Subtype.ext (units_map_xu ι e6Data_valid γ c)

private theorem scPhi_comp (ι : k →+* k₁) (ι₁ : k₁ →+* k₂) :
    (scPhi ι₁).comp (scPhi ι) = scPhi (ι₁.comp ι) := by
  refine minGroup_hom_eq_of_gens e6Data_valid _ _ fun γ hγ c => ?_
  simp only [MonoidHom.comp_apply]
  rw [scPhi_xm ι hγ, scPhi_xm ι₁ hγ, scPhi_xm (ι₁.comp ι) hγ]
  rfl

private theorem scPhi_id : scPhi (RingHom.id k) = MonoidHom.id ↥(e6Data_valid.minGroup k) := by
  refine minGroup_hom_eq_of_gens e6Data_valid _ _ fun γ hγ c => ?_
  simp only [MonoidHom.id_apply]
  rw [scPhi_xm (RingHom.id k) hγ]
  rfl

theorem scPhi_sigma {θ : k →+* k} {θ₁ : k₁ →+* k₁}
    (hθ : ∀ c, θ c = c ^ 2 ^ n) (hθ₁ : ∀ c, θ₁ c = c ^ 2 ^ n) (e : k ≃+* k₁) :
    (scPhi e.toRingHom).comp (sigma k θ) = (sigma k₁ θ₁).comp (scPhi e.toRingHom) := by
  refine minGroup_hom_eq_of_gens e6Data_valid _ _ fun γ hγ c => ?_
  simp only [MonoidHom.comp_apply]
  rw [sigma_xm θ hγ c, scPhi_xm e.toRingHom hγ, scPhi_xm e.toRingHom (isRoot_rho hγ),
    sigma_xm θ₁ hγ (e.toRingHom c), map_mul, map_intCast, hθ c, map_pow,
    hθ₁ (e.toRingHom c)]

private theorem scPhi_symm_comp (e : k ≃+* k₁) :
    (scPhi e.symm.toRingHom).comp (scPhi e.toRingHom) =
      MonoidHom.id ↥(e6Data_valid.minGroup k) := by
  rw [scPhi_comp]
  have h : e.symm.toRingHom.comp e.toRingHom = RingHom.id k :=
    RingHom.ext fun c => by simp
  rw [h, scPhi_id]

private theorem scPhi_comp_symm (e : k ≃+* k₁) :
    (scPhi e.toRingHom).comp (scPhi e.symm.toRingHom) =
      MonoidHom.id ↥(e6Data_valid.minGroup k₁) := by
  rw [scPhi_comp]
  have h : e.toRingHom.comp e.symm.toRingHom = RingHom.id k₁ :=
    RingHom.ext fun c => by simp
  rw [h, scPhi_id]

private noncomputable def fixedGroupMap {θ : k →+* k} {θ₁ : k₁ →+* k₁}
    (hθ : ∀ c, θ c = c ^ 2 ^ n) (hθ₁ : ∀ c, θ₁ c = c ^ 2 ^ n) (e : k ≃+* k₁) :
    ↥(fixedGroup k θ) →* ↥(fixedGroup k₁ θ₁) where
  toFun x :=
    ⟨scPhi e.toRingHom x, by
      rw [mem_fixedGroup]
      have h := congrArg (fun f : ↥(e6Data_valid.minGroup k) →* ↥(e6Data_valid.minGroup k₁) =>
        f (x : e6Data_valid.minGroup k)) (scPhi_sigma hθ hθ₁ e)
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, x.2] at h
      exact h.symm⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)

noncomputable def fixedGroupMulEquiv {θ : k →+* k} {θ₁ : k₁ →+* k₁}
    (hθ : ∀ c, θ c = c ^ 2 ^ n)
    (hθ₁ : ∀ c, θ₁ c = c ^ 2 ^ n) (e : k ≃+* k₁) :
    ↥(fixedGroup k θ) ≃* ↥(fixedGroup k₁ θ₁) where
  toFun := fixedGroupMap hθ hθ₁ e
  invFun := fixedGroupMap hθ₁ hθ e.symm
  left_inv x := by
    refine Subtype.ext ?_
    exact congrArg (fun f : ↥(e6Data_valid.minGroup k) →* ↥(e6Data_valid.minGroup k) =>
      f (x : e6Data_valid.minGroup k)) (scPhi_symm_comp e)
  right_inv x := by
    refine Subtype.ext ?_
    exact congrArg (fun f : ↥(e6Data_valid.minGroup k₁) →* ↥(e6Data_valid.minGroup k₁) =>
      f (x : e6Data_valid.minGroup k₁)) (scPhi_comp_symm e)
  map_mul' x y := map_mul (fixedGroupMap hθ hθ₁ e) x y

noncomputable def fixedGroupMulEquiv_galois [Finite k] (hn : 1 ≤ n) (θ : k →+* k)
    (hk : Nat.card k = (2 ^ n) ^ 2) (hθ : ∀ c, θ c = c ^ 2 ^ n) :
    ↥(fixedGroup k θ) ≃*
      ↥(fixedGroup (GaloisField 2 (2 * n)) (frobQ 2 n)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  letI : Fintype k := Fintype.ofFinite k
  letI : Fintype (GaloisField 2 (2 * n)) := Fintype.ofFinite _
  have hcard : Fintype.card k = Fintype.card (GaloisField 2 (2 * n)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hk,
      GaloisField.card 2 (2 * n) (by omega), ← pow_mul, mul_comm]
  exact fixedGroupMulEquiv hθ (fun c => frobQ_apply 2 n c) (FiniteField.ringEquivOfCardEq hcard)

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6Transport
