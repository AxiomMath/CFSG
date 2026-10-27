module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelCheckDefs

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf

noncomputable def sigmaThetaEquiv : A5 × A5 ≃* A5 × A5 :=
  ((MulEquiv.prodCongr iota iota).trans thetaEquiv).trans
    (MulEquiv.prodCongr iota.symm iota.symm)

theorem sigmaThetaEquiv_apply (g : A5 × A5) :
    sigmaThetaEquiv g =
      (iota.symm (frobSL (iota g.2)), iota.symm (frobSL (iota g.1))) := by
  rfl

private lemma polarBilin_map_eq {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    {q : QuadraticForm (ZMod 2) W} {f : W ≃ₗ[ZMod 2] W} (hf : ∀ v, q (f v) = q v)
    (x y : W) : q.polarBilin (f x) (f y) = q.polarBilin x y := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar, QuadraticMap.polar, ← map_add f x y, hf, hf, hf]

theorem b0_conj_sigma0 (g : A5 × A5) : b0 * sigma0 g * b0⁻¹ = sigma0 (sigmaThetaEquiv g) := by
  have hb0 : b0 * b0 = 1 := by
    apply LinearEquiv.ext
    intro M
    rw [LinearEquiv.mul_apply]
    exact b0Fun_b0Fun M
  have hbinv : b0⁻¹ = b0 := inv_eq_of_mul_eq_one_right hb0
  apply LinearEquiv.ext
  intro v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hbinv]
  change b0Fun (actFun (iota g.1, iota g.2) (b0Fun v)) =
    sigma0 (sigmaThetaEquiv g) v
  rw [b0Fun_actFun, b0Fun_b0Fun]
  rw [sigma0_apply, sigmaThetaEquiv_apply]
  simp only [thetaB0, MulEquiv.apply_symm_apply]

theorem swapsFactorsAut_sigmaThetaEquiv : Swap.SwapsFactorsAut sigmaThetaEquiv := by
  constructor
  · intro x
    exact ⟨iota.symm (frobSL (iota x)), by rw [sigmaThetaEquiv_apply]; simp [frobSL_one]⟩
  · intro y
    exact ⟨iota.symm (frobSL (iota y)), by rw [sigmaThetaEquiv_apply]; simp [frobSL_one]⟩

theorem swapsFactors_b0 : Swap.SwapsFactors sigma0 b0 :=
  Swap.swapsFactors_of_aut sigma0 b0 sigmaThetaEquiv swapsFactorsAut_sigmaThetaEquiv
    b0_conj_sigma0

theorem cSideFreeSwap_b0 (h : cSideModelProp) : cSideFreeSwap q0 sigma0 b0 := by
  classical
  have hK6a : cSideK6a := h.2.2.2.2.2.1
  have hneg : ∀ M : V0, -M = M := fun M => by
    rw [← neg_one_smul (ZMod 2) M, show (-1 : ZMod 2) = 1 by decide, one_smul]
  have hfix : ∀ M : V0, M ∈ LinearMap.ker ((b0 : V0 →ₗ[ZMod 2] V0) + 1) ↔ b0Fun M = M := by
    intro M
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply]
    constructor
    · intro hM
      have h2 : b0Fun M = -M := (add_eq_zero_iff_eq_neg).mp hM
      rwa [hneg M] at h2
    · intro hM
      change b0Fun M + M = 0
      rw [hM]
      exact (neg_eq_iff_add_eq_zero).mp (hneg M)
  have hker : Nat.card (LinearMap.ker ((b0 : V0 →ₗ[ZMod 2] V0) + 1)) = 16 := by
    rw [Nat.card_eq_fintype_card]
    let e : LinearMap.ker ((b0 : V0 →ₗ[ZMod 2] V0) + 1) ≃ {M : V0 // b0Fun M = M} :=
      { toFun := fun M => ⟨M.1, (hfix M.1).mp M.2⟩
        invFun := fun M => ⟨M.1, (hfix M.1).mpr M.2⟩
        left_inv := fun M => Subtype.ext rfl
        right_inv := fun M => Subtype.ext rfl }
    rw [Fintype.card_congr e, Fintype.card_subtype]
    exact hK6a.2
  have hfindim : finrank (ZMod 2) (LinearMap.ker ((b0 : V0 →ₗ[ZMod 2] V0) + 1)) = 4 := by
    haveI : FiniteDimensional (ZMod 2) V0 := Module.Finite.of_finite
    have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := LinearMap.ker ((b0 : V0 →ₗ[ZMod 2] V0) + 1))
    rw [hker, Nat.card_zmod] at hcard
    have h24 : 2 ^ finrank (ZMod 2) (LinearMap.ker ((b0 : V0 →ₗ[ZMod 2] V0) + 1)) =
        (2 : ℕ) ^ (4 : ℕ) := by
      rw [← hcard]
      norm_num
    exact Nat.pow_right_injective (a := 2) (by norm_num) h24
  have hfree : 4 ≤ finrank (ZMod 2) (LinearMap.range ((b0 : V0 →ₗ[ZMod 2] V0) + 1)) := by
    haveI : FiniteDimensional (ZMod 2) V0 := Module.Finite.of_finite
    have hrn := LinearMap.finrank_range_add_finrank_ker ((b0 : V0 →ₗ[ZMod 2] V0) + 1)
    rw [hfindim, finrank_V0] at hrn
    have : finrank (ZMod 2) (LinearMap.range ((b0 : V0 →ₗ[ZMod 2] V0) + 1)) = 4 := by
      omega
    exact le_of_eq this.symm
  refine ⟨?_, ?_, swapsFactors_b0, hfree⟩
  · apply LinearEquiv.ext
    intro M
    rw [LinearEquiv.mul_apply]
    exact b0Fun_b0Fun M
  · intro M
    exact hK6a.1 M

theorem exists_eq_sigma0_mul_b0 (h : cSideModelProp) {b : V0 ≃ₗ[ZMod 2] V0}
    (hb : cSideFreeSwap q0 sigma0 b) : ∃ m : A5 × A5, b = sigma0 m * b0 := by
  obtain ⟨hb2, hbq, hbsw, hbfree⟩ := hb
  obtain ⟨hb0sq, hb0q, hb0sw, hb0free⟩ := cSideFreeSwap_b0 h
  exact Swap.exists_mul_of_swap_free sigma0 stdHyp_sigma0 q0.polarBilin q0_nondegenerate
    (fun g => polarBilin_map_eq (q0_sigma0 g)) hb2 hb0sq
    (polarBilin_map_eq hbq) (polarBilin_map_eq hb0q) hbsw hb0sw hbfree hb0free

end CFSG.EvenSporadicStandard.HNRecog.CSide
