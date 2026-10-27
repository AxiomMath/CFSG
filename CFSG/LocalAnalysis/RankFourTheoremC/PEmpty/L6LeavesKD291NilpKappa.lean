module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofAutSL
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseAMat

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291N

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.RankFourTheoremC (l212in_lift_linear l212in_conjAut_eq_one
  l212in_dvd_of_pow_mem)

theorem lift_kappa {p : ℕ} (hp : p.Prime) (hn : 3 ≤ p) {K : Type} [Field K] [Finite K]
    {ŷ : GL (Fin p) K} {ω : K}
    (hŷ : ((ŷ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) ^ p = Matrix.scalar (Fin p) ω)
    (hω : ∀ b : K, b ^ p ≠ ω) (α : MulAut (projectiveSL p K))
    (hα : α * conjAut p K ŷ = conjAut p K ŷ * α) :
    ∃ Ã : SpecialLinearGroup (Fin p) K →* SpecialLinearGroup (Fin p) K,
      (∀ s, proj p K (Ã s) = α (proj p K s)) ∧ ∀ z ∈ scalars p K, Ã z = z := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨κ, Ã, t, hπÃ, hÃker, hΦt, hdet⟩ := l212in_lift_linear hn α
  refine ⟨Ã, hπÃ, fun z hz => ?_⟩
  have hz' : z ∈ (proj p K).ker := by rw [ker_proj]; exact hz
  rw [hÃker z hz']
  have h1 : conjAut p K (t ŷ) = conjAut p K ŷ := by
    rw [← hΦt, hα, mul_inv_cancel_right]
  have h2 : conjAut p K (ŷ⁻¹ * t ŷ) = 1 := by
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  obtain ⟨c, hc⟩ := l212in_conjAut_eq_one hn (ŷ⁻¹ * t ŷ) h2
  have hnotpow : ¬ ∃ c : Kˣ, GeneralLinearGroup.det ŷ = c ^ p := by
    rintro ⟨c, hc'⟩
    refine I292CaseA.not_pow_det hp hp2 hŷ hω (c : K) ?_
    have := congrArg (fun u : Kˣ => (u : K)) hc'
    simpa [GeneralLinearGroup.val_det_apply, Units.val_pow_eq_pow_val] using this.symm
  have hBb : ∃ c' : Kˣ, GeneralLinearGroup.det ŷ ^ (κ - 1) = c' ^ p := by
    refine ⟨c, ?_⟩
    have h3 : GeneralLinearGroup.det ŷ ^ κ = GeneralLinearGroup.det ŷ * c ^ p := by
      rw [← hdet ŷ, ← hc, map_mul, map_inv]
      group
    calc GeneralLinearGroup.det ŷ ^ (κ - 1)
        = GeneralLinearGroup.det ŷ ^ κ * (GeneralLinearGroup.det ŷ)⁻¹ := zpow_sub_one _ _
      _ = GeneralLinearGroup.det ŷ * c ^ p * (GeneralLinearGroup.det ŷ)⁻¹ := by rw [h3]
      _ = c ^ p := by rw [mul_right_comm, mul_inv_cancel, one_mul]
  have hpdvd : (p : ℤ) ∣ κ - 1 :=
    l212in_dvd_of_pow_mem hp hnotpow ⟨GeneralLinearGroup.det ŷ, rfl⟩ hBb
  obtain ⟨m, hm⟩ := hpdvd
  have hκ1 : κ = 1 + (p : ℤ) * m := by omega
  have hzp : z ^ p = 1 := by
    obtain ⟨c0, hc0, hz0⟩ := mem_scalars.1 hz
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hz0, ← map_pow, ← Units.val_pow_eq_pow_val, hc0]
    simp
  rw [hκ1, _root_.zpow_add, _root_.zpow_one, _root_.zpow_mul, _root_.zpow_natCast, hzp,
    _root_.one_zpow, mul_one]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291N
