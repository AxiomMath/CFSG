module

public import CFSG.LocalAnalysis.ABGTheoremB.Statements
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.NotPGroupInputs

public section

namespace CFSG.ABGTheoremB.TotallyInverted

open CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem abg_IV_6_2_of_propIV62 {σ : Setting G} (h : σ.PropIV62) {r : ℕ} (hr : r.Prime)
    (hdvd : r ∣ Nat.card σ.ON) : ABG_IV_6_2 σ r := by
  intro H hH R₁ hR₁ hR₁p hle hD hcov hX
  refine h r hr hdvd H hH R₁ hR₁ hR₁p hle hD ?_ hX
  intro g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp (hcov hg)
  have hbH : b ∈ H := oddCoreIn_le H hb
  have haH : a ∈ H := by
    have h1 : a * b * b⁻¹ ∈ H := H.mul_mem hg (H.inv_mem hbH)
    rwa [mul_inv_cancel_right] at h1
  exact Set.mul_mem_mul ⟨haH, ha⟩ hb

end CFSG.ABGTheoremB.TotallyInverted
