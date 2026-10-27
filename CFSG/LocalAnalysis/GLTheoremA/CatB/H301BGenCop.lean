module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.CoprimeDecomp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open scoped commutatorElement

section Planes

variable {X : Type*} [Group X] [Finite X]

theorem commute_of_trivial_free {p : ℕ} [Fact p.Prime] {b : X} {P Q Z : Subgroup X}
    (hb : IsPGroup p (Subgroup.zpowers b)) (hQb : b ∈ Subgroup.normalizer (Q : Set X))
    (hQp : Nat.Coprime p (Nat.card Q)) (hQfree : ∀ q ∈ Q, b * q = q * b → q ∈ Z)
    (hPb : ∀ x ∈ P, b * x = x * b) (hPQ : ∀ x ∈ P, ∀ q ∈ Q, ⁅x, q⁆ ∈ Z)
    (hZb : ∀ z ∈ Z, b * z = z * b) (hZQ : ∀ z ∈ Z, ∀ q ∈ Q, q * z = z * q)
    (hZP : ∀ z ∈ Z, ∀ x ∈ P, x * z = z * x) :
    ∀ x ∈ P, ∀ q ∈ Q, x * q = q * x := by
  intro x hx
  have hdec := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.le_sup_centralizer_commutator hb
    (by rwa [Subgroup.zpowers_le]) hQp
  have hcomm : ⁅Q, Subgroup.zpowers b⁆ ≤ Subgroup.centralizer ({x} : Set X) := by
    rw [Subgroup.commutator_le]
    intro q hq c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    set w := ⁅x, q⁆ with hw
    have hwZ : w ∈ Z := hPQ x hx q hq
    have hxc : Commute x (b ^ k) := Commute.zpow_right (hPb x hx).symm k
    have hwc : Commute w (b ^ k) := (Commute.zpow_left (hZb w hwZ) k).symm
    have hwq : Commute w q := (hZQ w hwZ q hq).symm
    have h1 : x * q * x⁻¹ = w * q := by rw [hw, commutatorElement_def]; group
    have h2 : x * b ^ k * x⁻¹ = b ^ k := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hxc.eq
    have h3 : x * q⁻¹ * x⁻¹ = q⁻¹ * w⁻¹ := by
      rw [show x * q⁻¹ * x⁻¹ = (x * q * x⁻¹)⁻¹ by group, h1, mul_inv_rev]
    have h4 : x * (b ^ k)⁻¹ * x⁻¹ = (b ^ k)⁻¹ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (hxc.inv_right).eq
    have hwm : Commute w (q * b ^ k * q⁻¹) := (hwq.mul_right hwc).mul_right hwq.inv_right
    have key : x * ⁅q, b ^ k⁆ * x⁻¹ = ⁅q, b ^ k⁆ := by
      calc x * ⁅q, b ^ k⁆ * x⁻¹
          = (x * q * x⁻¹) * (x * b ^ k * x⁻¹) * (x * q⁻¹ * x⁻¹) * (x * (b ^ k)⁻¹ * x⁻¹) := by
            rw [commutatorElement_def]; group
        _ = w * (q * b ^ k * q⁻¹) * w⁻¹ * (b ^ k)⁻¹ := by rw [h1, h2, h3, h4]; group
        _ = (q * b ^ k * q⁻¹) * w * w⁻¹ * (b ^ k)⁻¹ := by rw [hwm.eq]
        _ = ⁅q, b ^ k⁆ := by rw [commutatorElement_def]; group
    exact (mul_inv_eq_iff_eq_mul.1 key).symm
  have hle : Q ≤ Subgroup.centralizer ({x} : Set X) := by
    refine hdec.trans (sup_le (fun q' hq' => ?_) hcomm)
    obtain ⟨hq'Q, hq'C⟩ := Subgroup.mem_inf.1 hq'
    have hbq : b * q' = q' * b := Subgroup.mem_centralizer_iff.1 hq'C b (Subgroup.mem_zpowers b)
    exact Subgroup.mem_centralizer_singleton_iff.2 (hZP q' (hQfree q' hq'Q hbq) x hx).symm
  intro q hq
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hq)).symm

end Planes

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
