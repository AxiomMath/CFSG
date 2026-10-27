module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big7
public import CFSG.CGT.PushingUpLit.SolKNA.R4.QuatAut

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.Blueprint

section Tight

variable {X : Type} [Group X] [Finite X]

theorem quatInvolution_eq_of_uniqueInvolution {r : ℕ} (hr : 4 ≤ r) {M R : Subgroup X} {z : X}
    (hz : IsUniqueInvolution M z) (hRM : R ≤ M) (e : ↥R ≃* QuaternionGroup (2 ^ (r - 2))) :
    quatInvolution r e = z := by
  rcases hz.unique (quatInvolution r e) (hRM (quatInvolution_mem hr e))
    (quatInvolution_sq hr e) with h | h
  · exact absurd h (quatInvolution_ne_one hr e)
  · exact h

theorem pow_two_pow_eq_one_of_tight {r : ℕ} (hr : 4 ≤ r) {Φ : Set (Subgroup X)}
    (hR : TypeRFam r Φ) {M : Subgroup X} (hM : M ∈ Φ) {z : X} (hz : IsUniqueInvolution M z)
    (hcent : ∀ (R : Subgroup X) (_ : ↥R ≃* QuaternionGroup (2 ^ (r - 2))), R ≤ M →
      ∀ x : X, (∀ y ∈ R, x * y = y * x) → (∃ k : ℕ, x ^ 2 ^ k = 1) → x = 1 ∨ x = z)
    {g : X} (hgz : g * z = z * g) {j : ℕ} (hgj : g ^ 2 ^ j = 1) : g ^ 2 ^ r = 1 := by
  have hgN : g ∈ Subgroup.normalizer (M : Set X) :=
    hR.tight M hM z hz (Subgroup.mem_centralizer_singleton_iff.mpr hgz)
  have hW : IsPGroup 2 (Subgroup.zpowers g) := by
    rintro ⟨a, ha⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    refine ⟨j, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hgj, one_zpow]
  obtain ⟨R, hRM, hfix⟩ := CFSG.ClassicalInvolution.Asc77.T3.exists_sylow_normalized hW
    (Subgroup.zpowers_le.mpr hgN)
  obtain ⟨eR⟩ := hR.quat M hM R hRM
  have hgR : ∀ q ∈ R, g * q * g⁻¹ ∈ R := by
    intro q hq
    have := Generic.conj_mem_conjSub (n := g) hq
    rwa [hfix g (Subgroup.mem_zpowers g)] at this
  have hcomm : ∀ y ∈ R, g ^ 2 ^ (r - 1) * y = y * g ^ 2 ^ (r - 1) :=
    fun y hy => QSub.pow_exponent_comm eR hr hgR hy
  have hx2 : (g ^ 2 ^ (r - 1)) ^ 2 ^ j = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hgj, one_pow]
  have h2r : 2 ^ r = 2 ^ (r - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rcases hcent R eR hRM.1 (g ^ 2 ^ (r - 1)) hcomm ⟨j, hx2⟩ with h1 | h1
  · rw [h2r, pow_mul, h1, one_pow]
  · rw [h2r, pow_mul, h1, pow_two, hz.sq]

end Tight

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
