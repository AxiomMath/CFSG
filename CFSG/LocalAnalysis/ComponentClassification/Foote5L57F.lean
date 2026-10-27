module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L57E
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CGT.M24S.Defs
public import CFSG.CGT.T75P.Inputs
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.SimpleCase
public import CFSG.GroupTheory.SupCommute
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L55B
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L57D

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_zpowers_of_pow_two {x : G} {k : ℕ} (hx : x ^ 2 ^ k = 1) :
    IsPGroup 2 (zpowers x) := by
  rintro ⟨g, hg⟩
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hg
  refine ⟨k, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

omit [Finite G] in
theorem mem_of_mem_oddCoreIn {A : Subgroup G} {n : G} (hn : n ∈ oddCoreIn A) : n ∈ A := by
  obtain ⟨m, -, rfl⟩ := hn
  exact m.2

section Lift

variable {A : Subgroup G} {𝕊 : Type} [Group 𝕊] (ε : A ⧸ pPrimeCore 2 A ≃* 𝕊)

omit [Finite G] in
include ε in
theorem conj_mem_oddCoreIn {x n : G} (hx : x ∈ normalizer (A : Set G)) (hn : n ∈ oddCoreIn A) :
    x * n * x⁻¹ ∈ oddCoreIn A := by
  have hnA := mem_of_mem_oddCoreIn hn
  have h1 := actG_psi ε hx ⟨n, hnA⟩
  rw [(psi_eq_one_iff ε ⟨n, hnA⟩).mpr hn, map_one] at h1
  exact (psi_eq_one_iff ε _).mp h1.symm

theorem exists_involution_lift {M : Subgroup G} {k : G} (hkM : k ∈ M) (hkA : k ∈ A)
    {a : 𝕊} (hka : psi A ε ⟨k, hkA⟩ = a) (ha2 : a * a = 1) (ha1 : a ≠ 1) :
    ∃ u ∈ M, ∃ hu : u ∈ A, psi A ε ⟨u, hu⟩ = a ∧ u * u = 1 ∧ u ≠ 1 ∧ ∃ m : ℕ, u = k ^ m := by
  obtain ⟨m, hm, j, hj⟩ := exists_odd_pow_two_element k
  have hamm : a ^ m = a := by
    obtain ⟨i, rfl⟩ := hm
    rw [pow_succ, pow_mul, sq, ha2, one_pow, one_mul]
  have hψ : psi A ε ⟨k ^ m, pow_mem hkA m⟩ = a := by
    rw [show (⟨k ^ m, pow_mem hkA m⟩ : A) = ⟨k, hkA⟩ ^ m from rfl, map_pow, hka, hamm]
  refine ⟨k ^ m, pow_mem hkM m, pow_mem hkA m, hψ, ?_, fun h1 => ha1 ?_, m, rfl⟩
  · have h1 : psi A ε ⟨k ^ m * k ^ m, mul_mem (pow_mem hkA m) (pow_mem hkA m)⟩ = 1 := by
      rw [show (⟨k ^ m * k ^ m, mul_mem (pow_mem hkA m) (pow_mem hkA m)⟩ : A) =
        ⟨k ^ m, pow_mem hkA m⟩ * ⟨k ^ m, pow_mem hkA m⟩ from rfl, map_mul, hψ, ha2]
    exact eq_one_of_mem_of_odd (isPGroup_zpowers_of_pow_two hj) (odd_card_oddCoreIn A)
      (mul_mem (mem_zpowers _) (mem_zpowers _)) ((psi_eq_one_iff ε _).mp h1)
  · rw [← hψ]
    have h2 : (⟨k ^ m, pow_mem hkA m⟩ : A) = 1 := Subtype.ext h1
    rw [h2, map_one]

end Lift

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

omit [Finite 𝕊] in
theorem exists_lift_of_fixed {v : G} (hvS : v ∈ S) (hvQ : ∀ q ∈ Q, q * v = v * q) {x : 𝕊}
    (hx : actG L ε v x = x) :
    ∃ k : G, ∃ hk : k ∈ L, k ∈ centralizer ((Q ⊔ zpowers v : Subgroup G) : Set G) ∧
      psi L ε ⟨k, hk⟩ = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPS : Q ⊔ zpowers v ≤ S := sup_le h.QS (zpowers_le.mpr hvS)
  have hP := h.isPGroup_S.to_le hPS
  have hcomm : ∀ c ∈ Q, ∀ d ∈ zpowers v, c * d = d * c := by
    intro c hc d hd
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hd
    exact (Commute.zpow_right (hvQ c hc) i).eq
  have hfix : ∀ p ∈ Q ⊔ zpowers v, actG L ε p x = x := by
    intro p hp
    obtain ⟨c, hc, d, hd, rfl⟩ := exists_mul_of_mem_sup_commute hcomm hp
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hd
    have hvN := h.S_le hvS
    have hcN := h.S_le (h.QS hc)
    rw [actG_mul ε hcN (zpow_mem hvN i), actG_zpow ε hvN i,
      (actG_eq_one_iff ε hcN).mpr (h.Q_le hc), one_mul]
    have hst : actG L ε v ∈ MulAction.stabilizer (MulAut 𝕊) x := hx
    exact zpow_mem hst i
  obtain ⟨⟨y, hyL⟩, rfl⟩ := psi_surjective ε x
  obtain ⟨y', hy'N, hy'⟩ := exists_commute_of_coprime (P := Q ⊔ zpowers v) (N := oddCoreIn L)
    hP (fun h2 => by have := Nat.odd_iff.mp (odd_card_oddCoreIn L); omega)
    (fun p hp n hn => conj_mem_oddCoreIn ε (h.S_le (hPS hp)) hn) (y := y) (fun p hp => by
      have hpN := h.S_le (hPS hp)
      have h1 := hfix p hp
      rw [actG_psi ε hpN] at h1
      exact (psi_eq_iff ε _ _).mp h1.symm)
  have hy'L : y' ∈ L := by
    rw [show y' = y * (y⁻¹ * y') by group]
    exact mul_mem hyL (mem_of_mem_oddCoreIn hy'N)
  refine ⟨y', hy'L, mem_centralizer_iff.mpr fun p hp => hy' p hp, ?_⟩
  exact (psi_eq_iff ε ⟨y, hyL⟩ ⟨y', hy'L⟩).mpr hy'N |>.symm

end Sec5

end CFSG.ComponentClassification.Foote5
