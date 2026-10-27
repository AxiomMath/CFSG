module

public import CFSG.ClassicalInvolution.Asc77.AscE184Quot
public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]

theorem eq_one_or_eq_of_map_eq_of_twin_gen (hΩ : HypOmegaGen Ω) (hN : Odd (Nat.card N))
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G}
    (hzK : IsUniqueInvolution K z) (hzJ : IsUniqueInvolution J z) {x k : G} (hx : x ∈ J)
    (hk : k ∈ K) (hk2 : IsPGroup 2 (Subgroup.zpowers k))
    (hxk : QuotientGroup.mk' N x = QuotientGroup.mk' N k) : k = 1 ∨ k = z := by
  exact CFSG.ClassicalInvolution.Asc77.E187C.eq_one_or_eq_of_map_eq_of_twin_of
    (fun hK hJ hKJ hzK hzJ => Sec6Gen.comm_le_oddCore_of_twin hΩ hK hJ hKJ hzK hzJ)
    (fun hK hz => Sec6Gen.center_two hΩ hK hz) hN hK hJ hKJ hzK hzJ hx hk hk2 hxk

theorem exists_conj_of_map_eq_gen (hΩ : HypOmegaGen Ω) (hN : Odd (Nat.card N))
    {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω)
    (h : K.map (QuotientGroup.mk' N) = L.map (QuotientGroup.mk' N)) :
    ∃ n ∈ N, L = conjSub n K := by
  exact CFSG.ClassicalInvolution.Asc77.E187C.exists_conj_of_map_eq_of (fun hK => Sec6Gen.exists_uniqueInvolution hΩ hK)
    hΩ.conjInvariant (fun hQ => Sec6Gen.eight_le_of_mem_RSet hΩ hQ)
    (fun hK hJ hKJ hzK hzJ => Sec6Gen.comm_le_oddCore_of_twin hΩ hK hJ hKJ hzK hzJ)
    (fun hK hz => Sec6Gen.center_two hΩ hK hz) hN hK hL h

end Lift

section Nbr

variable {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}

theorem exists_conj_omegaNbr_of_commute (hΩ : HypOmegaGen Λ) {N : Subgroup Y} [N.Normal]
    (hN : Odd (Nat.card N)) {K M : Subgroup Y} (hK : K ∈ Λ) (hM : M ∈ Λ)
    (hne : M.map (QuotientGroup.mk' N) ≠ K.map (QuotientGroup.mk' N))
    (hcomm : ∀ x ∈ M, ∀ y ∈ K, QuotientGroup.mk' N x * QuotientGroup.mk' N y =
      QuotientGroup.mk' N y * QuotientGroup.mk' N x) :
    ∃ n ∈ N, M ∈ omegaNbr Λ (conjSub n K) := by
  obtain ⟨R, hR, hRM, -⟩ := exists_mem_RSet_ge hM (isPGroup_two_bot' (G := Y)) bot_le
  have hperm : ∀ v ∈ R, ∃ n ∈ N, conjSub v K = conjSub n K := by
    intro v hv
    have hvM : v ∈ M := hRM.1 hv
    have hvc : QuotientGroup.mk' N v ∈
        Subgroup.centralizer ((K.map (QuotientGroup.mk' N) : Subgroup (Y ⧸ N)) : Set (Y ⧸ N)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨k, hk, rfl⟩
      exact (hcomm v hvM k hk).symm
    have himg : K.map (QuotientGroup.mk' N) = (conjSub v K).map (QuotientGroup.mk' N) := by
      rw [AscQuot.map_conjSub]
      exact (conjSub_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ hvc)).symm
    obtain ⟨n, hn, hnK⟩ := exists_conj_of_map_eq_gen hΩ hN hK (hΩ.conjInvariant v K hK) himg
    exact ⟨n, hn, hnK⟩
  obtain ⟨n, hn, hRn⟩ := exists_conj_normalizer_of_perm hN K hRM.2.1 hperm
  refine ⟨n, hn, hM, ?_, R, hR, hRM.1, hRn⟩
  intro hMK
  apply hne
  rw [hMK, AscQuot.map_conjSub, show QuotientGroup.mk' N n = 1 from
    (QuotientGroup.eq_one_iff _).mpr hn, conjSub_one]

theorem exists_noncomm_map_of_mem (hΩ : HypOmegaGen Λ) {K : Subgroup Y} (hK : K ∈ Λ) :
    ∃ x ∈ K, ∃ y ∈ K, oddQuot Y x * oddQuot Y y ≠ oddQuot Y y * oddQuot Y x := by
  obtain ⟨R₀, hR₀, hR₀1, -⟩ := exists_mem_RSet_ge hK (isPGroup_two_bot' (G := Y)) bot_le
  obtain ⟨x, hx, y, hy, hxy⟩ := (Sec6Gen.isQuatSub_of_mem_RSet hΩ hR₀).exists_not_commute
  refine ⟨x, hR₀1.1 hx, y, hR₀1.1 hy, fun h => hxy ?_⟩
  have h1 : oddQuot Y (x * y * x⁻¹ * y⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have h3 := quot_injOn_of_isPGroup hR₀1.2.1 _ (R₀.mul_mem (R₀.mul_mem (R₀.mul_mem hx hy)
    (R₀.inv_mem hx)) (R₀.inv_mem hy)) h1
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h3, one_mul]

end Nbr

end CFSG.ClassicalInvolution.Q3.Q3T6
