module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SCI1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SCI4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEFin1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G]

theorem sec9ci_layer_ne_bot (hT6 : Asc82Tab6M) [Finite G] {L : Subgroup G} (hL : IsOm6M L)
    {hQ : Q.Nondegenerate} (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G} (hs2 : orderOf s = 2)
    (hsN : s ∈ Subgroup.normalizer (L : Set G))
    (h1 : SimHasDim (ffInducesHom hm e ⟨s, hsN⟩) 1) : layerCent L s ≠ ⊥ := by
  intro hbot
  rcases (hT6.layer_trivial G L hL s hs2 hsN).mp hbot with h4 | ⟨α, h3⟩
  · have hd4 := simHasDim_of_inducesTypeSome hm e hsN h4
    rcases sec9ci_dim_exclusive hQ hm.1 h1 hd4 with h | h <;> omega
  · have hd3 := simHasDim_of_inducesTypeSome hm e hsN h3
    rcases sec9ci_dim_exclusive hQ hm.1 h1 hd3 with h | h <;> omega

theorem sec9ci_exists_layer_inv (hT6 : Asc82Tab6M) [Finite G] {L : Subgroup G} (hL : IsOm6M L)
    {s : G} (hs2 : orderOf s = 2) (hsN : s ∈ Subgroup.normalizer (L : Set G))
    (hne : layerCent L s ≠ ⊥) {w : G}
    (hw : w ∈ twoRes (L ⊓ Subgroup.centralizer ({s} : Set G))) (hw2 : w ^ 2 ∈ centerIn L) :
    ∃ x : G, x ∈ layerCent L s ∧ x * x = 1 ∧ ∀ c ∈ L, x * c * x⁻¹ = w * c * w⁻¹ := by
  have hX : XOut L s = layerCent L s := hT6.xout_eq G L hL s hs2 hsN hne
  have hm_odd : Odd (orderOf (w ^ 2)) := sec9ci_centerIn_odd_order hL hw2
  refine ⟨w ^ orderOf (w ^ 2), ?_, ?_, ?_⟩
  · have hx_out : w ^ orderOf (w ^ 2) ∈ XOut L s := by
      rw [XOut, twoPrimeRes]
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · exact (twoRes (L ⊓ Subgroup.centralizer ({s} : Set G))).pow_mem hw _
      · have hpow2 : (w ^ orderOf (w ^ 2)) ^ 2 = 1 := by
          rw [← pow_mul, show orderOf (w ^ 2) * 2 = 2 * orderOf (w ^ 2) from by omega,
            pow_mul, pow_orderOf_eq_one]
        have hdvd : orderOf (w ^ orderOf (w ^ 2)) ∣ 2 := by
          rw [orderOf_dvd_iff_pow_eq_one]
          exact hpow2
        obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (p := 2) (m := 1) Nat.prime_two).mp hdvd
        exact ⟨k, hk⟩
    rw [hX] at hx_out
    exact hx_out
  · rw [← pow_two]
    rw [← pow_mul, show orderOf (w ^ 2) * 2 = 2 * orderOf (w ^ 2) from by omega,
      pow_mul, pow_orderOf_eq_one]
  · intro c hc
    have hz_center : (w ^ 2) ^ ((orderOf (w ^ 2) - 1) / 2) ∈ centerIn L :=
      (centerIn L).pow_mem hw2 _
    have hz_comm : (w ^ 2) ^ ((orderOf (w ^ 2) - 1) / 2) * c =
        c * (w ^ 2) ^ ((orderOf (w ^ 2) - 1) / 2) :=
      ((sec4_mem_centerIn_iff _).mp hz_center).2 c hc
    have hfac : w ^ orderOf (w ^ 2) =
        w * (w ^ 2) ^ ((orderOf (w ^ 2) - 1) / 2) := by
      obtain ⟨k, hk⟩ := hm_odd
      have hmid : (orderOf (w ^ 2) - 1) / 2 = k := by omega
      rw [hmid, hk, pow_succ', pow_mul]
    rw [hfac]
    have hzc : (w ^ 2) ^ ((orderOf (w ^ 2) - 1) / 2) * c *
        ((w ^ 2) ^ ((orderOf (w ^ 2) - 1) / 2))⁻¹ = c := by
      rw [hz_comm]
      group
    calc (w * (w ^ 2) ^ ((orderOf (w ^ 2) - 1) / 2)) * c *
          (w * (w ^ 2) ^ ((orderOf (w ^ 2) - 1) / 2))⁻¹
        = w * ((w ^ 2) ^ ((orderOf (w ^ 2) - 1) / 2) * c *
            ((w ^ 2) ^ ((orderOf (w ^ 2) - 1) / 2))⁻¹) * w⁻¹ := by group
      _ = w * c * w⁻¹ := by rw [hzc]

end CFSG.OddStandard.SmallF3.Omega
