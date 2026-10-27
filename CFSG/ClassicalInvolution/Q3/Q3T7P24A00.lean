module

public import CFSG.ClassicalInvolution.Q3.Q3T8Bridge
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenE612

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

namespace Disconnected.AschTight

theorem hypOmegaGen_of_mod {G : Type} [Group G] {Ω : Set (Subgroup G)}
    (h : Asc77.HypOmegaMod Ω) : HypOmegaGen Ω := h

namespace Sec7

theorem l6_12_mod (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (hP : Asc77.PartIHyp Ω)
    (htr : ∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) (S : Sylow 2 G) :
    let M : Subgroup G := ⨆ U ∈ {U : Subgroup G | (∃ η ∈ etaG Ω, U ∈ η) ∧
      U ≤ (S : Subgroup G)}, U
    (∃ η ∈ etaG Ω, (∀ m ∈ M, ∀ U ∈ η, conjSub m U ∈ η) ∧
      (∀ η' ∈ etaG Ω, (∀ m ∈ M, ∀ U ∈ η', conjSub m U ∈ η') → η' = η) ∧
      ∀ g : G, (∀ U ∈ η, conjSub g U ≤ (S : Subgroup G)) → ∀ U ∈ η, conjSub g U ∈ η) ∨
    ∀ K ∈ Ω, 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) → K ⊓ (S : Subgroup G) ∈ RSet Ω :=
  Q3T6.Gen612.l6_12_on hP.hyp (fun S => Sec6Gen.exists_invariant_mem_etaSet hP.hyp S)
    (fun _ ⟨_, hS, hinv⟩ =>
      (Sec6Gen.eta_abelian_of_cyc66 hP.hyp (Sec6Gen.cyc66 hP.hyp) hS hinv).1)
    (Sec6Gen.l6_11Gen G _ hP.hyp) htr S

end Sec7

end Disconnected.AschTight

end CFSG.ClassicalInvolution.Q3.Q3T8

namespace CFSG.ClassicalInvolution.Q3.Q3T7P24

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

theorem lemma33_involution {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : HypOmegaGen Ω) {K R : Subgroup G} (hK : K ∈ Ω) (hR : IsSylow2In R K) {t : G}
    (ht : t * t = 1) (htK : t ∈ Subgroup.normalizer (K : Set G))
    (htR : ∀ r ∈ R, r * t = t * r) : ∀ k ∈ K, ⁅t, k⁆ ∈ oddCoreOf K := by
  have hV : IsPGroup 2 ↥(Subgroup.zpowers t) := by
    have h2 : orderOf t ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two]; exact ht)
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hle : Subgroup.zpowers t ≤ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.mpr htK
  have hcomm : Commutes (Subgroup.zpowers t) R := by
    intro v hv r hr
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_left (show Commute t r from (htR r hr).symm) m).eq
  intro k hk
  have hcomm' : ⁅Subgroup.zpowers t, K⁆ ≤ oddCoreOf K :=
    Subgroup.commutator_le.mpr fun v hv k hk =>
      Sec6Gen.centSylow hΩ hK hR hV (fun _ hy => mem_normalizer_iff_conjSub_eq.mp (hle hy))
        (fun r hr w hw => (hcomm w hw r hr).symm) k hk v hv
  exact hcomm' (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers t) hk)

end CFSG.ClassicalInvolution.Q3.Q3T7P24
