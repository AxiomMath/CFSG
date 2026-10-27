module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporDefs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

variable {S : Type} [Group S] [Finite S]

theorem exists_conj_of_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥)
    (hout : Nat.card (Outer S) ≤ 2) (β : MulAut S) (hβ : β ^ p = 1) :
    ∃ s : S, MulAut.conj s = β ∧ s ^ p = 1 := by
  have hψ : Function.Injective (MulAut.conj : S →* MulAut S) :=
    conj_injective_of_center_eq_bot hcen
  let q : MulAut S →* Outer S := QuotientGroup.mk' (inner S)
  have hqker : ∀ y : MulAut S, q y = 1 ↔ y ∈ innerAut S := fun y =>
    QuotientGroup.eq_one_iff y
  have hsq : ∀ y : MulAut S, (q y) ^ 2 = 1 := by
    intro y
    have hc : (q y) ^ Nat.card (Outer S) = 1 := pow_card_eq_one'
    have hpos : 0 < Nat.card (Outer S) := Nat.card_pos
    interval_cases hn : Nat.card (Outer S)
    · have : q y = 1 := by simpa using hc
      rw [this, one_pow]
    · exact hc
  have hxi : β ∈ innerAut S := by
    refine (hqker β).1 ?_
    have h3 : (q β) ^ p = 1 := by
      rw [← map_pow, hβ, map_one]
    have h4 : orderOf (q β) ∣ Nat.gcd p 2 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one (hsq β))
    have hg : Nat.gcd p 2 = 1 := by
      rw [Nat.gcd_comm]
      exact (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at h4
    exact h4
  obtain ⟨s, rfl⟩ := hxi
  refine ⟨s, rfl, hψ ?_⟩
  rw [map_pow, hβ, map_one]

theorem fixSubgroup_conj (s : S) :
    fixSubgroup (MulAut.conj s : MulAut S) = Subgroup.centralizer ({s} : Set S) := by
  ext a
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc a * s = (s * a * s⁻¹) * s := by rw [h]
      _ = s * a := by group
  · intro h
    calc s * a * s⁻¹ = (a * s) * s⁻¹ := by rw [h]
      _ = a := by group

theorem layer_comm_one [IsSimpleGroup S] (p : ℕ) :
    ⁅GLAPLayer p (fixSubgroup (1 : MulAut S)), GLAPPrimeCoreOf p (fixSubgroup (1 : MulAut S))⁆ =
      ⊥ := by
  have hfix : fixSubgroup (1 : MulAut S) = ⊤ := by
    ext a; simp [mem_fixSubgroup]
  rw [hfix]
  by_cases hO : GLAPPrimeCoreOf p (⊤ : Subgroup S) = ⊥
  · rw [hO]; exact Subgroup.commutator_bot_right _
  · have hnorm : (GLAPPrimeCoreOf p (⊤ : Subgroup S)).Normal :=
      ⟨fun n hn g => CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_conj_mem g (Subgroup.mem_top g) n hn⟩
    have htop : GLAPPrimeCoreOf p (⊤ : Subgroup S) = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left hO
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 (sSup_le fun J hJ => ?_)
    exfalso
    have hbot : barX p ⊤ J = ⊥ :=
      (i183_barX_eq_bot_iff (le_top : J ≤ ⊤)).2 (by rw [htop]; exact le_top)
    have hq : CFSG.Open.IsQuasisimple ↥(barX p ⊤ J) := hJ.2.2.1.2.2
    rw [hbot] at hq
    have hnt := hq.2.toNontrivial
    have hss : Subsingleton (↥(⊥ : Subgroup (↥(⊤ : Subgroup S) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup S))) ⧸
        Subgroup.center ↥(⊥ : Subgroup (↥(⊤ : Subgroup S) ⧸ GLAPPrimeCore p ↥(⊤ : Subgroup S)))) :=
      (QuotientGroup.mk'_surjective _).subsingleton
    exact (not_nontrivial_iff_subsingleton.2 hss) hnt

theorem b3SporPair_of_oPrimeCoreTrivial {name : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hOut : SporadicOuterLeTwo)
    (h : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
      Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) → OPrimeCoreTrivialAt p S) :
    B3SporPair name p := by
  intro S _ _ hs hnc he β hβ
  have := hs
  have : Fact p.Prime := ⟨hp⟩
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hnc
  have hout : Nat.card (Outer S) ≤ 2 := hOut S hs hnc name he
  obtain ⟨s, rfl, hsp⟩ := exists_conj_of_pow hp hp2 hcen hout β hβ
  by_cases hs1 : s = 1
  · subst hs1
    rw [map_one]
    exact layer_comm_one p
  · have hord : orderOf s = p := orderOf_eq_prime hsp hs1
    rw [fixSubgroup_conj, h S he s hord, Subgroup.commutator_bot_right]

end CFSG.HardMathSupport.Solomon.Coordinator
