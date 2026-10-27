module

import CFSG.Adapters.WholeGroupLayer
public import CFSG.GH74.GLS.Stage2.Local.Basic
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt41

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section SecLemmas

variable {G : Type} [Group G]

theorem orderOf_zSec {z : G} (hz2 : orderOf z = 2) {H₀ : Subgroup G} (hz : z ∈ H₀)
    (H₁ : Subgroup ↥H₀) [H₁.Normal] (hodd : Odd (Nat.card ↥H₁)) :
    orderOf (zSec z H₀ hz H₁) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · show (QuotientGroup.mk ⟨z, hz⟩ : ↥H₀ ⧸ H₁) ^ 2 = 1
    rw [← QuotientGroup.mk_pow]
    have h1 : (⟨z, hz⟩ : ↥H₀) ^ 2 = 1 := by
      apply Subtype.ext
      have := pow_orderOf_eq_one z
      rw [hz2] at this
      simpa using this
    rw [h1]; rfl
  · intro h
    have hmem : (⟨z, hz⟩ : ↥H₀) ∈ H₁ := (QuotientGroup.eq_one_iff _).mp h
    have h2 : orderOf (⟨⟨z, hz⟩, hmem⟩ : ↥H₁) ∣ Nat.card ↥H₁ := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hz2] at h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

end SecLemmas

section PCoreLemmas

variable {A : Type} [Group A] [Finite A]

theorem le_pCore_of_isPGroup_of_le_fitting {p : ℕ} [Fact p.Prime] {Y : Subgroup A}
    (hY : IsPGroup p ↥Y) (hF : Y ≤ fittingSubgroup A) : Y ≤ pCore p A := by
  have hnil : Group.IsNilpotent ↥(fittingSubgroup A) := by
    rw [fitting_eq_sup_pCore]
    exact isNilpotent_iSup_pCore
  have hYF : IsPGroup p ↥(Y.subgroupOf (fittingSubgroup A)) :=
    hY.of_equiv (Subgroup.subgroupOfEquivOfLe hF).symm
  obtain ⟨Q, hQ⟩ := hYF.exists_le_sylow
  have hle := Sylow.map_le_pCore (inferInstance : (fittingSubgroup A).Normal) hnil p Q
  intro y hy
  apply hle
  have : (⟨y, hF hy⟩ : ↥(fittingSubgroup A)) ∈ Y.subgroupOf (fittingSubgroup A) := hy
  exact ⟨⟨y, hF hy⟩, hQ this, rfl⟩

theorem centralizer_generalizedFitting_le_fitting' (A : Type) [Group A] [Finite A] :
    centralizer ((generalizedFitting A : Subgroup A) : Set A) ≤ fittingSubgroup A :=
  CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup A

end PCoreLemmas

theorem prop_4_1a_of (h19 : B_signalizer_19_9) : Prop4_1a := by
  intro G _ _ z k S ctx H₀ H₁ _ hz p X sig r hr hr2
  by_cases hrp : r = p
  · subst hrp
    rw [sig.op]
    intro x _ y hy
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
    subst hy
    simp
  · have hz2 := orderOf_zSec ctx.orderOf_z hz H₁ sig.odd
    exact (h19 (Sec H₀ H₁) (zSec z H₀ hz H₁) hz2 p sig.A.prime sig.A.odd X sig.A.pgroup
      (fun c hc => sig.A.inv c (Subgroup.mem_top c) hc) sig.A.comm).1 r hr hr2 hrp

theorem prop_4_1b_of (h19 : B_signalizer_19_9) : Prop4_1b := by
  intro G _ _ z k S ctx H₀ H₁ _ hz p X sig
  have ha := prop_4_1a_of h19 G z k S ctx H₀ H₁ hz p X sig
  have : Fact p.Prime := ⟨sig.A.prime⟩
  rw [eq_bot_iff]
  set A := Sec H₀ H₁
  set X₀ : Subgroup A := X ⊓ centralizer (((pCore 2 A ⊔ layer A : Subgroup A)) : Set A) with hX₀
  have hX₀X : X₀ ≤ X := inf_le_left
  have hX₀c : X₀ ≤ centralizer (((pCore 2 A ⊔ layer A : Subgroup A)) : Set A) := inf_le_right
  have hsup : (pCore 2 A ⊔ layer A) ≤ centralizer (X₀ : Set A) := Subgroup.le_centralizer_iff.mp hX₀c
  have hfit : fittingSubgroup A ≤ centralizer (X₀ : Set A) := by
    rw [fitting_eq_sup_pCore]
    refine iSup_le fun q => ?_
    have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
    by_cases h2 : q.1.1 = 2
    · rw [h2]; exact le_sup_left.trans hsup
    · by_cases hp : q.1.1 = p
      · rw [hp, sig.op]; exact bot_le
      · exact Subgroup.le_centralizer_iff.mp (hX₀X.trans (ha q.1.1 hq h2))
  have hF : generalizedFitting A ≤ centralizer (X₀ : Set A) :=
    sup_le hfit (le_sup_right.trans hsup)
  have hX₀F : X₀ ≤ fittingSubgroup A :=
    (Subgroup.le_centralizer_iff.mpr hF).trans (centralizer_generalizedFitting_le_fitting' A)
  have hp0 : X₀ ≤ pCore p A :=
    le_pCore_of_isPGroup_of_le_fitting (sig.A.pgroup.to_le hX₀X) hX₀F
  rw [sig.op] at hp0
  exact hp0

end CFSG.GH74.GLS.Stage2.Signalizer
