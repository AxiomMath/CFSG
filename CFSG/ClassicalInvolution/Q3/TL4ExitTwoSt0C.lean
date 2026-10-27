module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotAEmpty
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {X : Subgroup G} [X.Normal]

theorem commutator_mul_central {a b c d : G} (hc : c ∈ Subgroup.center G)
    (hd : d ∈ Subgroup.center G) : ⁅a * c, b * d⁆ = ⁅a, b⁆ :=
  CFSG.ClassicalInvolution.Asc77.AscE186.commutator_mul_central hc hd

theorem eq_of_map_cent (hΩ : HypOmegaGen Ω)
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2))
    (hXc : X ≤ Subgroup.center G) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : K.map (QuotientGroup.mk' X) = J.map (QuotientGroup.mk' X)) : K = J := by
  by_contra hKJ
  obtain ⟨P, hP, ⟨e⟩⟩ := hq8 K hK
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  set r₁ : G := (e.symm (QuaternionGroup.a 1) : G) with hr₁def
  set r₂ : G := (e.symm (QuaternionGroup.xa 0) : G) with hr₂def
  set z₀ : G := (e.symm (QuaternionGroup.a 2) : G) with hz₀def
  have hr₁K : r₁ ∈ K := hP.1 (e.symm _).2
  have hr₂K : r₂ ∈ K := hP.1 (e.symm _).2
  have hz₀K : z₀ ∈ K := hP.1 (e.symm _).2
  have hq : (QuaternionGroup.a 1 * QuaternionGroup.xa 0 * (QuaternionGroup.a 1)⁻¹ *
      (QuaternionGroup.xa 0)⁻¹ : QuaternionGroup 2) = QuaternionGroup.a 2 := by decide
  have hcomm₀ : ⁅r₁, r₂⁆ = z₀ := by
    simp only [commutatorElement_def, hr₁def, hr₂def, hz₀def]
    have := congrArg (fun y => ((e.symm y : ↥P) : G)) hq
    simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using this
  have hz₀sq : z₀ * z₀ = 1 := by
    have hq2 : (QuaternionGroup.a 2 * QuaternionGroup.a 2 : QuaternionGroup 2) = 1 := by decide
    have := congrArg (fun y => ((e.symm y : ↥P) : G)) hq2
    rw [hz₀def]
    simpa only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one] using this
  have hz₀1 : z₀ ≠ 1 := by
    intro h1
    have h2 : e.symm (QuaternionGroup.a 2) = 1 := Subtype.ext h1
    have h3 : (QuaternionGroup.a 2 : QuaternionGroup 2) = 1 := by simpa using h2
    exact absurd h3 (by decide)
  have hzz : z₀ = z := (hz.unique z₀ hz₀K hz₀sq).resolve_left hz₀1
  have hlift : ∀ r ∈ K, ∃ j ∈ J, ∃ ν ∈ Subgroup.center G, r = j * ν := by
    intro r hr
    have hr' : QuotientGroup.mk' X r ∈ J.map (QuotientGroup.mk' X) :=
      h ▸ Subgroup.mem_map_of_mem _ hr
    obtain ⟨j, hj, hjr⟩ := hr'
    have hν : j⁻¹ * r ∈ X := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' X (j⁻¹ * r) = 1
      rw [map_mul, map_inv, hjr, inv_mul_cancel]
    exact ⟨j, hj, j⁻¹ * r, hXc hν, by group⟩
  obtain ⟨j₁, hj₁, ν₁, hν₁, hr₁e⟩ := hlift r₁ hr₁K
  obtain ⟨j₂, hj₂, ν₂, hν₂, hr₂e⟩ := hlift r₂ hr₂K
  have hzJ : z ∈ J := by
    have : ⁅r₁, r₂⁆ = ⁅j₁, j₂⁆ := by
      rw [hr₁e, hr₂e]
      exact commutator_mul_central hν₁ hν₂
    rw [← hzz, ← hcomm₀, this]
    simp only [commutatorElement_def]
    exact J.mul_mem (J.mul_mem (J.mul_mem hj₁ hj₂) (J.inv_mem hj₁)) (J.inv_mem hj₂)
  have hzt : z = t := (ht.unique z hzJ hz.sq).resolve_left hz.ne_one
  have hcommKJ := Sec6Gen.comm_le_oddCore_of_twin hΩ hK hJ hKJ hz (hzt ▸ ht)
  have hzO : z ∈ oddCoreOf K := by
    have h1 : ⁅r₁, r₂⁆ = ⁅j₁, r₂⁆ := by
      have := commutator_mul_central (a := j₁) (b := r₂) (c := ν₁) (d := 1) hν₁
        (Subgroup.one_mem _)
      rw [mul_one] at this
      rw [hr₁e]
      exact this
    have h2 : ⁅j₁, r₂⁆ ∈ ⁅K, J⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hj₁ hr₂K
    rw [← hzz, ← hcomm₀, h1]
    exact (hcommKJ h2).1
  have hz1 := eq_one_of_isPGroup_of_mem_odd (odd_natCard_oddCoreOf K) hzO
    (isPGroup_zpowers_of_involution hz.ne_one hz.sq)
  exact hz.ne_one hz1

theorem normalizer_of_map_cent (hΩ : HypOmegaGen Ω)
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2))
    (hXc : X ≤ Subgroup.center G) {K : Subgroup G} (hK : K ∈ Ω) {u : G}
    (hu : QuotientGroup.mk' X u ∈ Subgroup.normalizer
      ((K.map (QuotientGroup.mk' X) : Subgroup (G ⧸ X)) : Set (G ⧸ X))) :
    u ∈ Subgroup.normalizer (K : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq]
  refine eq_of_map_cent hΩ hq8 hXc (hΩ.conjInvariant u K hK) hK ?_
  rw [AscQuot.map_conjSub]
  exact mem_normalizer_iff_conjSub_eq.mp hu

theorem centQuotGen (hΩ : HypOmegaGen Ω)
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2))
    (hXc : X ≤ Subgroup.center G) (hmeet : ∀ J ∈ Ω, J ⊓ X = ⊥) : CentQuotGen Ω X where
  hyp := hΩ
  hyp' := CentQ.quotient_hypOmegaGen hΩ X hXc (fun K hK => by
    rw [inf_comm, hmeet K hK, Subgroup.card_bot]
    exact odd_one)
  meet := hmeet
  eq_of_map := fun K hK J hJ h => eq_of_map_cent hΩ hq8 hXc hK hJ h
  normalizer_of_map := fun K hK u hu => normalizer_of_map_cent hΩ hq8 hXc hK hu

theorem q8_quot_cent
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2))
    (hmeet : ∀ J ∈ Ω, J ⊓ X = ⊥) :
    ∀ L ∈ quotFamily Ω X, ∃ P : Subgroup (G ⧸ X),
      IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2) := by
  rintro _ ⟨K, hK, rfl⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := hq8 K hK
  have hPN : P ⊓ X = ⊥ := eq_bot_iff.mpr ((inf_le_inf_right X hP.1).trans (hmeet K hK).le)
  obtain ⟨V₀, hV₀, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := K.map (QuotientGroup.mk' X))
    (IsPGroup.of_bot) bot_le
  have hKcard : Nat.card ↥(K.map (QuotientGroup.mk' X)) = Nat.card K :=
    (Nat.card_congr (AscQuot.quotRestrictEquiv (hmeet K hK)).toEquiv).symm
  have hcard : Nat.card P = Nat.card V₀ := by
    rw [natCard_eq_pow_of_isSylow2In hP, natCard_eq_pow_of_isSylow2In hV₀, hKcard]
  have hmapcard : Nat.card ↥(P.map (QuotientGroup.mk' X)) = Nat.card P :=
    (Nat.card_congr (AscQuot.quotRestrictEquiv hPN).toEquiv).symm
  exact ⟨P.map (QuotientGroup.mk' X),
    hV₀.of_natCard_le (hP.2.1.map _) (Subgroup.map_mono hP.1) (by rw [hmapcard, hcard]),
    ⟨(AscQuot.quotRestrictEquiv hPN).symm.trans e⟩⟩

theorem two_quot_cent (h2 : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L))
    (hmeet : ∀ J ∈ Ω, J ⊓ X = ⊥) :
    ∀ L ∈ quotFamily Ω X, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L) := by
  rintro _ ⟨K, hK, rfl⟩
  have hodd : Odd (Nat.card ↥(X ⊓ K)) := by
    rw [inf_comm, hmeet K hK, Subgroup.card_bot]
    exact odd_one
  obtain ⟨e⟩ := AscQuot.nonempty_quotOddCoreEquiv hodd
  exact (h2 K hK).of_equiv e

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo
