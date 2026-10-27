module

public import CFSG.LieType.Chevalley.OrdinaryEOuterOrder
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)


theorem exists_hom_ringAut_E6_three (K : Type) [Field K] [Finite K]
    (hK : ¬ 3 ∣ Nat.card K - 1) :
    ∃ Θ : MulAut (adjointGroup .E6 K) →* RingAut K, ∀ x ∈ Θ.ker, x ^ 3 = 1 →
      x ∈ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range := by
  obtain ⟨Φ, -, hΦker, -⟩ := exists_outer_hom_E (K := K) (τ := .E6) (Or.inl rfl)
  refine ⟨(MonoidHom.fst _ _).comp (Φ.comp (QuotientGroup.mk' (inner (adjointGroup .E6 K)))), ?_⟩
  intro x hx hxp
  set y := QuotientGroup.mk' (inner (adjointGroup .E6 K)) x with hy
  have hyp : y ^ 3 = 1 := by rw [hy, ← map_pow, hxp, map_one]
  have h1 : (Φ y).1 = 1 := hx
  have h2 : (Φ y).2 = 1 := by
    have : NeZero (exactE Tag.E6) := ⟨by simp [exactE]⟩
    have hcard : Nat.card (Multiplicative (ZMod (exactE Tag.E6))) = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
      simp [exactE]
    have hz2 : (Φ y).2 ^ 2 = 1 := by
      have h0 : (Φ y).2 ^ Nat.card (Multiplicative (ZMod (exactE Tag.E6))) = 1 :=
        pow_card_eq_one'
      rwa [hcard] at h0
    have hz3 : (Φ y).2 ^ 3 = 1 := by
      have := congrArg Prod.snd (show Φ y ^ 3 = 1 by rw [← map_pow, hyp, map_one])
      simpa using this
    exact (pow_eq_one_iff_of_coprime (by norm_num : Nat.Coprime 2 3)).1 ⟨hz2, hz3⟩
  have hyk : y ∈ Φ.ker := Prod.ext h1 h2
  have hkerq : Nat.card Φ.ker ∣ (Nat.card K - 1) ^ Tag.E6.rank := by
    rw [hΦker]
    refine (Subgroup.card_range_dvd _).trans ?_
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.card_units]
  have hcop : Nat.Coprime (Nat.card Φ.ker) 3 :=
    Nat.Coprime.coprime_dvd_left hkerq (Nat.Coprime.pow_left _
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hK).symm)
  have hw : (⟨y, hyk⟩ : Φ.ker) = 1 :=
    (pow_eq_one_iff_of_coprime hcop).1 ⟨pow_card_eq_one', Subtype.ext (by simpa using hyp)⟩
  exact (QuotientGroup.eq_one_iff (N := inner (adjointGroup .E6 K)) x).1 (congrArg Subtype.val hw)

theorem exists_hom_ringAut_twistedE6_three {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (h3 : ¬ 3 ∣ ℓ ^ f + 1) :
    ∃ Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K, ∀ x ∈ Θ.ker, x ^ 3 = 1 →
      x ∈ (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, hcube, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  refine ⟨Θ, fun x hx hxp => ?_⟩
  rw [hker] at hx
  exact CFSG.HardMathSupport.Lang.Coordinator.mem_inner_of_mem_inn_sup_diag Nat.prime_three hK hσ
    (fun h => h3 (h.trans (Nat.gcd_dvd_right _ _))) hcube hxp hx

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
