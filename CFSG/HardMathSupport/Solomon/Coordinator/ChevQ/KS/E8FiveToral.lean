module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveToralColumns
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FrameDatum

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveSq
  CFSG.ComponentClassification.CatLeafProof
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist

set_option linter.unusedSectionVars false

section Statements


@[expose] def E8OneFiveToralNormalizes : Prop :=
  ∀ (K : Type) [Field K] [Finite K], orderOf ((Nat.card K : ℕ) : ZMod 5) = 1 →
    ∀ E₀ : Subgroup (adjointGroup .E8 K), CFSG.Open.IsElemAbelian 5 E₀ → Nat.card E₀ = 5 ^ 3 →
      Nonempty (LangPlaneData .E8 K E₀) → NormalizesRGroup (ringChar K) E₀

@[expose] def E8OneFiveNonToralGriess : Prop :=
  ∀ (K : Type) [Field K] [Finite K], orderOf ((Nat.card K : ℕ) : ZMod 5) = 1 →
    ∀ E₀ : Subgroup (adjointGroup .E8 K), CFSG.Open.IsElemAbelian 5 E₀ → Nat.card E₀ = 5 ^ 3 →
      IsEmpty (LangPlaneData .E8 K E₀) → ¬ NormalizesRGroup (ringChar K) E₀ →
      ∃ (ζ : K) (hζ : IsPrimitiveRoot ζ 5) (a : Fin Tag.E8.rank → Kˣ) (g : adjointGroup .E8 K),
        E₀ = (griessCubeT hζ a).map (MulAut.conj g).toMonoidHom

@[expose] def E8TwoFiveToralInD8 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 5 ∣ Nat.card K + 1 →
    ∀ E₀ : Subgroup (adjointGroup .E8 K), CFSG.Open.IsElemAbelian 5 E₀ → Nat.card E₀ = 5 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → Nonempty (LangPlaneData .E8 K E₀) →
      ∃ g : adjointGroup .E8 K, E₀.map (MulAut.conj g).toMonoidHom ≤ ⨆ k, e8D8Chain K k

@[expose] def E8TwoFiveNonToral : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 5 ∣ Nat.card K + 1 →
    ∀ E₀ : Subgroup (adjointGroup .E8 K), CFSG.Open.IsElemAbelian 5 E₀ → Nat.card E₀ = 5 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → IsEmpty (LangPlaneData .E8 K E₀) → HyperGen 5 ⊤ E₀

theorem e8OneFiveCubeRest4_of_toral_nonToral (ht : E8OneFiveToralNormalizes)
    (hn : E8OneFiveNonToralGriess) : SeitzExcOpenRest4.E8OneFiveCubeRest4 := by
  intro K _ _ he E₀ hE₀ hc hN hnot
  rcases isEmpty_or_nonempty (LangPlaneData .E8 K E₀) with h | h
  · obtain ⟨ζ, hζ, a, g, hg⟩ := hn K he E₀ hE₀ hc h hN
    exact absurd hg (hnot ζ hζ a g)
  · exact absurd (ht K he E₀ hE₀ hc h) hN

theorem e8TwoFiveCubeRest_of_toral_nonToral (ht : E8TwoFiveToralInD8) (hn : E8TwoFiveNonToral) :
    SeitzExcOpenRest3.E8TwoFiveCubeRest := by
  intro K _ _ hpq E₀ hE₀ hc hN hnot
  rcases isEmpty_or_nonempty (LangPlaneData .E8 K E₀) with h | h
  · exact hn K hpq E₀ hE₀ hc hN h
  · exact absurd (ht K hpq E₀ hE₀ hc hN h) hnot

end Statements

section Toral


theorem regular_of_not_normalizes {K : Type} [Field K] [Finite K]
    {E₀ : Subgroup (adjointGroup Tag.E8 K)} (D : LangPlaneData Tag.E8 K E₀)
    (hN : ¬ NormalizesRGroup (ringChar K) E₀) : ∀ α, IsRoot Tag.E8 α → ¬ D.Kills α :=
  fun α hα hk => by
    obtain ⟨u, hu, hur, hc⟩ := langPlaneKillsRoot_E8 K E₀ D α hα hk
    exact hN (SeitzExcOpenRest4.normalizesRGroup_of_commute hu hur hc)

theorem e8OneFiveToralNormalizes_holds : E8OneFiveToralNormalizes := by
  intro K _ _ he E₀ hE₀ hc ⟨D⟩
  by_contra hN
  have hpK : ¬ 5 ∣ Nat.card K := e8Five_not_dvd_of_orderOf_eq_one he
  obtain ⟨z, hz⟩ := exists_eigenTriple_of_langPlaneData hpK hE₀ hc D
    (regular_of_not_normalizes D hN)
  have hq : ((Nat.card K : ℕ) : ZMod 5) = 1 := orderOf_eq_one_iff.1 he
  rw [hq] at hz
  exact hN (normalizesRGroup_of_native (e8_normalizesRNative_of_split_datum D hz.eq_one))

theorem e8TwoFiveToralWeyl_holds :
    ∀ (K : Type) [Field K] [Finite K], 5 ∣ Nat.card K + 1 →
      ∀ E₀ : Subgroup (adjointGroup .E8 K), CFSG.Open.IsElemAbelian 5 E₀ → Nat.card E₀ = 5 ^ 3 →
        ¬ NormalizesRGroup (ringChar K) E₀ → ∀ D : LangPlaneData .E8 K E₀,
          ∀ u : Fin Tag.E8.rank → ℤ, D.w • u = -u := by
  intro K _ _ hpq E₀ hE₀ hc hN D
  have hpK : ¬ 5 ∣ Nat.card K :=
    CFSG.HardMathSupport.Timmesfeld.Proving.not_five_dvd_of_dvd_add_one hpq
  obtain ⟨z, hz⟩ := exists_eigenTriple_of_langPlaneData hpK hE₀ hc D
    (regular_of_not_normalizes D hN)
  have hq : ((Nat.card K : ℕ) : ZMod 5) = -1 := by
    have h := (ZMod.natCast_eq_zero_iff (Nat.card K + 1) 5).2 hpq
    rw [Nat.cast_add, Nat.cast_one] at h
    exact eq_neg_of_add_eq_zero_left h
  rw [hq] at hz
  obtain ⟨w₀, hw₀⟩ := exists_weyl_neg_E8_five
  exact hz.eq_neg hw₀

theorem e8TwoFiveToralInD8_holds : E8TwoFiveToralInD8 := by
  intro K _ _ hpq E₀ hE₀ hc hN ⟨D⟩
  obtain ⟨k, hk⟩ := exists_conj_le_of_frameDatum hE₀.2 D
    (e8FiveTwoFrameDatum_holds K hpq D.Fr D.hFr D.w (e8TwoFiveToralWeyl_holds K hpq E₀ hE₀ hc hN D))
  exact ⟨k, hk.trans e8FrameGroup_le_d8⟩

theorem e8OneFiveCubeRest4_of_nonToral (h : E8OneFiveNonToralGriess) :
    SeitzExcOpenRest4.E8OneFiveCubeRest4 :=
  e8OneFiveCubeRest4_of_toral_nonToral e8OneFiveToralNormalizes_holds h

theorem e8TwoFiveCubeRest_of_nonToral (h : E8TwoFiveNonToral) :
    SeitzExcOpenRest3.E8TwoFiveCubeRest :=
  e8TwoFiveCubeRest_of_toral_nonToral e8TwoFiveToralInD8_holds h

end Toral

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
