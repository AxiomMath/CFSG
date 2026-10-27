module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeExcBasic
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Transport
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclTE6Kac
public import CFSG.GroupTheory.InnerNormalizedAutomorphisms

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (primePower_p_eq_two_of_card_eq_two)


theorem exists_eq_conj_of_pow_three_E6 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {α : MulAut ↥(adjointGroup Tag.E6 K)} (hα : α ^ 3 = 1) :
    ∃ x : ↥(adjointGroup Tag.E6 K), α = MulAut.conj x := by
  obtain ⟨hfin, hle⟩ :=
    CFSG.SeitzReduction.SeitzQ2.card_outer_le_two_of_mulEquiv_E6_two (K := K) hK
      (MulEquiv.refl ↥(adjointGroup Tag.E6 K))
  haveI := hfin
  have hne : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      ↥(adjointGroup Tag.E6 K)) := by
    intro h3
    have hge : 3 ≤ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        ↥(adjointGroup Tag.E6 K)) :=
      Nat.le_of_dvd (Nat.card_pos (α := CFSG.ComponentClassification.OuterAutomorphisms.Outer
        ↥(adjointGroup Tag.E6 K))) h3
    omega
  have hmem := CFSG.LocalAnalysis.GLTheoremA.CatB.forall_cube_inner_of_card_outer hne α hα
  rw [CFSG.ComponentClassification.OuterAutomorphisms.inner] at hmem
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hmem
  exact ⟨x, hx.symm⟩

theorem noSmall_adjointGroup_E6 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    HStdExcl.NoSmall ↥(adjointGroup Tag.E6 K) := by
  intro α hα3 hα1 I hI hsmall
  have hcomp := CFSG.StandardType.ExcThreeAtTwo.centCompNotExcThreeAt_three_adjointGroup
    (τ := Tag.E6) (Or.inr (Or.inl rfl)) CFSG.StandardType.excThreeTwoRatNotExc_E6 hK
  obtain ⟨s, hs⟩ := exists_eq_conj_of_pow_three_E6 hK hα3
  have hs3 : s ^ 3 = 1 := by
    have hconj : MulAut.conj (s ^ 3) = 1 := by rw [map_pow, ← hs, hα3]
    have hmem := CFSG.InnerNormalizedAutomorphisms.mem_center_of_conj_eq_one hconj
    rwa [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.mem_bot] at hmem
  have hfix : fixSubgroup α = Subgroup.centralizer ({s} : Set ↥(adjointGroup Tag.E6 K)) := by
    rw [hs, CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_fixSubgroup_conj]
  rw [hfix] at hI
  exact HStdExcl.not_smallOrd_of_ggNotExcThreeOrder I
    (hcomp s hs3 I ((CFSG.Assembly.isComponentOf_iff_open).mpr hI)) hsmall

theorem noSmall_adjointGroup_E7_E8 {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    HStdExcl.NoSmall ↥(adjointGroup τ K) := by
  intro α hα3 hα1 I hI hsmall
  have hrat : CFSG.StandardType.ExcThreeTwoRatNotExc τ := by
    rcases hτ with rfl | rfl
    · exact CFSG.StandardType.excThreeTwoRatNotExc_E7
    · exact CFSG.StandardType.excThreeTwoRatNotExc_E8
  have hcomp := CFSG.StandardType.ExcThreeAtTwo.centCompNotExcThreeAt_three_adjointGroup
    (τ := τ) (by rcases hτ with rfl | rfl <;> simp) hrat hK
  obtain ⟨s, hs⟩ := CFSG.SeitzReduction.E8Pilot.exists_eq_conj_of_card_eq_two hτ hK α
  have hs3 : s ^ 3 = 1 := by
    have hconj : MulAut.conj (s ^ 3) = 1 := by rw [map_pow, ← hs, hα3]
    have hmem := CFSG.InnerNormalizedAutomorphisms.mem_center_of_conj_eq_one hconj
    rwa [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.mem_bot] at hmem
  have hfix : fixSubgroup α = Subgroup.centralizer ({s} : Set ↥(adjointGroup τ K)) := by
    rw [hs, CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_fixSubgroup_conj]
  rw [hfix] at hI
  exact HStdExcl.not_smallOrd_of_ggNotExcThreeOrder I
    (hcomp s hs3 I ((CFSG.Assembly.isComponentOf_iff_open).mpr hI)) hsmall

theorem noSmall_lie_E6 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid)
    (hq : q.card = 2) :
    HStdExcl.NoSmall (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group := by
  have hmodel := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6 q hv (primePower_p_eq_two_of_card_eq_two hq)
    (MulEquiv.refl _)
  obtain ⟨K, hfield, hfinite, hK, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup Tag.E6 hmodel
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hK2 : Nat.card K = 2 := by
    rw [hK, ← TauCeti.PrimePower.card_def]
    exact hq
  exact noSmall_of_mulEquiv e (noSmall_adjointGroup_E6 hK2)

theorem noSmall_lie_E7 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid)
    (hq : q.card = 2) :
    HStdExcl.NoSmall (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group := by
  have hmodel := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_E7 q hv (primePower_p_eq_two_of_card_eq_two hq)
    (MulEquiv.refl _)
  obtain ⟨K, hfield, hfinite, hK, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup Tag.E7 hmodel
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hK2 : Nat.card K = 2 := by
    rw [hK, ← TauCeti.PrimePower.card_def]
    exact hq
  exact noSmall_of_mulEquiv e (noSmall_adjointGroup_E7_E8 (Or.inl rfl) hK2)

theorem noSmall_lie_E8 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid)
    (hq : q.card = 2) :
    HStdExcl.NoSmall (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group := by
  have hmodel := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_E8 q hv (primePower_p_eq_two_of_card_eq_two hq)
    (MulEquiv.refl _)
  obtain ⟨K, hfield, hfinite, hK, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup Tag.E8 hmodel
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hK2 : Nat.card K = 2 := by
    rw [hK, ← TauCeti.PrimePower.card_def]
    exact hq
  exact noSmall_of_mulEquiv e (noSmall_adjointGroup_E7_E8 (Or.inr rfl) hK2)

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
