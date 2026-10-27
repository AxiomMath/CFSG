module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdExclHolds
public import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoRat
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc
public import CFSG.Goldschmidt.Steps.G310Comp
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassical
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalRows
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwo
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalModel
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4O2
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.L44CoverTrivial
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8L4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTM5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cClause
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE81
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
public import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs
public import Certificates.Certificate9530
public import Certificates.Data.U62Rank.Check

public section

namespace CFSG.LocalAnalysis.GLTheoremA.FStdDiag

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Solomon.Coordinator renaming fixSubgroup → coordFix
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (components_of_langSetup fixSubgroup_congr)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  (exists_langSetup_of_inner_untw_of_prime langSetup_hTame_of_prime natCast_ne_zero_algebraicClosure
    baseChange_mem_adjointGroup_of_mem_inndiag monomialToralAt_exc monomialToralAt_E6_five
    monomialToralAt_E7_five)
open CFSG.LocalAnalysis.GLTheoremA.HStdExcl (SmallOrd NoSmall smallOrd_of_mulEquiv exclTE6_holds)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived mem_innAutDerived_congr)
open CFSG.StandardType CFSG.StandardType.ExcThreeAtTwo

@[expose] def FStdNoSmallInn (S : Type) [Group S] : Prop :=
  ∀ α : MulAut S, α ∈ innAutDerived S → α ^ 3 = 1 → α ≠ 1 →
    ∀ I : Subgroup S, IsComponentOf I (coordFix α) → ¬ SmallOrd I

theorem fstdNoSmallInn_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (h : FStdNoSmallInn T) : FStdNoSmallInn S := by
  intro α hα hα3 hα1 I hI hsmall
  have hmem : MulAut.congr e α ∈ innAutDerived T := (mem_innAutDerived_congr e).2 hα
  have hp : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have h1 : MulAut.congr e α ≠ 1 := fun h' =>
    hα1 ((MulAut.congr e).injective (h'.trans (map_one _).symm))
  have hI' : IsComponentOf (I.map (e : S →* T)) (coordFix (MulAut.congr e α)) := by
    rw [fixSubgroup_congr e α]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hI
  exact h _ hmem hp h1 _ hI'
    (smallOrd_of_mulEquiv (Subgroup.equivMapOfInjective I (e : S →* T) e.injective) hsmall)

theorem fstdNoSmallInn_of_noSmall {S : Type} [Group S] (h : NoSmall S) : FStdNoSmallInn S :=
  fun α _ h3 h1 I hI => h α h3 h1 I hI

section Lang


theorem fstdNoSmallInn_adjointGroup_two {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) : FStdNoSmallInn ↥(adjointGroup τ K) := by
  classical
  intro β hβ hβ3 hβ1 J hJ hsmall
  obtain ⟨h, hh, hβh, hp1, hh1⟩ : ∃ h ∈ CFSG.StandardType.RecipeExcLang.inndiagGroup τ K,
      (∀ c : adjointGroup τ K, (β c : ModGL τ K) = h * c * h⁻¹) ∧ h ^ 3 = 1 ∧ h ≠ 1 := by
    rcases hτ with rfl | rfl | rfl | rfl
    · exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.exists_inndiag_of_mem_innAutDerived_F4
        β hβ hβ3 hβ1
    · exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.exists_inndiag_of_mem_innAutDerived_E
        (Or.inl rfl) Nat.prime_three β hβ hβ3 hβ1
    · exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.exists_inndiag_of_mem_innAutDerived_E
        (Or.inr (Or.inl rfl)) Nat.prime_three β hβ hβ3 hβ1
    · exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw.exists_inndiag_of_mem_innAutDerived_E
        (Or.inr (Or.inr rfl)) Nat.prime_three β hβ hβ3 hβ1
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h | h <;> simp [h]
  have hτ2 : τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h | h <;> simp [h]
  have hτ3 : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h | h <;> simp [h]
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ := single_edge_perfect τ K hτ2
  have h3K : ¬ 3 ∣ Nat.card K := by rw [hK]; norm_num
  have h5K : ¬ 5 ∣ Nat.card K := by rw [hK]; norm_num
  have hmon : MonomialToralAt τ 3 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five hτ3 Nat.prime_three
      (by norm_num)
  obtain ⟨S, a, ι, hSq, ⟨Fr, hFr1, hFr2⟩, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime hτ' Nat.prime_three h3K Nat.prime_five h5K
      (Or.inl le_rfl) hmon hperf β h (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1
  have h3L : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure Nat.prime_three h3K
  have hTame := langSetup_hTame_of_prime S Nat.prime_three h3L
    (fun h' => absurd h' (by rcases hτ with h | h | h | h <;> simp [h])) hT hap h1
  obtain ⟨i, hq, hJR⟩ := components_of_langSetup S Nat.prime_three ι hinj hrange β hconj hT hap
    h1 hTame hJ
  have hrat : ExcThreeTwoRatNotExc τ := by
    rcases hτ with rfl | rfl | rfl | rfl
    · exact excThreeTwoRatNotExc_F4
    · exact excThreeTwoRatNotExc_E6
    · exact excThreeTwoRatNotExc_E7
    · exact excThreeTwoRatNotExc_E8
  obtain ⟨-, h25920, h360⟩ := hrat (AlgebraicClosure K) 5 S
    ⟨Fr, fun c => by rw [hSq]; exact hFr1 c, hFr2⟩ (hSq.trans hK) a hT hap h1 i hq
  have hcq : ggCQ J = ggCQ (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
    rw [← ggCQ_map_of_injective ι hinj J, hJR]
  rcases hsmall with h' | h'
  · exact h25920 (by rw [← hcq]; exact h')
  · exact h360 (by rw [← hcq]; exact h')

theorem fstdNoSmallInn_twistedE6_two {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = 4) (hσ : ∀ c, σ c = c ^ 2) : FStdNoSmallInn ↥(twistedE6RootGroup K σ) :=
  fstdNoSmallInn_of_noSmall (exclTE6_holds K σ hK hσ)

end Lang

end CFSG.LocalAnalysis.GLTheoremA.FStdDiag

end
