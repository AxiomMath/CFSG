module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93Facts
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticRank
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallTits
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.ExcTits

public section

namespace CFSG.LocalAnalysis.GLTheoremA.List93

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem subset_inn_of_card_outer_two {G : Type} [Group G] [Finite G]
    (hO : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer G) = 2)
    {E : Subgroup (MulAut G)} (hE : CFSG.Open.IsElemAbelian 3 E) :
    (E : Set (MulAut G)) ⊆ Set.range (MulAut.conj : G →* MulAut G) := by
  intro y hy
  have hy3 : y ^ 3 = 1 := hE.2 y hy
  set q : CFSG.ComponentClassification.OuterAutomorphisms.Outer G :=
    QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner G) y with hq
  have h3 : q ^ 3 = 1 := by
    rw [hq, ← map_pow, hy3, map_one]
  have h2 : q ^ 2 = 1 := by
    rw [← hO]
    exact pow_card_eq_one'
  have h1 : q ^ Nat.gcd 3 2 = 1 := pow_gcd_eq_one.mpr ⟨h3, h2⟩
  have hq1 : q = 1 := by simpa using h1
  have hmem : y ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner G :=
    (QuotientGroup.eq_one_iff y).mp hq1
  exact MonoidHom.mem_range.mp hmem

section Certs


theorem tits_holds : ∀ (S : Type) [Group S] [Finite S], catalogIs S titsIdx →
    (∀ E : Subgroup (MulAut S), CFSG.Open.IsElemAbelian 3 E → Nat.card E < 3 ^ 3) ∧
      ∀ E : Subgroup (MulAut S), CFSG.Open.IsElemAbelian 5 E → Nat.card E < 5 ^ 3 := by
  intro S _ _ hS
  obtain ⟨i, hi, ⟨e⟩⟩ := hS
  cases i with
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    have hd : d1 = TauCeti.LieTypeIndex.tits := hi
    subst hd
    have hO : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) = 2 :=
      CFSG.LocalAnalysis.RankThreeTheoremC.card_outer_of_tits ⟨hv, ⟨e⟩⟩
    have hR : CFSG.Blueprint.ReeTitsModel S .Tits 2 1 :=
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.reeTitsModel_tits_of_equiv e
    obtain ⟨eT⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv S 2 1 hR
    have hZ : Subgroup.center S = ⊥ :=
      CFSG.StandardType.TableBExcSmallRest.center_eq_bot_of_mulEquiv eT
        CFSG.Sporadic.Schreier.Tits.titsD_center
    refine ⟨fun E hE => ?_, fun E hE => ?_⟩
    · exact CFSG.StandardType.TableBExcSmallRest.card_lt_of_subset_inn (p := 3) (k := 3) hZ
        (fun A hA => CFSG.StandardType.TableBExcSmallRest.card_lt_of_mulEquiv eT
          (fun E' hE' => CFSG.StandardType.TableBExcSmallRest.ggTitsThreeRankInput_holds E' hE') hA)
        (subset_inn_of_card_outer_two hO hE) hE
    · have hB : Nat.card E ≤ 5 ^ 2 :=
        CFSG.LocalAnalysis.RankFourTheoremC.autRankTwoAt_tits (d := ⟨_, hv⟩) rfl S ⟨e⟩ E hE
      exact lt_of_le_of_lt hB (by norm_num)
  | cyclic p h => exact False.elim hi
  | alternating n h => exact False.elim hi
  | sporadic s => exact False.elim hi

end Certs

end CFSG.LocalAnalysis.GLTheoremA.List93

end
