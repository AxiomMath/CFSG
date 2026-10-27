module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.ThreeA
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.FiveOrbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.TOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.Simple
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.U35

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem tableVII_of_hyps_of_fiveAInv (h5 : TableVIIFiveAInv) (hS : SuborbitFacts)
    (h28 : Segev28) {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z)
    (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z) (_hF3 : Vert Fusion3Facts a z)
    (hPic : Vert A8Pictures a z) (hPar : Vert ParityFacts a z) (hT4 : Vert TableIVFacts a z)
    (hT5 : Vert TableVFacts a z) (hS7 : Vert S7Facts a z) (hT6 : Vert TableVIFacts a z) :
    TableVIIFacts a z := by
  have hPar' := hPar.self
  have hT4' := hT4.self
  have hT5' := hT5.self
  have hS7' := hS7.self
  have hT6' := hT6.self
  have d01 : Disjoint (orb3A a a) (orb5A a a) := Set.disjoint_left.2 fun c h3 h5' => by
    have e1 : orderOf (a * c) = 3 := h3.2.1
    have e2 : orderOf (a * c) = 5 := h5'.2.1
    omega
  have d02 : Disjoint (orb3A a a) (orb5E a a) := Set.disjoint_left.2 fun c h3 h5' => by
    have e1 : orderOf (a * c) = 3 := h3.2.1
    have e2 : orderOf (a * c) = 5 := h5'.2.1
    omega
  have d12 : Disjoint (orb5A a a) (orb5E a a) := tableVII_disjoint_5A_5E
  refine ⟨⟨?_, ?_, ?_, ?_⟩, tableVII_order_three_five h hPar' hT4' hT5' hT6',
    tableVII_card_3A hS7', ?_⟩
  · intro i
    fin_cases i
    · exact tableVII_orb3A_subset h
    · exact fun c hc => hc.1
    · exact fun c hc => hc.1
  · intro c hc
    rcases tableVII_order_three_five h hPar' hT4' hT5' hT6' c hc with h3 | h5'
    · exact ⟨0, tableVII_mem_orb3A h hPar' hT5' hS7' hT6' hc h3⟩
    · rcases tableVII_mem_orb5A_or_orb5E h hPar' hT4' hT5' hT6' hc h5' with hA | hE
      · exact ⟨1, hA⟩
      · exact ⟨2, hE⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact d01
    · exact d02
    · exact d01.symm
    · exact absurd rfl hij
    · exact d12
    · exact d02.symm
    · exact d12.symm
    · exact absurd rfl hij
  · intro i
    fin_cases i
    · exact hS7'.orbit
    · exact tableVII_orbit_5A h hPar' hT4' hT5' hT6'
    · exact tableVII_orbit_5E h hPar' hT4' hT5' hT6'
  · intro c hc
    obtain ⟨t, ht, htc⟩ := hc.1.2.2.2
    have hY : IsNonsplitDoubleCoverOfS5 ↥(Gxyz a t c) := hc.2.2 t ht htc
    obtain ⟨htB, hc5⟩ := tableVII_row5_of_orb5A h hPar' hT4' hT5' hT6' hc ht htc
    obtain ⟨t₁, ht₁, ht₁A, ht₁t⟩ := tableVII_exists_tOne h5 h hF1 hF2 hPic hT5' htB hc5
    obtain ⟨ht₁a, -, ht₁c⟩ := mem_Gxyz.1 ht₁
    have hk := tableVII_conj_in_Gxy h hPar' hT4' hT5' hT6' hc ht htc ht₁A
      (mem_Gxy.2 ⟨ht₁a, ht₁c⟩)
    have ht2 : orderOf t = 2 := tableVII_orderOf_of_isConj_a h ht
    have hsimp : IsSimpleGroup ↥(Gxy a c) :=
      tableVII_isSimple h28 htc ht2 hY ht₁ (tableVII_sq_of_isConj_a h ht₁A) ht₁t hk
    have ht1 : t ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at ht2
      exact absurd ht2 (by decide)
    exact tableVII_shape_U35 hS h htc (tableVII_sq_of_isConj_a h ht) ht1 hsimp hY

theorem tableVII_of_hyps (hS : SuborbitFacts) (h28 : Segev28) {G : Type} [Group G] [Finite G]
    {a z : G} (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z)
    (hF3 : Vert Fusion3Facts a z) (hPic : Vert A8Pictures a z) (hPar : Vert ParityFacts a z)
    (hT4 : Vert TableIVFacts a z) (hT5 : Vert TableVFacts a z) (hS7 : Vert S7Facts a z)
    (hT6 : Vert TableVIFacts a z) : TableVIIFacts a z :=
  tableVII_of_hyps_of_fiveAInv (tableVII_fiveAInv_of_suborbit hS) hS h28 h hF1 hF2 hF3 hPic hPar
    hT4 hT5 hS7 hT6

end CFSG.EvenSporadicStandard.HNRecog.Section3
