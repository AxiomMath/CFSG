module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.Count
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.Row2B
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.Row4A
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.Sets

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem tableIII_of_hyps (hI : TwoHSInterface) (hS : SuborbitFacts) {G : Type} [Group G]
    [Finite G] {a z : G} (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z)
    (hF2 : Vert Fusion2Facts a z) (hF3 : Vert Fusion3Facts a z) (hPic : Vert A8Pictures a z)
    (hOrb : Vert GzOrbitFacts a z) (hSGz : Vert StructGzFacts a z)
    (hSX : Vert StructXFacts a z) : TableIIIFacts a z := by
  have hOrb0 : GzOrbitFacts a z := hOrb.self
  have hSGz0 : StructGzFacts a z := hSGz.self
  have key : ∀ a' ∈ Qz z, IsConj a a' →
      IsOrbitPartition (Gxy a' z) (tab3Base a z a') (tab3Set a z a') ∧
        StabCard (Gxy a' z) (tab3Set a z a') ![2 ^ 8 * 3, 2 ^ 10, 2 ^ 7 * 5] := by
    intro a' ha'Q ha'
    have hX : XStruct a z a' := hSX.self.x_struct a' ha'Q ha'
    refine tableIII_count (tableIII_card_Gxy hX) (tableIII_card_base hI h hOrb0 ha'Q ha')
      tableIII_subset (tableIII_cover h hF1 hF2 ha'Q ha') (tableIII_disjoint hI h)
      (fun i k hk c hc => tableIII_conj_mem i hk hc) ?_ ?_ ?_
    · rw [tableIII_set0_eq hI h hX ha'Q ha']
      exact hX.o1
    · intro c hc
      rw [← Gxyz_eq_inf]
      exact tableIII_card_stab_2B hI h hF2 hSGz0 hX ha'Q ha' hc
    · intro c hc
      rw [← Gxyz_eq_inf]
      exact tableIII_card_stab_4A hI h hSGz0 hX ha'Q ha' hc
  refine ⟨fun a' ha'Q ha' => tableIII_card_base hI h hOrb0 ha'Q ha',
    fun a' ha'Q ha' => (key a' ha'Q ha').1, fun a' ha'Q ha' => (key a' ha'Q ha').2, ?_⟩
  intro a' ha'Q ha' c hc
  have hcard : Nat.card ↥(Gxy a' z ⊓ Gx c) = 2 ^ 7 * 5 := (key a' ha'Q ha').2 2 c hc
  rw [← Gxyz_eq_inf] at hcard
  exact tableIII_shape_4A (tableIII_card_inf_Qz_4A hI h ha'Q ha' hc) hcard

end CFSG.EvenSporadicStandard.HNRecog.Section3
