module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieForkDefs
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieThreeModel
import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429Inner
import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM5Lemmas

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.CatLeaf (lieSylowExponent)


theorem i1430LieThree_of_fork (hF : H1420.LieOuterThree) : I1430LieThree := by
  rintro S _ _ hs hnab d hc ⟨e⟩ α hα3 hα1 ⟨J, hJ, hT⟩
  by_cases hin : α ∈ inner S
  · have hchev : IsChevSimple 3 S := Or.inl ⟨.lie d, hc, ⟨e⟩⟩
    have hbot := h1429_kdChevInner_three S hs hnab hchev α hα3 hα1 hin
    exact (glaPComponent_ne_bot' hJ (le_bot_iff.1 (hbot ▸ le_sSup hJ))).elim
  have hO := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  obtain ⟨t, n, f, hm, -, hA⟩ := H1431c.lieS3_exists_model d (by omega) e
  rw [hc] at hm
  have hX360 : Nat.card (PSimple 3 J) = 360 := by
    obtain ⟨i, hi, ⟨g⟩⟩ := hT
    rw [Nat.card_congr g.toEquiv]
    exact SFM5.card_of_isA6 i hi
  obtain ⟨t', n', f', hsh, hX⟩ := (hF S t n f hm.admissible trivial hm α hα3 hin J hJ).resolve_right
    fun h => absurd h.2.2 (by rw [hX360]; decide)
  obtain ⟨rfl, rfl, -, rfl⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltFacts4.tuple_of_card_360 hO hX.admissible hX
      hX360
  rcases hsh with ⟨-, rfl, rfl, rfl⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, h, -⟩
  · obtain ⟨q, hv, rfl⟩ := hA rfl rfl
    have hp : q.p = 3 := by
      change (TauCeti.LieTypeIndex.A 1 q).characteristic = 3 at hc
      rwa [TauCeti.LieTypeIndex.characteristic_A] at hc
    have hm2 : CFSG.Blueprint.LieModel S .PSL (1 + 1) q.p q.exponent :=
      CFSG.Models.LieModel.toBlueprint (by simp [CFSG.Blueprint.classicalTags])
        (CFSG.Models.lieModel_A 1 q hv e)
    rw [hp] at hm2
    have h6 := (hO S _ _ _ _ hm.admissible hm).2.2
    have hk := (hO S _ _ _ _ hm2.admissible hm2).2.2
    rw [h6] at hk
    norm_num [lieSylowExponent] at hk
    have hk6 : q.exponent = 6 := by omega
    show q.card = 729
    norm_num [TauCeti.PrimePower.card_def, hp, hk6]
  all_goals exact absurd h (by decide)

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

end
