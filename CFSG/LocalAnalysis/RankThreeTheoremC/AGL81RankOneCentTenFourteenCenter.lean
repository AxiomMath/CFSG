module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentTenFourteen
import CFSG.LieType.Catalog.Realization
import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusBlocks
import CFSG.Sporadic.Bridge.J4Surj
import CFSG.Sporadic.Presentation.McLExact
public import CFSG.Sporadic.McL.Simple

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers

theorem isSimpleGroup_sporadic_of_bridge {s : TauCeti.SporadicName}
    (hb : Nonempty (Blueprint.NativeSporadic.Carrier s ≃* s.Group))
    (hs : IsSimpleGroup (Blueprint.NativeSporadic.Carrier s)) :
    IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group :=
  hb.some.symm.isSimpleGroup

theorem isSimpleGroup_of_isTenFourteenOneIndex
    {p : ℕ} : ∀ {i : TauCeti.CFSGIndex}, IsTenFourteenOneIndex p i → IsSimpleGroup i.Group
  | .cyclic _ _, h => h.elim
  | .alternating n _, h => by
      change IsSimpleGroup (alternatingGroup (Fin n))
      refine alternatingGroup.isSimpleGroup ?_
      rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  | .lie d, _ => by
      obtain ⟨t, n, r, f, -, hm, -, -, -⟩ :=
        CFSG.RankThree.PartOne.CTP.seitzBridge d.Group d.1 ⟨d.2, ⟨MulEquiv.refl _⟩⟩
      exact (CFSG.LieType.Catalog.lieModel_finite_simple d.Group t n r f hm).2.2
  | .sporadic s, h => by
      rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact isSimpleGroup_sporadic_of_bridge CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
          CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
      · exact isSimpleGroup_sporadic_of_bridge CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
          CFSG.Sporadic.McL.fam_mcl_simplicity.2.2
      · exact isSimpleGroup_sporadic_of_bridge CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
          CFSG.Sporadic.J4.fam_j4_simplicity.2.2

theorem center_eq_bot_of_tenFourteenOneGroup
    {p : ℕ} {K : Type*} [Group K] (hK : TenFourteenOneGroup p K)
    (hnc : ∃ a b : K, a * b ≠ b * a) : Subgroup.center K = ⊥ := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hK
  haveI := isSimpleGroup_of_isTenFourteenOneIndex hi
  haveI : IsSimpleGroup K := e.isSimpleGroup
  rcases (Subgroup.center K).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnc
    exact (hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)).elim

variable {G : Type} [Group G] [Finite G]

theorem exists_not_comm_of_d1KBar_ne_bot {p : ℕ} {M C : Subgroup G} (h : d1KBar p M C ≠ ⊥) :
    ∃ a b : ↥(d1KBar p M C), a * b ≠ b * a := by
  obtain ⟨L, hL, hLX⟩ : ∃ L : Subgroup (C ⧸ primeComplementCore (G := C) p),
      IsComponentOf L ⊤ ∧ ¬ L ≤ d1X0 p M C := by
    by_contra hno
    push Not at hno
    exact h (iSup₂_eq_bot.mpr fun L hL => absurd hL.2 (not_not.mpr (hno L hL.1)))
  have hLK : L ≤ d1KBar p M C := le_iSup₂_of_le L ⟨hL, hLX⟩ le_rfl
  by_contra hc
  push Not at hc
  refine LeviBlock.orthMinus_not_isQuasisimple_of_comm (fun x y => ?_) hL.2.2
  have := hc ⟨x, hLK x.2⟩ ⟨y, hLK y.2⟩
  exact Subtype.ext (by simpa using congrArg Subtype.val this)

theorem center_d1KBar_eq_bot_of_tenFourteenOneGroup
    {p : ℕ} {M C : Subgroup G} (h : d1KBar p M C ≠ ⊥)
    (hK : TenFourteenOneGroup p ↥(d1KBar p M C)) : Subgroup.center ↥(d1KBar p M C) = ⊥ :=
  center_eq_bot_of_tenFourteenOneGroup hK (exists_not_comm_of_d1KBar_ne_bot h)

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
