module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottSporOddCent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtCMaxHe
public import CFSG.Quasithin.Vol2.KGFactHeInspRank
public import CFSG.Sporadic.Bridge.HeSurj

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

theorem row_He_17 :
    KFactSporLocalRow .He 17 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have eH : CFSG.Blueprint.NativeSporadic.Carrier .He ≃* ↥CFSG.Sporadic.HeldB.heP :=
    CFSG.Sporadic.HeldB.heEquivP
  have h8 : orderOf (2 : ZMod 17) = 8 :=
    orderOf_two_zmod_eq 17 8 (by norm_num) (by decide) (by decide)
  refine row_of_oddCent_rank ↥CFSG.Sporadic.HeldB.heP ⟨CFSG.Sporadic.HeldB.heEquivP.symm.trans b⟩
    ?_ ?_
  · intro t z ht hz htz
    have hzC : z ∈ Subgroup.centralizer ({t} : Set ↥CFSG.Sporadic.HeldB.heP) :=
      Subgroup.mem_centralizer_singleton_iff.mpr htz.symm
    have h17 : 17 ∣ Nat.card (Subgroup.centralizer ({t} : Set ↥CFSG.Sporadic.HeldB.heP)) := by
      rw [← hz, ← Subgroup.orderOf_mk z hzC]
      exact orderOf_dvd_natCard _
    rcases CFSG.Quasithin.GoldCMaxA.he_card_centralizer (MulEquiv.refl _) ht with h | h <;>
      rw [h] at h17 <;> norm_num at h17
  · rw [h8]
    exact CFSG.QuasithinUnique.Lin2.RankCert.ElemAbelianLt.of_mulEquiv eH.symm
      CFSG.Quasithin.H13.KGRank.elemAbelianLt_he

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
