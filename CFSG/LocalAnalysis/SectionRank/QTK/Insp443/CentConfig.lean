module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConfig
public import CFSG.Quasithin.Vol2.KGFactC31Orb
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual

public section

namespace CFSG.SectionRank.QTK.Insp443

variable {K : Type} [Group K] {L V MK : Subgroup K}

theorem KConfig.le_centralizer (h : KConfig K L V MK) :
    V ≤ Subgroup.centralizer (V : Set K) :=
  Subgroup.le_centralizer_iff_isMulCommutative.mpr h.elemAbelian.1

theorem KConfig.centralizer_eq_of_le (h : KConfig K L V MK) {U : Subgroup K} (hUV : U ≤ V)
    (hab : ∀ a ∈ Subgroup.centralizer (U : Set K), ∀ b ∈ Subgroup.centralizer (U : Set K),
      a * b = b * a) :
    Subgroup.centralizer (V : Set K) = Subgroup.centralizer (U : Set K) := by
  have hVC : V ≤ Subgroup.centralizer (U : Set K) :=
    h.le_centralizer.trans (Subgroup.centralizer_le hUV)
  refine le_antisymm (Subgroup.centralizer_le hUV) fun c hc => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact hab v (hVC hv) c hc

theorem KConfig.le_normalizer_centralizer (h : KConfig K L V MK) :
    L ≤ Subgroup.normalizer (Subgroup.centralizer (V : Set K) : Set K) :=
  h.le_normalizer.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer V)

theorem KConfig.normalizer_centralizer_le (h : KConfig K L V MK)
    (h2 : IsPGroup 2 ↥(Subgroup.centralizer (V : Set K))) :
    Subgroup.normalizer (Subgroup.centralizer (V : Set K) : Set K) ≤
      Subgroup.normalizer (L : Set K) := by
  refine (h.normalizer_le _ ?_ h2 fun σ hσV _ _ => ?_).trans h.MK_le_normalizer
  · intro hbot
    apply h.ne_bot
    rw [eq_bot_iff, ← hbot]
    exact h.le_centralizer
  · have hc := CFSG.Quasithin.KGC31.map_centralizer_eq σ.toMonoidHom σ.injective V
    rwa [MonoidHom.range_eq_top.mpr σ.surjective, top_inf_eq, hσV] at hc

end CFSG.SectionRank.QTK.Insp443

end
