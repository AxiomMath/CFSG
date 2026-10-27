module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbTwoVeq
public import CFSG.CGT.PushingUpLit.CGT6.EmbCbTwoModel

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

variable {V : Type} [CommGroup V] [Finite V]

theorem EndCfg4.noTwoLifts {G T Y : Subgroup (MulAut V)} (h2 : Alt2Rank1)
    (h : EndCfg4 G T Y) (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ} (hm : 7 ≤ m) (hodd : Odd m)
    (hY : YAlt Y m) {t : MulAut V} (htG : t ∈ G) (htT : t ∈ T) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    {X₁ X₂ : Subgroup (MulAut V)} (h₁ : IsCbLift G Y t m X₁) (h₂ : IsCbLift G Y t m X₂)
    (hne : X₁ ≠ X₂) : False := by
  obtain ⟨K⟩ := CbtCtx.exists h2 h hV hm hodd hY htG htT ht2 ht1 h₁ h₂ hne
  have hv₂ := K.step2_v
  have hv₁ := K.symm.step2_v
  obtain ⟨hzv₂, hzv₁⟩ := K.beta_eq hv₂ hv₁ K.symm.step2_z K.step2_z
  exact K.false_of_rel ⟨hv₂, hzv₂, hv₁, hzv₁, K.V_eq hv₂ hzv₂ hv₁ hzv₁,
    fun r hr => K.t_fix_R hr⟩

end CFSG.CGT.PushingUpLit.CGT6
