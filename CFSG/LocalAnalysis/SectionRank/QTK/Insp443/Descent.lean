module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.DescentConfig
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.DescentConcl
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.RefConfig
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.OddCoversLift

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Quasithin CFSG.Quasithin.B69K.OddCovers CFSG.RankThree.PerfectCover

theorem KConf.conclK_of_mulEquiv {K X : Type} [Group K] [Finite K] [Group X]
    {L V MK : Subgroup K} (hK : KConf K L V MK) (e : K ⧸ Subgroup.center K ≃* X)
    (hX : ∀ L V MK : Subgroup X, KConfig X L V MK → ConclK X L V MK)
    (hLZ : L ⊓ Subgroup.center K = ⊥)
    (hJ4 : CFSG.Quasithin.IsSporadic .J4 X → Subgroup.center K = ⊥) : ConclK K L V MK := by
  let Z := Subgroup.center K
  let q : K →* K ⧸ Z := QuotientGroup.mk' Z
  let π : K →* X := e.toMonoidHom.comp q
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hker : π.ker = Z := by
    ext l
    simp only [π, q, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hodd : Odd (Nat.card π.ker) := by
    rw [hker]
    exact hK.odd_card_center
  have hc : ConclK X (L.map π) (V.map π) (MK.map π) := by
    have hbar : KConfig X ((L.map q).map e.toMonoidHom) ((V.map q).map e.toMonoidHom)
        ((MK.map q).map e.toMonoidHom) := (hK.kConfig_bar).map_mulEquiv e
    have h1 := hX _ _ _ hbar
    simpa only [Subgroup.map_map] using h1
  exact conclK_of_map π hπ (le_of_eq hker) hodd hK.elemAbelian hK.le_normalizer
    (by rw [hker]; exact hLZ) (fun hJ => by rw [hker]; exact hJ4 hJ) hc

theorem center_eq_bot_of_hopfMultiplier {K X : Type} [Group K] [Finite K] [Group X]
    (hK : CFSG.IsQuasisimple K) (hodd : Odd (Nat.card (Subgroup.center K)))
    (e : K ⧸ Subgroup.center K ≃* X) (hM : Nat.card (hopfMultiplier X) ∣ 2) :
    Subgroup.center K = ⊥ := by
  have hdvd : Nat.card (Subgroup.center K) ∣ 2 :=
    (card_center_dvd_hopfMultiplier hK.1 e).trans hM
  have hcop : Nat.Coprime (Nat.card (Subgroup.center K)) 2 :=
    (Nat.coprime_two_left.mpr hodd).symm
  exact Subgroup.card_eq_one.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem forK_of_kConfig {X : Type} [Group X] [Finite X]
    (hM : Nat.card (hopfMultiplier X) ∣ 2)
    (hX : ∀ L V MK : Subgroup X, KConfig X L V MK → ConclK X L V MK) :
    ForK (fun S _ => Nonempty (S ≃* X)) := by
  intro K _ _ L V MK hK h
  obtain ⟨e⟩ := h
  have hZ : Subgroup.center K = ⊥ :=
    center_eq_bot_of_hopfMultiplier hK.quasisimple hK.odd_card_center e hM
  exact hK.conclK_of_mulEquiv e hX (by rw [hZ, inf_bot_eq]) (fun _ => hZ)

end CFSG.SectionRank.QTK.Insp443

end
