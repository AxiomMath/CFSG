module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Descent

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Quasithin.B69K.OddCovers CFSG.RankThree.PerfectCover

theorem forK_of_kConfig_three {X : Type} [Group X] [Finite X]
    (hM : Nat.card (hopfMultiplier X) = 3)
    (h3 : ∀ (K : Type) [Group K] [Finite K] (L V MK : Subgroup K), KConf K L V MK →
      (K ⧸ Subgroup.center K ≃* X) → Nat.card (Subgroup.center K) = 3 → False)
    (hX : ∀ L V MK : Subgroup X, KConfig X L V MK → ConclK X L V MK) :
    ForK (fun S _ => Nonempty (S ≃* X)) := by
  intro K _ _ L V MK hK h
  obtain ⟨e⟩ := h
  have hdvd : Nat.card (Subgroup.center K) ∣ 3 :=
    hM ▸ card_center_dvd_hopfMultiplier hK.quasisimple.1 e
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3'
  · have hZ : Subgroup.center K = ⊥ := Subgroup.card_eq_one.mp h1
    exact hK.conclK_of_mulEquiv e hX (by rw [hZ, inf_bot_eq]) (fun _ => hZ)
  · exact (h3 K L V MK hK e h3').elim

end CFSG.SectionRank.QTK.Insp443

end
