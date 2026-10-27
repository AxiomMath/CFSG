module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAltK3
import CFSG.CGT.PushingUpLit.CGT6.EmbAltIH

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open
open CFSG.ComponentClassification

theorem altM4_of (hNL : NatLiftStatement) : AltM4 := by
  intro V _ _ hV G T Y h m hm hodd hY θ a b c d hab hac had hbc hbd hcd hstab
  have hYG : Y ≤ G := fun y hy => (h.adm.hYC hy).1
  have hLG : conjClosure Y G ≤ G := conjClosure_le hYG
  have hYL : Y ≤ conjClosure Y G := le_conjClosure
  have hLn : ((conjClosure Y G).subgroupOf G).Normal :=
    ⟨fun n hn g => (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure g.2) n).mp hn⟩
  have hLnt : Nontrivial ↥(conjClosure Y G) := by
    obtain ⟨ε⟩ := hY
    have : Nontrivial (alternatingGroup (Fin m)) :=
      alternatingGroup.nontrivial_of_three_le_card (by simp; omega)
    have hYnt : Nontrivial ↥Y := ε.toEquiv.nontrivial
    rw [Subgroup.nontrivial_iff_ne_bot] at hYnt ⊢
    exact ne_bot_of_le_ne_bot hYnt hYL
  obtain ⟨K, θK, hKL, hKst, hnat⟩ :=
    h.natSection_stab_two hV hm hodd hY hLG θ hYL hab hac had hbc hbd hcd hstab
  obtain ⟨hC, hVL⟩ := h.fixV_commV_of_normal hLG hLn hLnt
  have hrec := rec418 hV (hodd.add_even even_two) (by omega : 7 ≤ m + 2) θ hcd hKL hKst θK hnat
    hC hVL
  obtain ⟨c0, rfl⟩ := hodd
  have hcard : ({a, b, c, d} : Finset (Fin (2 * c0 + 1 + 4))).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]
  have hlift := hNL V hV (conjClosure Y G) Y (c0 + 2) c0 (by omega) (by omega) (by omega) θ hrec
    {a, b, c, d} (by rw [hcard]; omega) hYL hstab
  exact h.nolift ⟨conjClosure Y G, hYL, hLG, hLn.isSubnormal, Or.inl hlift⟩

theorem alt2Rank1_holds (hB : TauCetiCatalogBridge)
    (hK3 : RankTwoStandard.RankTwoAlternatingStandard) (hNL : NatLiftStatement) : Alt2Rank1 :=
  alt2Rank1_of hB hK3 (altM4_of hNL)

end CFSG.CGT.PushingUpLit.CGT6
