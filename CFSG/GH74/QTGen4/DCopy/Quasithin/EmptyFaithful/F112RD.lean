module

public import CFSG.Quasithin.EmptyFaithful.F112RD
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152UF112

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X
open CFSG.Quasithin.He9 (isQuasithinSub_of)

theorem input15208F112At_S3_S3_of_gold_F4 (hGoldP : F6.GoldschmidtCharTwoLargePair.{0})
    (h1515 : StageLemma1515CE) (h1519 : StageLemma1519) (h15207 : StageLemma15207_F4)
    (h15201 : StageLemma15201_F4) (h15112 : StageLemma15112) :
    Input15208F112At_F4 (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3)) := by
  intro G _ _ T Mc M hs H hH Y₁ hY₁ hqH hq₁
  have c : F112RR.Ctx T Mc M H Y₁ :=
    ⟨hs, hH, h1515 G T Mc M hs.qtfe hs.mf hs.ce, h1519 G T Mc M hs.qtfe hs.mf hs.ce, hY₁,
      h15207 G T Mc M hs Y₁ hY₁⟩
  obtain ⟨hUab, hUP, hPT, -, hU64⟩ := F112RR.exists_elemAbelian_card_ge hs hH c.c1519
    (h15201 G T Mc M hs) (h15112 G T Mc M hs.qtfe hs.mf hs.ce H hH).1
  have hpair := c.goldschmidtPair hqH hq₁
  have hUT : conjClosure (V154 T Mc M) H ≤ H ⊓ (Y₁ ⊔ T) := by
    rw [c.H_inf_X hqH]
    exact hUP.trans hPT
  have hcard : 32 ≤ Nat.card ↥(H ⊓ (Y₁ ⊔ T)) :=
    (by omega : 32 ≤ 64).trans (hU64.trans (Subgroup.card_le_of_le hUT))
  have hcase := hGoldP G H (Y₁ ⊔ T) hpair c.charTwo_H c.charTwo_X hcard
  rcases F6.isGoldCaseVICat_of_charTwo hcase c.charTwo_H c.charTwo_X with h | h
  · have := F112RR.card_elemAbelian_lt_sixtyFour hpair h hUT hUab
    omega
  · have hUT' : conjClosure (V154 T Mc M) H ≤ (Y₁ ⊔ T) ⊓ H := by rwa [inf_comm]
    have := F112RR.card_elemAbelian_lt_sixtyFour hpair.symm h hUT' hUab
    omega

end CFSG.Quasithin
