module

public import CFSG.Quasithin.EmptyFaithful.F112F53Res
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152UF112

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X
open CFSG.Quasithin.He9 (isQuasithinSub_of)

theorem input15208F112At_S5_S3_of_res_F4 (hR : Input15208F53Res) (h1515 : StageLemma1515CE)
    (h1519 : StageLemma1519) (h15207 : StageLemma15207_F4) (h15201 : StageLemma15201_F4)
    (h15112 : StageLemma15112) :
    Input15208F112At_F4 (Equiv.Perm (Fin 5)) (Equiv.Perm (Fin 3)) := by
  intro G _ _ T Mc M hs H hH Y₁ hY₁ hφ hq₁
  obtain ⟨φ⟩ := hφ
  have c : S5Ctx T Mc M H Y₁ φ :=
    ⟨hs, hH, h1515 G T Mc M hs.qtfe hs.mf hs.ce, h1519 G T Mc M hs.qtfe hs.mf hs.ce, hY₁,
      h15207 G T Mc M hs Y₁ hY₁⟩
  have hc := (h15112 G T Mc M hs.qtfe hs.mf hs.ce H hH).1
  obtain ⟨hUab, hUP, hPT, hnorm, hU64⟩ := F112RR.exists_elemAbelian_card_ge hs hH c.c1519
    (h15201 G T Mc M hs) hc
  have hHeq : kS5 H φ ⊔ T = H := sup_kS5_eq φ c.hT
  have := hR G (Y₁ ⊔ rcOf Mc M) (kS5 H φ) T (F112RR.S5Ctx.hyp111_S3 c hq₁)
    (isQuasithinSub_of c.hs.qtfe.qtke _) hq₁ (nonempty_oTwoQuot_kS5 H φ)
    (nonempty_oTwoQuot_of_eq hHeq.symm ⟨φ⟩) (by rw [hHeq]; exact c.hT)
    (conjClosure (V154 T Mc M) H) (hUP.trans hPT) hUab
    (by rw [hHeq]; exact hnorm) (by rw [hHeq]; exact hc.chief)
    (by rw [hHeq]; exact hc.shape trivial)
  omega

end CFSG.Quasithin
