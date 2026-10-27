module

public import CFSG.Quasithin.EmptyFaithful.F112RE
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152UF112

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X
open CFSG.Quasithin.He9 (isQuasithinSub_of)

theorem input15208F112At_S3_five_of_hay_F4 (hHay : HayashiFiveThree) (hTits : TitsRankLeFive)
    (hF4 : TwistedF4RankLeFive) (h1515 : StageLemma1515CE) (h1519 : StageLemma1519)
    (h15207 : StageLemma15207_F4) (h15201 : StageLemma15201_F4) (h15112 : StageLemma15112) :
    Input15208F112At_F4 (Equiv.Perm (Fin 3)) (DihedralGroup 5) ∧
      Input15208F112At_F4 (Equiv.Perm (Fin 3)) ↥(CFSG.Open.Sz 0) := by
  have key : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
      ∀ H : Subgroup G, IsHStar T M H → ∀ Y₁ : Subgroup G, IsY1 T Mc M Y₁ →
      Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3)) →
      (Nonempty (OTwoQuot (Y₁ ⊔ rcOf Mc M) ≃* DihedralGroup 5) ∨
        Nonempty (OTwoQuot (Y₁ ⊔ rcOf Mc M) ≃* ↥(CFSG.Open.Sz 0))) → False := by
    intro G _ _ T Mc M hs H hH Y₁ hY₁ hqH hq₁
    have c : F112RR.Ctx T Mc M H Y₁ :=
      ⟨hs, hH, h1515 G T Mc M hs.qtfe hs.mf hs.ce, h1519 G T Mc M hs.qtfe hs.mf hs.ce, hY₁,
        h15207 G T Mc M hs Y₁ hY₁⟩
    obtain ⟨hUab, hUP, hPT, -, hU64⟩ := F112RR.exists_elemAbelian_card_ge hs hH c.c1519
      (h15201 G T Mc M hs) (h15112 G T Mc M hs.qtfe hs.mf hs.ce H hH).1
    have hUT : conjClosure (V154 T Mc M) H ≤ (Y₁ ⊔ T) ⊓ H := by
      rw [inf_comm, c.H_inf_X hqH]
      exact hUP.trans hPT
    rcases c.case_five hqH hq₁ hHay with h | h
    · have := F112RR.card_le_of_caseTits hTits h hUT hUab
      omega
    · have := F112RR.card_le_of_case2F4 hF4 h hUT hUab
      omega
  exact ⟨fun G _ _ T Mc M hs H hH Y₁ hY₁ hqH hq₁ =>
      key G T Mc M hs H hH Y₁ hY₁ hqH (Or.inl hq₁),
    fun G _ _ T Mc M hs H hH Y₁ hY₁ hqH hq₁ =>
      key G T Mc M hs H hH Y₁ hY₁ hqH (Or.inr hq₁)⟩

end CFSG.Quasithin
