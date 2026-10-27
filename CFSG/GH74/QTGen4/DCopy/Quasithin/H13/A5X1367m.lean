module

public import CFSG.Quasithin.H13.A5X1367m
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5X1367e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5X1367k
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5X1367l

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem exists_goodComp_F4 (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4)
    (h56 : AsB56) (hH : S.Hyp1367) : ∃ K, S.GoodComp K := by
  by_contra hno
  push Not at hno
  have hF := hH.hF
  have hVv := hH.hVv
  have hJ := hH.hJ
  have hUe := S.elemAbelian_Uv_F4 h1222 h517 hF
  have : IsMulCommutative ↥S.Uv := hUe.1
  have hcent : ∀ K, IsComponentOf K (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv) →
      autOn (thompsonJ S.Tv) S.Uv ≤ Subgroup.centralizer (K : Set (MulAut ↥S.Uv)) := by
    intro K hK
    by_contra hc
    exact hno K ⟨hK, S.autOn_thompsonJ_le_normalizer_F4 h1222 h517 hF hK, hc⟩
  have hfalse : ∀ {N : Subgroup (MulAut ↥S.Uv)}, N ≤ S.JGv →
      (∀ x ∈ S.JGv, ∀ n ∈ N, x * n * x⁻¹ ∈ N) → CFSG.IsQuasisimple ↥N → False := fun hNJ hNn hq =>
    S.false_of_qs_normal_JGv hcent hNJ hNn hq
  have hnormJ : ∀ {X : Subgroup (MulAut ↥S.Uv)}, X ≤ S.JGv →
      S.JGv ≤ Subgroup.normalizer (X : Set (MulAut ↥S.Uv)) →
      ∀ x ∈ S.JGv, ∀ n ∈ X, x * n * x⁻¹ ∈ X :=
    fun _ hJX x hx n hn => (Subgroup.mem_normalizer_iff.mp (hJX hx) n).mp hn
  have hdirect : ∀ {A B : Subgroup (MulAut ↥S.Uv)}, A ⊔ B = S.JGv →
      (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) → ∀ x ∈ S.JGv, ∀ n ∈ A, x * n * x⁻¹ ∈ A :=
    fun hsup hc => (SzN17.normal_of_commuting hsup hc).1
  rcases S.b56Cases_JGv_F4 h1222 h517 h56 hF hJ with h1 | h2 | h3 | h4 | h5
  ·
    obtain ⟨hq, -, -⟩ := h1
    exact hfalse (quasithinGenFitting_le S.JGv) (hnormJ (quasithinGenFitting_le S.JGv)
      (le_normalizer_quasithinGenFitting S.JGv)) hq
  ·
    exact S.false_of_case2_F4 h1222 h517 hF hVv S.JGv_le_GvS S.GvS_le_normalizer_JGv h2
  ·
    obtain ⟨G₁, G₂, hsup, hinf, hc, hf₁, hf₂, W₁, W₂, -, -, hinv₁, hinv₂, hWsup, hWinf, hp₁,
      hp₂⟩ := h3
    have hsup' : G₂ ⊔ G₁ = S.JGv := by rw [sup_comm]; exact hsup
    have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
    have hG₁J : G₁ ≤ S.JGv := hsup ▸ le_sup_left
    have hG₂J : G₂ ≤ S.JGv := hsup ▸ le_sup_right
    rcases S153L.factor_of_list hf₁ with ⟨h6₁, nc₁, -⟩ | ⟨N₁, hN₁, hFN₁⟩
    · rcases S153L.factor_of_list hf₂ with ⟨h6₂, nc₂, -⟩ | ⟨N₂, hN₂, hFN₂⟩
      ·
        obtain ⟨hW₁eq, hW₁c⟩ := piece_of_card_six h6₁ hp₁
        obtain ⟨hW₂eq, hW₂c⟩ := piece_of_card_six h6₂ hp₂
        obtain ⟨y₁, hy₁, hy₁3⟩ := exists_order_three h6₁
        obtain ⟨y₂, hy₂, hy₂3⟩ := exists_order_three h6₂
        refine S.false_of_ds3_F4 h1222 h517 hF hVv (J := S.JGv) (G₁ := G₁) (G₂ := G₂) (W₁ := W₁)
          (W₂ := W₂) (y₁ := y₁) (y₂ := y₂) ⟨hsup, hinf, hc, h6₁, h6₂, nc₁, nc₂, hWsup, hWinf,
            fun g hg w hw => hinv₁ ⟨g, hg⟩ w hw, fun g hg w hw => hinv₂ ⟨g, hg⟩ w hw,
            hW₁eq, hW₂eq, hW₁c, hW₂c, hy₁, hy₂, hy₁3, hy₂3⟩ S.JGv_le_GvS
          S.GvS_le_normalizer_JGv
      · exact hfalse (hFN₂.1.trans hG₂J) (S153L.comp_normal_in_join hsup' hc' hFN₂.1 hFN₂.2.1)
          (hFN₂.2.2.1.resolve_left hN₂)
    · exact hfalse (hFN₁.1.trans hG₁J) (S153L.comp_normal_in_join hsup hc hFN₁.1 hFN₁.2.1)
        (hFN₁.2.2.1.resolve_left hN₁)
  ·
    obtain ⟨G₁, G₂, t, hJt, -, hc, ⟨e₁⟩, -, -, -, -, -, -, ht₁, -, -, -⟩ := h4
    have hG₁J : G₁ ≤ S.JGv := by rw [hJt]; exact le_sup_left.trans le_sup_left
    have hJN : S.JGv ≤ Subgroup.normalizer (G₁ : Set (MulAut ↥S.Uv)) := by
      rw [hJt]
      refine sup_le (sup_le Subgroup.le_normalizer fun b hb => ?_)
        ((Subgroup.zpowers_le).mpr ht₁)
      refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) fun x hx => ?_
      · rw [← hc x hx b hb, mul_inv_cancel_right]; exact hx
      · have h := hc x hx b hb
        have e : b⁻¹ * x * b = x := by rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [e]; exact hx
    have hs : IsSimpleGroup ↥G₁ :=
      @MulEquiv.isSimpleGroup _ _ _ _ (alternatingGroup.isSimpleGroup (by simp)) e₁
    have hcard : Nat.card ↥G₁ = 360 := by
      rw [Nat.card_congr e₁.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    exact hfalse hG₁J (hnormJ hG₁J hJN)
      (S153L.comp_quasisimple_of_simple hs (by rw [hcard]; norm_num))
  ·
    obtain ⟨G₁, G₂, hsup, -, hc, -, ⟨e₁⟩, -, -, -⟩ := h5
    have hG₁J : G₁ ≤ S.JGv := hsup ▸ le_sup_left
    have hs : IsSimpleGroup ↥G₁ :=
      @MulEquiv.isSimpleGroup _ _ _ _
        (NQRigid.isSimpleGroup_statedSL_three_odd (F := ZMod 2) (m := 1)
          (by rw [Nat.card_zmod]; norm_num) (by decide)) e₁
    have hcard : Nat.card ↥G₁ = 168 := by
      rw [Nat.card_congr e₁.toEquiv, card_statedSL_three_eq, Nat.card_zmod]
      norm_num
    exact hfalse hG₁J (hdirect hsup hc)
      (S153L.comp_quasisimple_of_simple hs (by rw [hcard]; norm_num))

end Setting

end CFSG.Quasithin.H13.A5
