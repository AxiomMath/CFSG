module

public import CFSG.CGT.T75I.NQuot
public import CFSG.CGT.T75I.JankoStmt
public import CFSG.CGT.T75I.Ctx

public section

namespace CFSG.CGT.T75I

open CFSG.Open CFSG.CGT.Timmesfeld75

theorem step610_of_janko_ctx (h22 : JankoM22CtxInput) (h23 : JankoM23CtxInput) (h214 : Lemma214)
    (hInv : InvolutionClassInput) (hIso : Section3IsoInput) (h57 : Step57) (h1 : Sec4NoA)
    (h62 : Sec62) (h63 : Sec63) (hBen : AschbacherDisconnectedInput) : Step610 := by
  intro G _ T T₁ hy h16 hnorm hhat
  have hc := ctx_of_hat h214 hInv hIso hy h16 hnorm hhat
  have : Finite G := hy.finite
  have : IsSimpleGroup G := hy.simple
  have hC := centralizer_eq_of_ctx h1 h57 h62 h63 hBen hc hhat
  have hwc : IsWC T := hy.pair.wc
  obtain ⟨hN6, hN7⟩ := nquot_equiv h1 h63 hc hC hhat
  have hinf : T ⊓ T₁ = ⊥ := hc.sec3.cfg.inf
  have hL : Nat.card (normIn T T₁) = 4 := by rw [hc.card_normIn]; norm_num
  have hL₁ : Nat.card (normIn T₁ T) = 4 := by rw [hc.card_normIn_swap, hL]
  have hgen : Subgroup.normalizer (T : Set G) ⊔ T₁ = ⊤ := by
    have h := hSub_sup_eq_top h1 h57 h62 h63 hBen hc hhat
    exact top_le_iff.1 (h ▸ sup_le_sup_right hSub_le_normalizer' T₁)
  have htr : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (T : Set G), g * x * g⁻¹ = y := fun x hx hx1 y hy' hy1 => by
    obtain ⟨h, hh, hxy⟩ := h57 G T T₁ hy x hx hx1 y hy' hy1
    exact ⟨h, hSub_le_normalizer' hh, hxy⟩
  have hcd : ∀ d ∈ T, d ≠ 1 →
      Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (T : Set G) :=
    fun d hd hd1 => hwc.centralizer_le_normalizer hd hd1
  rcases hhat with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (h22 G hy.nonab T T₁ hwc h16 hinf hy.pair.conj hL hL₁ hcd hC htr hgen (hN6 h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (h23 G hy.nonab T T₁ hwc h16 hinf hy.pair.conj hL hL₁ hcd hC htr hgen (hN7 h)))))))

end CFSG.CGT.T75I
