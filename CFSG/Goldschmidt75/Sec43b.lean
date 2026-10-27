module

public import CFSG.Goldschmidt75.Sec43
public import CFSG.Goldschmidt75.Sec42K

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {S₁ S₂ : Subgroup G}

theorem MinCE.normalizer_ne_top (h : MinCE G T S₁ S₂) {B : Subgroup G} (hB : B ≤ S₁)
    (hB1 : B ≠ ⊥) : normalizer (B : Set G) ≠ ⊤ := by
  have := h.isSimpleGroup
  intro htop
  have hBn : B.Normal := normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B with h0 | h0
  · exact hB1 h0
  · apply h.symm.ne_bot
    rw [eq_bot_iff, ← h.disj]
    intro x hx
    exact ⟨hB (h0 ▸ mem_top x), hx⟩

theorem MinCE.step_43 (h : MinCE G T S₁ S₂) {B : Subgroup G} (hB : B ≤ S₁) (hB1 : B ≠ ⊥)
    (ih : normalizer ((S₁ ⊓ normalizer (B : Set G) : Subgroup G) : Set G) ≤
      normalizer ((kSub S₂ S₁ ⊔ oddCoreOf (normalizer
        ((S₁ ⊓ normalizer (B : Set G) : Subgroup G) : Set G)) : Subgroup G) : Set G)) :
    normalizer (B : Set G) ≤
      normalizer ((kSub S₂ S₁ ⊔ oddCoreOf (normalizer (B : Set G)) : Subgroup G) : Set G) := by
  set L := normalizer (B : Set G) with hL
  set B₁ := S₁ ⊓ L with hB₁
  set L₁ := normalizer (B₁ : Set G) with hL₁
  set K₂ := kSub S₂ S₁ with hK₂
  have hC₁ : S₂ ≤ centralizer (S₁ : Set G) := le_centralizer_iff.mp h.comm
  have hK₂C : K₂ ≤ centralizer (S₁ : Set G) := kSub_le_centralizer hC₁
  have hCB : centralizer (S₁ : Set G) ≤ centralizer (B : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.mpr hB)
  have hCB₁ : centralizer (S₁ : Set G) ≤ centralizer (B₁ : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left)
  have hS₂L : S₂ ≤ L := hC₁.trans (hCB.trans (centralizer_le_normalizer _))
  have hK₂L : K₂ ≤ L := hK₂C.trans (hCB.trans (centralizer_le_normalizer _))
  have hK₂B₁ : K₂ ≤ centralizer (B₁ : Set G) := hK₂C.trans hCB₁
  have hB₁L : B₁ ≤ L := inf_le_right
  obtain ⟨P, Q₁, Q₂, hBQ, hSQ, hQ₁L, hQ₂L, hQ₁P, hQ₂P, hQ₁c, hQ₂c, hQc, hQd⟩ :=
    h.exists_hat (L := L) inf_le_left le_rfl hB₁L hS₂L
  have hA := thmA_in (h.ihG L (card_lt_of_ne_top (h.normalizer_ne_top hB hB1))) P hQ₁P hQ₂P
    hQ₁c hQ₂c hQc hQd
  set N := normalClosureIn L S₂ with hN
  have hNL : N ≤ L := map_subtype_le _
  have hLN : L ≤ normalizer (N : Set G) := le_normalizer_normalClosureIn L S₂
  have hmono : normalClosureIn L S₂ ≤ normalClosureIn L Q₂ :=
    map_mono (normalClosure_mono fun x hx => mem_subgroupOf.mpr (hSQ (mem_subgroupOf.mp hx)))
  have hQ₁N : Q₁ ≤ normalClosureIn L Q₁ := fun x hx =>
    ⟨⟨x, hQ₁L hx⟩, subset_normalClosure (mem_subgroupOf.mpr hx), rfl⟩
  have hcommL : ⁅N, B₁⁆ ≤ oddCoreOf L := by
    rw [commutator_comm]
    exact (commutator_mono (hBQ.trans hQ₁N) hmono).trans hA
  have hcommN : ⁅N, B₁⁆ ≤ oddCoreOf N :=
    (le_inf hcommL (commutator_le_of_le_normalizer (hB₁L.trans hLN))).trans
      (oddCoreOf_inf_le_of_le hNL)
  set ON := oddCoreOf N with hON
  have hONN : ON ≤ N := map_subtype_le _
  have hLON : L ≤ normalizer (ON : Set G) := le_normalizer_oddCoreOf_of_le_normalizer hLN
  set Y := N ⊓ centralizer (B₁ : Set G) with hY
  have hNY : N ≤ Y ⊔ ON :=
    le_inf_centralizer_sup (T.isPGroup'.to_le (inf_le_left.trans h.le₁)) hONN
      (sup_le (hNL.trans hLON) (hB₁L.trans hLON)) (Balance.odd_card_oddCoreOf N) hcommN
  have hYN : Y ≤ N := inf_le_left
  have hYL₁ : Y ≤ L₁ := inf_le_right.trans (centralizer_le_normalizer _)
  have hK₂N : K₂ ≤ N := normalClosureIn_le_normalClosureIn T h.le₂ h.sc₂
    (hC₁.trans (centralizer_le_normalizer _)) hK₂L
  have hK₂Y : K₂ ≤ Y := le_inf hK₂N hK₂B₁
  set OY := oddCoreOf Y with hOY
  have hOYY : OY ≤ Y := map_subtype_le _
  have hYOY : Y ≤ normalizer (OY : Set G) := Completion.le_normalizer_oddCoreOf Y
  have hOYN : OY ≤ ON :=
    le_oddCoreOf_of_le_sup hYN hNY hOYY hYOY (Balance.odd_card_oddCoreOf Y)
  have hYK : ∀ y ∈ Y, ∀ k ∈ K₂, y * k * y⁻¹ ∈ K₂ ⊔ OY := by
    intro y hy k hk
    have h1 : y * k * y⁻¹ ∈ K₂ ⊔ oddCoreOf L₁ :=
      (mem_normalizer_iff.mp (ih (hYL₁ hy)) k).mp (mem_sup_left hk)
    have hK₂L₁ : K₂ ≤ normalizer (oddCoreOf L₁ : Set G) :=
      (hK₂B₁.trans (centralizer_le_normalizer _)).trans (Completion.le_normalizer_oddCoreOf L₁)
    have h1' : y * k * y⁻¹ ∈ ((K₂ ⊔ oddCoreOf L₁ : Subgroup G) : Set G) := h1
    rw [coe_mul_of_left_le_normalizer_right _ _ hK₂L₁] at h1'
    obtain ⟨k', hk', o, ho, hko⟩ := h1'
    have hoY : o ∈ Y := by
      have e : o = k'⁻¹ * (y * k * y⁻¹) := by rw [← hko]; group
      rw [e]
      exact mul_mem (inv_mem (hK₂Y hk')) (mul_mem (mul_mem hy (hK₂Y hk)) (inv_mem hy))
    have hoOY : o ∈ OY := oddCoreOf_inf_le_of_le hYL₁ (mem_inf.mpr ⟨ho, hoY⟩)
    rw [← hko]
    exact mul_mem (mem_sup_left hk') (mem_sup_right hoOY)
  have hK₂ON : K₂ ≤ normalizer (ON : Set G) := (hK₂N.trans hNL).trans hLON
  have hYKN : Y ≤ normalizer ((K₂ ⊔ ON : Subgroup G) : Set G) :=
    le_normalizer_sup_of_maps hK₂ON (fun y hy k hk => (sup_le_sup_left hOYN _) (hYK y hy k hk))
      (fun y hy o ho => (mem_normalizer_iff.mp (hLON (hNL (hYN hy))) o).mp ho)
  have hONK : ON ≤ normalizer ((K₂ ⊔ ON : Subgroup G) : Set G) := by
    refine le_normalizer_sup_of_maps hK₂ON (fun o ho k hk => ?_)
      (fun o ho o' ho' => mul_mem (mul_mem ho ho') (inv_mem ho))
    have h1 : o * k * o⁻¹ * k⁻¹ ∈ ON := by
      have := (mem_normalizer_iff.mp (hK₂ON hk) o⁻¹).mp (inv_mem ho)
      have e : o * k * o⁻¹ * k⁻¹ = o * (k * o⁻¹ * k⁻¹) := by group
      rw [e]
      exact mul_mem ho this
    have e : o * k * o⁻¹ = (o * k * o⁻¹ * k⁻¹) * k := by group
    rw [e]
    exact mul_mem (mem_sup_right h1) (mem_sup_left hk)
  have hNK : N ≤ normalizer ((K₂ ⊔ ON : Subgroup G) : Set G) := by
    intro n hn
    have hn' : n ∈ ((Y ⊔ ON : Subgroup G) : Set G) := hNY hn
    rw [coe_mul_of_left_le_normalizer_right _ _ (hYN.trans (hNL.trans hLON))] at hn'
    obtain ⟨y, hy, o, ho, rfl⟩ := hn'
    exact mul_mem (hYKN hy) (hONK ho)
  have hNeq : N ≤ K₂ ⊔ ON := normalClosureIn_le_of_le_normalizer T h.le₂ h.sc₂ hS₂L
    ((le_kSub (hC₁.trans (centralizer_le_normalizer _))).trans le_sup_left) hNK
  have hONL : ON ≤ oddCoreOf L := oddCoreOf_le_of_le_normalizer hNL hLN
  have heq : K₂ ⊔ oddCoreOf L = N ⊔ oddCoreOf L :=
    le_antisymm (sup_le_sup_right hK₂N _)
      (sup_le (hNeq.trans (sup_le le_sup_left (hONL.trans le_sup_right))) le_sup_right)
  rw [heq]
  exact le_normalizer_sup hLN (Completion.le_normalizer_oddCoreOf L)

theorem MinCE.le_normalizer_kSub_sup (h : MinCE G T S₁ S₂) {B : Subgroup G} (hB : B ≤ S₁)
    (hB1 : B ≠ ⊥) : normalizer (B : Set G) ≤
      normalizer ((kSub S₂ S₁ ⊔ oddCoreOf (normalizer (B : Set G)) : Subgroup G) : Set G) := by
  suffices key : ∀ n, ∀ B : Subgroup G, B ≤ S₁ → B ≠ ⊥ → Nat.card S₁ - Nat.card B = n →
      normalizer (B : Set G) ≤
        normalizer ((kSub S₂ S₁ ⊔ oddCoreOf (normalizer (B : Set G)) : Subgroup G) : Set G) from
    key _ B hB hB1 rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B hB hB1 hn
  by_cases hBS : B = S₁
  · subst hBS
    exact le_normalizer_sup (fun x hx => mem_normalizer_of_forall
      (fun y hy => conj_mem_kSub hx hy) (fun y hy => by simpa using conj_mem_kSub (inv_mem hx) hy))
      (Completion.le_normalizer_oddCoreOf _)
  · have hlt : B < S₁ := lt_of_le_of_ne hB hBS
    have hBB₁ : B < S₁ ⊓ normalizer (B : Set G) :=
      lt_inf_normalizer (T.isPGroup'.to_le h.le₁) hlt
    have hc1 : Nat.card B < Nat.card (S₁ ⊓ normalizer (B : Set G) : Subgroup G) :=
      lt_of_le_of_ne (Subgroup.card_le_of_le hBB₁.le) fun he =>
        hBB₁.ne (Subgroup.eq_of_le_of_card_ge hBB₁.le he.ge)
    have hc2 : Nat.card (S₁ ⊓ normalizer (B : Set G) : Subgroup G) ≤ Nat.card S₁ :=
      Subgroup.card_le_of_le inf_le_left
    exact h.step_43 hB hB1 (ih _ (by omega) _ inf_le_left (ne_bot_of_gt hBB₁) rfl)

end CFSG.Goldschmidt75
