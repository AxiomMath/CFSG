module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma82

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

namespace S8

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem card_le_of_cyclic {E : Subgroup G} (hp : p.Prime) (hE : IsElemAbelian p E) (hc : IsCyclic E) :
    Nat.card E ≤ p := by
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian hp hE
  by_contra hlt
  push Not at hlt
  have h2 : p ^ 2 ≤ Nat.card E := by
    rw [hk]
    rcases k with _ | _ | k
    · rw [hk] at hlt; simp at hlt; exact absurd hlt (by have := hp.two_le; omega)
    · rw [hk] at hlt; simp at hlt
    · exact Nat.pow_le_pow_right hp.pos (by omega)
  exact S3.not_isCyclic_of_card hp hE h2 hc

theorem lemma85 (hc : S8Ctx G p) (h1017 : I1017At G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h82 : Sp82 G p B x L) (hsp : catalogIs (PSimple p L) isSporIndex)
    (h83 : ¬ catalogIs (PSimple p L) (sporIs .HN)) (h84 : ¬ catalogIs (PSimple p L) (sporIs .ONan)) :
    ∃ row : Row, RowL row p L ∧ ∃ E : Subgroup G, E ≤ L ⊔ B ∧ IsElemAbelian p E ∧
      Nat.card B < Nat.card E := by
  have hp := hc.ctx.prime
  have hrk1 : ∀ A : Subgroup G, IsElemAbelian p A → A ≤ cx x → (∀ a ∈ A, CentMod p L a) →
      Nat.card A ≤ p := fun A hA _ hAc =>
    card_le_of_cyclic hp hA (h82.hcyc A hAc (isPGroup_of_isElemAbelian hA))
  obtain ⟨T, hTL, hT2, hTB, hTT, hTn⟩ := h82.hT
  have hTnle : ¬ (⁅T, B⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p L := by rwa [hTT]
  obtain ⟨hrows, hmore⟩ := h1017 hp hc.ctx.odd B x L h82.hB hc.ctx.rank_ge h82.hxB h82.hx1 h82.hL
    (isKGroup_cx hc.ctx h82.hx1) h82.hBN hsp h82.hcent hrk1 ⟨T, hTL, hT2, hTB, hTnle⟩
  rcases hrows with ⟨row, hrow⟩ | ⟨hp3, hON | hHN⟩
  · exact ⟨row, hrow, hmore row hrow⟩
  · subst hp3; exact absurd hON h84
  · subst hp3; exact absurd hHN h83

theorem lemma86 (hc : S8Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G} (h82 : Sp82 G p B x L)
    {E : Subgroup G} (hEL : E ≤ L ⊔ B) (hE : IsElemAbelian p E) (hbig : Nat.card B < Nat.card E) :
    Odd (Nat.card (GLAPPrimeCoreOf p (cx x))) :=
  odd_core_of_big_rank hc.ctx.prime h82.hB
    (hEL.trans (sup_le h82.hL.1 (le_cx_of_isElemAbelian h82.hB.1 h82.hxB))) hE hbig

theorem lemma87 (hc : S8Ctx G p) (h1016 : I1016RowAt G p) (h301 : I301AAt G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} (h82 : Sp82 G p B x L) {row : Row} (hrow : RowL row p L)
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf p (cx x)))) : Nonempty (SporCfg G p x L row) := by
  have hp := hc.ctx.prime
  have hrk1 : ∀ A : Subgroup G, IsElemAbelian p A → A ≤ cx x → (∀ a ∈ A, CentMod p L a) →
      Nat.card A ≤ p := fun A hA _ hAc =>
    card_le_of_cyclic hp hA (h82.hcyc A hAc (isPGroup_of_isElemAbelian hA))
  have hx : orderOf x = p := orderOf_eq_of_isElemAbelian hp h82.hB.1 h82.hxB h82.hx1
  obtain ⟨T, hTL, hT2, hTB, hTT, hTn⟩ := h82.hT
  have hBle : B ≤ L ⊔ Subgroup.zpowers x := h82.hBL.trans (sup_le_sup_right inf_le_right _)
  have hbound : Nat.card B ≤ p ^ row.rank :=
    h1016 x L row h82.hx1 hx h82.hL (isKGroup_cx hc.ctx h82.hx1) hrow hrk1 B T hBle h82.hB.1 hTL hT2 hTn hTB
  rw [h82.hB.2.1] at hbound
  exact h301 x L row h82.hx1 hx h82.hL (isKGroup_cx hc.ctx h82.hx1) hrow hodd hrk1
    ((Nat.pow_le_pow_iff_right hp.one_lt).1 hbound)

end S8

end CFSG.LocalAnalysis.GLTheoremA
