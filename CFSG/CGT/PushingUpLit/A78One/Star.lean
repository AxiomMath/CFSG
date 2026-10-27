module

public import CFSG.CGT.PushingUpLit.A78One.OneStmts
import CFSG.CGT.PushingUpLit.A78One.CjLemmas
import CFSG.CGT.PushingUpLit.A78One.DictStar
import CFSG.CGT.PushingUpLit.T2K.FourSevenB

public section

namespace CFSG.CGT.PushingUpLit.A78One

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.T2K
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace CexCtx

variable {L M : Subgroup G} {n : ℕ} {T T' : Subgroup G} {x : G}

theorem v0_P_le (c : CexCtx L M n T T' x) : cexP L T ≤ T' := le_sup_right.trans c.ge

theorem v0_inf_eq (c : CexCtx L M n T T' x) :
    T' ⊓ Subgroup.centralizer (blockU L : Set G) = cexP L T :=
  le_antisymm (le_inf (inf_le_left.trans c.le) inf_le_right) (le_inf c.v0_P_le inf_le_right)

theorem v0_blockU_le_P (c : CexCtx L M n T T' x) : blockU L ≤ cexP L T :=
  le_inf (NatBlock.blockU_le_sylow c.hyp.le c.nM c.sylow) (fun v hv =>
    Subgroup.mem_centralizer_iff.2 fun w hw => c.hyp.natBlock.blockU_comm w hw v hv)

theorem v0_le_normalizer_P (c : CexCtx L M n T T' x) :
    L ≤ Subgroup.normalizer (cexP L T : Set G) := by
  have key : ∀ l ∈ L, ∀ p ∈ cexP L T, l * p * l⁻¹ ∈ cexP L T := by
    intro l hl p hp
    have hpM : p ∈ M ⊓ Subgroup.centralizer (blockU L : Set G) := ⟨c.sylow.le hp.1, hp.2⟩
    have h1 := c.hyp.natBlock.comm_centralizer_mem_blockU c.nM hpM l hl
    have e : l * p * l⁻¹ = (⁅p, l⁆)⁻¹ * p := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (inv_mem (c.v0_blockU_le_P h1)) hp
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro p
  exact ⟨fun hp => key l hl p hp, fun hp => by
    have := key l⁻¹ (L.inv_mem hl) _ hp
    simpa [mul_assoc] using this⟩

theorem v0_le_normalizer_P' (c : CexCtx L M n T T' x) :
    T ≤ Subgroup.normalizer (cexP L T : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro p
  have hV : t ∈ Subgroup.normalizer (blockU L : Set G) :=
    NatBlock.le_normalizer_blockU_of_le c.nM (c.sylow.le ht)
  have hC : t ∈ Subgroup.normalizer (Subgroup.centralizer (blockU L : Set G) : Set G) :=
    mem_normalizer_centralizer hV
  have h1 := Subgroup.mem_normalizer_iff.1 hC p
  have h2 := Subgroup.mem_normalizer_iff.1
    (Subgroup.le_normalizer ht : t ∈ Subgroup.normalizer (T : Set G)) p
  simp only [cexP, Subgroup.mem_inf, h1, h2]

theorem v0_blockU_le_of_isMax_P (c : CexCtx L M n T T' x) {D : Subgroup G}
    (hD : IsMaxElemAbelian (cexP L T) D) : blockU L ≤ D := by
  have hcomm : ∀ v ∈ blockU L, ∀ d ∈ D, v * d = d * v := fun v hv d hd =>
    Subgroup.mem_centralizer_iff.1 (hD.1 hd).2 v hv
  have hsup := isElemAbelian_sup' c.hyp.natBlock.isElemAbelian_blockU hD.2.1 hcomm
  have hle : blockU L ⊔ D ≤ cexP L T := sup_le c.v0_blockU_le_P hD.1
  have hcard := hD.2.2 _ hle hsup
  have heq : D = blockU L ⊔ D := Subgroup.eq_of_le_of_card_ge le_sup_right hcard
  exact le_sup_left.trans heq.ge

theorem v0_ne_bot_of_isMax_P (c : CexCtx L M n T T' x) {D : Subgroup G}
    (hD : IsMaxElemAbelian (cexP L T) D) : D ≠ ⊥ := fun h =>
  c.hyp.blockU_ne_bot (le_bot_iff.1 (h ▸ c.v0_blockU_le_of_isMax_P hD))

theorem v0_isPGroup_of_le_P (c : CexCtx L M n T T' x) {D : Subgroup G} (hD : D ≤ cexP L T) :
    IsPGroup 2 D := c.sylow.isPGroup.to_le (hD.trans inf_le_left)

theorem v0_isMax_P_of_le (c : CexCtx L M n T T' x) {A : Subgroup G} (hA : IsMaxElemAbelian T' A)
    (hle : A ≤ cexP L T) : IsMaxElemAbelian (cexP L T) A :=
  ⟨hle, hA.2.1, fun B hB hBe => hA.2.2 B (hB.trans c.v0_P_le) hBe⟩

theorem v0_not_le_centralizer (c : CexCtx L M n T T' x) {A : Subgroup G}
    (hA : IsMaxElemAbelian T' A) (hnt : ¬ A ≤ cexP L T) :
    ¬ A ≤ Subgroup.centralizer (blockU L : Set G) := fun h' =>
  hnt (by rw [← c.v0_inf_eq]; exact le_inf hA.1 h')

theorem exists_not_le (c : CexCtx L M n T T' x) :
    ∃ A, IsMaxElemAbelian T' A ∧ ¬ A ≤ cexP L T := by
  by_contra hcon
  push Not at hcon
  obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian T'
  have hA₀P : A₀ ≤ cexP L T := hcon A₀ hA₀
  have hiff : ∀ D, IsMaxElemAbelian (cexP L T) D ↔ IsMaxElemAbelian T' D := by
    intro D
    constructor
    · intro hD
      exact ⟨hD.1.trans c.v0_P_le, hD.2.1, fun B hB hBe =>
        (hA₀.2.2 B hB hBe).trans (hD.2.2 A₀ hA₀P hA₀.2.1)⟩
    · intro hD
      exact ⟨hcon D hD, hD.2.1, fun B hB hBe => hD.2.2 B (hB.trans c.v0_P_le) hBe⟩
  have hJ : thompsonJ T' = thompsonJ (cexP L T) := by
    apply le_antisymm
    · exact iSup_le fun D => iSup_le fun hD => le_thompsonJ' ((hiff D).2 hD)
    · exact iSup_le fun D => iSup_le fun hD => le_thompsonJ' ((hiff D).1 hD)
  have hU : blockU L ≤ A₀ := c.v0_blockU_le_of_isMax_P ((hiff A₀).2 hA₀)
  have hX_ne : thompsonJ T' ≠ ⊥ := by
    intro hbot
    apply c.hyp.blockU_ne_bot
    exact le_bot_iff.1 (hbot ▸ hU.trans (le_thompsonJ' hA₀))
  have hX2 : IsPGroup 2 (thompsonJ T') :=
    c.sylow.isPGroup.to_le (thompsonJ_le.trans c.le)
  have hLX : L ≤ Subgroup.normalizer (thompsonJ T' : Set G) := by
    intro l hl
    rw [hJ]
    exact T2K.normalizer_le_normalizer_thompsonJ _ (c.v0_le_normalizer_P hl)
  have hxX : x ∈ Subgroup.normalizer (thompsonJ T' : Set G) :=
    T2K.normalizer_le_normalizer_thompsonJ T' c.hx
  exact c.hxM (c.hyp.mem_of_normalized (X := thompsonJ T') hX_ne hX2 hLX
    (cjx_le_normalizer hLX hxX))

theorem isMax_of_isMax_P (c : CexCtx L M n T T' x) {A : Subgroup G}
    (hA : IsMaxElemAbelian (cexP L T) A) : IsMaxElemAbelian T' A := by
  obtain ⟨A₁, hA₁, hA₁P⟩ := c.exists_not_le
  have H45 := c.hyp45 hA₁ (c.v0_not_le_centralizer hA₁ hA₁P)
  have hBP : IsMaxElemAbelian (cexP L T) (Hyp45.bGrp L A₁) := by
    have := H45.isMaxElemAbelian_B_P
    rwa [c.v0_inf_eq] at this
  have h1 : Nat.card ↥A = Nat.card ↥(Hyp45.bGrp L A₁) :=
    le_antisymm (hBP.2.2 A hA.1 hA.2.1) (hA.2.2 _ hBP.1 hBP.2.1)
  rw [H45.card_B] at h1
  exact ⟨hA.1.trans c.v0_P_le, hA.2.1, fun B hB hBe => by
    rw [h1]
    exact hA₁.2.2 B hB hBe⟩

theorem le_normalizer_of_isMax_P (c : CexCtx L M n T T' x) {D : Subgroup G}
    (hD : IsMaxElemAbelian (cexP L T) D) : L ≤ Subgroup.normalizer (D : Set G) := by
  obtain ⟨A₁, hA₁, hA₁P⟩ := c.exists_not_le
  have H45 := c.hyp45 hA₁ (c.v0_not_le_centralizer hA₁ hA₁P)
  have hD' : IsMaxElemAbelian (T' ⊓ Subgroup.centralizer (blockU L : Set G)) D := by
    rwa [c.v0_inf_eq]
  exact H45.le_normalizer_of_isMaxElemAbelian_P hD'

theorem star (c : CexCtx L M n T T' x) {D : Subgroup G}
    (h0 : IsMaxElemAbelian (cexP L T) D)
    (h1 : IsMaxElemAbelian (cj x⁻¹ (cexP L T)) D) : False := by
  have hL0 := c.le_normalizer_of_isMax_P h0
  have hD' : IsMaxElemAbelian (cexP L T) (cj x D) := by
    have := cjx_isMax x h1
    rwa [cjx_cj_inv] at this
  have hL1 := c.le_normalizer_of_isMax_P hD'
  have hLg : cj x⁻¹ L ≤ Subgroup.normalizer (D : Set G) := by
    have := T2Hyp.normalizer_map_conj_of_le (g := x⁻¹) hL1
    rwa [show (cj x D).map (MulAut.conj x⁻¹).toMonoidHom = D from cjx_inv_cj x D] at this
  have hx : x⁻¹ ∈ M := c.hyp.mem_of_normalized (c.v0_ne_bot_of_isMax_P h0)
    (c.v0_isPGroup_of_le_P h0.1) hL0 hLg
  exact c.hxM (by simpa using M.inv_mem hx)

end CexCtx

end CFSG.CGT.PushingUpLit.A78One
