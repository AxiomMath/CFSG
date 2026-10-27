module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.Diagonal
public import CFSG.CGT.PushingUpLit.CGT6.Nine7Amb

public section

namespace CFSG.EvenSporadicStandard.Induction.ThmU

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
  CFSG.ComponentClassification.AschbacherToolkit
open scoped commutatorElement

variable {G : Type} [Group G]

structure SwapConfig (B : Subgroup G) (x y : G) (M : Subgroup G) : Prop where
  x_ord : orderOf x = 2
  y_ord : orderOf y = 2
  comm : x * y = y * x
  isCompIn : IsCompIn M (centralizer ({y} : Set G))
  ne : cj x M ≠ M
  mem_iff : ∀ b : G, b ∈ B ↔ ∃ m ∈ M, b = diag x m
  inj : ∀ m ∈ M, diag x m = 1 → m = 1

namespace SwapConfig

variable {B M : Subgroup G} {x y : G}

theorem x_mul_self (h : SwapConfig B x y M) : x * x = 1 :=
  mul_self_eq_one_of_orderOf h.x_ord

theorem isCompIn_cj (h : SwapConfig B x y M) :
    IsCompIn (cj x M) (centralizer ({y} : Set G)) :=
  isCompIn_cj_centralizer h.comm h.isCompIn

theorem diagComm [Finite G] (h : SwapConfig B x y M) : DiagComm x M :=
  IsCompIn.commute_of_ne h.isCompIn h.isCompIn_cj h.ne.symm

theorem le_sup [Finite G] (h : SwapConfig B x y M) : B ≤ M ⊔ cj x M := by
  intro b hb
  obtain ⟨m, hm, rfl⟩ := (h.mem_iff b).1 hb
  exact diag_mem_sup hm

theorem not_centralizes_left [Finite G] (h : SwapConfig B x y M) :
    ¬ ∀ b ∈ B, ∀ m ∈ M, b * m = m * b := by
  intro hc
  apply diag_not_centralize_left h.x_mul_self h.diagComm (IsCompIn.not_commute h.isCompIn)
  intro m hm n hn
  exact hc (diag x m) ((h.mem_iff _).2 ⟨m, hm, rfl⟩) n hn

theorem not_centralizes_right [Finite G] (h : SwapConfig B x y M) :
    ¬ ∀ b ∈ B, ∀ m ∈ cj x M, b * m = m * b := by
  intro hc
  apply diag_not_centralize_right h.x_mul_self h.diagComm (IsCompIn.not_commute h.isCompIn)
  intro m hm n hn
  exact hc (diag x m) ((h.mem_iff _).2 ⟨m, hm, rfl⟩) (x * n * x⁻¹) (conj_mem_cj hn)

theorem support [Finite G] (h : SwapConfig B x y M) {L : Subgroup G}
    (hL : IsCompIn L (centralizer ({y} : Set G))) :
    (¬ ∀ b ∈ B, ∀ l ∈ L, b * l = l * b) ↔ (L = M ∨ L = cj x M) := by
  constructor
  · intro hnc
    by_contra hcon
    push Not at hcon
    exact hnc (commute_of_le_sup_of_ne h.isCompIn h.isCompIn_cj hL hcon.1 hcon.2 h.le_sup)
  · rintro (rfl | rfl)
    · exact h.not_centralizes_left
    · exact h.not_centralizes_right

theorem cj_mem_support [Finite G] (h : SwapConfig B x y M) {g : G} (hgy : g * y = y * g)
    (hgB : ∀ b ∈ B, g * b = b * g) : cj g M = M ∨ cj g M = cj x M := by
  refine (h.support (isCompIn_cj_centralizer hgy h.isCompIn)).1 ?_
  intro hcomm
  apply h.not_centralizes_left
  intro b hb m hm
  have key : b * (g * m * g⁻¹) = (g * m * g⁻¹) * b :=
    hcomm b hb (g * m * g⁻¹) (conj_mem_cj hm)
  have hgb : Commute g b := hgB b hb
  have h1 : g * (b * m) * g⁻¹ = g * (m * b) * g⁻¹ := by
    calc g * (b * m) * g⁻¹ = (g * b) * m * g⁻¹ := by group
      _ = (b * g) * m * g⁻¹ := by rw [hgb.eq]
      _ = b * (g * m * g⁻¹) := by group
      _ = (g * m * g⁻¹) * b := key
      _ = g * m * (g⁻¹ * b) := by group
      _ = g * m * (b * g⁻¹) := by rw [hgb.inv_left.eq]
      _ = g * (m * b) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h1)

end SwapConfig

theorem cj_ne_of_not_centralizes [Finite G] {B : Subgroup G} {u b : G}
    {M' : Subgroup G} (h : SwapConfig B u b M') {L : Subgroup G}
    (hL : IsCompIn L (centralizer ({b} : Set G)))
    (hBL : ¬ ∀ c ∈ B, ∀ l ∈ L, c * l = l * c) : cj u L ≠ L := by
  intro hLu
  rcases (h.support hL).1 hBL with hLM | hLcj
  · apply h.ne
    rw [← hLM]
    exact hLu
  · have h1 : cj u L = M' := by rw [hLcj, cj_cj_of_mul_self h.x_mul_self M']
    apply h.ne
    rw [← hLcj]
    exact hLu.symm.trans h1

theorem commutator_zpowers_le_sup_cj {L : Subgroup G} {x : G} (hx : x * x = 1) :
    ⁅L, zpowers x⁆ ≤ L ⊔ cj x L := by
  rw [Subgroup.commutator_le]
  intro l hl a ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
  have hdecomp : k = 2 * (k / 2) + k % 2 := by
    have := Int.ediv_mul_add_emod k 2
    omega
  have hxk : x ^ k = 1 ∨ x ^ k = x := by
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      rw [hdecomp, hk, add_zero, zpow_mul, hx2, one_zpow]
    · right
      rw [hdecomp, hk, zpow_add, zpow_mul, hx2, one_zpow, one_mul, zpow_one]
  rcases hxk with hk | hk
  · rw [hk, commutatorElement_one_right]
    exact Subgroup.one_mem _
  · rw [hk]
    have hmem : x * l⁻¹ * x⁻¹ ∈ cj x L := conj_mem_cj (L.inv_mem hl)
    have heq : ⁅l, x⁆ = l * (x * l⁻¹ * x⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hmem)

private theorem isCompIn_nine7_aux {M X : Subgroup G} (h : IsCompIn M X) :
    CFSG.CGT.PushingUpLit.CGT6.Nine7.IsCompIn M X :=
  ⟨h.1, h.2.2, h.isQuasisimple.1.commutator_eq_top, h.isQuasisimple.2.1⟩

theorem exists_swapConfig [Finite G] (hLB : LayerBalanceAt G) (hglaub : GlaubermanSimplePerfect)
    {B : Subgroup G} (hB : MaximalF B) {x y : G} (hx : GoodInv B x) (hy : BadInv B y)
    (hxy : x * y = y * x) :
    ∃ M : Subgroup G, SwapConfig B x y M ∧ MaximalF M ∧ Nonempty (↥B ≃* ↥M) := by
  let X : Subgroup G := centralizer ({y} : Set G)
  have hxX : x ∈ X := by
    change x ∈ centralizer ({y} : Set G)
    rw [mem_centralizer_singleton_iff]
    exact hxy
  have hBxy : IsCompIn B (X ⊓ centralizer ({x} : Set G)) :=
    isCompIn_of_le hx.2 (le_inf (show B ≤ X from hy.2.1) hx.2.1) inf_le_right
  have hlay : B ≤ layerIn X := hLB.le_layerIn hx.1 hy.1 hxy hx.2 hy.2.1
  obtain ⟨L, hL, hBL⟩ := exists_isCompIn_not_commute hB.1.isQuasisimple hlay
  have hglaubAt : CFSG.CGT.PushingUpLit.CGT6.Nine7.GlaubermanAt
      (↥L ⧸ Subgroup.center ↥L) :=
    fun hX' _ hev S K hK hfix => hglaub _ hX' hev S K hK hfix
  have key := CFSG.CGT.PushingUpLit.CGT6.Nine7.lemma_2_7_two_amb
    (H := X) (t := x) hxX hx.1 (isCompIn_nine7_aux hBxy) (isCompIn_nine7_aux hL) hglaubAt
  rcases key with hbot | hleL | ⟨hneL, hBLc⟩
  · exfalso
    apply hBL
    intro b hb l hl
    exact (Subgroup.mem_centralizer_iff.1
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot hb) l hl).symm
  · have hLtF : LtF B L := ⟨x, y, hx.1, hy.1, hxy, hx.2, hL, hleL.trans le_sup_left⟩
    obtain ⟨e⟩ := hB.2 L (Relation.TransGen.single hLtF)
    have hcard : Nat.card B = Nat.card L := Nat.card_congr e.toEquiv
    have hEq : B = L := Subgroup.eq_of_le_of_card_ge hleL hcard.ge
    exact (hy.2.2 (hEq.symm ▸ hL)).elim
  · have hxmul : x * x = 1 := mul_self_eq_one_of_orderOf hx.1
    have hLcj : IsCompIn (cj x L) X := isCompIn_cj_centralizer hxy hL
    have hneL' : cj x L ≠ L := by
      have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxmul
      have hcj : cj x L = CFSG.conjugate L x := by
        simp only [cj, CFSG.conjugate, hxinv]
      rw [hcj]
      exact hneL
    have hle_sup : B ≤ L ⊔ cj x L :=
      hBLc.trans (commutator_zpowers_le_sup_cj (L := L) (x := x) hxmul)
    have hLtF : LtF B L := ⟨x, y, hx.1, hy.1, hxy, hx.2, hL, hle_sup⟩
    obtain ⟨e₁⟩ := hB.2 L (Relation.TransGen.single hLtF)
    have hcardBL : Nat.card B = Nat.card L := Nat.card_congr e₁.toEquiv
    have hc : DiagComm x L := IsCompIn.commute_of_ne hL hLcj hneL'.symm
    have hfix : ∀ k ∈ B, x * k * x⁻¹ = k := by
      intro k hk
      have hk' : k * x = x * k := mem_centralizer_singleton_iff.1 (hx.2.1 hk)
      rw [← hk']; group
    have hdiag := diag_of_le_sup_conj (M := L) (K := B) hxmul hc (IsCompIn.perfect hx.2)
      hle_sup hfix hcardBL
    refine ⟨L, ⟨hx.1, hy.1, hxy, hL, hneL', hdiag.1, hdiag.2⟩, ?_, ⟨e₁⟩⟩
    refine ⟨⟨y, hy.1, hL⟩, ?_⟩
    intro L' hL'
    obtain ⟨e₂⟩ := hB.2 L' (Relation.TransGen.head hLtF hL')
    exact ⟨e₁.symm.trans e₂⟩

end CFSG.EvenSporadicStandard.Induction.ThmU
