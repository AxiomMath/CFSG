module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I113Lift
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I113Setup
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132Good

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1132

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open scoped commutatorElement

theorem isElemAbelian_sup_of_commute {Q : Type*} [Group Q] {n : ℕ} {P R : Subgroup Q}
    (hP : IsElemAbelian n P) (hR : IsElemAbelian n R) (h : ∀ p ∈ P, ∀ r ∈ R, p * r = r * p) :
    IsElemAbelian n (P ⊔ R) := by
  have hcomm : ∀ z ∈ P ⊔ R, ∀ w ∈ P ⊔ R, z * w = w * z := by
    intro z hz w hw
    obtain ⟨p, hp, r, hr, rfl⟩ := t113_mem_sup h hz
    obtain ⟨p', hp', r', hr', rfl⟩ := t113_mem_sup h hw
    have e1 : p * p' = p' * p := by
      have := hP.1.is_comm.comm (⟨p, hp⟩ : P) ⟨p', hp'⟩
      exact congrArg Subtype.val this
    have e2 : r * r' = r' * r := by
      have := hR.1.is_comm.comm (⟨r, hr⟩ : R) ⟨r', hr'⟩
      exact congrArg Subtype.val this
    calc p * r * (p' * r') = p * (r * p') * r' := by group
      _ = p * (p' * r) * r' := by rw [← h p' hp' r hr]
      _ = (p * p') * (r * r') := by group
      _ = (p' * p) * (r' * r) := by rw [e1, e2]
      _ = p' * (p * r') * r := by group
      _ = p' * (r' * p) * r := by rw [h p hp r' hr']
      _ = p' * r' * (p * r) := by group
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)⟩⟩, ?_⟩
  intro z hz
  obtain ⟨p, hp, r, hr, rfl⟩ := t113_mem_sup h hz
  have hc : Commute p r := h p hp r hr
  rw [hc.mul_pow, hP.2 p hp, hR.2 r hr, one_mul]

variable {G : Type} [Group G] [Finite G]

theorem lift_step {X D N : Subgroup G} (hDX : D ≤ X) (hNX : N ≤ X) (hDel : IsElemAbelian 3 D)
    (hDN : D ≤ Subgroup.normalizer (N : Set G)) (E : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X))
    (hEN : E ≤ barX 3 X N) (hEel : IsElemAbelian 3 E)
    (hcent : ∀ z ∈ barX 3 X D, ∀ e ∈ E, z * e = e * z) :
    ∃ W : Subgroup G, W ≤ X ∧ W ≤ N ∧ IsElemAbelian 3 W ∧ barX 3 X W = E ∧
      (∀ b ∈ D, ∀ w ∈ W, b * w = w * b) ∧ IsElemAbelian 3 (D ⊔ W) ∧
      barX 3 X (D ⊔ W) = barX 3 X D ⊔ E ∧
      Nat.card ↥(D ⊔ W) = Nat.card ↥(barX 3 X D ⊔ E) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hD : IsPGroup 3 D := isPGroup_of_isElemAbelian hDel
  obtain ⟨W, hWX, hWN, hWp, hDW, hWE⟩ := I113.exists_W hDX hNX hD hDN E hEN
    (fun e he => hEel.2 e he) hcent
  have hWmem : ∀ x : ↥X, (x : G) ∈ W →
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) x ∈ E := fun x hx => by
    rw [← hWE]
    exact ⟨x, hx, rfl⟩
  have hcomm : ∀ b ∈ D, ∀ w ∈ W, b * w = w * b := by
    intro b hb w hw
    have hbX := hDX hb
    have hwX := hWX hw
    have hcW : b * w * b⁻¹ * w⁻¹ ∈ W := by
      have h1 : b * w * b⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 (hDW hb) w).1 hw
      exact W.mul_mem h1 (W.inv_mem hw)
    have h2 : (⁅(⟨b, hbX⟩ : ↥X), (⟨w, hwX⟩ : ↥X)⁆ : ↥X) = 1 := by
      refine I113.eq_of_mk'_eq hWp hWX (x := ⁅(⟨b, hbX⟩ : ↥X), (⟨w, hwX⟩ : ↥X)⁆) (y := 1) hcW
        W.one_mem ?_
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2, map_one]
      exact hcent _ ⟨⟨b, hbX⟩, hb, rfl⟩ _ (hWmem ⟨w, hwX⟩ hw)
    exact commutatorElement_eq_one_iff_mul_comm.1 (congrArg Subtype.val h2)
  have hWel : IsElemAbelian 3 W := by
    refine isElemAbelian_of_forall (fun a ha b hb => ?_) (fun a ha => ?_)
    · have haX := hWX ha
      have hbX := hWX hb
      have h1 := isElemAbelian_commute hEel (hWmem ⟨a, haX⟩ ha) (hWmem ⟨b, hbX⟩ hb)
      have h2 := I113.eq_of_mk'_eq hWp hWX (x := ⟨a, haX⟩ * ⟨b, hbX⟩) (y := ⟨b, hbX⟩ * ⟨a, haX⟩)
        (W.mul_mem ha hb) (W.mul_mem hb ha) (by rw [map_mul, map_mul]; exact h1)
      exact congrArg Subtype.val h2
    · have haX := hWX ha
      have h2 := I113.eq_of_mk'_eq hWp hWX (x := (⟨a, haX⟩ : ↥X) ^ 3) (y := 1) (W.pow_mem ha 3)
        W.one_mem (by rw [map_pow, map_one]; exact hEel.2 _ (hWmem ⟨a, haX⟩ ha))
      exact congrArg Subtype.val h2
  have hAel : IsElemAbelian 3 (D ⊔ W) := isElemAbelian_sup_of_commute hDel hWel hcomm
  have hAX : D ⊔ W ≤ X := sup_le hDX hWX
  have hbar : barX 3 X (D ⊔ W) = barX 3 X D ⊔ E := by
    rw [I113.barX_sup hDX hWX, hWE]
  refine ⟨W, hWX, hWN, hWel, hWE, hcomm, hAel, hbar, ?_⟩
  rw [← hbar]
  exact (i113g_card_barX hp3 (isPGroup_of_isElemAbelian hAel) hAX).symm

theorem i1132_of_good {X B L : Subgroup G} (hB : GLAIsBmax 3 B) (hBX : B ≤ X)
    (hL : GLAPComponent 3 X L) {D E1 E2 M4 : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)}
    (hG : GoodData (barX 3 X B) (barX 3 X L) D E1 E2 M4)
    (h2 : 2 ∣ Nat.card (GLAPPrimeCoreOf 3 X) ∨
      ∃ T : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X), T ≠ ⊥ ∧ IsPGroup 2 T ∧
        D ⊔ E1 ⊔ E2 ≤ Subgroup.normalizer (T : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))) :
    ∃ A : Subgroup G, GLAIsBmax 3 A ∧ B ⊓ centModSubgroup 3 L ≤ A ∧
      A ≤ Subgroup.normalizer (L : Set G) ∧
      (∀ a ∈ A, ∃ u ∈ A ⊓ B, ∃ v ∈ A ⊓ centModSubgroup 3 L, a = u * v) ∧
      ∃ E : Subgroup G, E ≤ A ⊓ closureIn L B ⊓ centModSubgroup 3 L ∧ IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ 3 := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) with hπ
  have hBp : IsPGroup 3 B := GLAIsBmax.isPGroup hB
  have hLX : L ≤ X := hL.1
  set D' : Subgroup G := B ⊓ (D.comap π).map X.subtype with hD'
  have hD'B : D' ≤ B := inf_le_left
  have hD'X : D' ≤ X := inf_le_right.trans (Subgroup.map_subtype_le _)
  have hD'mem : ∀ x : ↥X, (x : G) ∈ D' ↔ (x : G) ∈ B ∧ π x ∈ D := by
    intro x
    constructor
    · rintro ⟨hxB, y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      subst this
      exact ⟨hxB, hy⟩
    · rintro ⟨hxB, hx⟩
      exact ⟨hxB, x, hx, rfl⟩
  have hD'bar : barX 3 X D' = D := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ((hD'mem x).1 hx).2
    · intro hz
      obtain ⟨x, hx, hxz⟩ := hG.D_le hz
      exact ⟨x, (hD'mem x).2 ⟨Subgroup.mem_subgroupOf.1 hx, by rw [hxz]; exact hz⟩, hxz⟩
  have hD'el : IsElemAbelian 3 D' := isElemAbelian_mono hB.1 hD'B
  have hB₀D' : B ⊓ centModSubgroup 3 L ≤ D' := by
    intro g hg
    have hgX : g ∈ X := hBX hg.1
    have h1 : π ⟨g, hgX⟩ ∈ barX 3 X (B ⊓ centModSubgroup 3 L) :=
      ⟨⟨g, hgX⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
    rw [I113.barX_B0_eq hBX hB.1 hL] at h1
    exact (hD'mem ⟨g, hgX⟩).2 ⟨hg.1, hG.B0_le h1⟩
  have hD'L : D' ≤ Subgroup.normalizer (L : Set G) := by
    intro g hg
    have hgX : g ∈ X := hD'X hg
    have h1 : π ⟨g, hgX⟩ ∈ D := ((hD'mem ⟨g, hgX⟩).1 hg).2
    have h2 : π ⟨g, hgX⟩ ∈ Subgroup.normalizer
        ((barX 3 X L : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) :=
      hG.D_norm h1
    have h3 : (⟨g, hgX⟩ : ↥X) ∈ (Subgroup.normalizer ((barX 3 X L :
        Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))).comap π := h2
    rw [i112f_comap_normalizer_barX hL] at h3
    exact Subgroup.mem_subgroupOf.1 h3
  have hN₁X : bClosure B L ≤ X := I113.bClosure_le_X hBX hLX
  have hE1N : E1 ≤ barX 3 X (bClosure B L) := by
    rw [i112f_barX_bClosure hBX hLX]
    exact hG.E1_le
  obtain ⟨W₁, hW₁X, hW₁N, hW₁el, hW₁E, hW₁comm, hD₁el, hD₁bar, -⟩ := lift_step hD'X hN₁X hD'el
    (hD'B.trans (I113.le_normalizer_bClosure' B L)) E1 hE1N hG.E1_el
    (fun z hz e he => hG.D_E1 z (by rwa [hD'bar] at hz) e he)
  have hW₁c : W₁ ≤ centModSubgroup 3 L := fun w hw =>
    I113.mem_centMod_of_comm hL (x := ⟨w, hW₁X hw⟩) (fun m hm => by
      have : π ⟨w, hW₁X hw⟩ ∈ E1 := by
        rw [← hW₁E]
        exact ⟨⟨w, hW₁X hw⟩, Subgroup.mem_subgroupOf.2 hw, rfl⟩
      exact hG.E1_cent _ this m hm)
  set D₁ : Subgroup G := D' ⊔ W₁ with hD₁
  have hD₁X : D₁ ≤ X := sup_le hD'X hW₁X
  have hD₁bar' : barX 3 X D₁ = D ⊔ E1 := by rw [hD₁bar, hD'bar]
  obtain ⟨L4, hL4, hL4bar⟩ := exists_glaPComponent_barX_eq (p := 3) X hG.M4_comp
  have hL4X : L4 ≤ X := hL4.1
  have hD₁N : D₁ ≤ Subgroup.normalizer (L4 : Set G) := by
    intro g hg
    have hgX : g ∈ X := hD₁X hg
    have h1 : π ⟨g, hgX⟩ ∈ barX 3 X D₁ := ⟨⟨g, hgX⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
    rw [hD₁bar'] at h1
    have h2 : π ⟨g, hgX⟩ ∈ Subgroup.normalizer
        ((barX 3 X L4 : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
      rw [hL4bar]
      exact hG.DE1_norm h1
    have h3 : (⟨g, hgX⟩ : ↥X) ∈ (Subgroup.normalizer ((barX 3 X L4 :
        Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) : Set (↥X ⧸ GLAPPrimeCore 3 ↥X))).comap π := h2
    rw [i112f_comap_normalizer_barX hL4] at h3
    exact Subgroup.mem_subgroupOf.1 h3
  obtain ⟨W₂, hW₂X, hW₂N, hW₂el, hW₂E, hW₂comm, hAel, hAbar, hAcard⟩ := lift_step hD₁X hL4X hD₁el
    hD₁N E2 (by rw [hL4bar]; exact hG.E2_le) hG.E2_el
    (fun z hz e he => hG.DE1_E2 z (by rwa [hD₁bar'] at hz) e he)
  have hW₂c : W₂ ≤ centModSubgroup 3 L := fun w hw =>
    I113.mem_centMod_of_comm hL (x := ⟨w, hW₂X hw⟩) (fun m hm => by
      have : π ⟨w, hW₂X hw⟩ ∈ E2 := by
        rw [← hW₂E]
        exact ⟨⟨w, hW₂X hw⟩, Subgroup.mem_subgroupOf.2 hw, rfl⟩
      exact hG.E2_cent _ this m hm)
  set A : Subgroup G := D₁ ⊔ W₂ with hA
  have hAX : A ≤ X := sup_le hD₁X hW₂X
  have hAp : IsPGroup 3 A := isPGroup_of_isElemAbelian hAel
  have hAbar' : barX 3 X A = D ⊔ E1 ⊔ E2 := by rw [hAbar, hD₁bar']
  have hBA : Nat.card B ≤ Nat.card A := by
    rw [hAcard, hD₁bar']
    calc Nat.card B = Nat.card (barX 3 X B) := (i113g_card_barX hp3 hBp hBX).symm
      _ ≤ _ := hG.card_le
  obtain ⟨S, hS1, hS2, hAS⟩ : ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 S ∧
      A ≤ Subgroup.normalizer (S : Set G) := by
    rcases h2 with hev | ⟨T, hT, hT2, hAT'⟩
    · obtain ⟨S, -, hS1, hS2, hAS⟩ := exists_two_subgroup_of_even hp3
        (not_dvd_card_glaPPrimeCoreOf hp3 X) hev hAp
        (hAX.trans (le_normalizer_glaPPrimeCoreOf 3 X))
      exact ⟨S, hS1, hS2, hAS⟩
    · have hAT : (A.subgroupOf X).map π ≤ Subgroup.normalizer (T : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
        show barX 3 X A ≤ _
        rw [hAbar']
        exact hAT'
      obtain ⟨S₀, hS₀1, hS₀2, hAS₀⟩ := I113.exists_two_abstract (GLAPPrimeCore 3 ↥X)
        (I113.not_dvd_card_glaPPrimeCore X)
        (hAp.comap_of_injective X.subtype X.subtype_injective) T hT hT2 hAT
      refine ⟨S₀.map X.subtype, ?_, hS₀2.map _, I113.le_normalizer_map_subtype hAX hAS₀⟩
      rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective]
  have hAB : GLAIsBmax 3 A :=
    ⟨hAel, le_antisymm (card_le_pow_glaTwoLocalRank hp3 hAel hS1 hS2 hAS)
      (by rw [← hB.2.1]; exact hBA), S, hS1, hS2, hAS⟩
  have hD'A : D' ≤ A := le_sup_left.trans le_sup_left
  have hW₁A : W₁ ≤ A := le_sup_right.trans le_sup_left
  have hW₂A : W₂ ≤ A := le_sup_right
  refine ⟨A, hAB, hB₀D'.trans hD'A, ?_, ?_, ?_⟩
  · exact sup_le (sup_le hD'L (fun g hg => (hW₁c hg).1)) (fun g hg => (hW₂c hg).1)
  · intro a ha
    obtain ⟨p, hp, r, hr, rfl⟩ := t113_mem_sup hW₂comm (show a ∈ D₁ ⊔ W₂ from ha)
    obtain ⟨d, hd, w, hw, rfl⟩ := t113_mem_sup hW₁comm (show p ∈ D' ⊔ W₁ from hp)
    exact ⟨d, ⟨hD'A hd, hD'B hd⟩, w * r, ⟨A.mul_mem (hW₁A hw) (hW₂A hr),
      (centModSubgroup 3 L).mul_mem (hW₁c hw) (hW₂c hr)⟩, by rw [mul_assoc]⟩
  · have hW₁card : Nat.card W₁ = Nat.card E1 := by
      rw [← hW₁E]
      exact (i113g_card_barX hp3 (isPGroup_of_isElemAbelian hW₁el) hW₁X).symm
    have h27 : 3 ^ 3 ∣ Nat.card W₁ := by
      rw [hW₁card]
      simpa using hG.E1_dvd
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 h27
    refine ⟨K.map W₁.subtype, ?_, isElemAbelian_mono hW₁el (Subgroup.map_subtype_le K), ?_⟩
    · rintro g ⟨k, -, rfl⟩
      exact ⟨⟨hW₁A k.2, by rw [I113.closureIn_eq_bClosure]; exact hW₁N k.2⟩, hW₁c k.2⟩
    · rw [Subgroup.card_map_of_injective W₁.subtype_injective, hK]

end CFSG.LocalAnalysis.GLTheoremA.I1132
