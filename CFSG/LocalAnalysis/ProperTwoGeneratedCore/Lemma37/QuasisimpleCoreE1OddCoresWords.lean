module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1OddCoresBalance

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Assembly.Dichotomy

theorem e1W_mul : ∀ v w : Fin 64, v.val % 4 = 0 → w.val % 4 = 0 → (c3Mul v w).val % 4 = 0 := by
  decide

theorem e1W_facts : (Finset.univ.filter fun v : Fin 64 => v.val % 4 = 0).card = 16 ∧
    (∀ v : Fin 64, v.val % 4 = 0 → c3Mul v v = 0) ∧
    ∀ v w : Fin 64, v.val % 4 = 0 → w.val % 4 = 0 → c3Mul v w = c3Mul w v := by
  decide

theorem e1W_conj : ∀ s w : Fin 64, w.val % 4 = 0 → (c3Conj s w).val % 4 = 0 := by
  decide +kernel

theorem e1P_facts : (∀ v w : Fin 64, v.val % 16 = 0 → w.val % 16 = 0 →
    (c3Mul v w).val % 16 = 0) ∧ (Finset.univ.filter fun v : Fin 64 => v.val % 16 = 0).card = 4 := by
  decide

theorem e1Q_facts : (∀ v w : Fin 64, (v.val < 16 ∧ v.val % 4 = 0) → (w.val < 16 ∧ w.val % 4 = 0) →
    ((c3Mul v w).val < 16 ∧ (c3Mul v w).val % 4 = 0)) ∧
    (Finset.univ.filter fun v : Fin 64 => v.val < 16 ∧ v.val % 4 = 0).card = 4 := by
  decide

theorem e1V_facts : (∀ v w : Fin 64, (v = 0 ∨ v = 20 ∨ v = 40 ∨ v = 60) →
    (w = 0 ∨ w = 20 ∨ w = 40 ∨ w = 60) →
      (c3Mul v w = 0 ∨ c3Mul v w = 20 ∨ c3Mul v w = 40 ∨ c3Mul v w = 60)) ∧
    (Finset.univ.filter fun v : Fin 64 => v = 0 ∨ v = 20 ∨ v = 40 ∨ v = 60).card = 4 ∧
    c3GenW 20 ∧ c3GenW 40 ∧ c3GenW 60 ∧ c3Mul 20 40 = 60 ∧ c3Mul 40 20 = 60 := by
  decide

theorem e1PQ_four : ∀ b : Fin 64, e1PQ b →
    (∀ q : Fin 64, (q.val < 16 ∧ q.val % 4 = 0) → q ≠ 0 → c3GenW (c3Mul b q)) ∨
      (∀ p : Fin 64, p.val % 16 = 0 → p ≠ 0 → c3GenW (c3Mul b p)) := by
  decide

variable {G : Type} [Group G]

@[expose] noncomputable def e1WBar (Z : Subgroup G) [Z.Normal] (u m y x : G) : Subgroup (G ⧸ Z) :=
  e1WordSubgroup Z u m y x fun v => v.val % 4 = 0

@[expose] noncomputable def e1PBar (Z : Subgroup G) [Z.Normal] (u m y x : G) : Subgroup (G ⧸ Z) :=
  e1WordSubgroup Z u m y x fun v => v.val % 16 = 0

@[expose] noncomputable def e1QBar (Z : Subgroup G) [Z.Normal] (u m y x : G) : Subgroup (G ⧸ Z) :=
  e1WordSubgroup Z u m y x fun v => v.val < 16 ∧ v.val % 4 = 0

@[expose] noncomputable def e1VBar (Z : Subgroup G) [Z.Normal] (u m y x : G) : Subgroup (G ⧸ Z) :=
  e1WordSubgroup Z u m y x fun v => v = 0 ∨ v = 20 ∨ v = 40 ∨ v = 60

namespace CaseC3BCD

variable {T Q P₁ S : Subgroup G} {e u y x m : G} {Z : Subgroup G} [Z.Normal]
  (hb : CaseC3BCD T Q P₁ S e u y x m Z) [Finite G]
include hb

theorem mem_e1WBar_iff {s : G ⧸ Z} :
    s ∈ e1WBar Z u m y x ↔ ∃ v : Fin 64, v.val % 4 = 0 ∧ caseC3Word Z u m y x v = s :=
  hb.mem_e1WordSubgroup_iff (by decide) e1W_mul

theorem caseC3Word_mem_e1WBar_iff {v : Fin 64} :
    caseC3Word Z u m y x v ∈ e1WBar Z u m y x ↔ v.val % 4 = 0 :=
  hb.caseC3Word_mem_e1WordSubgroup_iff (by decide) e1W_mul

theorem card_e1WBar : Nat.card (e1WBar Z u m y x) = 16 :=
  (hb.card_e1WordSubgroup (P := fun v : Fin 64 => v.val % 4 = 0) (by decide) e1W_mul).trans
    e1W_facts.1

theorem mul_self_of_mem_e1WBar {s : G ⧸ Z} (hs : s ∈ e1WBar Z u m y x) : s * s = 1 := by
  obtain ⟨v, hv, rfl⟩ := hb.mem_e1WBar_iff.mp hs
  rw [hb.caseC3Word_mul_self_eq_one_iff]
  exact e1W_facts.2.1 v hv

theorem commute_of_mem_e1WBar {s t : G ⧸ Z} (hs : s ∈ e1WBar Z u m y x)
    (ht : t ∈ e1WBar Z u m y x) : s * t = t * s := by
  obtain ⟨v, hv, rfl⟩ := hb.mem_e1WBar_iff.mp hs
  obtain ⟨w, hw, rfl⟩ := hb.mem_e1WBar_iff.mp ht
  rw [hb.caseC3Word_mul, hb.caseC3Word_mul, e1W_facts.2.2 v w hv hw]

theorem isElemAbelian_e1WBar : CFSG.Assembly.IsElemAbelian 2 (e1WBar Z u m y x) :=
  ⟨⟨⟨fun s t => Subtype.ext (hb.commute_of_mem_e1WBar s.2 t.2)⟩⟩,
    fun s hs => by rw [pow_two]; exact hb.mul_self_of_mem_e1WBar hs⟩

theorem map_le_normalizer_e1WBar :
    S.map (QuotientGroup.mk' Z) ≤ Subgroup.normalizer (e1WBar Z u m y x : Set (G ⧸ Z)) := by
  intro s hs
  refine mem_normalizer_of_forall_conj_mem fun t ht => ?_
  obtain ⟨v, rfl⟩ := hb.exists_caseC3Word hs
  obtain ⟨w, hw, rfl⟩ := hb.mem_e1WBar_iff.mp ht
  rw [hb.caseC3Word_conj, hb.caseC3Word_mem_e1WBar_iff]
  exact e1W_conj v w hw

theorem mem_e1PBar_iff {s : G ⧸ Z} :
    s ∈ e1PBar Z u m y x ↔ ∃ v : Fin 64, v.val % 16 = 0 ∧ caseC3Word Z u m y x v = s :=
  hb.mem_e1WordSubgroup_iff (by decide) e1P_facts.1

theorem card_e1PBar : Nat.card (e1PBar Z u m y x) = 4 :=
  (hb.card_e1WordSubgroup (P := fun v : Fin 64 => v.val % 16 = 0) (by decide)
    e1P_facts.1).trans e1P_facts.2

theorem e1PBar_le_e1WBar : e1PBar Z u m y x ≤ e1WBar Z u m y x := fun s hs => by
  obtain ⟨v, hv, rfl⟩ := hb.mem_e1PBar_iff.mp hs
  exact hb.caseC3Word_mem_e1WBar_iff.mpr (by omega)

theorem mem_e1QBar_iff {s : G ⧸ Z} : s ∈ e1QBar Z u m y x ↔
    ∃ v : Fin 64, (v.val < 16 ∧ v.val % 4 = 0) ∧ caseC3Word Z u m y x v = s :=
  hb.mem_e1WordSubgroup_iff (by decide) e1Q_facts.1

theorem card_e1QBar : Nat.card (e1QBar Z u m y x) = 4 :=
  (hb.card_e1WordSubgroup (P := fun v : Fin 64 => v.val < 16 ∧ v.val % 4 = 0) (by decide)
    e1Q_facts.1).trans e1Q_facts.2

theorem e1QBar_le_e1WBar : e1QBar Z u m y x ≤ e1WBar Z u m y x := fun s hs => by
  obtain ⟨v, hv, rfl⟩ := hb.mem_e1QBar_iff.mp hs
  exact hb.caseC3Word_mem_e1WBar_iff.mpr hv.2

theorem mem_e1VBar_iff {s : G ⧸ Z} : s ∈ e1VBar Z u m y x ↔
    ∃ v : Fin 64, (v = 0 ∨ v = 20 ∨ v = 40 ∨ v = 60) ∧ caseC3Word Z u m y x v = s :=
  hb.mem_e1WordSubgroup_iff (by decide) e1V_facts.1

theorem card_e1VBar : Nat.card (e1VBar Z u m y x) = 4 :=
  (hb.card_e1WordSubgroup (P := fun v : Fin 64 => v = 0 ∨ v = 20 ∨ v = 40 ∨ v = 60) (by decide)
    e1V_facts.1).trans e1V_facts.2.1

theorem e1VBar_le_e1WBar : e1VBar Z u m y x ≤ e1WBar Z u m y x := fun s hs => by
  obtain ⟨v, hv, rfl⟩ := hb.mem_e1VBar_iff.mp hs
  refine hb.caseC3Word_mem_e1WBar_iff.mpr ?_
  rcases hv with rfl | rfl | rfl | rfl <;> decide

end CaseC3BCD

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
  (htype : ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
    s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
      CaseC3.Genuine (Subgroup.center J) s)
include d htype

theorem involutionOddCore_inf_le_of_mem_e1WBar
    {a b : J ⧸ Subgroup.center J}
    (ha : a ∈ e1WBar (Subgroup.center J) u m y x) (hb : b ∈ e1WBar (Subgroup.center J) u m y x)
    (hb1 : b ≠ 1) : involutionOddCore a ⊓ Subgroup.centralizer {b} ≤ involutionOddCore b := by
  have hc := d.caseC3BCD
  have hab : a * b = b * a := hc.commute_of_mem_e1WBar ha hb
  obtain ⟨vb, hvb4, rfl⟩ := hc.mem_e1WBar_iff.mp hb
  have hvb0 : vb ≠ 0 := fun h => hb1 (by rw [h, CaseC3BCD.caseC3Word_zero])
  by_cases hgen : c3GenW vb
  · exact d.involutionOddCore_inf_le_of_genuine htype (hc.mul_self_of_mem_e1WBar ha) hab
      (hc.mul_self_of_mem_e1WBar hb) hb1 (hc.genuine_of_c3GenW hgen)
  have hPQ : e1PQ vb := ⟨hvb4, hvb0, hgen⟩
  set W := e1WBar (Subgroup.center J) u m y x with hW
  have hWb : W ≤ Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x vb} := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hc.commute_of_mem_e1WBar hs hb)
  have hWa : W ≤ Subgroup.centralizer {a} := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hc.commute_of_mem_e1WBar hs ha)
  have hYodd : Odd (Nat.card ↥(involutionOddCore a ⊓
      Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x vb} :
        Subgroup (J ⧸ Subgroup.center J))) :=
    (odd_card_involutionOddCore a).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hWY : W ≤ Subgroup.normalizer ((involutionOddCore a ⊓
      Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x vb} :
        Subgroup (J ⧸ Subgroup.center J)) : Set (J ⧸ Subgroup.center J)) := fun s hs =>
    mem_normalizer_of_forall_conj_mem fun c hc' => ⟨conj_mem_involutionOddCore (hWa hs) hc'.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hWb hs) hc'.2) (Subgroup.inv_mem _ (hWb hs))⟩
  have hgen' : ∀ {t : Fin 64}, c3GenW (c3Mul vb t) →
      CaseC3.Genuine (Subgroup.center J) (caseC3Word (Subgroup.center J) u m y x vb *
        caseC3Word (Subgroup.center J) u m y x t) ∧
      caseC3Word (Subgroup.center J) u m y x vb * caseC3Word (Subgroup.center J) u m y x t ≠ 1 :=
    fun {t} ht => by
      rw [hc.caseC3Word_mul, Ne, hc.caseC3Word_eq_one_iff]
      exact ⟨hc.genuine_of_c3GenW ht, ne_zero_of_c3GenW _ ht⟩
  have hbg := d.not_genuine_of_e1PQ hPQ
  have hbb := hc.mul_self_of_mem_e1WBar hb
  rcases e1PQ_four vb hPQ with hq | hp
  · refine d.le_involutionOddCore_of_not_genuine htype hbb hb1 hbg
      (V := e1QBar (Subgroup.center J) u m y x) (hc.e1QBar_le_e1WBar.trans hWb)
      (fun s hs => hc.mul_self_of_mem_e1WBar (hc.e1QBar_le_e1WBar hs)) hc.card_e1QBar
      (fun s hs hs1 => ?_) inf_le_right hYodd (hc.e1QBar_le_e1WBar.trans hWY)
    obtain ⟨q, hq', rfl⟩ := hc.mem_e1QBar_iff.mp hs
    exact hgen' (hq q hq' fun h => hs1 (by rw [h, CaseC3BCD.caseC3Word_zero]))
  · refine d.le_involutionOddCore_of_not_genuine htype hbb hb1 hbg
      (V := e1PBar (Subgroup.center J) u m y x) (hc.e1PBar_le_e1WBar.trans hWb)
      (fun s hs => hc.mul_self_of_mem_e1WBar (hc.e1PBar_le_e1WBar hs)) hc.card_e1PBar
      (fun s hs hs1 => ?_) inf_le_right hYodd (hc.e1PBar_le_e1WBar.trans hWY)
    obtain ⟨p, hp', rfl⟩ := hc.mem_e1PBar_iff.mp hs
    exact hgen' (hp p hp' fun h => hs1 (by rw [h, CaseC3BCD.caseC3Word_zero]))

theorem oddCoreSpanCompleted_e1WBar :
    OddCoreSpanCompleted (e1WBar (Subgroup.center J) u m y x) :=
  (balanced_oddCoreSpan_completed _ d.caseC3BCD.isElemAbelian_e1WBar
    (by rw [d.caseC3BCD.card_e1WBar]; norm_num)
    fun _ ha _ _ hb hb1 => d.involutionOddCore_inf_le_of_mem_e1WBar htype ha hb hb1).1

theorem oddCoreSpan_e1PBar :
    oddCoreSpan (e1PBar (Subgroup.center J) u m y x) =
    oddCoreSpan (e1WBar (Subgroup.center J) u m y x) :=
  oddCoreSpan_eq_of_completed _ _ d.caseC3BCD.isElemAbelian_e1WBar
    (by rw [d.caseC3BCD.card_e1WBar]; norm_num) (d.oddCoreSpanCompleted_e1WBar htype)
    d.caseC3BCD.e1PBar_le_e1WBar (by rw [d.caseC3BCD.card_e1PBar])

theorem oddCoreSpan_e1VBar :
    oddCoreSpan (e1VBar (Subgroup.center J) u m y x) =
    oddCoreSpan (e1WBar (Subgroup.center J) u m y x) :=
  oddCoreSpan_eq_of_completed _ _ d.caseC3BCD.isElemAbelian_e1WBar
    (by rw [d.caseC3BCD.card_e1WBar]; norm_num) (d.oddCoreSpanCompleted_e1WBar htype)
    d.caseC3BCD.e1VBar_le_e1WBar (by rw [d.caseC3BCD.card_e1VBar])

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
