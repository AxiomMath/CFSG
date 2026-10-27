module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsGroup
public import CFSG.RankThree.PartTwo.Sec4.T444.Coprime

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem pRank_barO2_eq_aux_notDvdCard {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ q ∣ Nat.card (CFSG.pCore 2 X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := X))
  rw [hn]
  intro h
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))

theorem pRank_barO2_eq_aux_powTwo {n : X} (hn : n ∈ CFSG.pCore 2 X) :
    ∃ k : ℕ, n ^ (2 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)) ⟨n, hn⟩
  exact ⟨k, congrArg Subtype.val hk⟩

theorem pRank_barO2_eq_aux_le (U : Subgroup X) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q U ≤ CFSG.Open.pRank q (barO2 U) := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨E, hEU, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt U
  have hEp : IsPGroup q E := IsPGroup.iff_card.2 ⟨_, hcard⟩
  have hbot : E ⊓ CFSG.pCore 2 X = ⊥ :=
    CFSG.RankThree.PartTwo.Sec4.inf_eq_bot_of_isPGroup_of_not_dvd hq hEp
      (pRank_barO2_eq_aux_notDvdCard hq hq2)
  have hinj : Function.Injective ((QuotientGroup.mk' (CFSG.pCore 2 X)).comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro e he
    have h1 : (e : X) ∈ CFSG.pCore 2 X := by
      simpa [QuotientGroup.eq_one_iff] using he
    have h2 : (e : X) ∈ E ⊓ CFSG.pCore 2 X := ⟨e.2, h1⟩
    rw [hbot, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  haveI := hE.1
  refine CFSG.SectionRank.le_pRank_of_injective hq.one_lt (fun a b => mul_comm' a b)
    (fun a => Subtype.ext (hE.2 _ a.2)) hcard _ hinj ?_
  rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact Subgroup.map_mono hEU

theorem pRank_barO2_eq_aux_eq (U : Subgroup X) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q U = CFSG.Open.pRank q (barO2 U) := by
  refine le_antisymm (pRank_barO2_eq_aux_le U hq hq2) ?_
  refine CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hq _ ?_ U
  rw [QuotientGroup.ker_mk']
  exact pRank_barO2_eq_aux_notDvdCard hq hq2

theorem pRank_barO2_eq {L : Subgroup X} (hL : IsC2 L) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q L = CFSG.Open.pRank q (barO2 L) := by
  have _ := hL
  exact pRank_barO2_eq_aux_eq L hq hq2

theorem pRank_add_le_pRank_sup_aux_comm {Y : Type} [Group Y] {q : ℕ} {E : Subgroup Y}
    (hE : CFSG.Open.IsElemAbelian q E) {a b : Y} (ha : a ∈ E) (hb : b ∈ E) :
    a * b = b * a := by
  haveI := hE.1
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E) ⟨b, hb⟩)

theorem pRank_add_le_pRank_sup_aux_commute {Y : Type} [Group Y] [Finite Y] {A B : Subgroup Y}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {q : ℕ} (hq : q.Prime) {s : ℕ}
    (hs : CFSG.Open.pRank q ((Subgroup.center ↥A).map A.subtype) ≤ s) :
    CFSG.Open.pRank q A + CFSG.Open.pRank q B ≤ CFSG.Open.pRank q (A ⊔ B) + s := by
  have hq1 : 1 < q := hq.one_lt
  obtain ⟨E₁, hE₁A, hE₁, hc₁⟩ := CFSG.SectionRank.exists_pRank hq1 A
  obtain ⟨E₂, hE₂B, hE₂, hc₂⟩ := CFSG.SectionRank.exists_pRank hq1 B
  have hcomm : ∀ x ∈ E₁, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy =>
    hc x (hE₁A hx) y (hE₂B hy)
  obtain ⟨hcard, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E₁ E₂ hcomm
  have hmem : ∀ x ∈ E₁ ⊔ E₂, ∃ a ∈ E₁, ∃ b ∈ E₂, x = a * b := by
    intro x hx
    have hx' : x ∈ ((E₁ ⊔ E₂ : Subgroup Y) : Set Y) := hx
    rw [hset] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    exact ⟨a, ha, b, hb, rfl⟩
  have hsupEA : CFSG.Open.IsElemAbelian q (E₁ ⊔ E₂) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha, b, hb, hxe⟩ := hmem x x.2
      obtain ⟨a', ha', b', hb', hye⟩ := hmem y y.2
      apply Subtype.ext
      change (x : Y) * y = y * x
      have c1 : Commute a a' := pRank_add_le_pRank_sup_aux_comm hE₁ ha ha'
      have c2 : Commute a b' := hcomm a ha b' hb'
      have c3 : Commute b a' := (hcomm a' ha' b hb).symm
      have c4 : Commute b b' := pRank_add_le_pRank_sup_aux_comm hE₂ hb hb'
      have c : Commute (a * b) (a' * b') :=
        Commute.mul_left (Commute.mul_right c1 c2) (Commute.mul_right c3 c4)
      rw [hxe, hye]
      exact c
    · obtain ⟨a, ha, b, hb, rfl⟩ := hmem x hx
      have c : Commute a b := hcomm a ha b hb
      rw [c.mul_pow, hE₁.2 a ha, hE₂.2 b hb, one_mul]
  have hinfEA : CFSG.Open.IsElemAbelian q (E₁ ⊓ E₂) :=
    ⟨⟨⟨fun x y => Subtype.ext (pRank_add_le_pRank_sup_aux_comm hE₁ x.2.1 y.2.1)⟩⟩,
      fun x hx => hE₁.2 x hx.1⟩
  have hinfZ : E₁ ⊓ E₂ ≤ (Subgroup.center ↥A).map A.subtype := by
    intro x hx
    have hxA : x ∈ A := hE₁A hx.1
    have hxB : x ∈ B := hE₂B hx.2
    refine ⟨⟨x, hxA⟩, ?_, rfl⟩
    show (⟨x, hxA⟩ : A) ∈ Subgroup.center ↥A
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2 x hxB)
  have hdvd1 : Nat.card ↥(E₁ ⊓ E₂) ∣ q ^ CFSG.Open.pRank q A := by
    rw [← hc₁]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨t, -, htcard⟩ := (Nat.dvd_prime_pow hq).1 hdvd1
  have ht : t ≤ s := (CFSG.SectionRank.le_pRank hq1 hinfZ hinfEA htcard).trans hs
  have hprod : Nat.card ↥(E₁ ⊔ E₂) * q ^ t = q ^ (CFSG.Open.pRank q A + CFSG.Open.pRank q B) := by
    rw [← htcard, hcard, hc₁, hc₂, pow_add]
  obtain ⟨j, -, hjcard⟩ := (Nat.dvd_prime_pow hq).1 (Dvd.intro _ hprod)
  rw [hjcard, ← pow_add] at hprod
  have hjt : j + t = CFSG.Open.pRank q A + CFSG.Open.pRank q B :=
    Nat.pow_right_injective hq.two_le hprod
  have hj : j ≤ CFSG.Open.pRank q (A ⊔ B) :=
    CFSG.SectionRank.le_pRank hq1 (sup_le_sup hE₁A hE₂B) hsupEA hjcard
  omega

theorem pRank_add_le_pRank_sup_aux_barO2_ne {L L' : Subgroup X} (hL : IsC2 L) (hL' : IsC2 L')
    (hbar : barO2 L ≠ barO2 L') {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {s : ℕ}
    (hs : CFSG.Open.pRank q ((Subgroup.center ↥(barO2 L)).map (barO2 L).subtype) ≤ s) :
    CFSG.Open.pRank q L + CFSG.Open.pRank q L' ≤ CFSG.Open.pRank q (L ⊔ L') + s := by
  have hcomm : ⁅barO2 L, barO2 L'⁆ = ⊥ :=
    kComp_holds.1 (X ⧸ CFSG.pCore 2 X) (barO2 L) (barO2 L') hL.component hL'.component hbar
  have hc : ∀ a ∈ barO2 L, ∀ b ∈ barO2 L', a * b = b * a := by
    intro a ha b hb
    have ha' := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm ha
    exact ((Subgroup.mem_centralizer_iff.1 ha') b hb).symm
  have hsup : barO2 (L ⊔ L') = barO2 L ⊔ barO2 L' := Subgroup.map_sup _ _ _
  have h3 : CFSG.Open.pRank q (L ⊔ L') = CFSG.Open.pRank q (barO2 L ⊔ barO2 L') := by
    rw [pRank_barO2_eq_aux_eq (L ⊔ L') hq hq2, hsup]
  rw [pRank_barO2_eq hL hq hq2, pRank_barO2_eq hL' hq hq2, h3]
  exact pRank_add_le_pRank_sup_aux_commute hc hq hs

theorem pRank_add_le_pRank_sup_aux_subn {H K : Subgroup X}
    (hHK : CFSG.Open.IsSubnormal H K) :
    H ≤ K ∧ ∀ h ∈ H, Odd (orderOf h) →
      ⁅CFSG.pCore 2 X ⊓ K, Subgroup.zpowers h⁆ ≤ H := by
  induction hHK with
  | refl H =>
    exact ⟨le_rfl, fun h hh _ =>
      Subgroup.commutator_le_of_le inf_le_right (Subgroup.zpowers_le.2 hh)⟩
  | @step H M K hHM hnorm hMK ih =>
    obtain ⟨hMK', ih⟩ := ih
    refine ⟨hHM.trans hMK', fun h hh hodd => ?_⟩
    have hhM : h ∈ M := hHM hh
    have hhK : h ∈ K := hMK' hhM
    have hZH : Subgroup.zpowers h ≤ H := Subgroup.zpowers_le.2 hh
    have hZK : Subgroup.zpowers h ≤ K := Subgroup.zpowers_le.2 hhK
    have hN'2 : IsPGroup 2 ↥(CFSG.pCore 2 X ⊓ K) :=
      (CFSG.pCore_isPGroup (p := 2) (G := X)).to_le inf_le_left
    have hKnorm : K ≤ Subgroup.normalizer ((CFSG.pCore 2 X ⊓ K : Subgroup X) : Set X) := by
      rw [Subgroup.le_normalizer_iff]
      intro k hk g hg
      exact ⟨CFSG.pCore_normal.conj_mem g hg.1 k, K.mul_mem (K.mul_mem hk hg.2) (K.inv_mem hk)⟩
    obtain ⟨-, hcop⟩ := kCop_holds X (CFSG.pCore 2 X ⊓ K) h hN'2 (hKnorm hhK) hodd
    have h1 : ⁅CFSG.pCore 2 X ⊓ K, Subgroup.zpowers h⁆ ≤ M := ih h hhM hodd
    have h2 : ⁅CFSG.pCore 2 X ⊓ K, Subgroup.zpowers h⁆ ≤ CFSG.pCore 2 X ⊓ K := by
      refine le_inf ?_ (Subgroup.commutator_le_of_le inf_le_right hZK)
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono_right inf_le_left).trans (Subgroup.commutator_le_right _ _)
    have h3 : ⁅CFSG.pCore 2 X ⊓ K, Subgroup.zpowers h⁆ ≤
        ⁅(CFSG.pCore 2 X ⊓ K) ⊓ M, Subgroup.zpowers h⁆ := by
      calc ⁅CFSG.pCore 2 X ⊓ K, Subgroup.zpowers h⁆
          = ⁅⁅CFSG.pCore 2 X ⊓ K, Subgroup.zpowers h⁆, Subgroup.zpowers h⁆ := hcop.symm
        _ ≤ ⁅(CFSG.pCore 2 X ⊓ K) ⊓ M, Subgroup.zpowers h⁆ :=
          Subgroup.commutator_mono_left (le_inf h2 h1)
    have h4 : ⁅(CFSG.pCore 2 X ⊓ K) ⊓ M, Subgroup.zpowers h⁆ ≤ H := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      have hg₂H : g₂ ∈ H := hZH hg₂
      have hconj := hnorm.conj_mem (⟨g₂, hHM hg₂H⟩ : M) hg₂H ⟨g₁, hg₁.2⟩
      have hconj' : g₁ * g₂ * g₁⁻¹ ∈ H := hconj
      exact H.mul_mem hconj' (H.inv_mem hg₂H)
    exact h3.trans h4

theorem pRank_add_le_pRank_sup_aux_normalizer {L : Subgroup X} (hL : IsC2 L) :
    CFSG.pCore 2 X ≤ Subgroup.normalizer (L : Set X) := by
  have hcl : Subgroup.closure {x : X | x ∈ L ∧ Odd (orderOf x)} = L := hL.2.1
  have hcomm := (pRank_add_le_pRank_sup_aux_subn hL.1).2
  have key : CFSG.pCore 2 X ≤
      Subgroup.normalizer ((Subgroup.closure {x : X | x ∈ L ∧ Odd (orderOf x)} : Subgroup X) :
        Set X) := by
    rw [Subgroup.le_normalizer_closure_iff]
    intro z hz g hg
    rw [hcl]
    have h1 : ⁅z, g⁆ ∈ L :=
      hcomm g hg.1 hg.2
        (Subgroup.commutator_mem_commutator ⟨hz, Subgroup.mem_top z⟩ (Subgroup.mem_zpowers g))
    have h2 : z * g * z⁻¹ = ⁅z, g⁆ * g := by
      simp [commutatorElement_def, mul_assoc]
    rw [h2]
    exact L.mul_mem h1 hg.1
  rwa [hcl] at key

theorem pRank_add_le_pRank_sup_aux_mem {L : Subgroup X}
    (hN : CFSG.pCore 2 X ≤ Subgroup.normalizer (L : Set X)) {x : X}
    (hx : x ∈ L ⊔ CFSG.pCore 2 X) (hodd : Odd (orderOf x)) : x ∈ L := by
  have hLW : L ≤ Subgroup.normalizer (L : Set X) := Subgroup.le_normalizer
  have hx' : x ∈ ((L ⊔ CFSG.pCore 2 X : Subgroup X) : Set X) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L (CFSG.pCore 2 X) hN] at hx'
  obtain ⟨l, hl, n, hn, rfl⟩ := hx'
  obtain ⟨k, hk⟩ := pRank_barO2_eq_aux_powTwo hn
  let W : Subgroup X := Subgroup.normalizer (L : Set X)
  let π : W →* W ⧸ L.subgroupOf W := QuotientGroup.mk' (L.subgroupOf W)
  let lw : W := ⟨l, hLW hl⟩
  let nw : W := ⟨n, hN hn⟩
  have h1 : π lw = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hl
  have h2 : π (lw * nw) = π nw := by rw [map_mul, h1, one_mul]
  have hd1 : orderOf (π nw) ∣ 2 ^ k := by
    refine (orderOf_map_dvd π nw).trans ?_
    rw [← Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one hk
  have hd2 : orderOf (π nw) ∣ orderOf (l * n) := by
    rw [← h2]
    refine (orderOf_map_dvd π (lw * nw)).trans ?_
    rw [← Subgroup.orderOf_coe]
    exact dvd_rfl
  have hcop : Nat.Coprime (2 ^ k) (orderOf (l * n)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have h3 : orderOf (π nw) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  have h4 : π (lw * nw) = 1 := by rw [h2]; exact orderOf_eq_one_iff.1 h3
  have h5 : lw * nw ∈ L.subgroupOf W := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h4
    exact h4
  exact h5

theorem pRank_add_le_pRank_sup_aux_le {L L' : Subgroup X} (hL : IsC2 L) (hL' : IsC2 L')
    (h : barO2 L' ≤ barO2 L) : L' ≤ L := by
  have hN := pRank_add_le_pRank_sup_aux_normalizer hL
  have hcl : Subgroup.closure {x : X | x ∈ L' ∧ Odd (orderOf x)} = L' := hL'.2.1
  rw [← hcl, Subgroup.closure_le]
  rintro x ⟨hxL', hxodd⟩
  have h1 : (QuotientGroup.mk' (CFSG.pCore 2 X)) x ∈ barO2 L := h (Subgroup.mem_map_of_mem _ hxL')
  have h2 : x ∈ (barO2 L).comap (QuotientGroup.mk' (CFSG.pCore 2 X)) := h1
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
  exact pRank_add_le_pRank_sup_aux_mem hN h2 hxodd

theorem pRank_add_le_pRank_sup_aux_inj {L L' : Subgroup X} (hL : IsC2 L) (hL' : IsC2 L')
    (h : barO2 L = barO2 L') : L = L' :=
  le_antisymm (pRank_add_le_pRank_sup_aux_le hL' hL h.le)
    (pRank_add_le_pRank_sup_aux_le hL hL' h.ge)

theorem pRank_add_le_pRank_sup {L L' : Subgroup X} (hL : IsC2 L) (hL' : IsC2 L') (hne : L ≠ L')
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {s : ℕ}
    (hs : CFSG.Open.pRank q ((Subgroup.center ↥(barO2 L)).map (barO2 L).subtype) ≤ s) :
    CFSG.Open.pRank q L + CFSG.Open.pRank q L' ≤ CFSG.Open.pRank q (L ⊔ L') + s :=
  pRank_add_le_pRank_sup_aux_barO2_ne hL hL'
    (fun h => hne (pRank_add_le_pRank_sup_aux_inj hL hL' h)) hq hq2 hs

end CFSG.LocalAnalysis.RankThreeUC.S15
