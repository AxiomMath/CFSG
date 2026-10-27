module

public import CFSG.Yardstones.Md0ec50421ce4.Definitions
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremB.GammaStarConj

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section ElemAbelian

variable {G : Type} [Group G]

theorem isPGroup_of_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsPGroup p E := fun g => ⟨1, by
  rw [pow_one]
  exact Subtype.ext (by simpa using hE.2 g g.2)⟩

theorem exists_card_eq_pow_of_isElemAbelian [Finite G] {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) : ∃ k : ℕ, Nat.card E = p ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  exact (isPGroup_of_isElemAbelian hE).exists_card_eq

theorem isElemAbelian_commute {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := by
  have h := hE.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val h

theorem isElemAbelian_mono {p : ℕ} {E F : Subgroup G} (hE : IsElemAbelian p E) (hFE : F ≤ E) :
    IsElemAbelian p F :=
  ⟨⟨⟨fun a b => Subtype.ext (isElemAbelian_commute hE (hFE a.2) (hFE b.2))⟩⟩, fun x hx => hE.2 x (hFE hx)⟩

theorem isElemAbelian_le_centralizer {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) {a : G}
    (ha : a ∈ E) : E ≤ Subgroup.centralizer ({a} : Set G) := by
  intro b hb
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (isElemAbelian_commute hE ha hb).symm

end ElemAbelian

section TwoLocalRank

variable {G : Type} [Group G] [Finite G]

theorem bddAbove_twoLocalPRanks {p : ℕ} (hp : 1 < p) :
    BddAbove {k | ∃ H : Subgroup G, IsTwoLocal H ∧ CFSG.Open.pRank p H = k} := by
  refine ⟨Nat.card G, ?_⟩
  rintro k ⟨H, -, rfl⟩
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hp H
  have h1 : CFSG.Open.pRank p H < p ^ CFSG.Open.pRank p H := Nat.lt_pow_self hp
  have h2 : p ^ CFSG.Open.pRank p H ≤ Nat.card G := hE ▸ Subgroup.card_le_card_group E
  change CFSG.Open.pRank p H ≤ Nat.card G
  omega

theorem pRank_normalizer_le {p : ℕ} (hp : 1 < p) {S : Subgroup G} (hS : S ≠ ⊥)
    (hS2 : IsPGroup 2 S) :
    CFSG.Open.pRank p (Subgroup.normalizer (S : Set G)) ≤ GLATwoLocalRank p G :=
  le_csSup (bddAbove_twoLocalPRanks hp) ⟨_, ⟨S, hS, hS2, rfl⟩, rfl⟩

theorem card_le_pow_glaTwoLocalRank {p : ℕ} (hp : p.Prime) {E S : Subgroup G}
    (hE : IsElemAbelian p E) (hS : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    (hES : E ≤ Subgroup.normalizer (S : Set G)) :
    Nat.card E ≤ p ^ GLATwoLocalRank p G := by
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian hp hE
  have h1 : k ≤ CFSG.Open.pRank p (Subgroup.normalizer (S : Set G)) :=
    CFSG.SectionRank.le_pRank hp.one_lt hES hE hk
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos (h1.trans (pRank_normalizer_le hp.one_lt hS hS2))

theorem GLAIsBmax.eq_of_le {p : ℕ} (hp : p.Prime) {B E S : Subgroup G} (hB : GLAIsBmax p B)
    (hBE : B ≤ E) (hE : IsElemAbelian p E) (hS : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    (hES : E ≤ Subgroup.normalizer (S : Set G)) : E = B := by
  have h1 := card_le_pow_glaTwoLocalRank hp hE hS hS2 hES
  rw [← hB.2.1] at h1
  exact (Subgroup.eq_of_le_of_card_ge hBE h1).symm

theorem GLAIsBmax.isPGroup {p : ℕ} {B : Subgroup G} (hB : GLAIsBmax p B) : IsPGroup p B :=
  isPGroup_of_isElemAbelian hB.1

end TwoLocalRank

section CentMod

variable {G : Type} [Group G]

theorem normalizer_le_normalizer_glaPPrimeCoreOf (p : ℕ) (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq] at hg ⊢
  rw [← glaPPrimeCoreOf_gLBConj, hg]

theorem commutatorElement_mul_right (l a b : G) :
    ⁅l, a * b⁆ = ⁅l, a⁆ * (a * ⁅l, b⁆ * a⁻¹) := by
  simp only [commutatorElement_def, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

theorem commutatorElement_inv_right (l a : G) :
    ⁅l, a⁻¹⁆ = a⁻¹ * ⁅l, a⁆⁻¹ * a := by
  simp only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]

@[expose] def centModSubgroup (p : ℕ) (L : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (L : Set G) ∧ ∀ l ∈ L, ⁅l, g⁆ ∈ GLAPPrimeCoreOf p L}
  one_mem' := ⟨Subgroup.one_mem _, fun l _ => by
    rw [commutatorElement_one_right]
    exact Subgroup.one_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha, hLa⟩ ⟨hb, hLb⟩
    refine ⟨Subgroup.mul_mem _ ha hb, fun l hl => ?_⟩
    rw [commutatorElement_mul_right]
    refine Subgroup.mul_mem _ (hLa l hl) ?_
    exact (Subgroup.mem_normalizer_iff.1
      (normalizer_le_normalizer_glaPPrimeCoreOf p L ha) _).1 (hLb l hl)
  inv_mem' := by
    rintro a ⟨ha, hLa⟩
    refine ⟨Subgroup.inv_mem _ ha, fun l hl => ?_⟩
    rw [commutatorElement_inv_right]
    have hinv := Subgroup.inv_mem _ ha
    have := (Subgroup.mem_normalizer_iff.1
      (normalizer_le_normalizer_glaPPrimeCoreOf p L hinv) ⁅l, a⁆⁻¹).1
      (Subgroup.inv_mem _ (hLa l hl))
    simpa [inv_inv] using this

theorem mem_centModSubgroup {p : ℕ} {L : Subgroup G} {g : G} :
    g ∈ centModSubgroup p L ↔
      g ∈ Subgroup.normalizer (L : Set G) ∧ ∀ l ∈ L, ⁅l, g⁆ ∈ GLAPPrimeCoreOf p L :=
  Iff.rfl

theorem centMod_iff {p : ℕ} {L : Subgroup G} {g : G} :
    CentMod p L g ↔ g ∈ centModSubgroup p L := by
  constructor
  · rintro ⟨hg, hL⟩
    exact ⟨hg, fun l hl => hL (Subgroup.commutator_mem_commutator hl
      (Subgroup.mem_zpowers g))⟩
  · intro hg
    refine ⟨hg.1, ?_⟩
    rw [Subgroup.commutator_le]
    intro l hl c hc
    have hc' : c ∈ centModSubgroup p L :=
      (Subgroup.zpowers_le.2 hg) hc
    exact hc'.2 l hl

theorem centMod_of_mem_centralizer {p : ℕ} {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (L : Set G)) : CentMod p L g := by
  rw [centMod_iff]
  refine ⟨Subgroup.centralizer_le_normalizer _ hg, fun l hl => ?_⟩
  have h : ⁅l, g⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.1 hg l hl
  rw [h]
  exact Subgroup.one_mem _

theorem centMod_mul {p : ℕ} {L : Subgroup G} {a b : G} (ha : CentMod p L a)
    (hb : CentMod p L b) : CentMod p L (a * b) := by
  rw [centMod_iff] at *
  exact Subgroup.mul_mem _ ha hb

theorem centMod_inv {p : ℕ} {L : Subgroup G} {a : G} (ha : CentMod p L a) :
    CentMod p L a⁻¹ := by
  rw [centMod_iff] at *
  exact Subgroup.inv_mem _ ha

theorem centMod_one (p : ℕ) (L : Subgroup G) : CentMod p L 1 := by
  rw [centMod_iff]
  exact Subgroup.one_mem _

end CentMod

section Product

variable {X : Type*} [Group X]

theorem card_sup_mul_card_inf_of_normal (A B : Subgroup X) [A.Normal] :
    Nat.card (A ⊔ B : Subgroup X) * Nat.card (A ⊓ B : Subgroup X) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := A ⊔ B)
  rw [Subgroup.relIndex_sup_left, inf_eq_left.mpr le_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [← h1, ← h2]
  ring

theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup X}
    (hB : B ≤ Subgroup.normalizer (A : Set X)) :
    Nat.card (A ⊔ B : Subgroup X) * Nat.card (A ⊓ B : Subgroup X) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set X)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal (A.subgroupOf N) (B.subgroupOf N)
  have hc : ∀ Y : Subgroup X, Y ≤ N → Nat.card (Y.subgroupOf N) = Nat.card Y := fun Y hY =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have hsup : A.subgroupOf N ⊔ B.subgroupOf N = (A ⊔ B).subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAN, inf_eq_left.mpr hB,
      inf_eq_left.mpr (sup_le hAN hB)]
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc _ hAN, hc _ hB] at h
  exact h

theorem not_dvd_card_sup_of_le_normalizer [Finite X] {p : ℕ} (hp : p.Prime) {A B : Subgroup X}
    (hB : B ≤ Subgroup.normalizer (A : Set X)) (hA : ¬ p ∣ Nat.card A) (hBp : ¬ p ∣ Nat.card B) :
    ¬ p ∣ Nat.card (A ⊔ B : Subgroup X) := by
  intro h
  have h1 := card_sup_mul_card_inf_of_le_normalizer hB
  have h2 : p ∣ Nat.card A * Nat.card B := h1 ▸ dvd_mul_of_dvd_left h _
  rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
  · exact hA h3
  · exact hBp h3

end Product

section MaxTwoLocal

variable {G : Type} [Group G] [Finite G]

theorem exists_maxTwoLocal_ge {H : Subgroup G} (hH : IsTwoLocal H) :
    ∃ M : Subgroup G, GLAIsMaxTwoLocal M ∧ H ≤ M := by
  classical
  set S : Set (Subgroup G) := {M | IsTwoLocal M ∧ H ≤ M} with hS
  obtain ⟨M, ⟨hM, hHM⟩, hmax⟩ := Set.exists_max_image S (fun M => Nat.card M) (Set.toFinite S)
    ⟨H, hH, le_rfl⟩
  refine ⟨M, ⟨hM, fun K hK hMK => ?_⟩, hHM⟩
  have hKS : K ∈ S := ⟨hK, hHM.trans hMK⟩
  exact (Subgroup.eq_of_le_of_card_ge hMK (hmax K hKS)).symm

theorem GLAIsBmax.exists_maxTwoLocal {p : ℕ} {B : Subgroup G} (hB : GLAIsBmax p B) :
    ∃ N : Subgroup G, GLAIsMaxTwoLocal N ∧ B ≤ N := by
  obtain ⟨U, hU, hU2, hBU⟩ := hB.2.2
  obtain ⟨N, hN, hUN⟩ := exists_maxTwoLocal_ge ⟨U, hU, hU2, rfl⟩
  exact ⟨N, hN, hBU.trans hUN⟩

end MaxTwoLocal

end CFSG.LocalAnalysis.GLTheoremA
