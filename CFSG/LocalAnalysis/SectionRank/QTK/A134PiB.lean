module

public import CFSG.LocalAnalysis.SectionRank.QTK.A134Pi
public import CFSG.Quasithin.Background.A3FactsA134Core

public section

namespace CFSG.SectionRank.QTK

open Subgroup CFSG.Quasithin.A3Facts

variable {ι : Type} [DecidableEq ι] {S : ι → Type} [∀ i, Group (S i)] {p : ℕ}

theorem exists_pi_pair_normalizer {i₁ i₂ : ι} (h : i₁ ≠ i₂) {R : Subgroup (S i₁)} (hR : R ≠ ⊥)
    (hR2 : IsPGroup 2 R) {E₁ : Subgroup (S i₁)} (hE₁N : E₁ ≤ normalizer (R : Set (S i₁)))
    (hE₁ : CFSG.Open.IsElemAbelian p E₁) {E₂ : Subgroup (S i₂)}
    (hE₂ : CFSG.Open.IsElemAbelian p E₂) :
    ∃ R' : Subgroup (∀ i, S i), R' ≠ ⊥ ∧ IsPGroup 2 R' ∧ ∃ E : Subgroup (∀ i, S i),
      E ≤ normalizer (R' : Set (∀ i, S i)) ∧ CFSG.Open.IsElemAbelian p E ∧
        Nat.card E = Nat.card E₁ * Nat.card E₂ := by
  set f := inclPair (S := S) h
  have hf := inclPair_injective (S := S) h
  refine ⟨(R.prod ⊥).map f, fun hb => hR ?_, (isPGroup_prod_bot hR2).map _,
    (E₁.prod E₂).map f, ?_, isElemAbelian_map _ (isElemAbelian_prod hE₁ hE₂), ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    have hmem : f (x, 1) ∈ (R.prod ⊥).map f := ⟨(x, 1), ⟨hx, Subgroup.one_mem _⟩, rfl⟩
    rw [hb, Subgroup.mem_bot, ← map_one f] at hmem
    exact Subgroup.mem_bot.mpr (congrArg Prod.fst (hf hmem))
  · exact (Subgroup.map_mono (prod_le_normalizer_prod_bot hE₁N E₂)).trans
      (Subgroup.le_normalizer_map _)
  · rw [Subgroup.card_map_of_injective hf, Nat.card_congr (Subgroup.prodEquiv E₁ E₂).toEquiv,
      Nat.card_prod]

theorem exists_pi_triple_normalizer {i₁ i₂ i₃ : ι} (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃)
    (h23 : i₂ ≠ i₃) {R : Subgroup (S i₁)} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    {E₁ : Subgroup (S i₁)} (hE₁N : E₁ ≤ normalizer (R : Set (S i₁)))
    (hE₁ : CFSG.Open.IsElemAbelian p E₁) {E₂ : Subgroup (S i₂)}
    (hE₂ : CFSG.Open.IsElemAbelian p E₂) {E₃ : Subgroup (S i₃)}
    (hE₃ : CFSG.Open.IsElemAbelian p E₃) :
    ∃ R' : Subgroup (∀ i, S i), R' ≠ ⊥ ∧ IsPGroup 2 R' ∧ ∃ E : Subgroup (∀ i, S i),
      E ≤ normalizer (R' : Set (∀ i, S i)) ∧ CFSG.Open.IsElemAbelian p E ∧
        Nat.card E = Nat.card E₁ * Nat.card E₂ * Nat.card E₃ := by
  set f := inclTriple (S := S) h12 h13 h23
  have hf := inclTriple_injective (S := S) h12 h13 h23
  refine ⟨((R.prod ⊥).prod ⊥).map f, fun hb => hR ?_,
    (isPGroup_prod_bot (isPGroup_prod_bot hR2)).map _, ((E₁.prod E₂).prod E₃).map f, ?_,
    isElemAbelian_map _ (isElemAbelian_prod (isElemAbelian_prod hE₁ hE₂) hE₃), ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    have hmem : f ((x, 1), 1) ∈ ((R.prod ⊥).prod ⊥).map f :=
      ⟨((x, 1), 1), ⟨⟨hx, Subgroup.one_mem _⟩, Subgroup.one_mem _⟩, rfl⟩
    rw [hb, Subgroup.mem_bot, ← map_one f] at hmem
    exact Subgroup.mem_bot.mpr (congrArg (fun z => z.1.1) (hf hmem))
  · exact (Subgroup.map_mono (prod_le_normalizer_prod_bot
      (prod_le_normalizer_prod_bot hE₁N E₂) E₃)).trans (Subgroup.le_normalizer_map _)
  · rw [Subgroup.card_map_of_injective hf,
      Nat.card_congr (Subgroup.prodEquiv (E₁.prod E₂) E₃).toEquiv, Nat.card_prod,
      Nat.card_congr (Subgroup.prodEquiv E₁ E₂).toEquiv, Nat.card_prod]

variable [Finite ι] [∀ i, Finite (S i)]

theorem pi_pair_pRank_le (hp : 1 < p) (hPi : ∀ R : Subgroup (∀ i, S i), R ≠ ⊥ → IsPGroup 2 R →
      CFSG.Open.pRank p (normalizer (R : Set (∀ i, S i))) ≤ 2)
    {i₁ i₂ : ι} (h : i₁ ≠ i₂) {R : Subgroup (S i₁)} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) :
    CFSG.Open.pRank p (normalizer (R : Set (S i₁))) +
      CFSG.Open.pRank p (⊤ : Subgroup (S i₂)) ≤ 2 := by
  obtain ⟨E₁, hE₁N, hE₁, hc₁⟩ := exists_eq_pRank hp (normalizer (R : Set (S i₁)))
  obtain ⟨E₂, -, hE₂, hc₂⟩ := exists_eq_pRank hp (⊤ : Subgroup (S i₂))
  obtain ⟨R', hR', hR'2, E, hEN, hE, hc⟩ :=
    exists_pi_pair_normalizer (p := p) h hR hR2 hE₁N hE₁ hE₂
  rw [hc₁, hc₂, ← pow_add] at hc
  exact (le_pRank_of_le hp hEN hE hc).trans (hPi R' hR' hR'2)

theorem pi_triple_pRank_le (hp : 1 < p) (hPi : ∀ R : Subgroup (∀ i, S i), R ≠ ⊥ → IsPGroup 2 R →
      CFSG.Open.pRank p (normalizer (R : Set (∀ i, S i))) ≤ 2)
    {i₁ i₂ i₃ : ι} (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃) {R : Subgroup (S i₁)}
    (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) :
    CFSG.Open.pRank p (normalizer (R : Set (S i₁))) + CFSG.Open.pRank p (⊤ : Subgroup (S i₂)) +
      CFSG.Open.pRank p (⊤ : Subgroup (S i₃)) ≤ 2 := by
  obtain ⟨E₁, hE₁N, hE₁, hc₁⟩ := exists_eq_pRank hp (normalizer (R : Set (S i₁)))
  obtain ⟨E₂, -, hE₂, hc₂⟩ := exists_eq_pRank hp (⊤ : Subgroup (S i₂))
  obtain ⟨E₃, -, hE₃, hc₃⟩ := exists_eq_pRank hp (⊤ : Subgroup (S i₃))
  obtain ⟨R', hR', hR'2, E, hEN, hE, hc⟩ :=
    exists_pi_triple_normalizer (p := p) h12 h13 h23 hR hR2 hE₁N hE₁ hE₂ hE₃
  rw [hc₁, hc₂, hc₃, ← pow_add, ← pow_add] at hc
  exact (le_pRank_of_le hp hEN hE hc).trans (hPi R' hR' hR'2)

end CFSG.SectionRank.QTK
