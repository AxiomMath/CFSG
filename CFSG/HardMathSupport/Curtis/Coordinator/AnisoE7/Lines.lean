module

public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.Assembly

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.Open CFSG.LieType.SeitzGeneration
open CFSG.Blueprint CFSG.Blueprint.Chevalley

section Lines

variable {G : Type*} [Group G]

@[expose] def E7SixLinesAt (p : ℕ) (E E₁ : Subgroup G) : Prop :=
  ∀ y ∈ E₁, y ≠ 1 → Subgroup.centralizer ({y} : Set G) ≤ hyperClosure p ⊤ E

theorem card_eq_of_relIndex_eq {p : ℕ} (hp : p.Prime) {E₁ B : Subgroup G} (hB : B ≤ E₁)
    (hc : Nat.card E₁ = p ^ 2) (hi : B.relIndex E₁ = p) : Nat.card B = p := by
  have h := Subgroup.relIndex_mul_card (H := B) (K := E₁)
  rw [inf_eq_left.2 hB, hi, hc] at h
  have hp0 : 0 < p := hp.pos
  have : p * Nat.card B = p * p := by rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_left hp0 this

end Lines

theorem e7SixStep3Adj_of_lines
    (h : ∀ (K : Type) [Field K] [Finite K] (r : ℕ) [Fact r.Prime] [CharP K r] (p : ℕ), p.Prime →
      orderOf ((Nat.card K : ℕ) : ZMod p) = 6 →
      ∃ E E₁ : Subgroup ↥(adjointGroup Tag.E7 K), IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
        E₁ ≤ E ∧ Nat.card E₁ = p ^ 2 ∧
        (∃ R : Subgroup ↥(adjointGroup Tag.E7 K), R ≠ ⊥ ∧ IsPGroup r R ∧
          ∀ x ∈ E₁, R.map (MulAut.conj x).toMonoidHom = R) ∧
        E7SixLinesAt p E E₁) :
    E7SixStep3Adj := by
  intro K _ _ r _ _ p hp hord
  obtain ⟨E, E₁, hE, hEc, hE₁E, hE₁c, hR, hlines⟩ := h K r p hp hord
  refine ⟨E, E₁, hE, hEc, hE₁E, ?_, hR, ?_⟩
  · intro h0
    rw [h0, Subgroup.card_bot] at hE₁c
    have := hp.one_lt
    nlinarith
  · intro B hB hBi k hk
    have hBc := card_eq_of_relIndex_eq hp hB hE₁c hBi
    have hBne : B ≠ ⊥ := by
      intro h0
      rw [h0, Subgroup.card_bot] at hBc
      exact hp.one_lt.ne hBc
    obtain ⟨y, hyne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hBne
    have hyne : (y : ↥(adjointGroup Tag.E7 K)) ≠ 1 := fun h' => hyne (Subtype.ext h')
    have hyB : (y : ↥(adjointGroup Tag.E7 K)) ∈ B := y.2
    refine hlines y (hB hyB) hyne ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact hk _ hyB

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
