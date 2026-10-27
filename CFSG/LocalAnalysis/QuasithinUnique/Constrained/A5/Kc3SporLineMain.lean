module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporLineGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Two
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Loc2

public section

namespace CFSG.QuasithinUnique.A5.Kc3SporLine

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Kc3J
  CFSG.QuasithinUnique.A5.Kc3L3

theorem delta5_facts {K : Type} [Group K] {E : Subgroup K}
    (β : ↥E ≃* Multiplicative ↥(evenWeight 5)) :
    (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x * x = 1) ∧ Nat.card E = 16 := by
  refine ⟨fun x hx y hy => congrArg Subtype.val (comm_of_beta β ⟨x, hx⟩ ⟨y, hy⟩), ?_, ?_⟩
  · intro x hx
    have h1 : β (⟨x, hx⟩ * ⟨x, hx⟩) = β 1 := by
      rw [map_mul, map_one]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one]
      exact Kc3L3.add_self_evenWeight _
    exact congrArg Subtype.val (β.injective h1)
  · rw [Nat.card_congr β.toEquiv, Nat.card_congr Multiplicative.toAdd]
    exact CFSG.QuasithinUnique.AppC.card_evenWeight

theorem noDelta5Norm_of_sylow {Γ : Type} [Group Γ] [Finite Γ] (X : Type) [MulAction Γ X]
    [Fintype X] [DecidableEq X] {R : Subgroup Γ} (hR : IsPGroup 2 R) (hRi : ¬ 2 ∣ R.index)
    (hall : ∀ E : Subgroup Γ, E ≤ R → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x * x = 1) → Nat.card E = 16 → ¬ PairFibersAllowed X E)
    (E : Subgroup Γ) (β : ↥E ≃* Multiplicative ↥(evenWeight 5)) : ¬ Delta5Norm E β := by
  intro hact
  obtain ⟨-, -, hcard⟩ := delta5_facts β
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_le hR hRi hE2
  have hact' := CFSG.QuasithinUnique.A5.Delta5Norm.map (MulAut.conj g) hact
  obtain ⟨hcomm', hsq', hcard'⟩ :=
    delta5_facts (((MulAut.conj g).subgroupMap E).symm.trans β)
  exact hall _ hg hcomm' hsq' hcard' (delta5Norm_pairFibersAllowed X hact')

theorem noDelta5Norm_of_equiv {K Γ : Type} [Group K] [Group Γ] (e : K ≃* Γ)
    (h : ∀ (E : Subgroup Γ) (β : ↥E ≃* Multiplicative ↥(evenWeight 5)), ¬ Delta5Norm E β) :
    ∀ (E : Subgroup K) (β : ↥E ≃* Multiplicative ↥(evenWeight 5)), ¬ Delta5Norm E β :=
  fun _ _ hact => h _ _ (CFSG.QuasithinUnique.A5.Delta5Norm.map e hact)

theorem kc3LocalData_of_noDelta5Norm {K : Type} [Group K]
    (h : ∀ (E : Subgroup K) (β : ↥E ≃* Multiplicative ↥(evenWeight 5)), ¬ Delta5Norm E β) :
    Kc3LocalData K :=
  fun E β hact => (h E β hact).elim

theorem kc3LocalFor_of_noDelta5Norm {P : ∀ (X : Type) [Group X], Prop} {Γ : Type} [Group Γ]
    (hP : ∀ (X : Type) [Group X], P X → Nonempty (X ≃* Γ))
    (h : ∀ (E : Subgroup Γ) (β : ↥E ≃* Multiplicative ↥(evenWeight 5)), ¬ Delta5Norm E β) :
    Kc3LocalFor P := by
  intro X _ _ hX
  obtain ⟨e⟩ := hP X hX
  exact kc3LocalData_of_noDelta5Norm (noDelta5Norm_of_equiv e h)

end CFSG.QuasithinUnique.A5.Kc3SporLine
