module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterKleinTwo
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoA

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.Monster.Existence

section Residual

variable {G : Type} [Group G]

@[expose] def TwoATwoCommuting (p : ℕ) (G : Type) [Group G] : Prop :=
  ∀ s : G, orderOf s = p → ¬ InvertedByTwoA s → ∃ a b : G,
    a ∈ Subgroup.centralizer ({s} : Set G) ∧ b ∈ Subgroup.centralizer ({s} : Set G) ∧
      orderOf a = 2 ∧ orderOf b = 2 ∧ a * b = b * a ∧ a ≠ b ∧
      Nat.card ↥(Subgroup.centralizer ({a} : Set G)) = 2 * monsterBabyOrder ∧
      Nat.card ↥(Subgroup.centralizer ({b} : Set G)) = 2 * monsterBabyOrder

@[expose] def TwoAPureKlein (p : ℕ) (G : Type) [Group G] : Prop :=
  ∀ s : G, orderOf s = p → ¬ InvertedByTwoA s → ∃ a b : G,
    a ∈ Subgroup.centralizer ({s} : Set G) ∧ b ∈ Subgroup.centralizer ({s} : Set G) ∧
      orderOf a = 2 ∧ orderOf b = 2 ∧ a * b = b * a ∧ a ≠ b ∧
      Nat.card ↥(Subgroup.centralizer ({a} : Set G)) = 2 * monsterBabyOrder ∧
      Nat.card ↥(Subgroup.centralizer ({b} : Set G)) = 2 * monsterBabyOrder ∧
      Nat.card ↥(Subgroup.centralizer ({a * b} : Set G)) = 2 * monsterBabyOrder

theorem natCard_centralizer_conj' (c a : G) :
    Nat.card ↥(Subgroup.centralizer ({c * a * c⁻¹} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({a} : Set G)) := by
  have := natCard_centralizer_mulEquiv (MulAut.conj c) a
  simpa [MulAut.conj_apply] using this

theorem TwoATwoCommuting.of_mulEquiv {G' : Type} [Group G'] (e : G ≃* G') {p : ℕ}
    (h : TwoATwoCommuting p G') : TwoATwoCommuting p G := by
  intro s hs hn
  obtain ⟨a, b, haC, hbC, ha, hb, hab, hne, hca, hcb⟩ := h (e s)
    (by rw [MulEquiv.orderOf_eq]; exact hs) (fun hi => hn (by
      have := hi.map e.symm
      rwa [MulEquiv.symm_apply_apply] at this))
  have hback : ∀ x : G', x ∈ Subgroup.centralizer ({e s} : Set G') →
      e.symm x ∈ Subgroup.centralizer ({s} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hx
  refine ⟨e.symm a, e.symm b, hback a haC, hback b hbC, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]; exact ha
  · rw [MulEquiv.orderOf_eq]; exact hb
  · apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hab
  · intro h
    exact hne (by simpa using congrArg e h)
  · rw [natCard_centralizer_mulEquiv e.symm a]
    exact hca
  · rw [natCard_centralizer_mulEquiv e.symm b]
    exact hcb

theorem TwoAPureKlein.of_mulEquiv {G' : Type} [Group G'] (e : G ≃* G') {p : ℕ}
    (h : TwoAPureKlein p G') : TwoAPureKlein p G := by
  intro s hs hn
  obtain ⟨a, b, haC, hbC, ha, hb, hab, hne, hca, hcb, hcab⟩ := h (e s)
    (by rw [MulEquiv.orderOf_eq]; exact hs) (fun hi => hn (by
      have := hi.map e.symm
      rwa [MulEquiv.symm_apply_apply] at this))
  have hback : ∀ x : G', x ∈ Subgroup.centralizer ({e s} : Set G') →
      e.symm x ∈ Subgroup.centralizer ({s} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hx
  refine ⟨e.symm a, e.symm b, hback a haC, hback b hbC, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]; exact ha
  · rw [MulEquiv.orderOf_eq]; exact hb
  · apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hab
  · intro h
    exact hne (by simpa using congrArg e h)
  · rw [natCard_centralizer_mulEquiv e.symm a]
    exact hca
  · rw [natCard_centralizer_mulEquiv e.symm b]
    exact hcb
  · rw [← map_mul, natCard_centralizer_mulEquiv e.symm (a * b)]
    exact hcab

theorem uninvertedOPrimeTrivial_of_twoATwoCommuting (hE : MonsterExistenceStatement G) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hB : OPrimeCoreTrivialAt p CFSG.Blueprint.NativeSporadic.B)
    (hCo : OPrimeCoreTrivialAt p CFSG.Blueprint.NativeSporadic.Co1)
    (h : TwoATwoCommuting p G) : UninvertedOPrimeTrivial p G := by
  intro s hs hn
  obtain ⟨a, b, haC, hbC, ha, hb, hab, hne, hca, hcb⟩ := h s hs hn
  exact gLAPPrimeCoreOf_eq_bot_of_two_twoA hE hp hp2 hB hCo hs haC hbC ha hb hab hne hca hcb

theorem uninvertedOPrimeTrivial_of_twoAPureKlein (hE : MonsterExistenceStatement G) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hB : OPrimeCoreTrivialAt p CFSG.Blueprint.NativeSporadic.B)
    (h : TwoAPureKlein p G) : UninvertedOPrimeTrivial p G := by
  intro s hs hn
  obtain ⟨a, b, haC, hbC, ha, hb, hab, hne, hca, hcb, hcab⟩ := h s hs hn
  exact gLAPPrimeCoreOf_eq_bot_of_three_twoA hE hp hp2 hB hs haC hbC ha hb hab hne hca hcb hcab

end Residual

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
