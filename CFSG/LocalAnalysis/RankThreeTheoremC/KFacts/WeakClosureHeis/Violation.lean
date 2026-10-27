module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Shape
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open Subgroup
open scoped commutatorElement Pointwise

private theorem elemAbelian_rank_le {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X]
    {Q Q₀ Q₁ : Subgroup X} (h : HeisShape p Q Q₀ Q₁) {E : Subgroup X} (hEQ : E ≤ Q)
    (hE : CFSG.Open.IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ 3 := by
  haveI := Fact.mk hp
  have hΩfin : {q : X | q ∈ Q ∧ q ^ p = 1}.Finite := Set.toFinite _
  have hsub : (E : Set X) ⊆ {q : X | q ∈ Q ∧ q ^ p = 1} := fun x hx => ⟨hEQ hx, hE.2 x hx⟩
  have hcard : (E : Set X).ncard = p ^ k := by
    rw [← hk]; exact (Nat.card_coe_set_eq (E : Set X)).symm
  have hle : p ^ k ≤ p ^ 4 := by
    rw [← hcard]; exact (Set.ncard_le_ncard hsub hΩfin).trans h.ncard_pow_eq_one_le
  have hk4 : k ≤ 4 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  by_contra hk3
  have hk4' : k = 4 := by omega
  subst hk4'
  have hEq : (E : Set X) = {q : X | q ∈ Q ∧ q ^ p = 1} :=
    Set.eq_of_subset_of_ncard_le hsub (h.ncard_pow_eq_one_le.trans hcard.ge) hΩfin
  haveI := hE.1
  apply h.nonab
  have hQ1 : ∀ a ∈ Q₁, a ∈ E := fun a ha => by
    have hmem : a ∈ {q : X | q ∈ Q ∧ q ^ p = 1} := ⟨h.right_le ha, h.exp a ha⟩
    rw [← hEq] at hmem
    exact hmem
  exact IsMulCommutative.of_setLike_mul_comm fun a ha b hb =>
    setLike_mul_comm (hQ1 a ha) (hQ1 b hb)

private theorem commutator_le_heisZ {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X]
    {Q Q₀ Q₁ : Subgroup X} (h : HeisShape p Q Q₀ Q₁) {W : Subgroup X} (hWQ : W ≤ Q) :
    ⁅W, W⁆ ≤ heisZ Q₁ := by
  haveI := Fact.mk hp
  rw [commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact h.commutator_mem (hWQ ha) (hWQ hb)

private theorem card_le_of_exp {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X]
    {Q Q₀ Q₁ : Subgroup X} (h : HeisShape p Q Q₀ Q₁) {W : Subgroup X} (hWQ : W ≤ Q)
    (hW : ∀ w ∈ W, w ^ p = 1) : Nat.card W ≤ p ^ 4 := by
  haveI := Fact.mk hp
  have hsub : (W : Set X) ⊆ {q : X | q ∈ Q ∧ q ^ p = 1} := fun x hx => ⟨hWQ hx, hW x hx⟩
  calc Nat.card W = (W : Set X).ncard := Nat.card_coe_set_eq (W : Set X)
    _ ≤ {q : X | q ∈ Q ∧ q ^ p = 1}.ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ p ^ 4 := h.ncard_pow_eq_one_le

private theorem exists_conj_le {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X]
    (Q : Sylow p X) {U : Subgroup X} (hU : IsPGroup p U) :
    ∃ g : X, U.map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup X) := by
  haveI := Fact.mk hp
  obtain ⟨P, hP⟩ := hU.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P Q
  refine ⟨g, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have h1 : (MulAut.conj g) • u ∈ (MulAut.conj g) • (P : Subgroup X) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (hP hu)
  have h2 : (↑(g • P) : Subgroup X) = (MulAut.conj g) • (P : Subgroup X) :=
    Sylow.coe_subgroup_smul
  rw [hg] at h2
  rw [h2]
  exact h1

theorem heis_violation_false {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X] (Q : Sylow p X)
    {Q₀ Q₁ : Subgroup X} (h : HeisShape p (Q : Subgroup X) Q₀ Q₁) (U : Subgroup X) (hU : IsPGroup p U)
    (hv : 4 ≤ CFSG.Open.pRank p U ∨ ¬ IsCyclic ↥⁅U, U⁆ ∨
      ((∀ u ∈ U, u ^ p = 1) ∧ p ^ 5 ≤ Nat.card U)) : False := by
  haveI := Fact.mk hp
  obtain ⟨g, hQ⟩ := exists_conj_le hp Q hU
  set f : X →* X := (MulAut.conj g).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj g).injective
  rcases hv with h4 | hcyc | ⟨hexp, hcard⟩
  ·
    have hr : CFSG.Open.pRank p U ≤ 3 := by
      refine csSup_le' ?_
      rintro k ⟨E, hEU, hE, hk⟩
      haveI := hE.1
      refine elemAbelian_rank_le hp h (E := E.map f) ((map_mono hEU).trans hQ)
        ⟨inferInstance, ?_⟩ ?_
      · rintro _ ⟨e, he, rfl⟩
        rw [← map_pow, hE.2 e he, map_one]
      · rw [Subgroup.card_map_of_injective hfinj]; exact hk
    omega
  ·
    apply hcyc
    have h1 : ⁅U, U⁆.map f ≤ heisZ Q₁ := by
      rw [Subgroup.map_commutator]
      exact commutator_le_heisZ hp h hQ
    have h2 : Nat.card ↥⁅U, U⁆ ∣ p := by
      rw [← Subgroup.card_map_of_injective hfinj]
      exact (Subgroup.card_dvd_of_le h1).trans (h.card_heisZ ▸ dvd_refl _)
    exact isCyclic_of_card_dvd_prime h2
  ·
    have hU'exp : ∀ w ∈ U.map f, w ^ p = 1 := by
      rintro _ ⟨u, hu, rfl⟩
      rw [← map_pow, hexp u hu, map_one]
    have h1 := card_le_of_exp hp h hQ hU'exp
    rw [Subgroup.card_map_of_injective hfinj] at h1
    have h2 : p ^ 4 < p ^ 5 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
