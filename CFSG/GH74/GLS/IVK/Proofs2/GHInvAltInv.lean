module

public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltBasic
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.GH74.GLS.IVK.GHInv

open Equiv Equiv.Perm

theorem perfect_hom_perm_eq_one {G X : Type*} [Group G] [Group.IsPerfect G] [Finite X]
    (hX : Nat.card X ≤ 4) (φ : G →* Equiv.Perm X) (g : G) : φ g = 1 := by
  have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have : Group.IsSolvable (Equiv.Perm X) := Equiv.Perm.isSolvable hX
  by_contra hne
  have : Nontrivial φ.range := ⟨⟨⟨φ g, g, rfl⟩, 1, fun h => hne (congrArg Subtype.val h)⟩⟩
  exact Group.IsPerfect.not_isSolvable φ.range inferInstance

section Inv

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem involution_cycle_data {σ : Perm Ω} (h : σ * σ = 1) :
    σ.support.card = 2 * σ.cycleType.card ∧ sign σ = (-1) ^ σ.cycleType.card := by
  have h2 : σ ^ 2 = 1 := by rw [sq]; exact h
  have hct : σ.cycleType = Multiset.replicate σ.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one h2
  have hsum : σ.support.card = 2 * σ.cycleType.card := by
    rw [← Equiv.Perm.sum_cycleType]
    conv_lhs => rw [hct]
    simp [mul_comm]
  refine ⟨hsum, ?_⟩
  rw [Equiv.Perm.sign_of_cycleType, Equiv.Perm.sum_cycleType, hsum, show 2 * σ.cycleType.card +
    σ.cycleType.card = σ.cycleType.card * 2 + σ.cycleType.card by ring, pow_add, pow_mul',
    neg_one_sq, one_pow, one_mul]

theorem exists_cycleType_card_le_four (hΩ : Fintype.card Ω ≤ 11) {a b : Perm Ω}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    a.cycleType.card ≤ 4 ∨ b.cycleType.card ≤ 4 ∨ (a * b).cycleType.card ≤ 4 := by
  have hab2 : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha, hb, mul_one]
  obtain ⟨ha1, ha2⟩ := involution_cycle_data ha
  obtain ⟨hb1, hb2⟩ := involution_cycle_data hb
  obtain ⟨hc1, hc2⟩ := involution_cycle_data hab2
  have hle : ∀ σ : Perm Ω, σ.support.card ≤ 11 := fun σ =>
    (Finset.card_le_univ _).trans hΩ
  have h1 := hle a
  have h2 := hle b
  have h3 := hle (a * b)
  by_contra hcon
  push Not at hcon
  obtain ⟨c1, c2, c3⟩ := hcon
  have e1 : a.cycleType.card = 5 := by omega
  have e2 : b.cycleType.card = 5 := by omega
  have e3 : (a * b).cycleType.card = 5 := by omega
  rw [e1] at ha2
  rw [e2] at hb2
  rw [e3] at hc2
  have := Equiv.Perm.sign_mul a b
  rw [ha2, hb2, hc2] at this
  revert this
  decide

theorem perfect_fixes_support {σ : Perm Ω} (hσ : σ * σ = 1) (hc : σ.cycleType.card ≤ 4)
    {P : Subgroup (Perm Ω)} (hP : Group.IsPerfect P) (hPc : ∀ x ∈ P, x * σ = σ * x) :
    ∀ x ∈ P, ∀ a, σ a ≠ a → x a = a := by
  have hσ2' : σ ^ 2 = 1 := by rw [sq]; exact hσ
  have hle : P ≤ Subgroup.centralizer {σ} := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hPc x hx)
  have hct : σ.cycleType = Multiset.replicate σ.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one hσ2'
  have hfix : ∀ x ∈ P, ∀ c ∈ σ.cycleFactorsFinset, Commute x c := by
    intro x hx c hc'
    let Φ : P →* Equiv.Perm σ.cycleFactorsFinset :=
      (Equiv.Perm.OnCycleFactors.toPermHom σ).comp (Subgroup.inclusion hle)
    have hΦ : Φ ⟨x, hx⟩ = 1 := perfect_hom_perm_eq_one (by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      have : σ.cycleFactorsFinset.card = σ.cycleType.card := by
        rw [Equiv.Perm.cycleType_def, Multiset.card_map]
        rfl
      omega) Φ ⟨x, hx⟩
    have hker : (⟨x, hle hx⟩ : Subgroup.centralizer {σ}) ∈
        (Equiv.Perm.OnCycleFactors.toPermHom σ).ker := hΦ
    exact (Equiv.Perm.OnCycleFactors.mem_ker_toPermHom_iff σ _).1 hker c hc'
  intro x hx a ha
  have hc' : σ.cycleOf a ∈ σ.cycleFactorsFinset :=
    Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.2 (Equiv.Perm.mem_support.2 ha)
  have hmem : a ∈ (σ.cycleOf a).support := by
    rw [Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self]
    exact ha
  have hV : ∀ x ∈ P, ∀ u, u ∈ (σ.cycleOf a).support ↔ x u ∈ (σ.cycleOf a).support := by
    intro x hx u
    have h := congrArg (fun f : Equiv.Perm Ω => f u) (hfix x hx _ hc').eq
    simp only [Equiv.Perm.mul_apply] at h
    rw [Equiv.Perm.mem_support, Equiv.Perm.mem_support, ← h, Ne, Ne, Equiv.apply_eq_iff_eq]
  have hcard2 : (σ.cycleOf a).support.card = 2 := by
    have hmem' : (σ.cycleOf a).support.card ∈ σ.cycleType := by
      rw [Equiv.Perm.cycleType_def]
      exact Multiset.mem_map_of_mem _ hc'
    rw [hct] at hmem'
    exact Multiset.eq_of_mem_replicate hmem'
  let ρ : P →* Equiv.Perm {u // u ∈ (σ.cycleOf a).support} :=
    MonoidHom.mk' (fun x => (x : Equiv.Perm Ω).subtypePerm fun u => (hV x x.2 u).symm)
      (fun x y => Equiv.ext fun u => Subtype.ext rfl)
  have hρ : ρ ⟨x, hx⟩ = 1 := perfect_hom_perm_eq_one (by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, hcard2]
      norm_num) ρ ⟨x, hx⟩
  exact congrArg (fun f : Equiv.Perm {u // u ∈ (σ.cycleOf a).support} =>
    (f ⟨a, hmem⟩).1) hρ

omit [Fintype Ω] in
theorem eq_bot_of_perfect_le_symOn {F : Finset Ω} (hF : F.card ≤ 4) {K : Subgroup (Perm Ω)}
    (hK : Group.IsPerfect K) (hKF : K ≤ symOn F) : K = ⊥ := by
  let φ : K →* Perm {x // x ∈ F} :=
    MonoidHom.mk' (fun k => (k : Perm Ω).subtypePerm (symOn_mem_iff (hKF k.2)))
      (fun x y => Equiv.ext fun u => Subtype.ext rfl)
  rw [eq_bot_iff]
  intro k hk
  rw [Subgroup.mem_bot]
  have h1 : φ ⟨k, hk⟩ = 1 := perfect_hom_perm_eq_one (by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]; exact hF) φ ⟨k, hk⟩
  ext x
  by_cases hx : x ∈ F
  · have := congrArg (fun f : Perm {x // x ∈ F} => (f ⟨x, hx⟩ : Ω)) h1
    simpa [φ] using this
  · exact hKF hk x hx

end Inv

end CFSG.GH74.GLS.IVK.GHInv
