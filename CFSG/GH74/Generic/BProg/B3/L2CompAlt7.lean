module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.BProg.B3.L2CompAlt7

open Equiv Equiv.Perm Subgroup

abbrev P7 := Perm (Fin 7)

theorem eq_one_of_comm_alt (τ : P7) (h : ∀ g : alternatingGroup (Fin 7), τ * (g : P7) = (g : P7) * τ) :
    τ = 1 := by
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, τ i ≠ i := by
    by_contra hall
    push Not at hall
    exact hne (Equiv.ext hall)
  have hex : ∀ i j : Fin 7, i ≠ j → ∃ a b : Fin 7, a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j ∧ a ≠ b := by
    decide
  obtain ⟨a, b, hai, haj, hbi, hbj, hab⟩ := hex i (τ i) (Ne.symm hi)
  let c : P7 := swap i a * swap a b
  have hc : c ∈ alternatingGroup (Fin 7) := by
    rw [mem_alternatingGroup]
    simp [c, Ne.symm hai, hab]
  have hcomm := h ⟨c, hc⟩
  have hconj : τ * c * τ⁻¹ = c := by
    rw [hcomm]
    simp
  have hci : c i = a := by
    simp [c, swap_apply_of_ne_of_ne (Ne.symm hai) (Ne.symm hbi)]
  have hsupp : i ∈ c.support := by
    rw [mem_support, hci]
    exact hai
  have hmem : τ i ∈ (τ * c * τ⁻¹).support := by
    rw [support_conj]
    exact Finset.mem_map_of_mem _ hsupp
  rw [hconj] at hmem
  have hsub : c.support ≤ ({i, a} : Finset (Fin 7)) ⊔ {a, b} := by
    refine (support_mul_le _ _).trans ?_
    refine sup_le_sup ?_ ?_
    · rw [support_swap (Ne.symm hai)]
    · rw [support_swap hab]
  have := hsub hmem
  rw [Finset.sup_eq_union, Finset.mem_union] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with (h1 | h1) | (h1 | h1)
  · exact hi h1
  · exact haj h1.symm
  · exact haj h1.symm
  · exact hbj h1.symm

@[expose] def s1 : P7 := swap 0 1
@[expose] def s2 : P7 := swap 0 1 * swap 2 3
@[expose] def s3 : P7 := swap 0 1 * swap 2 3 * swap 4 5
@[expose] def a1 : P7 := swap 0 1 * c[2, 3, 4, 5]
@[expose] def b1 : P7 := swap 0 1 * swap 2 4
@[expose] def a2 : P7 := c[0, 2, 1, 3] * swap 4 5
@[expose] def b2 : P7 := swap 0 1 * swap 4 5

theorem ct_swap {i j : Fin 7} (h : i ≠ j) : (swap i j).cycleType = {2} := by
  rw [(isCycle_swap h).cycleType, card_support_swap h]

theorem ct1 : s1.cycleType = {2} := ct_swap (by decide)

theorem ct2 : s2.cycleType = {2, 2} := by
  have hd : Equiv.Perm.Disjoint (swap (0 : Fin 7) 1) (swap 2 3) := by
    intro x
    fin_cases x <;> simp [swap_apply_def]
  rw [s2, hd.cycleType_mul, ct_swap (by decide), ct_swap (by decide)]
  rfl

theorem ct3 : s3.cycleType = {2, 2, 2} := by
  have hd : Equiv.Perm.Disjoint (swap (0 : Fin 7) 1 * swap 2 3) (swap 4 5) := by
    intro x
    fin_cases x <;> simp [swap_apply_def]
  rw [s3, hd.cycleType_mul]
  have := ct2
  rw [s2] at this
  rw [this, ct_swap (by decide)]
  rfl

theorem cycleType_of_invol (σ : P7) (h2 : σ * σ = 1) (h1 : σ ≠ 1) :
    σ.cycleType = {2} ∨ σ.cycleType = {2, 2} ∨ σ.cycleType = {2, 2, 2} := by
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact h2) h1
  have hall : ∀ n ∈ σ.cycleType, n = 2 := by
    intro n hn
    have h2le := two_le_of_mem_cycleType hn
    have hdvd : n ∣ 2 := hord ▸ dvd_of_mem_cycleType hn
    exact (Nat.dvd_prime Nat.prime_two).1 hdvd |>.resolve_left (by omega)
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate_card.2 hall
  have hsum : σ.cycleType.sum = σ.support.card := sum_cycleType σ
  have hsupp : σ.support.card ≤ 7 := by
    have := Finset.card_le_univ σ.support
    simpa using this
  set k := Multiset.card σ.cycleType with hk
  have hsum' : σ.cycleType.sum = 2 * k := by
    rw [hrep]
    simp [mul_comm]
  have hk1 : 1 ≤ k := by
    by_contra h0
    have : k = 0 := by omega
    have hz : σ.cycleType = 0 := Multiset.card_eq_zero.1 this
    exact h1 (cycleType_eq_zero.1 hz)
  have hk3 : k ≤ 3 := by omega
  interval_cases k
  · left; simpa using hrep
  · right; left; simpa using hrep
  · right; right; simpa using hrep

theorem exists_D8_of_invol (σ : P7) (h2 : σ * σ = 1) (h1 : σ ≠ 1) :
    ∃ a b : P7, sign a = 1 ∧ sign b = 1 ∧ σ * a = a * σ ∧ σ * b = b * σ ∧ a ^ 4 = 1 ∧
      a ^ 2 ≠ 1 ∧ b * b = 1 ∧ b * a * b⁻¹ = a⁻¹ := by
  have key : ∀ (s a₀ b₀ : P7), σ.cycleType = s.cycleType → sign a₀ = 1 → sign b₀ = 1 →
      s * a₀ = a₀ * s → s * b₀ = b₀ * s → a₀ ^ 4 = 1 → a₀ ^ 2 ≠ 1 → b₀ * b₀ = 1 →
      b₀ * a₀ * b₀⁻¹ = a₀⁻¹ →
      ∃ a b : P7, sign a = 1 ∧ sign b = 1 ∧ σ * a = a * σ ∧ σ * b = b * σ ∧ a ^ 4 = 1 ∧
        a ^ 2 ≠ 1 ∧ b * b = 1 ∧ b * a * b⁻¹ = a⁻¹ := by
    intro s a₀ b₀ hct hsa hsb hsa' hsb' ha4 ha2 hb2 hba
    obtain ⟨ρ, hρ⟩ := isConj_iff.1 ((isConj_iff_cycleType_eq).2 hct)
    have hσ : σ = ρ⁻¹ * s * ρ := by rw [← hρ]; group
    refine ⟨ρ⁻¹ * a₀ * ρ, ρ⁻¹ * b₀ * ρ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hsa]
    · simp [hsb]
    · rw [hσ]
      calc ρ⁻¹ * s * ρ * (ρ⁻¹ * a₀ * ρ) = ρ⁻¹ * (s * a₀) * ρ := by group
        _ = ρ⁻¹ * (a₀ * s) * ρ := by rw [hsa']
        _ = _ := by group
    · rw [hσ]
      calc ρ⁻¹ * s * ρ * (ρ⁻¹ * b₀ * ρ) = ρ⁻¹ * (s * b₀) * ρ := by group
        _ = ρ⁻¹ * (b₀ * s) * ρ := by rw [hsb']
        _ = _ := by group
    · have hc : ∀ i : ℕ, (ρ⁻¹ * a₀ * ρ) ^ i = ρ⁻¹ * a₀ ^ i * ρ := fun i => by
        have := conj_pow (a := ρ⁻¹) (b := a₀) (i := i)
        simpa using this
      calc (ρ⁻¹ * a₀ * ρ) ^ 4 = ρ⁻¹ * a₀ ^ 4 * ρ := hc 4
        _ = 1 := by rw [ha4]; group
    · have hc : ∀ i : ℕ, (ρ⁻¹ * a₀ * ρ) ^ i = ρ⁻¹ * a₀ ^ i * ρ := fun i => by
        have := conj_pow (a := ρ⁻¹) (b := a₀) (i := i)
        simpa using this
      intro h
      rw [hc 2] at h
      apply ha2
      calc a₀ ^ 2 = ρ * (ρ⁻¹ * a₀ ^ 2 * ρ) * ρ⁻¹ := by group
        _ = 1 := by rw [h]; group
    · calc ρ⁻¹ * b₀ * ρ * (ρ⁻¹ * b₀ * ρ) = ρ⁻¹ * (b₀ * b₀) * ρ := by group
        _ = 1 := by rw [hb2]; group
    · calc ρ⁻¹ * b₀ * ρ * (ρ⁻¹ * a₀ * ρ) * (ρ⁻¹ * b₀ * ρ)⁻¹ = ρ⁻¹ * (b₀ * a₀ * b₀⁻¹) * ρ := by group
        _ = (ρ⁻¹ * a₀ * ρ)⁻¹ := by rw [hba]; group
  rcases cycleType_of_invol σ h2 h1 with h | h | h
  · exact key s1 a1 b1 (h.trans ct1.symm) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact key s2 a2 b2 (h.trans ct2.symm) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  · exact key s3 a2 b2 (h.trans ct3.symm) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)

end CFSG.GH74.Generic.BProg.B3.L2CompAlt7
