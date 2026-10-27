module

public import Mathlib.GroupTheory.Sylow

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Lang.Triality

open MulAut

variable {C : Type*} [Group C]

theorem mulAut_mul_conj_mul_inv (δ : MulAut C) (u : C) :
    δ * MulAut.conj u * δ⁻¹ = MulAut.conj (δ u) := by
  refine MulEquiv.ext fun x => ?_
  simp [MulAut.conj_apply]

theorem mulAut_mul_conj (δ : MulAut C) (u : C) :
    δ * MulAut.conj u = MulAut.conj (δ u) * δ := by
  refine MulEquiv.ext fun x => ?_
  simp [MulAut.conj_apply]

theorem conj_injective_of_center_eq_bot {G : Type*} [Group G] (h : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun φ : MulAut G => φ x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = (g * x * g⁻¹) * g := by rw [this]
      _ = g * x := by group
  rw [h] at hc
  exact hc

theorem card_fixed_conj (ε β : MulAut C) :
    Nat.card {x : C // (ε * β * ε⁻¹) x = x} = Nat.card {x : C // β x = x} := by
  refine Nat.card_congr ⟨fun x => ⟨ε.symm x, ?_⟩, fun y => ⟨ε y, ?_⟩, ?_, ?_⟩
  · have h : ε (β (ε.symm x)) = x := by simpa using x.2
    exact ε.injective (by rw [h, ε.apply_symm_apply])
  · have h : β y = y := y.2
    simp [h]
  · intro x; ext; simp
  · intro y; ext; simp

section Ext

variable (U : Subgroup C) (δ : MulAut C) (hδ3 : δ ^ 3 = 1) (hδU : ∀ u ∈ U, δ u ∈ U)

include hδU in
theorem pow_apply_mem (i : ℕ) : ∀ u ∈ U, (δ ^ i) u ∈ U := by
  induction i with
  | zero => intro u hu; simpa using hu
  | succ i ih =>
    intro u hu
    rw [pow_succ', MulAut.mul_apply]
    exact hδU _ (ih u hu)

include hδ3 in
theorem pow_inv_eq (i : ℕ) : (δ ^ i)⁻¹ = δ ^ (2 * i) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, hδ3, one_pow]

def innExt : Subgroup (MulAut C) where
  carrier := {x | ∃ u ∈ U, ∃ i : ℕ, x = MulAut.conj u * δ ^ i}
  one_mem' := ⟨1, U.one_mem, 0, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨u, hu, i, rfl⟩ ⟨u', hu', j, rfl⟩
    refine ⟨u * (δ ^ i) u', U.mul_mem hu (pow_apply_mem U δ hδU i u' hu'), i + j, ?_⟩
    rw [map_mul, pow_add, mul_assoc, ← mul_assoc (δ ^ i), mulAut_mul_conj]
    group
  inv_mem' := by
    rintro _ ⟨u, hu, i, rfl⟩
    refine ⟨(δ ^ (2 * i)) u⁻¹, pow_apply_mem U δ hδU _ _ (U.inv_mem hu), 2 * i, ?_⟩
    rw [mul_inv_rev, pow_inv_eq δ hδ3, ← map_inv, mulAut_mul_conj]

include hδ3 in
theorem pow_eq_pow_mod (i : ℕ) : δ ^ i = δ ^ (i % 3) := by
  conv_lhs => rw [← Nat.div_add_mod i 3, pow_add, pow_mul, hδ3, one_pow, one_mul]

theorem innExt_rep {x : MulAut C} (hx : x ∈ innExt U δ hδ3 hδU) :
    ∃ u ∈ U, ∃ i : Fin 3, x = MulAut.conj u * δ ^ (i : ℕ) := by
  obtain ⟨u, hu, i, rfl⟩ := hx
  exact ⟨u, hu, ⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, by
    rw [pow_eq_pow_mod δ hδ3 i]⟩

variable {U δ hδ3 hδU}

theorem not_pow_eq (hδ3 : δ ^ 3 = 1) (hδI : δ ∉ (MulAut.conj : C →* MulAut C).range) (a b : C)
    (i j : Fin 3) (hij : i ≠ j) (h : MulAut.conj a * δ ^ (i : ℕ) = MulAut.conj b * δ ^ (j : ℕ)) :
    False := by
  have h1 : ∀ w : C, δ ≠ MulAut.conj w := fun w hw => hδI ⟨w, hw.symm⟩
  have h2 : ∀ w : C, δ ^ 2 ≠ MulAut.conj w := fun w hw => hδI ⟨w * w, by
    have h4 : δ = δ ^ 2 * δ ^ 2 := by
      rw [← pow_add]
      calc δ = δ ^ 3 * δ := by rw [hδ3, one_mul]
        _ = δ ^ (2 + 2) := by rw [← pow_succ]
    rw [h4, hw, map_mul]⟩
  have hh : δ ^ (i : ℕ) = MulAut.conj (a⁻¹ * b) * δ ^ (j : ℕ) := by
    rw [map_mul, map_inv, mul_assoc]
    exact eq_inv_mul_of_mul_eq h
  generalize a⁻¹ * b = w at hh
  fin_cases i <;> fin_cases j <;> simp at hij <;> simp at hh
  · exact h1 w⁻¹ (by rw [map_inv]; exact eq_inv_of_mul_eq_one_right hh.symm)
  · exact h2 w⁻¹ (by rw [map_inv]; exact eq_inv_of_mul_eq_one_right hh.symm)
  · exact h1 w hh
  · have : (1 : MulAut C) = MulAut.conj w * δ := by
      refine mul_right_cancel (b := δ) ?_
      rw [one_mul, mul_assoc, ← sq]
      exact hh
    exact h1 w⁻¹ (by rw [map_inv]; exact eq_inv_of_mul_eq_one_right this.symm)
  · exact h2 w hh
  · exact h1 w (mul_right_cancel (b := δ) (by rw [← sq]; exact hh))

variable (hδ3 hδU) in
theorem card_innExt [Finite C] (hZ : Function.Injective (MulAut.conj : C →* MulAut C))
    (hδI : δ ∉ (MulAut.conj : C →* MulAut C).range) :
    Nat.card (innExt U δ hδ3 hδU) = 3 * Nat.card U := by
  let f : U × Fin 3 → innExt U δ hδ3 hδU := fun p =>
    ⟨MulAut.conj (p.1 : C) * δ ^ (p.2 : ℕ), p.1, p.1.2, p.2, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨u, i⟩ ⟨u', j⟩ h
      have h' : MulAut.conj (u : C) * δ ^ (i : ℕ) = MulAut.conj (u' : C) * δ ^ (j : ℕ) :=
        congrArg Subtype.val h
      by_cases hij : i = j
      · subst hij
        have := hZ (mul_right_cancel h')
        rw [Subtype.ext this]
      · exact (not_pow_eq hδ3 hδI _ _ i j hij h').elim
    · rintro ⟨x, hx⟩
      obtain ⟨u, hu, i, rfl⟩ := innExt_rep U δ hδ3 hδU hx
      exact ⟨(⟨u, hu⟩, i), rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, Nat.card_fin]
  ring

theorem exists_conj_mem_innExt [Finite C] (P : Sylow 3 C)
    (hZ : Function.Injective (MulAut.conj : C →* MulAut C))
    (hδ3 : δ ^ 3 = 1) (hδU : ∀ u ∈ (P : Subgroup C), δ u ∈ (P : Subgroup C))
    (hδI : δ ∉ (MulAut.conj : C →* MulAut C).range)
    (g : C) (hα3 : (MulAut.conj g * δ) ^ 3 = 1) :
    ∃ (ε : MulAut C) (u : C), u ∈ (P : Subgroup C) ∧
      (ε * (MulAut.conj g * δ) * ε⁻¹ = MulAut.conj u * δ ∨
        ε * (MulAut.conj g * δ)⁻¹ * ε⁻¹ = MulAut.conj u * δ) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set U : Subgroup C := (P : Subgroup C) with hUdef
  set 𝓗 := innExt (⊤ : Subgroup C) δ hδ3 (fun _ _ => trivial) with h𝓗
  set P₀ := innExt U δ hδ3 hδU with hP₀
  have hle : P₀ ≤ 𝓗 := by
    rintro _ ⟨u, hu, i, rfl⟩
    exact ⟨u, trivial, i, rfl⟩
  have hαH : MulAut.conj g * δ ∈ 𝓗 := ⟨g, trivial, 1, by simp⟩
  have hUcard : Nat.card U = 3 ^ (Nat.card C).factorization 3 := P.card_eq_multiplicity
  have hP₀card : Nat.card P₀ = 3 ^ ((Nat.card C).factorization 3 + 1) := by
    rw [hP₀, card_innExt hδ3 hδU hZ hδI, hUcard, pow_succ]; ring
  have hHcard : Nat.card 𝓗 = 3 * Nat.card C := by
    rw [h𝓗, card_innExt (U := ⊤) hδ3 (fun _ _ => trivial) hZ hδI, Subgroup.card_top]
  have hHfac : (Nat.card 𝓗).factorization 3 = (Nat.card C).factorization 3 + 1 := by
    rw [hHcard, Nat.factorization_mul (by norm_num) Nat.card_pos.ne']
    simp [Nat.Prime.factorization_self Nat.prime_three, add_comm]
  have hsubcard : Nat.card (P₀.subgroupOf 𝓗) = Nat.card P₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  let S₀ : Sylow 3 ↥𝓗 := Sylow.ofCard (P₀.subgroupOf 𝓗) (by rw [hsubcard, hP₀card, hHfac])
  have hαne : MulAut.conj g * δ ∉ (MulAut.conj : C →* MulAut C).range := by
    rintro ⟨h, hh⟩
    refine hδI ⟨g⁻¹ * h, ?_⟩
    rw [map_mul, map_inv, hh]
    group
  have hα1 : MulAut.conj g * δ ≠ 1 := fun h => hαne ⟨1, by rw [map_one, h]⟩
  have hαord : orderOf (MulAut.conj g * δ) = 3 := orderOf_eq_prime hα3 hα1
  let a' : ↥𝓗 := ⟨MulAut.conj g * δ, hαH⟩
  have ha'ord : orderOf a' = 3 := by rw [← hαord]; exact Subgroup.orderOf_mk _ _
  have hp : IsPGroup 3 (Subgroup.zpowers a') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ha'ord]; norm_num
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥𝓗 Q S₀
  have hmem : h * a' * h⁻¹ ∈ (S₀ : Subgroup ↥𝓗) := by
    rw [← hh, Sylow.coe_subgroup_smul]
    have := Subgroup.smul_mem_pointwise_smul a' (MulAut.conj h) (Q : Subgroup ↥𝓗)
      (hQ (Subgroup.mem_zpowers a'))
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have hmem' : (h : MulAut C) * (MulAut.conj g * δ) * (h : MulAut C)⁻¹ ∈ P₀ := by
    have : ((h * a' * h⁻¹ : ↥𝓗) : MulAut C) ∈ P₀ := hmem
    simpa using this
  generalize (h : MulAut C) = ε at hmem'
  obtain ⟨u, hu, i, hβ⟩ := hmem'
  have hβne : ε * (MulAut.conj g * δ) * ε⁻¹ ∉ (MulAut.conj : C →* MulAut C).range := by
    rintro ⟨x, hx⟩
    refine hαne ⟨(ε⁻¹ x : C), ?_⟩
    rw [← mulAut_mul_conj_mul_inv ε⁻¹ x, hx]
    group
  have hi : i % 3 ≠ 0 := by
    intro h0
    refine hβne ⟨u, ?_⟩
    rw [hβ, pow_eq_pow_mod δ hδ3 i, h0, pow_zero, mul_one]
  have hi' : i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hi' with h1 | h2
  · refine ⟨ε, u, hu, Or.inl ?_⟩
    rw [hβ, pow_eq_pow_mod δ hδ3 i, h1, pow_one]
  · refine ⟨ε, δ (u⁻¹), hδU _ (U.inv_mem hu), Or.inr ?_⟩
    have hinv : ε * (MulAut.conj g * δ)⁻¹ * ε⁻¹ = (ε * (MulAut.conj g * δ) * ε⁻¹)⁻¹ := by
      group
    rw [hinv, hβ, pow_eq_pow_mod δ hδ3 i, h2, mul_inv_rev, pow_inv_eq δ hδ3 2,
      show 2 * 2 = 3 + 1 by norm_num, pow_add, hδ3, one_mul, pow_one, ← map_inv,
      mulAut_mul_conj]

end Ext

end CFSG.HardMathSupport.Lang.Triality
