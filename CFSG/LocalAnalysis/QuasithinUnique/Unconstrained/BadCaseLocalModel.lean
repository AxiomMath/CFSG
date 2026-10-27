module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel4

public section

namespace CFSG.QuasithinUnique.A6Facts.Core

set_option maxRecDepth 100000

@[expose] def ccC (ψ ψi τ : List Nat) : List Nat := cmul (cmul (cmul τ ψ) τ) ψi

@[expose] def starCheck (r ψ ψi : List Nat) : Bool :=
  (cmul (cmul ψ zbC) ψi == cmul zbC r) && (cmul (cmul ψ r) ψi == r) && (cmul ψ ψi == cid) &&
    pslLit.contains ψ && pslLit.contains ψi &&
    e4Lit.all (fun τ => ccC ψ ψi τ == cid || ccC ψ ψi τ == r) &&
    e4Lit.all (fun τ => e4Lit.all fun τ' =>
      cmul τ τ' != zbC || ((ccC ψ ψi τ == r) != (ccC ψ ψi τ' == r)))

@[expose] def starTable : List (List Nat × List Nat × List Nat) :=
  [([0, 2, 1, 6, 8, 7, 3, 5, 4, 9], [0, 3, 6, 2, 5, 8, 1, 4, 7, 9], [0, 6, 3, 1, 7, 4, 2, 8, 5, 9]),
   ([3, 2, 1, 0, 5, 4, 9, 7, 8, 6], [0, 4, 5, 3, 1, 2, 9, 8, 7, 6], [0, 4, 5, 3, 1, 2, 9, 8, 7, 6]),
   ([6, 2, 1, 9, 4, 5, 0, 8, 7, 3], [0, 7, 8, 9, 5, 4, 6, 1, 2, 3], [0, 7, 8, 9, 5, 4, 6, 1, 2, 3]),
   ([9, 2, 1, 3, 7, 8, 6, 4, 5, 0], [1, 0, 9, 6, 7, 5, 3, 4, 8, 2], [1, 0, 9, 6, 7, 5, 3, 4, 8, 2])]

theorem star_table_ok : starTable.all (fun x => starCheck x.1 x.2.1 x.2.2) = true := by
  decide +kernel

theorem star_table_cover :
    (dLit.filter isRefl).all (fun r => starTable.any fun x => x.1 == r) = true := by
  decide +kernel

theorem sq_D_check : dLit.all (fun d => cmul d d == cid || cmul d d == zbC) = true := by
  decide +kernel

end CFSG.QuasithinUnique.A6Facts.Core

namespace CFSG.QuasithinUnique.A6Facts

theorem sq_D {d : P10} (hd : d ∈ P0) (hd' : d ∈ A6Models.psl29) : d * d = 1 ∨ d * d = zb := by
  have h := Core.sq_D_check
  rw [List.all_eq_true] at h
  have h1 := h (code d) (code_mem_dLit hd hd')
  simp only [Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 with h1 | h1
  · left
    apply code_injective
    rw [code_mul, code_one]
    exact h1
  · right
    apply code_injective
    rw [code_mul, zb_code]
    exact h1

theorem isRefl_conj {r π : P10} (hr : IsRefl r) (hπ : π ∈ P0) : IsRefl (π * r * π⁻¹) := by
  obtain ⟨hrP, hrpsl, hr1, hrz, hrsq⟩ := hr
  refine ⟨P0.mul_mem (P0.mul_mem hπ hrP) (P0.inv_mem hπ), ?_, ?_, ?_, ?_⟩
  · exact psl29_normal π (P0_le_autA6 hπ) r hrpsl
  · intro h
    apply hr1
    calc r = π⁻¹ * (π * r * π⁻¹) * π := by group
      _ = 1 := by rw [h]; group
  · intro h
    apply hrz
    have hc : zb * π⁻¹ = π⁻¹ * zb := zb_central π⁻¹ (P0.inv_mem hπ)
    calc r = π⁻¹ * (π * r * π⁻¹) * π := by group
      _ = π⁻¹ * zb * π := by rw [h]
      _ = zb := by rw [← hc]; group
  · calc π * r * π⁻¹ * (π * r * π⁻¹) = π * (r * r) * π⁻¹ := by group
      _ = 1 := by rw [hrsq]; group

theorem exists_star {r : P10} (hr : IsRefl r) :
    ∃ ψ : P10, ψ ∈ A6Models.psl29 ∧ ψ * zb * ψ⁻¹ = zb * r ∧ ψ * r * ψ⁻¹ = r ∧
      (∀ τ, InE4 τ → τ * ψ * τ * ψ⁻¹ = 1 ∨ τ * ψ * τ * ψ⁻¹ = r) ∧
      (∀ τ τ', InE4 τ → InE4 τ' → τ * τ' = zb →
        ((τ * ψ * τ * ψ⁻¹ = r) ↔ ¬ (τ' * ψ * τ' * ψ⁻¹ = r))) := by
  have hmem : code r ∈ Core.dLit.filter Core.isRefl := by
    rw [List.mem_filter]
    exact ⟨List.contains_iff_mem.mp (by
      have := isRefl_of hr
      unfold Core.isRefl at this
      simp only [Bool.and_eq_true] at this
      exact this.1.1.1), isRefl_of hr⟩
  have hcov := Core.star_table_cover
  rw [List.all_eq_true] at hcov
  have h1 := hcov (code r) hmem
  rw [List.any_eq_true] at h1
  obtain ⟨⟨r', ψc, ψic⟩, hmemT, hrr⟩ := h1
  simp only [beq_iff_eq] at hrr
  have hok := Core.star_table_ok
  rw [List.all_eq_true] at hok
  have h2 := hok _ hmemT
  simp only [Core.starCheck, Bool.and_eq_true, beq_iff_eq] at h2
  obtain ⟨⟨⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩, hF⟩, hG⟩ := h2
  subst hrr
  obtain ⟨ψ, hψ, rfl⟩ := exists_psl29_of_code (List.contains_iff_mem.mp hD)
  obtain ⟨ψi, hψi, rfl⟩ := exists_psl29_of_code (List.contains_iff_mem.mp hE)
  have hinv : ψi = ψ⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    apply code_injective
    rw [code_mul, code_one]
    exact hC
  subst hinv
  have hcc : ∀ τ : P10, Core.ccC (code ψ) (code ψ⁻¹) (code τ) = code (τ * ψ * τ * ψ⁻¹) := by
    intro τ
    simp only [Core.ccC, code_mul]
  refine ⟨ψ, hψ, ?_, ?_, ?_, ?_⟩
  · apply code_injective
    rw [code_mul, code_mul, code_mul, zb_code]
    exact hA
  · apply code_injective
    rw [code_mul, code_mul]
    exact hB
  · intro τ hτ
    rw [List.all_eq_true] at hF
    have h3 := hF (code τ) ((inE4_iff τ).1 hτ)
    rw [hcc τ] at h3
    simp only [Bool.or_eq_true, beq_iff_eq] at h3
    rcases h3 with h3 | h3
    · left
      apply code_injective
      rw [code_one]
      exact h3
    · right
      apply code_injective
      exact h3
  · intro τ τ' hτ hτ' hττ'
    rw [List.all_eq_true] at hG
    have h3 := hG (code τ) ((inE4_iff τ).1 hτ)
    rw [List.all_eq_true] at h3
    have h4 := h3 (code τ') ((inE4_iff τ').1 hτ')
    have h5 : (Core.cmul (code τ) (code τ') != Core.zbC) = false := by
      rw [← code_mul, hττ', zb_code]
      simp
    have hp : (code (τ * ψ * τ * ψ⁻¹) == code r) = true ↔ τ * ψ * τ * ψ⁻¹ = r := by
      rw [beq_iff_eq]
      exact ⟨fun h => code_injective h, fun h => by rw [h]⟩
    have hq : (code (τ' * ψ * τ' * ψ⁻¹) == code r) = true ↔ τ' * ψ * τ' * ψ⁻¹ = r := by
      rw [beq_iff_eq]
      exact ⟨fun h => code_injective h, fun h => by rw [h]⟩
    rw [h5, hcc τ, hcc τ'] at h4
    simp only [Bool.false_or] at h4
    rw [← hp, ← hq]
    generalize (code (τ * ψ * τ * ψ⁻¹) == code r) = p at h4 ⊢
    generalize (code (τ' * ψ * τ' * ψ⁻¹) == code r) = q at h4 ⊢
    cases p <;> cases q <;> simp_all
end CFSG.QuasithinUnique.A6Facts
