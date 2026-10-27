module

public import CFSG.GroupTheory.GL52.InvolutionsConj

public noncomputable section

namespace CFSG.GroupTheory.GL52

open Matrix Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ord3T2M : M5 :=
  !![0, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def ord3T4M : M5 :=
  !![0, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1]

theorem ord3_T_facts : ord3T2M * ord3T2M ^ 2 = 1 ∧ ord3T4M * ord3T4M ^ 2 = 1 ∧
    ord3T2M ^ 3 = 1 ∧ ord3T4M ^ 3 = 1 ∧ ord3T2M ≠ 1 ∧ ord3T4M ≠ 1 := by
  decide +kernel

@[expose] def ord3T2 : G52 :=
  mk5 ord3T2M (ord3T2M ^ 2) ord3_T_facts.1

@[expose] def ord3T4 : G52 :=
  mk5 ord3T4M (ord3T4M ^ 2) ord3_T_facts.2.1

theorem orderOf_ord3T2 : orderOf ord3T2 = 3 := by
  refine orderOf_eq_prime (Units.ext ?_) fun h => ord3_T_facts.2.2.2.2.1 ?_
  · rw [Units.val_pow_eq_pow_val, ord3T2, coe_mk5, Units.val_one]
    exact ord3_T_facts.2.2.1
  · have := congrArg (fun g : G52 => (g : M5)) h
    simpa [ord3T2] using this

theorem orderOf_ord3T4 : orderOf ord3T4 = 3 := by
  refine orderOf_eq_prime (Units.ext ?_) fun h => ord3_T_facts.2.2.2.2.2 ?_
  · rw [Units.val_pow_eq_pow_val, ord3T4, coe_mk5, Units.val_one]
    exact ord3_T_facts.2.2.2.1
  · have := congrArg (fun g : G52 => (g : M5)) h
    simpa [ord3T4] using this

theorem ord3_eq_of_add_eq_zero {a b : V5} (h : a + b = 0) : a = b := by
  calc a = a + (b + b) := by rw [inv_add_self_V5, add_zero]
    _ = (a + b) + b := by abel
    _ = b := by rw [h, zero_add]

section Tau

variable {τ : G52} (hτ : orderOf τ = 3)
include hτ

theorem ord3_cube : (τ : M5) * ((τ : M5) * (τ : M5)) = 1 := by
  have h : τ ^ 3 = 1 := by
    rw [← hτ]
    exact pow_orderOf_eq_one τ
  rw [← Units.val_mul, ← Units.val_mul, ← pow_three, h, Units.val_one]

theorem ord3_ne_one : τ ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at hτ
  norm_num at hτ

theorem ord3_N_mul_P :
    ((τ : M5) - 1) * ((τ : M5) * (τ : M5) + (τ : M5) + 1) = 0 := by
  have h3 := ord3_cube hτ
  rw [inv_sub_eq_add_M5]
  calc ((τ : M5) + 1) * ((τ : M5) * (τ : M5) + (τ : M5) + 1) =
      (τ : M5) * ((τ : M5) * (τ : M5)) + ((τ : M5) * (τ : M5) + (τ : M5) * (τ : M5)) +
        ((τ : M5) + (τ : M5)) + 1 := by noncomm_ring
    _ = 0 := by rw [h3, inv_add_self_M5, inv_add_self_M5, add_zero, add_zero, inv_add_self_M5]

theorem ord3_sq_on_U {u : V5} (hu : u ∈ LinearMap.range (toLin' ((τ : M5) - 1))) :
    (τ : M5) *ᵥ ((τ : M5) *ᵥ u) = (τ : M5) *ᵥ u + u := by
  obtain ⟨v, rfl⟩ := hu
  rw [toLin'_apply]
  have hPN : ((τ : M5) * (τ : M5) + (τ : M5) + 1) * ((τ : M5) - 1) = 0 := by
    have hc : Commute ((τ : M5) * (τ : M5) + (τ : M5) + 1) ((τ : M5) - 1) := by
      apply Commute.sub_right _ (Commute.one_right _)
      exact ((Commute.mul_left (Commute.refl _) (Commute.refl _)).add_left
        (Commute.refl _)).add_left (Commute.one_left _)
    rw [hc.eq, ord3_N_mul_P hτ]
  have e : ((τ : M5) * (τ : M5) + (τ : M5) + 1) *ᵥ (((τ : M5) - 1) *ᵥ v) = 0 := by
    rw [mulVec_mulVec, hPN, zero_mulVec]
  rw [add_mulVec, add_mulVec, one_mulVec, ← mulVec_mulVec] at e
  have e' := ord3_eq_of_add_eq_zero (a := (τ : M5) *ᵥ ((τ : M5) *ᵥ (((τ : M5) - 1) *ᵥ v)))
    (b := (τ : M5) *ᵥ (((τ : M5) - 1) *ᵥ v) + ((τ : M5) - 1) *ᵥ v) (by rw [← add_assoc]; exact e)
  exact e'

theorem ord3_U_inf_C {u : V5} (hu : u ∈ LinearMap.range (toLin' ((τ : M5) - 1)))
    (hc : ((τ : M5) - 1) *ᵥ u = 0) : u = 0 := by
  have hfix : (τ : M5) *ᵥ u = u := by
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at hc
    exact hc
  have h := ord3_sq_on_U hτ hu
  rw [hfix, hfix, inv_add_self_V5] at h
  exact h

omit hτ in
theorem ord3_U_invariant {u : V5} (hu : u ∈ LinearMap.range (toLin' ((τ : M5) - 1))) :
    (τ : M5) *ᵥ u ∈ LinearMap.range (toLin' ((τ : M5) - 1)) := by
  obtain ⟨v, rfl⟩ := hu
  refine ⟨(τ : M5) *ᵥ v, ?_⟩
  rw [toLin'_apply, toLin'_apply, mulVec_mulVec, mulVec_mulVec, sub_mul, mul_sub, one_mul,
    mul_one]

theorem ord3_pair_indep {u : V5} (hu : u ∈ LinearMap.range (toLin' ((τ : M5) - 1)))
    (hu0 : u ≠ 0) : LinearIndependent (ZMod 2) ![u, (τ : M5) *ᵥ u] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hcase : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hcase t with rfl | rfl
  · rw [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.1 hst).resolve_right hu0, rfl⟩
  · exfalso
    rw [one_smul] at hst
    have hτu : (τ : M5) *ᵥ u = s • u := (ord3_eq_of_add_eq_zero hst).symm
    rcases hcase s with rfl | rfl
    · rw [zero_smul] at hτu
      exact hu0 (eq_zero_of_mulVec_eq_zero τ hτu)
    · rw [one_smul] at hτu
      exact hu0 (ord3_U_inf_C hτ hu (by rw [sub_mulVec, one_mulVec, hτu, sub_self]))

theorem ord3_snoc_pair {n : ℕ} {v : Fin n → V5} (hv : LinearIndependent (ZMod 2) v)
    (hS : ∀ s ∈ Submodule.span (ZMod 2) (Set.range v),
      (τ : M5) *ᵥ s ∈ Submodule.span (ZMod 2) (Set.range v))
    {u : V5} (hu : u ∈ LinearMap.range (toLin' ((τ : M5) - 1)))
    (huS : u ∉ Submodule.span (ZMod 2) (Set.range v)) :
    LinearIndependent (ZMod 2)
      (Fin.snoc (Fin.snoc v u) ((τ : M5) *ᵥ u) : Fin (n + 2) → V5) := by
  refine linearIndependent_finSnoc.2 ⟨linearIndependent_finSnoc.2 ⟨hv, huS⟩, ?_⟩
  rw [Fin.range_snoc, Submodule.mem_span_insert]
  rintro ⟨a, z, hz, hτu⟩
  have h2 := ord3_sq_on_U hτ hu
  have hcase : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hcase a with rfl | rfl
  ·
    rw [zero_smul, zero_add] at hτu
    apply huS
    have hz' := hS z hz
    rw [← hτu] at hz hz'
    have e : u = (τ : M5) *ᵥ ((τ : M5) *ᵥ u) + (τ : M5) *ᵥ u := by
      rw [h2, add_comm, ← add_assoc, inv_add_self_V5, zero_add]
    rw [e]
    exact add_mem hz' hz
  ·
    rw [one_smul] at hτu
    apply huS
    have hz' : (τ : M5) *ᵥ ((τ : M5) *ᵥ u + u) ∈ Submodule.span (ZMod 2) (Set.range v) := by
      have : (τ : M5) *ᵥ u + u = z := by
        rw [hτu, add_comm u z, add_assoc, inv_add_self_V5, add_zero]
      rw [this]
      exact hS z hz
    rw [mulVec_add, h2] at hz'
    have e : (τ : M5) *ᵥ u + u + (τ : M5) *ᵥ u = u := by
      rw [add_comm ((τ : M5) *ᵥ u) u, add_assoc, inv_add_self_V5, add_zero]
    rwa [e] at hz'

theorem ord3_snoc_pair_invariant {n : ℕ} {v : Fin n → V5}
    (hS : ∀ s ∈ Submodule.span (ZMod 2) (Set.range v),
      (τ : M5) *ᵥ s ∈ Submodule.span (ZMod 2) (Set.range v))
    {u : V5} (hu : u ∈ LinearMap.range (toLin' ((τ : M5) - 1))) :
    ∀ s ∈ Submodule.span (ZMod 2)
        (Set.range (Fin.snoc (Fin.snoc v u) ((τ : M5) *ᵥ u) : Fin (n + 2) → V5)),
      (τ : M5) *ᵥ s ∈ Submodule.span (ZMod 2)
        (Set.range (Fin.snoc (Fin.snoc v u) ((τ : M5) *ᵥ u) : Fin (n + 2) → V5)) := by
  set W := Submodule.span (ZMod 2)
    (Set.range (Fin.snoc (Fin.snoc v u) ((τ : M5) *ᵥ u) : Fin (n + 2) → V5)) with hW
  have hvW : Submodule.span (ZMod 2) (Set.range v) ≤ W := by
    rw [hW, Fin.range_snoc, Fin.range_snoc]
    exact Submodule.span_mono (Set.subset_insert _ _ |>.trans (Set.subset_insert _ _))
  have huW : u ∈ W := by
    rw [hW, Fin.range_snoc, Fin.range_snoc]
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hτuW : (τ : M5) *ᵥ u ∈ W := by
    rw [hW, Fin.range_snoc]
    exact Submodule.subset_span (Set.mem_insert _ _)
  let τL := toLin' (τ : M5)
  have hgen : Set.range (Fin.snoc (Fin.snoc v u) ((τ : M5) *ᵥ u) : Fin (n + 2) → V5) ⊆
      W.comap τL := by
    rw [Fin.range_snoc, Fin.range_snoc]
    rintro x hx
    rw [SetLike.mem_coe, Submodule.mem_comap, toLin'_apply]
    rcases hx with rfl | rfl | ⟨i, rfl⟩
    · rw [ord3_sq_on_U hτ hu]
      exact add_mem hτuW huW
    · exact hτuW
    · exact hvW (hS _ (Submodule.subset_span ⟨i, rfl⟩))
  intro s hs
  have := (Submodule.span_le.2 hgen) hs
  rwa [Submodule.mem_comap, toLin'_apply] at this

omit hτ in
theorem ord3_mem_U (u : V5) (hu : u ∈ LinearMap.range (toLin' ((τ : M5) - 1))) :
    ∀ a b : ZMod 2, a • u + b • ((τ : M5) *ᵥ u) ∈ LinearMap.range (toLin' ((τ : M5) - 1)) :=
  fun a b => add_mem (Submodule.smul_mem _ a hu) (Submodule.smul_mem _ b (ord3_U_invariant hu))

theorem ord3_conj_two {u : V5} (hu : u ∈ LinearMap.range (toLin' ((τ : M5) - 1))) (hu0 : u ≠ 0)
    (hC : finrank (ZMod 2) (LinearMap.ker (toLin' ((τ : M5) - 1))) = 3) : IsConj ord3T2 τ := by
  have hl2 := ord3_pair_indep hτ hu hu0
  let bs := Module.finBasisOfFinrankEq (ZMod 2) (LinearMap.ker (toLin' ((τ : M5) - 1))) hC
  set c : Fin 3 → V5 := fun i => (bs i : V5) with hc
  have hcl : LinearIndependent (ZMod 2) c :=
    bs.linearIndependent.map' (LinearMap.ker (toLin' ((τ : M5) - 1))).subtype
      (Submodule.ker_subtype _)
  have hcK : ∀ i, ((τ : M5) - 1) *ᵥ c i = 0 := fun i => by
    have := (bs i).2
    rwa [LinearMap.mem_ker, toLin'_apply] at this
  have hcfix : ∀ i, (τ : M5) *ᵥ c i = c i := fun i => by
    have := hcK i
    rwa [sub_mulVec, one_mulVec, sub_eq_zero] at this
  have hb : LinearIndependent (ZMod 2) ![u, (τ : M5) *ᵥ u, c 0, c 1, c 2] := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    replace ha : a 0 • u + a 1 • ((τ : M5) *ᵥ u) + a 2 • c 0 + a 3 • c 1 + a 4 • c 2 = 0 := by
      simpa [Fin.sum_univ_five] using ha
    have hN : ((τ : M5) - 1) *ᵥ (a 0 • u + a 1 • ((τ : M5) *ᵥ u)) = 0 := by
      have := congrArg (fun v => ((τ : M5) - 1) *ᵥ v) ha
      simp only [mulVec_add, mulVec_smul, hcK, smul_zero, add_zero, mulVec_zero] at this
      rw [mulVec_add, mulVec_smul, mulVec_smul]
      exact this
    have h01 := ord3_U_inf_C hτ (ord3_mem_U u hu (a 0) (a 1)) hN
    obtain ⟨h0, h1⟩ := LinearIndependent.pair_iff.1 hl2 _ _ h01
    rw [h0, h1, zero_smul, zero_smul, zero_add, zero_add] at ha
    have h234 := Fintype.linearIndependent_iff.1 hcl ![a 2, a 3, a 4] (by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two]
      exact ha)
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h234 0
    · exact h234 1
    · exact h234 2
  refine isConj_of_basis _ hb fun j => ?_
  have h2 := ord3_sq_on_U hτ hu
  fin_cases j <;> simp [ord3T2, ord3T2M, Fin.sum_univ_five, h2, hcfix, add_comm]

theorem ord3_conj_four {u₁ u₂ : V5} (hu₁ : u₁ ∈ LinearMap.range (toLin' ((τ : M5) - 1)))
    (hu₂ : u₂ ∈ LinearMap.range (toLin' ((τ : M5) - 1)))
    (hl4 : LinearIndependent (ZMod 2) ![u₁, (τ : M5) *ᵥ u₁, u₂, (τ : M5) *ᵥ u₂])
    (hC : finrank (ZMod 2) (LinearMap.ker (toLin' ((τ : M5) - 1))) = 1) : IsConj ord3T4 τ := by
  let bs := Module.finBasisOfFinrankEq (ZMod 2) (LinearMap.ker (toLin' ((τ : M5) - 1))) hC
  set c : V5 := (bs 0 : V5) with hc
  have hc0 : c ≠ 0 := by
    intro h
    apply bs.ne_zero 0
    exact Subtype.ext h
  have hcK : ((τ : M5) - 1) *ᵥ c = 0 := by
    have := (bs 0).2
    rwa [LinearMap.mem_ker, toLin'_apply] at this
  have hcfix : (τ : M5) *ᵥ c = c := by
    have := hcK
    rwa [sub_mulVec, one_mulVec, sub_eq_zero] at this
  have hb : LinearIndependent (ZMod 2) ![u₁, (τ : M5) *ᵥ u₁, u₂, (τ : M5) *ᵥ u₂, c] := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    replace ha : a 0 • u₁ + a 1 • ((τ : M5) *ᵥ u₁) + a 2 • u₂ + a 3 • ((τ : M5) *ᵥ u₂) +
        a 4 • c = 0 := by
      simpa [Fin.sum_univ_five] using ha
    set w := a 0 • u₁ + a 1 • ((τ : M5) *ᵥ u₁) + a 2 • u₂ + a 3 • ((τ : M5) *ᵥ u₂) with hw
    have hwU : w ∈ LinearMap.range (toLin' ((τ : M5) - 1)) := by
      rw [hw, add_assoc]
      exact add_mem (ord3_mem_U u₁ hu₁ _ _) (ord3_mem_U u₂ hu₂ _ _)
    have hN : ((τ : M5) - 1) *ᵥ w = 0 := by
      have := congrArg (fun v => ((τ : M5) - 1) *ᵥ v) ha
      simp only [mulVec_add, mulVec_smul, hcK, smul_zero, add_zero, mulVec_zero] at this
      exact this
    have hw0 := ord3_U_inf_C hτ hwU hN
    have hw0' := hw0
    rw [hw] at hw0'
    have h0123 := Fintype.linearIndependent_iff.1 hl4 ![a 0, a 1, a 2, a 3] (by
      simpa [Fin.sum_univ_four] using hw0')
    have h4 : a 4 = 0 := by
      rw [hw0, zero_add] at ha
      exact (smul_eq_zero.1 ha).resolve_right hc0
    intro i
    fin_cases i
    · exact h0123 0
    · exact h0123 1
    · exact h0123 2
    · exact h0123 3
    · exact h4
  refine isConj_of_basis _ hb fun j => ?_
  have h1 := ord3_sq_on_U hτ hu₁
  have h2 := ord3_sq_on_U hτ hu₂
  fin_cases j <;> simp [ord3T4, ord3T4M, Fin.sum_univ_five, h1, h2, hcfix, add_comm]

end Tau

theorem ord3_classify {τ : G52} (hτ : orderOf τ = 3) :
    (commDim τ = 2 ∧ IsConj ord3T2 τ) ∨ (commDim τ = 4 ∧ IsConj ord3T4 τ) := by
  set U := LinearMap.range (toLin' ((τ : M5) - 1)) with hU
  have hrn : commDim τ + finrank (ZMod 2) (LinearMap.ker (toLin' ((τ : M5) - 1))) = 5 :=
    inv_rank_nullity τ
  have hdim : commDim τ = finrank (ZMod 2) U := rfl
  have hU5 : finrank (ZMod 2) U ≤ 5 := by
    have := Submodule.finrank_le U
    rwa [inv_finrank_V5] at this
  obtain ⟨u₁, hu₁, hu₁0⟩ : ∃ u ∈ U, u ≠ 0 := by
    by_contra h
    apply inv_invN_ne_zero (ord3_ne_one hτ)
    refine ext_cols fun j => ?_
    rw [zero_mulVec]
    by_contra hj
    exact h ⟨_, ⟨Pi.single j 1, rfl⟩, hj⟩
  have hS0 : ∀ s ∈ Submodule.span (ZMod 2) (Set.range (Fin.elim0 : Fin 0 → V5)),
      (τ : M5) *ᵥ s ∈ Submodule.span (ZMod 2) (Set.range (Fin.elim0 : Fin 0 → V5)) := by
    intro s hs
    rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at hs ⊢
    rw [hs, mulVec_zero]
  have hu₁S : u₁ ∉ Submodule.span (ZMod 2) (Set.range (Fin.elim0 : Fin 0 → V5)) := by
    rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot]
    exact hu₁0
  set v2 : Fin (0 + 2) → V5 :=
    Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → V5) u₁) ((τ : M5) *ᵥ u₁) with hv2
  have hl2 : LinearIndependent (ZMod 2) v2 :=
    ord3_snoc_pair hτ linearIndependent_empty_type hS0 hu₁ hu₁S
  have hS2 := ord3_snoc_pair_invariant hτ hS0 hu₁
  have hv2U : Submodule.span (ZMod 2) (Set.range v2) ≤ U := by
    rw [Submodule.span_le, hv2, Fin.range_snoc, Fin.range_snoc]
    rintro x (rfl | rfl | ⟨i, rfl⟩)
    · exact ord3_U_invariant hu₁
    · exact hu₁
    · exact i.elim0
  have hf2 : finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range v2)) = 2 := by
    rw [finrank_span_eq_card hl2, Fintype.card_fin]
  have h2le : 2 ≤ finrank (ZMod 2) U := by
    have := Submodule.finrank_mono hv2U
    rwa [hf2] at this
  by_cases h2 : finrank (ZMod 2) U = 2
  · left
    refine ⟨h2, ord3_conj_two hτ hu₁ hu₁0 (by omega)⟩
  have hlt2 : Submodule.span (ZMod 2) (Set.range v2) < U := by
    refine lt_of_le_of_ne hv2U fun h => h2 ?_
    rw [← h, hf2]
  obtain ⟨u₂, hu₂, hu₂S⟩ := IsConcreteLE.exists_of_lt hlt2
  set v4 : Fin (2 + 2) → V5 := Fin.snoc (Fin.snoc v2 u₂) ((τ : M5) *ᵥ u₂) with hv4
  have hl4 : LinearIndependent (ZMod 2) v4 := ord3_snoc_pair hτ hl2 hS2 hu₂ hu₂S
  have hS4 := ord3_snoc_pair_invariant hτ hS2 hu₂
  have hv4U : Submodule.span (ZMod 2) (Set.range v4) ≤ U := by
    rw [Submodule.span_le, hv4, Fin.range_snoc, Fin.range_snoc]
    rintro x (rfl | rfl | ⟨i, rfl⟩)
    · exact ord3_U_invariant hu₂
    · exact hu₂
    · exact hv2U (Submodule.subset_span ⟨i, rfl⟩)
  have hf4 : finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range v4)) = 4 := by
    rw [finrank_span_eq_card hl4, Fintype.card_fin]
  have h4le : 4 ≤ finrank (ZMod 2) U := by
    have := Submodule.finrank_mono hv4U
    rwa [hf4] at this
  by_cases h4 : finrank (ZMod 2) U = 4
  · right
    refine ⟨h4, ord3_conj_four hτ hu₁ hu₂ ?_ (by omega)⟩
    convert hl4 using 1
    funext i
    fin_cases i <;> rfl
  exfalso
  have hlt4 : Submodule.span (ZMod 2) (Set.range v4) < U := by
    refine lt_of_le_of_ne hv4U fun h => h4 ?_
    rw [← h, hf4]
  obtain ⟨u₃, hu₃, hu₃S⟩ := IsConcreteLE.exists_of_lt hlt4
  have hl6 := ord3_snoc_pair hτ hl4 hS4 hu₃ hu₃S
  have := hl6.fintype_card_le_finrank
  rw [Fintype.card_fin, inv_finrank_V5] at this
  omega

end CFSG.GroupTheory.GL52
