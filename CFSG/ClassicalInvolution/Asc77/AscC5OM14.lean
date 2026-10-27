module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM13

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix

variable {F : Type} [Field F] {M : gsp 2 F}

theorem form_sub_right' (v a b : Fin 2 ⊕ Fin 2 → F) : form v (a - b) = form v a - form v b := by
  rw [sub_eq_add_neg, form_add_right, form_neg_right', ← sub_eq_add_neg]

@[expose] def piProj (M : gsp 2 F) (u y : Fin 2 ⊕ Fin 2 → F) : Fin 2 ⊕ Fin 2 → F :=
  y - form y (gm M *ᵥ u) • u + form y u • (gm M *ᵥ u)

theorem form_u_piProj {u : Fin 2 ⊕ Fin 2 → F} (hu : form u (gm M *ᵥ u) = 1)
    (y : Fin 2 ⊕ Fin 2 → F) : form u (piProj M u y) = 0 := by
  rw [piProj, form_add_right, form_sub_right', form_smul_right, form_smul_right, form_self', hu,
    form_antisymm y u]
  ring

theorem form_u_gm_piProj (hN : gm M * gm M = (-mu M) • 1) {u : Fin 2 ⊕ Fin 2 → F}
    (hu : form u (gm M *ᵥ u) = 1) (y : Fin 2 ⊕ Fin 2 → F) :
    form u (gm M *ᵥ piProj M u y) = 0 := by
  rw [piProj, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
    gm_gm_mulVec_of_minus hN, form_add_right, form_sub_right', form_smul_right, form_smul_right,
    form_neg_right', form_smul_right, form_self', hu, form_gm_symm_of_minus hN y u]
  ring

theorem piProj_add (u y z : Fin 2 ⊕ Fin 2 → F) :
    piProj M u (y + z) = piProj M u y + piProj M u z := by
  ext i
  simp only [piProj, form_add_left, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem eq_of_piProj (u y : Fin 2 ⊕ Fin 2 → F) :
    y = piProj M u y + form y (gm M *ᵥ u) • u - form y u • (gm M *ᵥ u) := by
  ext i
  simp only [piProj, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem eq_zero_of_gm_mulVec (hN : gm M * gm M = (-mu M) • 1) {v : Fin 2 ⊕ Fin 2 → F}
    (hv : gm M *ᵥ v = 0) : v = 0 := by
  have h := gm_gm_mulVec_of_minus hN v
  rw [hv, Matrix.mulVec_zero, eq_comm, neg_eq_zero] at h
  exact (smul_eq_zero.mp h).resolve_left (Units.ne_zero _)

theorem exists_piProj_ne (h2 : (2 : F) ≠ 0) (hN : gm M * gm M = (-mu M) • 1)
    {u : Fin 2 ⊕ Fin 2 → F} (hu : form u (gm M *ᵥ u) = 1) :
    ∃ y, form (piProj M u y) (gm M *ᵥ piProj M u y) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hπ : ∀ y z, form (piProj M u y) (gm M *ᵥ piProj M u z) = 0 := by
    intro y z
    have h := hcon (y + z)
    rw [piProj_add, Matrix.mulVec_add, form_add_left, form_add_right, form_add_right, hcon y,
      hcon z] at h
    have hs := form_gm_symm_of_minus hN (piProj M u z) (piProj M u y)
    have : (2 : F) * form (piProj M u y) (gm M *ᵥ piProj M u z) = 0 := by
      linear_combination h + hs
    exact (mul_eq_zero.1 this).resolve_left h2
  have hall : ∀ y z, form z (gm M *ᵥ piProj M u y) = 0 := by
    intro y z
    rw [form_gm_symm_of_minus hN (piProj M u y) z]
    have hz := eq_of_piProj (M := M) u z
    have hNz : gm M *ᵥ z = gm M *ᵥ piProj M u z + form z (gm M *ᵥ u) • (gm M *ᵥ u) -
        form z u • (gm M *ᵥ (gm M *ᵥ u)) := by
      conv_lhs => rw [hz]
      rw [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    have e2 : form (piProj M u y) (gm M *ᵥ u) = 0 := by
      rw [form_gm_symm_of_minus hN u (piProj M u y)]
      exact form_u_gm_piProj hN hu y
    have e3 : form (piProj M u y) u = 0 := by
      rw [form_antisymm u (piProj M u y), form_u_piProj hu, neg_zero]
    rw [hNz, form_sub_right', form_add_right, form_smul_right, form_smul_right, hπ,
      gm_gm_mulVec_of_minus hN, form_neg_right', form_smul_right, e2, e3]
    ring
  have hzero : ∀ y, piProj M u y = 0 := fun y =>
    eq_zero_of_gm_mulVec hN (C25W.Sp.eq_zero_of_form_left (m := 1) _ (fun z => hall y z))
  set S := Submodule.span F (Set.range ![u, gm M *ᵥ u]) with hS
  have hmem : ∀ y, y ∈ S := by
    intro y
    rw [eq_of_piProj (M := M) u y, hzero, zero_add]
    refine Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have htop : S = ⊤ := eq_top_iff.mpr fun y _ => hmem y
  have h1 : Module.finrank F S ≤ 2 := by
    have := finrank_range_le_card (R := F) ![u, gm M *ᵥ u]
    simpa [Set.finrank, hS] using this
  rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card] at h1
  simp at h1

@[expose] def nMinus (μ : F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks 0 (-μ • 1) 1 0

theorem nMinus_mulVec_inl (μ : F) (k : Fin 2) :
    nMinus μ *ᵥ Pi.single (Sum.inl k) 1 = Pi.single (Sum.inr k) 1 := by
  ext r
  rw [mulVec_single_one_apply]
  rcases r with r | r <;> fin_cases r <;> fin_cases k <;> simp [nMinus]

theorem nMinus_mulVec_inr (μ : F) (k : Fin 2) :
    nMinus μ *ᵥ Pi.single (Sum.inr k) 1 = (-μ) • Pi.single (Sum.inl k) 1 := by
  ext r
  rw [mulVec_single_one_apply]
  rcases r with r | r <;> fin_cases r <;> fin_cases k <;> simp [nMinus]

theorem matrix_ext_single {A B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (h : ∀ j, A *ᵥ Pi.single j 1 = B *ᵥ Pi.single j 1) : A = B := by
  ext r j
  rw [← mulVec_single_one_apply A j r, ← mulVec_single_one_apply B j r, h]

theorem exists_conj_nMinus [Finite F] (h2 : (2 : F) ≠ 0) (hN : gm M * gm M = (-mu M) • 1) :
    ∃ g : StatedSp 2 F, mat 2 F g * nMinus (mu M) = gm M * mat 2 F g := by
  obtain ⟨x, hx⟩ := exists_form_gm_ne h2 hN
  obtain ⟨α, β, hαβ⟩ := exists_form_gm_eq_one h2 hN hx
  set u₁ := α • x + β • (gm M *ᵥ x) with hu₁
  obtain ⟨y, hy⟩ := exists_piProj_ne h2 hN hαβ
  obtain ⟨α', β', hαβ'⟩ := exists_form_gm_eq_one h2 hN hy
  set x₂ := piProj M u₁ y with hx₂
  set u₂ := α' • x₂ + β' • (gm M *ᵥ x₂) with hu₂
  have o1 : form u₁ x₂ = 0 := form_u_piProj hαβ y
  have o2 : form u₁ (gm M *ᵥ x₂) = 0 := form_u_gm_piProj hN hαβ y
  have p1 : form u₁ u₂ = 0 := by
    rw [hu₂, form_add_right, form_smul_right, form_smul_right, o1, o2]
    ring
  have p2 : form u₁ (gm M *ᵥ u₂) = 0 := by
    rw [hu₂, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      gm_gm_mulVec_of_minus hN, form_add_right, form_smul_right, form_smul_right,
      form_neg_right', form_smul_right, o1, o2]
    ring
  have p3 : form (gm M *ᵥ u₁) u₂ = 0 := by
    rw [form_gm_left_of_minus hN, p2, neg_zero]
  have p4 : form (gm M *ᵥ u₁) (gm M *ᵥ u₂) = 0 := by
    rw [form_gm_gm, p1, mul_zero]
  obtain ⟨g, g1, g2, g3, g4⟩ := exists_sp_apply_eq_two (m := 0) u₁ (gm M *ᵥ u₁) u₂
    (gm M *ᵥ u₂) hαβ hαβ' p1 p2 p3 p4
  have g1' : mat 2 F g *ᵥ Pi.single (Sum.inl 0) 1 = u₁ := g1
  have g2' : mat 2 F g *ᵥ Pi.single (Sum.inr 0) 1 = gm M *ᵥ u₁ := g2
  have g3' : mat 2 F g *ᵥ Pi.single (Sum.inl 1) 1 = u₂ := g3
  have g4' : mat 2 F g *ᵥ Pi.single (Sum.inr 1) 1 = gm M *ᵥ u₂ := g4
  have key : ∀ k : Fin 2,
      (mat 2 F g *ᵥ (nMinus (mu M) *ᵥ Pi.single (Sum.inl k) 1) =
        gm M *ᵥ (mat 2 F g *ᵥ Pi.single (Sum.inl k) 1)) ∧
      (mat 2 F g *ᵥ (nMinus (mu M) *ᵥ Pi.single (Sum.inr k) 1) =
        gm M *ᵥ (mat 2 F g *ᵥ Pi.single (Sum.inr k) 1)) := by
    intro k
    rw [nMinus_mulVec_inl, nMinus_mulVec_inr, Matrix.mulVec_smul]
    fin_cases k
    · refine ⟨?_, ?_⟩
      · show mat 2 F g *ᵥ Pi.single (Sum.inr 0) 1 = gm M *ᵥ (mat 2 F g *ᵥ Pi.single (Sum.inl 0) 1)
        rw [g2', g1']
      · show (-mu M) • (mat 2 F g *ᵥ Pi.single (Sum.inl 0) 1) =
          gm M *ᵥ (mat 2 F g *ᵥ Pi.single (Sum.inr 0) 1)
        rw [g1', g2', gm_gm_mulVec_of_minus hN, neg_smul]
    · refine ⟨?_, ?_⟩
      · show mat 2 F g *ᵥ Pi.single (Sum.inr 1) 1 = gm M *ᵥ (mat 2 F g *ᵥ Pi.single (Sum.inl 1) 1)
        rw [g4', g3']
      · show (-mu M) • (mat 2 F g *ᵥ Pi.single (Sum.inl 1) 1) =
          gm M *ᵥ (mat 2 F g *ᵥ Pi.single (Sum.inr 1) 1)
        rw [g3', g4', gm_gm_mulVec_of_minus hN, neg_smul]
  refine ⟨g, matrix_ext_single fun j => ?_⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rcases j with j | j
  · exact (key j).1
  · exact (key j).2

end CFSG.ClassicalInvolution.Asc77.C5O.M
