module

public import CFSG.LargeExtraspecial.GLW4Tau

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module Matrix QuadraticMap CFSG.LargeExtraspecial.GLR

section Basis

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {β : LinearMap.BilinForm (ZMod 2) V}

theorem exists_basis_J (hβ : β.IsAlt) (hnd : β.Nondegenerate) (h4 : finrank (ZMod 2) V = 4)
    {a : V} (ha : a ≠ 0) :
    ∃ b : Basis (Fin 4) (ZMod 2) V, b 0 = a ∧ ∀ i j, β (b i) (b j) = J i j := by
  obtain ⟨m, c, hc, hc0⟩ := hβ.exists_basis_apply_eq_J_inl_zero_eq hnd ha
  have hm : m = 1 := by
    have h := finrank_eq_card_basis c
    rw [h4, Fintype.card_sum, Fintype.card_fin] at h
    omega
  subst hm
  refine ⟨c.reindex finSumFinEquiv, ?_, fun i j => ?_⟩
  · rw [Basis.reindex_apply, ← hc0]
    rfl
  · rw [Basis.reindex_apply, Basis.reindex_apply, hc]
    fin_cases i <;> fin_cases j <;> simp [Matrix.J, J, finSumFinEquiv, Fin.addCases]


omit [FiniteDimensional (ZMod 2) V] in
theorem zmod2_add_mul_self (x : ZMod 2) : x + x * x = 0 := by revert x; decide

omit [FiniteDimensional (ZMod 2) V] in
@[expose] def diagLin (hsym : ∀ a b, β a b = β b a) : V →ₗ[ZMod 2] ZMod 2 where
  toFun a := β a a
  map_add' a b := by
    simp only [map_add, LinearMap.add_apply]
    rw [hsym b a]
    have h2 : β a b + β a b = 0 := CharTwo.add_self_eq_zero _
    linear_combination h2
  map_smul' c a := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← mul_assoc, show c * c = c by revert c; decide]

omit [FiniteDimensional (ZMod 2) V] in
theorem diagLin_apply (hsym : ∀ a b, β a b = β b a) (a : V) : diagLin hsym a = β a a := rfl

omit [FiniteDimensional (ZMod 2) V] in
@[expose] noncomputable def altPart (hsym : ∀ a b, β a b = β b a) :
    LinearMap.BilinForm (ZMod 2) V :=
  β + (LinearMap.mul (ZMod 2) (ZMod 2)).compl₁₂ (diagLin hsym) (diagLin hsym)

omit [FiniteDimensional (ZMod 2) V] in
theorem altPart_apply (hsym : ∀ a b, β a b = β b a) (a b : V) :
    altPart hsym a b = β a b + β a a * β b b := rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem altPart_isAlt (hsym : ∀ a b, β a b = β b a) : (altPart hsym).IsAlt := fun a => by
  rw [altPart_apply]
  exact zmod2_add_mul_self _



theorem diag_rep_eq_zero (hsym : ∀ a b, β a b = β b a) (hnd : β.Nondegenerate)
    (h4 : finrank (ZMod 2) V = 4) {u₀ : V} (hu₀ : ∀ w, β u₀ w = β w w) : β u₀ u₀ = 0 := by
  by_contra h1
  have h1' : β u₀ u₀ = 1 := by revert h1; generalize β u₀ u₀ = x; revert x; decide
  set lam := diagLin hsym with hlam
  set K := LinearMap.ker lam with hK
  have hkey : ∀ v : V, v + β v v • u₀ ∈ K := fun v => by
    rw [hK, LinearMap.mem_ker, map_add, map_smul, diagLin_apply, diagLin_apply, h1', smul_eq_mul,
      mul_one]
    exact CharTwo.add_self_eq_zero _
  have hleft : ∀ w : K, (∀ w' : K, β w w' = 0) → w = 0 := fun w hw => by
    apply Subtype.ext
    refine hnd.1 _ fun v => ?_
    have hwu : β w u₀ = 0 := by
      rw [hsym, hu₀]; exact (LinearMap.mem_ker.mp w.2 : β w w = 0)
    have hv : v = (v + β v v • u₀) + β v v • u₀ := by
      rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
    rw [hv, map_add, map_smul, smul_eq_mul, hwu, mul_zero, add_zero]
    exact hw ⟨_, hkey v⟩
  have hKalt : (β.restrict K).IsAlt := fun w => (LinearMap.mem_ker.mp w.2 : β w w = 0)
  have hKnd : (β.restrict K).Nondegenerate :=
    ⟨fun w hw => hleft w hw, fun w hw => hleft w fun w' => by rw [hsym]; exact hw w'⟩
  have hrange : LinearMap.range lam = ⊤ := by
    refine eq_top_iff.mpr fun c _ => ⟨c • u₀, ?_⟩
    rw [map_smul, diagLin_apply, h1', smul_eq_mul, mul_one]
  have hdim := LinearMap.finrank_range_add_finrank_ker lam
  rw [hrange, finrank_top, Module.finrank_self, h4] at hdim
  have hK3 : finrank (ZMod 2) K = 3 := by rw [hK]; omega
  have heven := hKalt.even_finrank hKnd
  rw [hK3] at heven
  exact absurd heven (by decide)

theorem exists_basis_N (hsym : ∀ a b, β a b = β b a) (hnd : β.Nondegenerate)
    (h4 : finrank (ZMod 2) V = 4) (hna : ∃ a, β a a ≠ 0) :
    ∃ b : Basis (Fin 4) (ZMod 2) V, ∀ i j, β (b i) (b j) = N i j := by
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : V, ∀ w, β u₀ w = β w w :=
    ⟨(β.toDual hnd).symm (diagLin hsym), fun w => by
      rw [← LinearMap.BilinForm.toDual_def hnd, LinearEquiv.apply_symm_apply]; rfl⟩
  have h0 := diag_rep_eq_zero hsym hnd h4 hu₀
  have hu₀ne : u₀ ≠ 0 := by
    rintro rfl
    obtain ⟨a, ha⟩ := hna
    exact ha (by rw [← hu₀]; simp)
  have hl : ∀ v, (∀ y, altPart hsym v y = 0) → v = 0 := fun v hv => by
    have h1 : ∀ y, β (v + β v v • u₀) y = 0 := fun y => by
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hu₀ y]
      have := hv y
      rwa [altPart_apply] at this
    have h2 := hnd.1 _ h1
    have hv' : v = β v v • u₀ := by
      have := eq_neg_of_add_eq_zero_left h2
      rwa [ZModModule.neg_eq_self] at this
    have h3 : β v v = 0 := by
      conv_lhs => rw [hv']
      rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, h0, mul_zero,
        mul_zero]
    rwa [h3, zero_smul, add_zero] at h2
  have hnd' : (altPart hsym).Nondegenerate :=
    ⟨hl, fun v hv => hl v fun y => by
      rw [altPart_apply, hsym, mul_comm]
      have := hv y
      rwa [altPart_apply] at this⟩
  obtain ⟨b, hb0, hb⟩ := exists_basis_J (altPart_isAlt hsym) hnd' h4 hu₀ne
  have hlam : ∀ i, β (b i) (b i) = J 0 i := fun i => by
    rw [← hu₀, ← hb0]
    have := hb 0 i
    rwa [altPart_apply, show β (b 0) (b 0) = 0 by rw [hb0]; exact h0, zero_mul, add_zero] at this
  refine ⟨b, fun i j => ?_⟩
  have := hb i j
  rw [altPart_apply, hlam i, hlam j] at this
  rw [N_eq_J_add, ← CharTwo.sub_eq_add]
  exact eq_sub_of_add_eq this

end Basis

section Config

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {C : Config S}

theorem formOf_nondegenerate {s : S.O} (hs : s ∈ S.Mbar) (hsX : s ∉ C.Xbar) :
    (C.formOf s).Nondegenerate :=
  ⟨fun _ h => Config.formOf_left hs hsX h, fun _ h => Config.formOf_right hs hsX h⟩

theorem exists_basis_gram_J (h4 : S.width = 4) {s : S.O} (hs : s ∈ S.Mbar) (hsX : s ∉ C.Xbar)
    (halt : ∀ a, C.formOf s a a = 0) : ∃ e : Basis (Fin 4) (ZMod 2) C.At, gram C e s = J := by
  have hr : finrank (ZMod 2) C.At = 4 := by rw [C.finrank_At, h4]
  have : Nontrivial C.At := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨a, ha⟩ := exists_ne (0 : C.At)
  obtain ⟨b, -, hb⟩ := exists_basis_J halt (formOf_nondegenerate hs hsX) hr ha
  exact ⟨b, funext fun i => funext fun j => hb i j⟩

theorem false_of_involution_alt [IsSimpleGroup G] (h4 : S.width = 4) {τ : G} (hτM : τ ∈ S.M)
    (hτX : τ ∉ C.X) (hττ : τ * τ = 1) (halt : ∀ a, C.formOf (S.ρ ⟨τ, hτM⟩) a a = 0) : False := by
  obtain ⟨e, he⟩ := exists_basis_gram_J h4 (Config.ρ_mem_Mbar _)
    (Config.ρ_not_mem_Xbar hτM hτX) halt
  exact false_of_involution_J h4 e hτM hτX hττ he

theorem formOf_symm_of_mul_self {s : S.O} (hss : s * s = 1) (a a' : C.At) :
    C.formOf s a a' = C.formOf s a' a := by
  rw [Config.formOf_apply, Config.formOf_apply, ← Config.polar_apply_apply s (a' : S.Qt),
    ← Config.mul_apply, hss]
  exact polar_comm _ _ _

theorem exists_basis_gram_N (h4 : S.width = 4) {s : S.O} (hs : s ∈ S.Mbar) (hsX : s ∉ C.Xbar)
    (hss : s * s = 1) (hna : ∃ a, C.formOf s a a ≠ 0) :
    ∃ e : Basis (Fin 4) (ZMod 2) C.At, gram C e s = N := by
  have hr : finrank (ZMod 2) C.At = 4 := by rw [C.finrank_At, h4]
  obtain ⟨b, hb⟩ := exists_basis_N (formOf_symm_of_mul_self hss) (formOf_nondegenerate hs hsX)
    hr hna
  exact ⟨b, funext fun i => funext fun j => hb i j⟩

end Config

end CFSG.LargeExtraspecial.GLW4
