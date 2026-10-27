module

public import CFSG.FeitThompson.Representations.InducedCharacterTraceFormula
public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap
import CFSG.FeitThompson.Representations.CharacterMultiplicitiesIrreducibility
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.VirtualCharacterNormCyclicGenerators

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace InducedCharacterConstruction

open scoped ComplexConjugate

variable {G : Type*} [Group G] {S : Subgroup G}

theorem mul_mem_classFun {k : Type*} [Field k] {f h : G → k} (hf : f ∈ classFun k G)
    (hh : h ∈ classFun k G) : f * h ∈ classFun k G :=
  mem_classFun.2 fun g c => by
    simp only [Pi.mul_apply, mem_classFun.1 hf g c, mem_classFun.1 hh g c]

theorem resClassFun_mem_classFun {f : G → ℂ} (hf : f ∈ classFun ℂ G) :
    resClassFun S f ∈ classFun ℂ ↥S :=
  mem_classFun.2 fun s c => resClassFun_conj S hf c s

theorem subgroupExtend_add (f₁ f₂ : S → ℂ) (y : G) :
    subgroupExtend S (f₁ + f₂) y = subgroupExtend S f₁ y + subgroupExtend S f₂ y := by
  by_cases hy : y ∈ S
  · lift y to S using hy with s hs; simp
  · simp [subgroupExtend_of_notMem _ _ hy]

theorem subgroupExtend_smul (c : ℂ) (f : S → ℂ) (y : G) :
    subgroupExtend S (c • f) y = c * subgroupExtend S f y := by
  by_cases hy : y ∈ S
  · lift y to S using hy with s hs; simp
  · simp [subgroupExtend_of_notMem _ _ hy]

theorem subgroupExtend_star (f : S → ℂ) (y : G) :
    subgroupExtend S (star f) y = conj (subgroupExtend S f y) := by
  by_cases hy : y ∈ S
  · lift y to S using hy with s hs; simp [Pi.star_apply]
  · simp [subgroupExtend_of_notMem _ _ hy]

theorem subgroupExtend_mul_resClassFun (f : S → ℂ) (h : G → ℂ) (y : G) :
    subgroupExtend S (f * resClassFun S h) y = subgroupExtend S f y * h y := by
  by_cases hy : y ∈ S
  · lift y to S using hy with s hs; simp [resClassFun_apply]
  · simp [subgroupExtend_of_notMem _ _ hy]

theorem indClassFun_add [Fintype G] (f₁ f₂ : S → ℂ) :
    indClassFun S (f₁ + f₂) = indClassFun S f₁ + indClassFun S f₂ := by
  funext g
  simp only [indClassFun_apply, subgroupExtend_add, Pi.add_apply, Finset.sum_add_distrib, mul_add]

theorem indClassFun_smul [Fintype G] (c : ℂ) (f : S → ℂ) :
    indClassFun S (c • f) = c • indClassFun S f := by
  funext g
  simp only [indClassFun_apply, subgroupExtend_smul, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

theorem indClassFun_zero [Fintype G] : indClassFun S (0 : S → ℂ) = 0 := by
  simpa using indClassFun_smul (S := S) (G := G) 0 0

theorem indClassFun_zsmul [Fintype G] (n : ℤ) (f : S → ℂ) :
    indClassFun S (n • f) = n • indClassFun S f := by
  have h : (n : ℂ) • f = n • f := by ext s; simp [zsmul_eq_mul]
  rw [← h, indClassFun_smul]
  ext g; simp [zsmul_eq_mul]

noncomputable def indClassFunₗ (S : Subgroup G) [Fintype G] : (S → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun := indClassFun S
  map_add' := indClassFun_add
  map_smul' := indClassFun_smul

theorem indClassFunₗ_apply [Fintype G] (f : S → ℂ) :
    indClassFunₗ S f = indClassFun S f := (rfl)

theorem indClassFun_mul_resClassFun [Fintype G] (f : S → ℂ) {h : G → ℂ}
    (hh : h ∈ classFun ℂ G) : indClassFun S (f * resClassFun S h) = indClassFun S f * h := by
  funext g
  have key : ∀ x : G, subgroupExtend S (f * resClassFun S h) (x⁻¹ * g * x)
      = subgroupExtend S f (x⁻¹ * g * x) * h g := by
    intro x
    rw [subgroupExtend_mul_resClassFun]
    congr 1
    simpa using mem_classFun.1 hh g x⁻¹
  rw [indClassFun_apply, Finset.sum_congr rfl fun x _ => key x, ← Finset.sum_mul,
    Pi.mul_apply, indClassFun_apply, mul_assoc]

theorem indClassFun_star [Fintype G] (f : S → ℂ) :
    indClassFun S (star f) = star (indClassFun S f) := by
  funext g
  rw [Pi.star_apply, indClassFun_apply, indClassFun_apply]
  simp only [subgroupExtend_star, Complex.star_def, map_mul, map_sum, map_inv₀,
    Complex.conj_natCast]

theorem indClassFun_conj_apply [Fintype G] (f : S → ℂ) (g : G) :
    indClassFun S (fun s => conj (f s)) g = conj (indClassFun S f g) :=
  congrFun (indClassFun_star f) g

open CFSG.FeitThompson in
theorem fdRepCharacter_mem_span_Irr {H : Type*} [Group H] [Finite H] (W : FDRep ℂ H) :
    FDRep.character W ∈ Submodule.span ℤ (Irr H) := by
  classical
  have : Fintype H := Fintype.ofFinite H
  obtain ⟨m, hm⟩ := exists_character_eq_sum_nsmul (show Representation ℂ H W.V from W.ρ)
  rw [show FDRep.character W = (show Representation ℂ H W.V from W.ρ).character from rfl, hm]
  refine Submodule.sum_mem _ fun ψ _ => ?_
  rw [Nat.cast_smul_eq_nsmul ℂ]
  exact nsmul_mem (Submodule.subset_span (mem_irrFinset.1 ψ.2)) _

open CFSG.FeitThompson in
theorem indClassFun_mem_span_Irr [Fintype G] {f : S → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr ↥S)) :
    indClassFun S f ∈ Submodule.span ℤ (Irr G) := by
  induction hf using Submodule.span_induction with
  | mem χ hχ =>
      obtain ⟨V, -, rfl⟩ := mem_Irr.1 hχ
      obtain ⟨W, hW⟩ := NormalInducedFamily.exists_fdRep_character_eq_indClassFun S V
      rw [← NormalInducedFamily.indClassFun_inducedCharacterConstruction_eq] at hW
      exact hW ▸ fdRepCharacter_mem_span_Irr W
  | zero => rw [indClassFun_zero]; exact Submodule.zero_mem _
  | add f₁ f₂ _ _ h₁ h₂ => rw [indClassFun_add]; exact Submodule.add_mem _ h₁ h₂
  | smul n f _ h => rw [indClassFun_zsmul]; exact Submodule.smul_mem _ n h

open CFSG.FeitThompson in
theorem indClassFun_mem_virtualChars [Fintype G] {f : S → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr ↥S)) : indClassFun S f ∈ virtualChars G :=
  span_Irr_le_virtualChars (indClassFun_mem_span_Irr hf)

end InducedCharacterConstruction

end CFSG.FeitThompson
