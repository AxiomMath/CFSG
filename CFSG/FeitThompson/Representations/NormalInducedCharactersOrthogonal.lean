module

public import CFSG.FeitThompson.Representations.InducedIrreducibleNormOrbitFormula
public import CFSG.FeitThompson.Representations.InducedCharacterTraceFormula
import CFSG.FeitThompson.Representations.CommutingOperatorFiniteScalarField

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalInducedFamily

open NormalInduction (conjClassFun conjClassFun_apply coe_conjNormal_inv)

variable {G : Type*} [Group G]

private theorem extendByZero_conjClassFun (N : Subgroup G) [N.Normal] (s : G) (ψ : N → ℂ)
    (y : G) : extendByZero N (conjClassFun N s ψ) y = extendByZero N ψ (s⁻¹ * y * s) := by
  by_cases hy : y ∈ N
  · lift y to N using hy with n hn
    rw [extendByZero_apply_coe, conjClassFun_apply,
      show s⁻¹ * (n : G) * s = ((MulAut.conjNormal s⁻¹ n : N) : G) from
        (coe_conjNormal_inv N s n).symm, extendByZero_apply_coe]
  · rw [extendByZero_of_notMem _ _ hy, extendByZero_of_notMem]
    intro hmem
    exact hy (by simpa [mul_assoc] using ‹N.Normal›.conj_mem _ hmem s)

theorem indClassFun_conjClassFun [Fintype G] (N : Subgroup G) [N.Normal] (s : G) (ψ : N → ℂ) :
    indClassFun N (conjClassFun N s ψ) = indClassFun N ψ := by
  funext g
  rw [indClassFun_eq_sum_extendByZero, indClassFun_eq_sum_extendByZero]
  congr 1
  refine Fintype.sum_bijective (fun x => x * s) (Group.mulRight_bijective s) _ _ fun x => ?_
  rw [extendByZero_conjClassFun]
  congr 1
  group

theorem relIndex_inertiaGroup_ne_zero [Finite G] (N : Subgroup G) [N.Normal] (χ : N → ℂ) :
    N.relIndex (inertiaGroup N χ) ≠ 0 := by
  rw [Subgroup.relIndex]
  exact Subgroup.FiniteIndex.index_ne_zero

theorem indClassFun_one_eq_index_mul [Fintype G] (H : Subgroup G) (f : H → ℂ) :
    indClassFun H f 1 = (H.index : ℂ) * f 1 := by
  rw [indClassFun_one]
  congr 1
  rw [div_eq_iff (by exact_mod_cast Nat.card_pos.ne' : (Nat.card H : ℂ) ≠ 0)]
  exact_mod_cast H.index_mul_card.symm

theorem exists_apply_one_eq_of_mem_Irr {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    ∃ d : ℕ, 0 < d ∧ χ 1 = (d : ℂ) := by
  obtain ⟨V, hirr, rfl⟩ := mem_Irr.1 hχ
  have : Representation.IsIrreducible V.ρ := hirr
  have : Nontrivial (V.V : Type _) := nontrivial_of_isIrreducible V.ρ
  exact ⟨Module.finrank ℂ (V.V : Type _), Module.finrank_pos, FDRep.char_one V⟩

theorem indClassFun_inducedCharacterConstruction_eq [Fintype G] (H : Subgroup G) (f : H → ℂ) :
    InducedCharacterConstruction.indClassFun H f = indClassFun H f := by
  funext g
  rw [InducedCharacterConstruction.indClassFun_apply, indClassFun_eq_sum_extendByZero]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : x⁻¹ * g * x ∈ H
  · lift (x⁻¹ * g * x) to H using h with z hz
    rw [extendByZero_apply_coe, InducedCharacterConstruction.subgroupExtend_coe]
  · rw [extendByZero_of_notMem _ _ h, InducedCharacterConstruction.subgroupExtend_of_notMem _ _ h]

theorem exists_fdRep_character_eq {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    ∃ W : FDRep ℂ G, FDRep.character W = ρ.character := by
  classical
  set n := Module.finrank ℂ V with hn
  set e : V ≃ₗ[ℂ] (Fin n → ℂ) := (Module.finBasis ℂ V).equivFun with he
  refine ⟨FDRep.of (((e.conjAlgEquiv ℂ : Module.End ℂ V ≃ₐ[ℂ] Module.End ℂ (Fin n → ℂ))
    : Module.End ℂ V →* Module.End ℂ (Fin n → ℂ)).comp ρ), ?_⟩
  funext g
  change LinearMap.trace ℂ _ ((FDRep.of _).ρ g) = _
  rw [FDRep.of_ρ']
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  rw [show ((e.conjAlgEquiv ℂ : Module.End ℂ V ≃ₐ[ℂ] Module.End ℂ (Fin n → ℂ))
    : Module.End ℂ V →* Module.End ℂ (Fin n → ℂ)) (ρ g) = e.conj (ρ g) from rfl,
    LinearMap.trace_conj']
  rfl

theorem exists_fdRep_character_eq_indClassFun [Fintype G] (H : Subgroup G) (V : FDRep ℂ H) :
    ∃ W : FDRep ℂ G, FDRep.character W = indClassFun H (FDRep.character V) := by
  classical
  have : Fintype (InducedCharacterConstruction.RightCosets H) := Fintype.ofFinite _
  have hfd : FiniteDimensional ℂ (Representation.IndV H.subtype V.ρ) :=
    ((Representation.equivOfIso (Rep.indCoindIso (Rep.of V.ρ))).toLinearEquiv.trans
        (InducedCharacterConstruction.coindEquivPi V.ρ)).symm.finiteDimensional
  obtain ⟨W, hW⟩ := exists_fdRep_character_eq (Representation.ind H.subtype V.ρ)
  refine ⟨W, ?_⟩
  rw [hW, InducedCharacterConstruction.character_ind_eq_indClassFun,
    indClassFun_inducedCharacterConstruction_eq]
  rfl

theorem indClassFun_eq_iff_exists_conjClassFun [Fintype G] (N : Subgroup G) [N.Normal]
    {χ ψ : N → ℂ} (hχ : χ ∈ Irr N) (hψ : ψ ∈ Irr N) :
    indClassFun N χ = indClassFun N ψ ↔ ∃ t : G, conjClassFun N t ψ = χ := by
  refine ⟨fun h => ?_, fun ⟨t, ht⟩ => by rw [← ht, indClassFun_conjClassFun]⟩
  by_contra hcon
  have hcon' : ∀ t : G, conjClassFun N t ψ ≠ χ := fun t ht => hcon ⟨t, ht⟩
  have h0 : cfInner (indClassFun N χ) (indClassFun N ψ) = 0 :=
    cfInner_indClassFun_indClassFun_eq_zero N hχ hψ hcon'
  rw [← h, cfInner_self_indClassFun N hχ] at h0
  exact relIndex_inertiaGroup_ne_zero N χ (by exact_mod_cast h0)

theorem exists_fdRep_character_eq_of_mem_indFam [Fintype G] (N : Subgroup G)
    {f : G → ℂ} (hf : f ∈ indFam N (Irr N)) :
    ∃ W : FDRep ℂ G, FDRep.character W = f := by
  obtain ⟨χ, hχ, rfl⟩ := (mem_indFam N).1 hf
  obtain ⟨V, -, rfl⟩ := mem_Irr.1 hχ
  exact exists_fdRep_character_eq_indClassFun N V

theorem exists_apply_one_eq_of_mem_indFam [Fintype G] (N : Subgroup G)
    {f : G → ℂ} (hf : f ∈ indFam N (Irr N)) :
    ∃ d : ℕ, 0 < d ∧ N.index ∣ d ∧ f 1 = (d : ℂ) := by
  obtain ⟨χ, hχ, rfl⟩ := (mem_indFam N).1 hf
  obtain ⟨e, he, hce⟩ := exists_apply_one_eq_of_mem_Irr hχ
  refine ⟨N.index * e, Nat.mul_pos (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero) he,
    Dvd.intro e rfl, ?_⟩
  rw [indClassFun_one_eq_index_mul, hce]
  push_cast
  ring

theorem ne_zero_of_mem_indFam [Fintype G] (N : Subgroup G) {f : G → ℂ}
    (hf : f ∈ indFam N (Irr N)) : f ≠ 0 := by
  obtain ⟨d, hd, -, hf1⟩ := exists_apply_one_eq_of_mem_indFam N hf
  intro h0
  rw [h0, Pi.zero_apply] at hf1
  exact hd.ne' (by exact_mod_cast hf1.symm)

theorem cfInner_eq_zero_of_mem_indFam [Fintype G] (N : Subgroup G) [N.Normal]
    {f h : G → ℂ} (hf : f ∈ indFam N (Irr N)) (hh : h ∈ indFam N (Irr N)) (hne : f ≠ h) :
    cfInner f h = 0 := by
  obtain ⟨χ, hχ, rfl⟩ := (mem_indFam N).1 hf
  obtain ⟨ψ, hψ, rfl⟩ := (mem_indFam N).1 hh
  exact cfInner_indClassFun_indClassFun_eq_zero N hχ hψ fun t ht =>
    hne ((indClassFun_eq_iff_exists_conjClassFun N hχ hψ).2 ⟨t, ht⟩)

end NormalInducedFamily

end CFSG.FeitThompson
