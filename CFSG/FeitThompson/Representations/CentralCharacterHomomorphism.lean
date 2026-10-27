module

public import CFSG.FeitThompson.Representations.ConjugacyClassSumScalar

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Module

namespace CFSG.FeitThompson

namespace Representation

variable {G k V : Type*} [Group G] [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] (ρ : _root_.Representation k G V) [ρ.IsIrreducible]

omit [IsAlgClosed k] [FiniteDimensional k V] in
private theorem algebraMap_end_injective (ρ : _root_.Representation k G V) [ρ.IsIrreducible] :
    Function.Injective (Algebra.ofId k (Module.End k V)) := by
  have : Nontrivial V := nontrivial_of_isIrreducible ρ
  exact FaithfulSMul.algebraMap_injective k (Module.End k V)

private theorem asAlgebraHom_mem_range_of_mem_center
    {z : MonoidAlgebra k G} (hz : z ∈ Subalgebra.center k (MonoidAlgebra k G)) :
    ρ.asAlgebraHom z ∈ (Algebra.ofId k (Module.End k V)).range := by
  have hcomm : ∀ g : G, Commute (ρ.asAlgebraHom z) (ρ g) := by
    intro g
    have h := (Subalgebra.mem_center_iff.1 hz) (MonoidAlgebra.of k G g)
    have h2 := congrArg ρ.asAlgebraHom h
    rw [map_mul, map_mul, _root_.Representation.asAlgebraHom_of] at h2
    exact h2.symm
  obtain ⟨c, hc⟩ := IsIrreducible.exists_eq_smul_one_of_commute ρ _ hcomm
  exact ⟨c, by simp [hc, Algebra.algebraMap_eq_smul_one]⟩

private noncomputable def asAlgebraHomCenter :
    Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] (Algebra.ofId k (Module.End k V)).range :=
  (ρ.asAlgebraHom.comp (Subalgebra.center k (MonoidAlgebra k G)).val).codRestrict _
    fun z => asAlgebraHom_mem_range_of_mem_center ρ z.2

private theorem coe_asAlgebraHomCenter (z : Subalgebra.center k (MonoidAlgebra k G)) :
    (asAlgebraHomCenter ρ z : Module.End k V) = ρ.asAlgebraHom z :=
  DFunLike.congr_fun (AlgHom.val_comp_codRestrict
    (ρ.asAlgebraHom.comp (Subalgebra.center k (MonoidAlgebra k G)).val) _
    (fun z => asAlgebraHom_mem_range_of_mem_center ρ z.2)) z

noncomputable def centralCharacter :
    Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k :=
  (AlgEquiv.ofInjective (Algebra.ofId k (Module.End k V))
      (algebraMap_end_injective ρ)).symm.toAlgHom.comp (asAlgebraHomCenter ρ)

theorem algebraMap_centralCharacter (z : Subalgebra.center k (MonoidAlgebra k G)) :
    algebraMap k (Module.End k V) (centralCharacter ρ z) = ρ.asAlgebraHom z := by
  rw [← coe_asAlgebraHomCenter ρ z]
  exact congrArg Subtype.val ((AlgEquiv.ofInjective (Algebra.ofId k (Module.End k V))
    (algebraMap_end_injective ρ)).apply_symm_apply _)

theorem asAlgebraHom_center_eq_smul_one (z : Subalgebra.center k (MonoidAlgebra k G)) :
    ρ.asAlgebraHom (z : MonoidAlgebra k G) = centralCharacter ρ z • (1 : Module.End k V) := by
  rw [← algebraMap_centralCharacter ρ z, Algebra.algebraMap_eq_smul_one]

theorem asAlgebraHom_center_apply (z : Subalgebra.center k (MonoidAlgebra k G)) (v : V) :
    ρ.asAlgebraHom (z : MonoidAlgebra k G) v = centralCharacter ρ z • v := by
  rw [← algebraMap_centralCharacter ρ z, Module.algebraMap_end_apply]

@[simp]
theorem centralCharacter_one : centralCharacter ρ 1 = 1 := map_one _

theorem centralCharacter_unique {f : Subalgebra.center k (MonoidAlgebra k G) → k}
    (hf : ∀ z : Subalgebra.center k (MonoidAlgebra k G),
      ρ.asAlgebraHom (z : MonoidAlgebra k G) = f z • (1 : Module.End k V)) :
    f = centralCharacter ρ := by
  funext z
  have h : (f z • (1 : Module.End k V)) = centralCharacter ρ z • (1 : Module.End k V) := by
    rw [← hf z, asAlgebraHom_center_eq_smul_one]
  exact algebraMap_end_injective ρ
    (by simpa [Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one] using h)

theorem existsUnique_centralCharacter :
    ∃! ω : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k,
      ∀ z : Subalgebra.center k (MonoidAlgebra k G),
        ρ.asAlgebraHom (z : MonoidAlgebra k G) = ω z • (1 : Module.End k V) :=
  ⟨centralCharacter ρ, asAlgebraHom_center_eq_smul_one ρ,
    fun _ hω => DFunLike.coe_injective (centralCharacter_unique ρ hω)⟩

variable [Finite G] [CharZero k]

theorem centralCharacter_conjClassSum (x : G) :
    centralCharacter ρ ⟨conjClassSum k x, conjClassSum_mem_center k x⟩ =
      ((conjClassFinset x).card : k) * ρ.character x / ρ.character 1 := by
  have h := asAlgebraHom_center_eq_smul_one ρ ⟨conjClassSum k x, conjClassSum_mem_center k x⟩
  rw [asAlgebraHom_conjClassSum_eq_smul_one ρ x, ← card_conjClassFinset] at h
  exact algebraMap_end_injective ρ
    (by simpa [Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one] using h.symm)

end Representation

end CFSG.FeitThompson
