module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupSevenWeakDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupSevenWeakSpor
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupSevenLie

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Sporadic.Schreier (fixSub)

@[expose] def WeakA7FixedLookup : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) → Catalog S →
    ∀ σ : MulAut S, σ * σ = 1 → σ ≠ 1 → ∀ B : Subgroup (fixedSubgroup σ), IsComponent B →
      Nonempty (B ≃* alternatingGroup (Fin 7)) →
        ∃ N : ℕ, Nonempty (S ≃* alternatingGroup (Fin N))

theorem weakA7Lookup_of_fixed (h : WeakA7FixedLookup) : WeakA7Lookup := by
  intro A _ _ W _ hWs hWnab hCW hcat a ha B hBW hBcomp hBm
  obtain ⟨B', hB', ⟨φ⟩⟩ := exists_isComponent_fixSub_of_le (a := a) hBW hBcomp
  have hσ2 : (MulAut.conjNormal a : MulAut W) * MulAut.conjNormal a = 1 :=
    conjNormal_mul_self ha
  have hσ1 : (MulAut.conjNormal a : MulAut W) ≠ 1 := by
    intro h1
    have h2 : a ∈ centralizer (W : Set A) := by
      rw [mem_centralizer_iff]
      intro w hw
      have h3 := congrArg (fun φ : MulAut W => ((φ ⟨w, hw⟩ : W) : A)) h1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
      calc w * a = a * w * a⁻¹ * a := by rw [h3]
        _ = a * w := by group
    rw [hCW, mem_bot] at h2
    rw [h2, orderOf_one] at ha
    omega
  have hfix : fixSub (MulAut.conjNormal a : MulAut W) = fixedSubgroup (MulAut.conjNormal a) := by
    ext x
    exact Iff.rfl
  let ψ := MulEquiv.subgroupCongr hfix
  exact h W hWs hWnab hcat _ hσ2 hσ1 (B'.map ψ.toMonoidHom)
    (CFSG.LocalCores.isComponent_map_mulEquiv ψ hB')
    ⟨(B'.equivMapOfInjective ψ.toMonoidHom ψ.injective).symm.trans (φ.trans hBm.some)⟩


theorem weakA7FixedLookup_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) (hEO : EvenLieOuterTwoComponentsInput) : WeakA7FixedLookup := by
  intro S _ _ hS hna hcat σ hσ2 hσ1 B hB ⟨eB⟩
  have hσo : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσ2) hσ1
  rcases (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat with
    ⟨n, -, hA⟩ | hodd | heven | hsp
  · exact ⟨n, hA⟩
  · exact absurd ⟨eB⟩ (not_alt7_of_oddLieType hGLS hO hodd hσo hB)
  · exact (false_of_evenLie_alt7 hO hEO hna heven hσ2 hσ1 hB eB).elim
  · exact (false_of_sporadic_alt7_weak hS hna hsp hσo hB eB).elim

theorem weakA7Lookup_of_inputs (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) (hEO : EvenLieOuterTwoComponentsInput) : WeakA7Lookup :=
  weakA7Lookup_of_fixed (weakA7FixedLookup_of_inputs hGLS hO hEO)

end CFSG.OddStandard.AltStdSec
