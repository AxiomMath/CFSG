module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupEven
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupSporOrd
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupSporA
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupSporB
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupSporC
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupSporSuz

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Sporadic.Schreier (fixSub)

@[expose] def AltFixedLookup : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) → Catalog S →
    ∀ σ : MulAut S, σ * σ = 1 → σ ≠ 1 → ∀ B : Subgroup (fixedSubgroup σ), IsComponent B →
      ∀ m : ℕ, 9 ≤ m → Nonempty (B ≃* alternatingGroup (Fin m)) →
        (∃ N : ℕ, Nonempty (S ≃* alternatingGroup (Fin N))) ∨
          (m = 10 ∧ Nonempty (S ≃* NativeSporadic.HN))

theorem altComponentLookup_of_fixed (h : AltFixedLookup) : AltComponentLookup := by
  intro A _ _ W _ hWs hWnab hCW hcat a ha B hBW hBcomp m hm hBm
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
    (CFSG.LocalCores.isComponent_map_mulEquiv ψ hB') m hm
    ⟨(B'.equivMapOfInjective ψ.toMonoidHom ψ.injective).symm.trans (φ.trans hBm.some)⟩


theorem altFixedLookup_of_inputs
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hEO : EvenLieOuterTwoComponentsInput) (hCo1 : Co1LocalComponentsInput)
    (hHN : HNLocalComponentsInput) (hFour : FourExactOuterInput) (hLy : LyOuterTrivialInput)
    (hFi22 : Fi22OuterComponentsInput) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) : AltFixedLookup := by
  intro S _ _ hS hna hcat σ hσ2 hσ1 B hB m hm hBm
  have hAlt : IsLargeAlt B := ⟨m, hm, hBm⟩
  rcases (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat with
    ⟨n, -, hA⟩ | hodd | heven | ⟨s, ⟨e⟩⟩
  · exact Or.inl ⟨n, hA⟩
  · exact absurd hAlt (not_largeAlt_of_oddLieType hGLS hO hodd
      (orderOf_eq_prime (by rw [sq]; exact hσ2) hσ1) hB)
  · exact Or.inl (fixed_lookup_evenLie hGLS hO hEO hna heven hσ2 hσ1 hB hAlt)
  · by_cases hsHN : s = .HN
    · subst hsHN
      exact Or.inr (fixed_lookup_HN hHN hFour hna e hσ2 hσ1 hB hm hBm)
    · exfalso
      have hdata : NoLargeAltComponents s := by
        cases s with
        | M11 | M12 | M22 | M23 | M24 | J1 | J2 | J3 | J4 | HS | He | Ru =>
          exact noLargeAlt_of_order (by simp)
        | McL => exact noLargeAlt_McL
        | Co1 => exact noLargeAlt_Co1 hCo1
        | Co2 => exact noLargeAlt_Co2
        | Co3 => exact noLargeAlt_Co3
        | Th => exact noLargeAlt_Th
        | Fi22 => exact noLargeAlt_Fi22 hFi22
        | Fi23 => exact noLargeAlt_Fi23
        | Fi24Prime =>
          exact noLargeAlt_Fi24 Sporadic.FischerOddCore.fi24primeOuterComponentsInput_holds
        | Ly => exact noLargeAlt_Ly hLy
        | B => exact noLargeAlt_B
        | M => exact noLargeAlt_M hMinn hMcomp
        | Suz => exact noLargeAlt_Suz
        | ONan => exact noLargeAlt_ON
        | HN => exact absurd rfl hsHN
      exact false_of_noLargeAlt hdata hna e hσ2 hσ1 hB hAlt

theorem altComponentLookup_of_inputs
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hEO : EvenLieOuterTwoComponentsInput) (hCo1 : Co1LocalComponentsInput)
    (hHN : HNLocalComponentsInput) (hFour : FourExactOuterInput) (hLy : LyOuterTrivialInput)
    (hFi22 : Fi22OuterComponentsInput) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) : AltComponentLookup :=
  altComponentLookup_of_fixed
    (altFixedLookup_of_inputs hGLS hO hEO hCo1 hHN hFour hLy hFi22 hMinn hMcomp)

end CFSG.OddStandard.AltStdSec
