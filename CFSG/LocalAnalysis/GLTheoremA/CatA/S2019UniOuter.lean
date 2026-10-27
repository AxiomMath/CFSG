module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalParts
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Outer
import CFSG.RankThree.SteinbergR3EUnitaryFieldDescent
import CFSG.SignalizerFunctorTheorem.NonLocal.UHeisenberg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem commutator_fixSubgroup_primeFormFieldHom_le (h : UnitaryFieldData ℓ f K) (n : ℕ)
    {σ : K ≃+* K} {e : ℕ} (h₀ : UnitaryFieldData ℓ e (fixSubfield σ))
    (hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c) :
    ⁅fixSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ),
        fixSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ)⁆ ≤
      (subfieldPSU h h₀ hbar n).range := by
  have hfix : ∀ g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ∈
        fixSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) →
      ∃ z ∈ Subgroup.center (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
        primeFormFieldSU h isPrimeFormGram_one σ g = g * z := by
    intro g hg
    have hg' : primeFormFieldAut h isPrimeFormGram_one σ
        (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
          (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := hg
    rw [primeFormFieldAut_mk, QuotientGroup.eq] at hg'
    refine ⟨((primeFormFieldSU h isPrimeFormGram_one σ g)⁻¹ * g)⁻¹,
      Subgroup.inv_mem _ (normOneScalars_le_center h _ n hg'), ?_⟩
    rw [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨z, hz, hgz⟩ := hfix g hx
  obtain ⟨z', hz', hgz'⟩ := hfix g' hy
  have key : primeFormFieldSU h isPrimeFormGram_one σ ⁅g, g'⁆ = ⁅g, g'⁆ := by
    rw [map_commutatorElement, hgz, hgz']
    exact commutatorElement_mul_mul_of_central (Subgroup.mem_center_iff.1 hz)
      (Subgroup.mem_center_iff.1 hz')
  have hcσ : glAut σ ((⁅g, g'⁆ : gramSU h _) : GL (Fin n) K) = ⁅g, g'⁆ :=
    congrArg Subtype.val key
  obtain ⟨g₀, hg₀⟩ := exists_subfieldGL_eq_of_fixed n hcσ
  have hg₀mem := mem_gramSU_of_subfieldGL h n h₀ hbar (g₀ := g₀)
    (by rw [hg₀]; exact (⁅g, g'⁆ : gramSU h _).2)
  refine ⟨((⟨g₀, hg₀mem⟩ : gramSU h₀ _) : primeFormP h₀ _), ?_⟩
  rw [subfieldPSU_mk]
  have e1 : (subfieldSU h h₀ hbar n ⟨g₀, hg₀mem⟩ : gramSU h _) = ⁅g, g'⁆ := Subtype.ext hg₀
  rw [e1]
  exact map_commutatorElement (QuotientGroup.mk' (normOneScalars h (gramSU h _) n)) g g'

theorem s2019UniOuter : S2019UniOuter := by
  intro p q hp hp2 hq hq2 hqp f K _ h n hn β hβp hβ
  classical
  haveI := h.finite
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (GL (Fin n) K) := Finite.of_injective (fun g : GL (Fin n) K =>
    (g : Matrix (Fin n) (Fin n) K)) Units.val_injective
  haveI : Finite (primeFormP h (idGram K n)) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hnq : ¬(n = 3 ∧ q ^ f = 2) := by
    rintro ⟨-, h2⟩
    have := hqodd.pow (n := f)
    rw [h2] at this
    exact absurd this (by decide)
  obtain ⟨-, -, -, -, huniq, hfac, -⟩ :=
    unitary_prime_form_full_semilinear_realization h isPrimeFormGram_one hn hnq
  set σ := primeFormFieldFactor h isPrimeFormGram_one hn hnq β with hσdef
  have hσp : σ ^ p = 1 := by rw [hσdef, ← map_pow, hβp, map_one]
  have hσ1 : σ ≠ 1 := by
    intro hσ1
    obtain ⟨φ, ⟨A, hA⟩, -⟩ := huniq β
    have hφ : φ = σ := by rw [hσdef, hA, hfac]
    apply hβ A
    rw [hA, hφ, hσ1, map_one, mul_one]
  have hσord : orderOf σ = p := orderOf_eq_prime hσp hσ1
  have hβ1 : β ≠ 1 := fun h1 => hσ1 (by rw [hσdef, h1, map_one])
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hnq hp hp2
      (Ne.symm hqp) β (orderOf_eq_prime hβp hβ1) σ hσdef.symm hσord
  have hβeq : β = primeFormConjHom h _ M * primeFormFieldHom h isPrimeFormGram_one σ *
      (primeFormConjHom h _ M)⁻¹ := by
    rw [← hM]
    group
  rw [hβeq]
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσord
  have hq₀ : ¬(n = 3 ∧ q ^ (f / p) = 2) := by
    rintro ⟨-, h2⟩
    have := hqodd.pow (n := f / p)
    rw [h2] at this
    exact absurd this (by decide)
  haveI := isSimpleGroup_primeFormP_one (fixSubfield_unitaryFieldData h hp hp2 hσord) hn hq₀
  exact s2019FixCentralizes_conj_of_nonLocalized p _ _ (range_subfieldPSU_le h n _ hbar)
    (commutator_fixSubgroup_primeFormFieldHom_le h n _ hbar)
    (MonoidHom.ofInjective (subfieldPSU_injective h _ hbar n (by omega))).symm.isSimpleGroup
    (CFSG.SignalizerFunctorTheorem.NonLocal.nonLocalized_unitarySubfield h _ hbar hn hq₀)

end CFSG.LocalAnalysis.GLTheoremA.S2019
