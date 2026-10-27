module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.LieArith
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryHeisenberg
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Transfer

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.PartOne.Sec66T
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification.CatLeaf
open scoped commutatorElement

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem commutator_fixed_le_range (h : UnitaryFieldData ℓ f K) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    ⁅fixSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ),
        fixSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ)⁆ ≤
      (primeSubfieldPSU h Nat.prime_three (by decide) hσ n).range := by
  classical
  rw [Subgroup.commutator_le]
  have key : ∀ g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ∈
        fixSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) →
      ∃ c : Kˣ, glAut σ (g : GL (Fin n) K) = (g : GL (Fin n) K) *
        GeneralLinearGroup.scalar (Fin n) c := by
    intro g hg
    have hg' : primeFormFieldAut h (isPrimeFormGram_one (n := n)) σ
        (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = g := hg
    rw [primeFormFieldAut_mk, QuotientGroup.eq] at hg'
    obtain ⟨c, -, -, hc⟩ := hg'
    refine ⟨c⁻¹, ?_⟩
    have h1 : (glAut σ (g : GL (Fin n) K))⁻¹ * (g : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) c := hc
    rw [map_inv]
    exact eq_mul_inv_of_mul_eq (inv_mul_eq_iff_eq_mul.mp h1).symm
  intro x hx y hy
  induction x using QuotientGroup.induction_on with
  | H g =>
  induction y using QuotientGroup.induction_on with
  | H g' =>
  obtain ⟨c, hc⟩ := key g hx
  obtain ⟨d, hd⟩ := key g' hy
  have hbar := fixSubfield_unitaryFieldData_bar h Nat.prime_three (by decide) hσ
  set h₀ := fixSubfield_unitaryFieldData h Nat.prime_three (by decide) hσ with hh₀
  have hw : ((⁅g, g'⁆ : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
      GL (Fin n) K) = ⁅(g : GL (Fin n) K), (g' : GL (Fin n) K)⁆ := rfl
  have hwσ : glAut σ ((⁅g, g'⁆ : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
      GL (Fin n) K) = ((⁅g, g'⁆ : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
      GL (Fin n) K) := by
    rw [hw, map_commutatorElement, hc, hd]
    exact commutatorElement_mul_mul' (GeneralLinearGroup.scalar_commute c _)
      (GeneralLinearGroup.scalar_commute c _).symm.symm (GeneralLinearGroup.scalar_commute d _)
  obtain ⟨g₀, hg₀⟩ := exists_subfieldGL_eq_of_fixed n hwσ
  have hg₀mem : g₀ ∈ gramSU h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ)) :=
    mem_gramSU_of_subfieldGL h n h₀ hbar (g₀ := g₀) (by rw [hg₀]; exact (⁅g, g'⁆).2)
  refine ⟨((⟨g₀, hg₀mem⟩ : gramSU h₀ _) : primeFormP h₀ _), ?_⟩
  change subfieldPSU h h₀ hbar n _ = _
  rw [subfieldPSU_mk]
  change ((subfieldSU h h₀ hbar n ⟨g₀, hg₀mem⟩ : gramSU h _) : primeFormP h _) =
    ((⁅g, g'⁆ : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
      primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
  congr 1
  exact Subtype.ext hg₀

theorem range_eq_commutator_of_perfect {A B : Type*} [Group A] [Group B] [Group.IsPerfect A]
    (j : A →* B) : j.range = ⁅j.range, j.range⁆ := by
  have htop : (⊤ : Subgroup A) = ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ := by
    have := Group.IsPerfect.commutator_eq_top (G := A)
    rw [commutator_def] at this
    exact this.symm
  calc j.range = (⊤ : Subgroup A).map j := MonoidHom.range_eq_map j
    _ = (⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆).map j := by rw [← htop]
    _ = ⁅(⊤ : Subgroup A).map j, (⊤ : Subgroup A).map j⁆ := Subgroup.map_commutator _ _ _
    _ = ⁅j.range, j.range⁆ := by rw [← MonoidHom.range_eq_map]

theorem noL2_of_commutator_solvable {P : Type} [Group P] [Finite P] (ψ : MulAut P)
    (S : Subgroup P) (hcomm : ⁅fixSubgroup ψ, fixSubgroup ψ⁆ ≤ S) (hS : Group.IsSolvable ↥S) :
    NoL2Layer ψ := by
  intro A hA r hr hT
  have hAD : A ≤ fixSubgroup ψ := hA.1
  have hperf : ⁅A, A⁆ = A := glaPComponent_perfect hA
  have hAS : A ≤ S := by
    calc A = ⁅A, A⁆ := hperf.symm
      _ ≤ ⁅fixSubgroup ψ, fixSubgroup ψ⁆ := Subgroup.commutator_mono hAD hAD
      _ ≤ S := hcomm
  haveI : Group.IsSolvable ↥A :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hAS)
  haveI : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.mpr hperf
  haveI : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr (glaPComponent_ne_bot hA)
  exact Group.IsPerfect.not_isSolvable ↥A inferInstance

theorem noL2Layer_fieldAut_psu (hO : LieOrderFormulasInput) (h : UnitaryFieldData ℓ f K)
    (hn : 3 ≤ n) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    NoL2Layer (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) := by
  classical
  have hfin := h.finite
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by decide
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  obtain ⟨h3f, hcard⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
  have hf0 : 1 ≤ f / 3 := by
    have : 3 ≤ f := Nat.le_of_dvd (by have := h.one_le; omega) h3f
    omega
  have hGL : Finite (GL (Fin n) K) :=
    Finite.of_injective (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) Units.val_injective
  have hfinT : Finite (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := inferInstance
  set j := primeSubfieldPSU h hp hp2 hσ n with hj
  have hinj : Function.Injective j := subfieldPSU_injective h h₀ hbar n (by omega)
  have hJC : j.range ≤ fixSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) :=
    range_subfieldPSU_le h n h₀ hbar
  have hCC := commutator_fixed_le_range (n := n) h hσ
  let eJ : primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ)) ≃* ↥j.range := MonoidHom.ofInjective hinj
  by_cases hq0 : n = 3 ∧ ℓ ^ (f / 3) = 2
  ·
    obtain ⟨rfl, hq2⟩ := hq0
    have hcard72 := card_primeFormP_three_two h₀ hq2
    haveI : Group.IsSolvable (primeFormP h₀ ((1 : GL (Fin 3) (fixSubfield σ)) :
        Matrix (Fin 3) (Fin 3) (fixSubfield σ))) :=
      CFSG.SignalizerFunctorTheorem.McBride.UnitaryHeisenberg.isSolvable_of_card_dvd_seventy_two
        (by rw [hcard72])
    haveI : Group.IsSolvable ↥j.range :=
      Group.isSolvable_of_isSolvable_injective (f := eJ.symm.toMonoidHom) eJ.symm.injective
    exact noL2_of_commutator_solvable _ j.range hCC inferInstance
  ·
    have hs₀ := isSimpleGroup_primeFormP_one h₀ hn hq0
    have hnc₀ := not_commute_primeFormP_one h₀ hn hq0
    haveI : IsSimpleGroup (primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
        Matrix (Fin n) (Fin n) (fixSubfield σ))) := hs₀
    haveI : IsSimpleGroup ↥j.range := eJ.symm.isSimpleGroup
    have hnab : ∃ a b : ↥j.range, a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      apply hnc₀
      intro x y
      apply eJ.injective
      rw [map_mul, map_mul]
      exact hcon _ _
    have hperf₀ : Group.IsPerfect (primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
        Matrix (Fin n) (Fin n) (fixSubfield σ))) := by
      have := isPerfect_gramSU_one h₀ hn hq0
      exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    have hJCC : j.range ≤ ⁅fixSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ),
        fixSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ)⁆ := by
      haveI := hperf₀
      calc j.range = ⁅j.range, j.range⁆ := range_eq_commutator_of_perfect j
        _ ≤ _ := Subgroup.commutator_mono hJC hJC
    have hadm₀ : StatedLieAdmissible .PSU n ℓ (f / 3) :=
      ⟨h.prime, hf0, hn, fun hc => hq0 ⟨(Prod.mk.inj hc).1, (Prod.mk.inj hc).2⟩⟩
    have hcard' : Nat.card (fixSubfield σ) = (ℓ ^ (f / 3)) ^ 2 := by
      rw [hcard, ← pow_mul, mul_comm]
    obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h₀
      (isPrimeFormGram_one (n := n) (K := fixSubfield σ))
    have hmodel : LieModel ↥j.range .PSU n ℓ (f / 3) :=
      (lieModel_classical_iff (by decide)).mpr
        ⟨hadm₀, ↥(fixSubfield σ), inferInstance, inferInstance, hcard',
          ⟨(eJ.symm.trans eP).trans (unitaryPSUEquiv h₀ (by omega))⟩⟩
    exact noL2_of_simple_commutator_fixed _ j.range (le_antisymm hJCC hCC) inferInstance hnab
      fun r hr hT => not_typeL2_of_lieModel hO hadm₀ hmodel (by decide) (by simp)
        (center_eq_bot_of_simple hnab) hr hT

end CFSG.HardMathSupport.Dickson.Sec6.I923
