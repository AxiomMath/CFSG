module

public import CFSG.LocalAnalysis.Gross82.OrderThree
public import CFSG.LocalAnalysis.Gross82.OrderThreeArith
public import CFSG.LocalAnalysis.Gross82.OrderThreeTools
public import CFSG.LocalAnalysis.Gross82.OrderThreeDiagonal
public import CFSG.LocalAnalysis.Gross82.FieldOrder

public section

namespace CFSG.LocalAnalysis.Gross82.OrderThree

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

noncomputable def primeFormPToPGL {ℓ f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData ℓ f F)
    (n : ℕ) : primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) →*
      Matrix.ProjGenLinGroup (Fin n) F :=
  QuotientGroup.lift _ (Matrix.ProjGenLinGroup.mk.comp
    (gramSU h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).subtype) (by
      intro g hg
      obtain ⟨c, -, -, hc⟩ := (mem_normOneScalars (m := n)).mp hg
      change Matrix.ProjGenLinGroup.mk (↑g : GL (Fin n) F) = 1
      rw [hc, Matrix.ProjGenLinGroup.mk_scalar])

theorem primeFormPToPGL_injective {ℓ f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData ℓ f F)
    {n : ℕ} (hn : 1 ≤ n) : Function.Injective (primeFormPToPGL h n) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hx' : Matrix.ProjGenLinGroup.mk (↑g : GL (Fin n) F) = 1 := by
      have h := hx
      simp only [primeFormPToPGL, QuotientGroup.lift_mk, MonoidHom.comp_apply] at h
      exact h
    rw [Matrix.ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx'
    obtain ⟨c, hc⟩ := hx'
    have hnorm : h.norm (c : F) = 1 := by
      have h1 := g.2.1
      rw [← hc, GeneralLinearGroup.coe_scalar] at h1
      have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) F => M ⟨0, hn⟩ ⟨0, hn⟩) h1
      simpa [Matrix.scalar_apply, UnitaryFieldData.norm, mul_comm] using h2
    have hcn : c ^ n = 1 := by
      have hdet := g.2.2
      rw [← hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.det_diagonal] at hdet
      exact Units.ext (by simpa using hdet)
    have hgN : g ∈ normOneScalars h (gramSU h ((1 : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F)) n :=
      (mem_normOneScalars (m := n)).mpr ⟨c, hnorm, hcn, hc.symm⟩
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff g).mpr hgN
  · intro hx
    rw [Subgroup.mem_bot] at hx
    rw [MonoidHom.mem_ker, hx, map_one]

theorem primeFormPToPGL_primeFormFieldHom {ℓ f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) (n : ℕ) (σ : F ≃+* F)
    (x : primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
    primeFormPToPGL h n (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ x) =
      CFSG.ComponentClassification.CatalogueBHigherLinearField.pglFieldAut (Fin n) F σ
        (primeFormPToPGL h n x) := by
  refine QuotientGroup.induction_on x fun g => ?_
  rw [show primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ (g : primeFormP h _) =
      ↑(primeFormFieldSU h (isPrimeFormGram_one (n := n)) σ g) from
    primeFormFieldAut_mk h _ σ g]
  simp only [primeFormPToPGL, QuotientGroup.lift_mk, MonoidHom.comp_apply]
  change Matrix.ProjGenLinGroup.mk (((glAut σ) ↑g : GL (Fin n) F)) =
    CFSG.ComponentClassification.CatalogueBHigherLinearField.pglFieldEquiv (Fin n) σ
      (Matrix.ProjGenLinGroup.mk (↑g : GL (Fin n) F))
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearField.pglFieldEquiv_mk]
  rfl

theorem card_fixedSubgroup_primeFormFieldHom_dvd {ℓ f : ℕ} {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData ℓ f F) {n : ℕ} (hn : 1 ≤ n) (σ : F ≃+* F) :
    Nat.card (fixedSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ)) ∣
      lieOrderNumerator .PSL n
        (Nat.card (CFSG.ComponentClassification.CatalogueBHigherLinearField.fixedField F σ)) :=
  calc Nat.card (fixedSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ))
      ∣ Nat.card (fixedSubgroup
          (CFSG.ComponentClassification.CatalogueBHigherLinearField.pglFieldAut (Fin n) F σ)) :=
        card_fixedSubgroup_dvd_of_injective_intertwine (primeFormPToPGL h n)
          (primeFormPToPGL_injective h hn)
          (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ)
          (CFSG.ComponentClassification.CatalogueBHigherLinearField.pglFieldAut (Fin n) F σ)
          (fun x => primeFormPToPGL_primeFormFieldHom h n σ x)
    _ = lieOrderNumerator .PSL n
        (Nat.card (CFSG.ComponentClassification.CatalogueBHigherLinearField.fixedField F σ)) :=
        card_fixedSubgroup_pglFieldAut hn σ

end CFSG.LocalAnalysis.Gross82.OrderThree

namespace CFSG.LocalAnalysis.Gross82

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.ComponentClassification.CatLeaf
  (lieOrderNumerator lieOrderDivisor lieSylowExponent LieOrderFormulasInput)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.HardMathSupport.Lang.Coordinator

private theorem card_fixedSubgroup_dvd_PSU_field {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    {F : Type} [Field F] (h : UnitaryFieldData ℓ f F) (hn : 3 ≤ n)
    (hne' : ¬(n = 3 ∧ ℓ ^ f = 2)) {α : MulAut K}
    {β : MulAut (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))}
    (hβp : β ^ 3 = 1) (hβ1 : β ≠ 1)
    (hcard : Nat.card (fixedSubgroup α) = Nat.card (fixedSubgroup β))
    (hσ1 : primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn hne' β ≠ 1) :
    3 ∣ f ∧ Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .PSL n ((ℓ ^ (f / 3)) ^ 2) := by
  haveI := h.finite
  set σ := primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn hne' β with hσdef
  have hσne : σ ≠ 1 := by rw [hσdef]; exact hσ1
  have hσp : σ ^ 3 = 1 := by rw [hσdef, ← map_pow, hβp, map_one]
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσp hσne
  have hβord : orderOf β = 3 := orderOf_eq_prime hβp hβ1
  obtain ⟨hpf, hcardσ, -, -, -, M, hM⟩ :=
    unitary_prime_semilinear_field_descent' h hn hne' Nat.prime_three (by norm_num) β hβord σ
      hσdef.symm hσord
  set u := primeFormConjHom h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) M with hu
  set fσ := primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ with hfσ
  have hβu : β * u = u * fσ := by
    rw [← hM]
    group
  have hcard1 : Nat.card (fixedSubgroup β) = Nat.card (fixedSubgroup fσ) :=
    (card_fixedSubgroup_eq_of_intertwine (u : _ ≃* _) fσ β fun x =>
      congrArg (fun g : MulAut _ => g x) hβu).symm
  refine ⟨hpf, ?_⟩
  rw [hcard, hcard1, hfσ, ← hcardσ,
    ← OrderThree.card_fixedField_eq_card_semilinearFixedSubfield]
  exact OrderThree.card_fixedSubgroup_primeFormFieldHom_dvd h (by omega) σ

private theorem false_of_PSU_field {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hLie : LieOrderFormulasInput) (hadm : StatedLieAdmissible .PSU n ℓ f)
    (hmodel : CFSG.Blueprint.LieModel K .PSU n ℓ f) {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) (hℓ : ℓ.Prime) (hn : 3 ≤ n)
    (hne' : ¬(n = 3 ∧ ℓ ^ f = 2)) {α : MulAut K} (P : Sylow 3 K)
    (hfix : ∀ x ∈ (P : Subgroup K), α x = x) (h3q : 3 ∣ ℓ ^ f + 1)
    {β : MulAut (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))}
    (hβp : β ^ 3 = 1) (hβ1 : β ≠ 1)
    (hcard : Nat.card (fixedSubgroup α) = Nat.card (fixedSubgroup β))
    (hσ1 : primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn hne' β ≠ 1) :
    False := by
  obtain ⟨hpf, hC⟩ := card_fixedSubgroup_dvd_PSU_field h hn hne' hβp hβ1 hcard hσ1
  have hf3 : 0 < f / 3 :=
    Nat.div_pos (Nat.le_of_dvd (by have := h.one_le; omega) hpf) (by norm_num)
  have hs : ℓ ^ f = (ℓ ^ (f / 3)) ^ 3 := by rw [← pow_mul, Nat.div_mul_cancel hpf]
  have hs2 : 2 ≤ ℓ ^ (f / 3) := hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
  have h3s : 3 ∣ ℓ ^ (f / 3) + 1 := by
    refine (CFSG.AGLEmbedding.OuterSylow.Stp.dvd_pow_add_one_iff (p := 3)).1 ?_
    rw [← hs]
    exact h3q
  have hN : 1 ≤ lieSylowExponent .PSL n := by
    simp only [lieSylowExponent]
    exact Nat.div_pos (Nat.mul_le_mul (by omega : 2 ≤ n) (by omega : 1 ≤ n - 1))
      (by norm_num)
  have ha : lieOrderNumerator .PSL n ((ℓ ^ (f / 3)) ^ 2) ≠ 0 :=
    CFSG.AGLEmbedding.OuterSylow.lieOrderNumerator_ne_zero (by decide) hN
      (hs2.trans (Nat.le_self_pow (by norm_num : 2 ≠ 0) _))
  have hlt : padicValNat 3 (lieOrderNumerator .PSL n ((ℓ ^ (f / 3)) ^ 2)) +
      padicValNat 3 (lieOrderDivisor .PSU n ((ℓ ^ (f / 3)) ^ 3)) <
      padicValNat 3 (lieOrderNumerator .PSU n ((ℓ ^ (f / 3)) ^ 3)) := by
    rw [OrderThree.padicValNat_three_lieOrder_psl_sq_eq_psu hs2 h3s]
    exact FieldOrder.padicValNat_three_lieOrder_psu_cube_lt hs2 (by omega)
  exact OrderThree.false_of_card_fixedSubgroup_dvd hLie hadm hmodel P hfix hs ha hC hlt

theorem grossThreeInnerOrderThree_PSU (hLie : LieOrderFormulasInput) {K : Type} [Group K]
    [Finite K] {n ℓ f : ℕ} (hadm : StatedLieAdmissible .PSU n ℓ f)
    (hmodel : CFSG.Blueprint.LieModel K .PSU n ℓ f)
    (h3 : 3 ∣ lieOrderDivisor .PSU n (ℓ ^ f)) : GrossThreeInnerOrderThree K := by
  intro α hα3 P hfix
  by_contra hαin
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcl : StatedClassicalModel K .PSU n ℓ f := hmodel.statedClassicalModel (by decide)
  obtain ⟨⟨hℓ, hf, hn, hne⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  have hne' : ¬(n = 3 ∧ ℓ ^ f = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  have h : UnitaryFieldData ℓ f F := ⟨hℓ, hf, by rw [hFcard, ← pow_mul, mul_comm]⟩
  haveI := h.finite
  have h3' : 3 ∣ Nat.gcd n (ℓ ^ f + 1) := h3
  have h3n : 3 ∣ n := h3'.trans (Nat.gcd_dvd_left n (ℓ ^ f + 1))
  have h3q : 3 ∣ ℓ ^ f + 1 := h3'.trans (Nat.gcd_dvd_right n (ℓ ^ f + 1))
  obtain ⟨θ⟩ : Nonempty (K ≃* primeFormP h ((1 : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F)) :=
    ⟨(e.trans (unitaryPSUEquiv h (by omega)).symm).trans
      (Classical.choice (unitary_prime_form_full_semilinear_realization h
        (isPrimeFormGram_one (n := n)) hn hne').1).symm⟩
  set β := MulAut.congr θ α with hβdef
  have hβp : β ^ 3 = 1 := by rw [hβdef, ← map_pow, hα3, map_one]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (primeFormP h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :=
    fun hin => hαin ((congr_mem_inner_iff θ α).mp hin)
  obtain ⟨P', hfix'⟩ := OrderThree.exists_sylow_fix_congr θ P hfix
  by_cases hσ1 : primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn hne' β = 1
  · have hD : β ∈ primeFormD h ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      rw [← ker_primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn hne']
      exact hσ1
    exact hβout (OrderThree.mem_inner_of_mem_primeFormD_of_fix_sylow h (by norm_num) hn h3n
      h3q P' β hD ⟨1, by simpa using hβp⟩ hfix')
  · have hβ1 : β ≠ 1 := fun h1 =>
      hβout (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
    have hcard : Nat.card (fixedSubgroup α) = Nat.card (fixedSubgroup β) :=
      (card_fixedSubgroup_congr θ α).symm
    exact false_of_PSU_field hLie hadm hmodel h hℓ hn hne' P hfix h3q hβp hβ1 hcard hσ1

end CFSG.LocalAnalysis.Gross82
