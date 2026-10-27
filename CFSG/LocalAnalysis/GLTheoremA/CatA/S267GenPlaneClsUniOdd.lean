module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsSpOrth
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitUnitaryBlocks
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CentralQuotient
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryFieldExport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks
  (exists_good_block_of_component primaryData_toLin' toLinSU toLinSU_mem_unitaryCentralizer)
open CFSG.RankThree.Classical (subfieldSU exists_subfieldGL_eq_of_fixed mem_gramSU_of_subfieldGL
  subfieldSU_injective fixSubfield_unitaryFieldData fixSubfield_unitaryFieldData_bar)
open CFSG.LieType.Chevalley (fixSubfield)

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem eq_one_of_mem_normOneScalars_of_not_dvd (h : UnitaryFieldData ℓ f K) {p : ℕ}
    (hp : p.Prime) (hpQ : ¬ p ∣ ℓ ^ f + 1) {C : Matrix (Fin n) (Fin n) K} {z : gramSU h C}
    (hz : z ∈ normOneScalars h (gramSU h C) n) (hzp : z ^ p = 1) : z = 1 := by
  obtain ⟨c, hc, -, hzc⟩ := hz
  have hcQ : c ^ (ℓ ^ f + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ, ← UnitaryFieldData.bar_apply,
      mul_comm, ← UnitaryFieldData.norm]
    exact hc
  have hzQ : z ^ (ℓ ^ f + 1) = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, hzc, ← map_pow, hcQ, map_one, OneMemClass.coe_one]
  have hcop : Nat.Coprime p (ℓ ^ f + 1) := (Nat.coprime_or_dvd_of_prime hp _).resolve_right hpQ
  have h1 : z ^ Nat.gcd p (ℓ ^ f + 1) = 1 := pow_gcd_eq_one.2 ⟨hzp, hzQ⟩
  rwa [hcop, pow_one] at h1

theorem compNormal_primeFormConjHom_of_not_dvd (h : UnitaryFieldData ℓ f K) {p : ℕ}
    (hp : p.Prime) (hpℓ : p ≠ ℓ) (hpQ : ¬ p ∣ ℓ ^ f + 1) (A : primeFormUnitary h (idGram K n))
    {c : Kˣ} (hA : (A : GL (Fin n) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    CompNormal (primeFormConjHom h (idGram K n) A) := by
  classical
  haveI := h.finite
  have hq : 2 ≤ ℓ ^ f := by
    have := Nat.one_lt_pow (by have := h.one_le; omega : f ≠ 0) h.prime.one_lt
    omega
  set X := gramSU h (idGram K n)
  set α : MulAut ↥X := primeFormConjSU h (idGram K n) A with hαdef
  let π : ↥X →* primeFormP h (idGram K n) := QuotientGroup.mk' (normOneScalars h X n)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hαβ : ∀ x, π (α x) = primeFormConjHom h (idGram K n) A (π x) := fun x =>
    (primeFormConjAut_mk h (idGram K n) A x).symm
  have hαp : α ^ p = 1 := by
    refine MulEquiv.ext fun g => Subtype.ext ?_
    have hpow : ∀ m : ℕ, (((α ^ m) g : ↥X) : GL (Fin n) K) =
        (A : GL (Fin n) K) ^ m * g * ((A : GL (Fin n) K) ^ m)⁻¹ := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', MulAut.mul_apply]
        change (A : GL (Fin n) K) * (((α ^ m) g : ↥X) : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ = _
        rw [ih]
        group
    rw [hpow, hA, (commute_scalar c (g : GL (Fin n) K)).eq.symm, mul_inv_cancel_right]
    rfl
  have hαZ : ∀ z ∈ π.ker, α z = z := by
    intro z hz
    rw [QuotientGroup.ker_mk'] at hz
    obtain ⟨d, -, -, hzd⟩ := hz
    apply Subtype.ext
    change (A : GL (Fin n) K) * z * (A : GL (Fin n) K)⁻¹ = z
    rw [hzd, (commute_scalar d (A : GL (Fin n) K)).eq, mul_inv_cancel_right]
  have hZp : ∀ z ∈ π.ker, z ^ p = 1 → z = 1 := by
    intro z hz hzp
    rw [QuotientGroup.ker_mk'] at hz
    exact eq_one_of_mem_normOneScalars_of_not_dvd h hp hpQ hz hzp
  have H := primaryData_toLin' h A.2 hp hpℓ hA
  set x : LinearMap.GeneralLinearGroup K (Fin n → K) :=
    Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) with hxdef
  refine compNormal_of_lift π hπ α _ hαβ hαp hαZ hZp
    (fun a : {a : CFSG.RankThree.PartOne.KCPrimary.primaryFactors (x : Module.End K (Fin n → K)) //
        CFSG.RankThree.PartOne.KCUnitary.IsGoodBlock h x a} =>
      (CFSG.RankThree.PartOne.KCUnitary.specialBlock (idForm h n) x (a.1 : Polynomial K)).comap
        (toLinSU h n)) ?_ ?_
  · intro a g hg u hu
    rw [Subgroup.mem_comap] at hu ⊢
    rw [map_mul, map_mul, map_inv]
    exact CFSG.RankThree.PartOne.KCUnitary.conj_mem_specialBlock
      (toLinSU_mem_unitaryCentralizer A hxdef hg) hu
  · intro T hT
    obtain ⟨a, ha⟩ := exists_good_block_of_component hq A hxdef H T hT
    exact ⟨a, ha⟩

private theorem fixSubgroup_primeFormFieldSU_eq_range_subfieldSU (h : UnitaryFieldData ℓ f K)
    {e : ℕ} {σ : K ≃+* K} (h₀ : UnitaryFieldData ℓ e (fixSubfield σ))
    (hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c)
    (hC : IsPrimeFormGram (1 : GL (Fin n) K)) :
    fixSubgroup (primeFormFieldSU h hC σ) = (subfieldSU h h₀ hbar n).range := by
  ext x
  rw [mem_fixSubgroup]
  constructor
  · intro hx
    have hx' : glAut σ (x : GL (Fin n) K) = x := congrArg Subtype.val hx
    obtain ⟨g₀, hg₀⟩ := exists_subfieldGL_eq_of_fixed n hx'
    have hg₀S := mem_gramSU_of_subfieldGL h n h₀ hbar (hg₀ ▸ x.2)
    exact ⟨⟨g₀, hg₀S⟩, Subtype.ext hg₀⟩
  · rintro ⟨y, rfl⟩
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    change σ ((((y : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)) i j :
      fixSubfield σ) : K) = (((y : GL (Fin n) (fixSubfield σ)) :
        Matrix (Fin n) (Fin n) (fixSubfield σ)) i j : K)
    exact (((y : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)) i j).2

private theorem isQuasisimple_fixSubgroup_primeFormFieldSU (h : UnitaryFieldData ℓ f K)
    (hn : 3 ≤ n) (hC : IsPrimeFormGram (1 : GL (Fin n) K)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {σ : K ≃+* K} (hσ : orderOf σ = p) (hq₀ : ¬ (n = 3 ∧ ℓ ^ (f / p) = 2)) :
    IsQuasisimple ↥(fixSubgroup (primeFormFieldSU h hC σ)) := by
  haveI := h.finite
  have h₀ : UnitaryFieldData ℓ (f / p) (fixSubfield σ) :=
    fixSubfield_unitaryFieldData h hp hp2 hσ
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  have hcard : Nat.card (fixSubfield σ) = (ℓ ^ (f / p)) ^ 2 := by
    rw [h₀.card, ← pow_mul, mul_comm]
  let e : ↥(CFSG.Open.StatedSU n (ℓ ^ (f / p)) (fixSubfield σ)) ≃*
      ↥(fixSubgroup (primeFormFieldSU h hC σ)) :=
    ((MulEquiv.subgroupCongr (unitarySU_eq_gramSU h₀ n)).trans
      (MonoidHom.ofInjective (subfieldSU_injective h h₀ hbar n))).trans
      (MulEquiv.subgroupCongr (fixSubgroup_primeFormFieldSU_eq_range_subfieldSU h h₀ hbar hC).symm)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hcard hn
      (fun heq => hq₀ ⟨(Prod.mk.inj heq).1, (Prod.mk.inj heq).2⟩)).1

theorem compNormal_primeFormFieldHom (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {σ : K ≃+* K} (hσ : orderOf σ = p) :
    CompNormal (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) := by
  classical
  haveI := h.finite
  set hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  set X := gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  set α : MulAut ↥X := primeFormFieldSU h hC σ
  let π : ↥X →* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    QuotientGroup.mk' (normOneScalars h X n)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥X := by
    rw [QuotientGroup.ker_mk']
    exact normOneScalars_le_center h _ n
  have hαβ : ∀ x, π (α x) = primeFormFieldHom h hC σ (π x) := fun x =>
    (primeFormFieldAut_mk h hC σ x).symm
  refine compNormal_of_unique _ fun K₁ K₂ h₁ h₂ => ?_
  have hq₀ := (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.unitary_fieldAut_components h hn hC
    hp hp2 hσ K₁ h₁).1
  have hq := isQuasisimple_fixSubgroup_primeFormFieldSU h hn hC hp hp2 hσ hq₀
  have hcomp : ∀ K' : Subgroup (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
      IsComponentOf K' (fixSubgroup (primeFormFieldHom h hC σ)) →
        K' = (fixSubgroup α).map π := fun K' hK' => by
    obtain ⟨-, hKi⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_centralQuotient
      π hπ hker α _ hαβ (fun _ : Unit => fixSubgroup α) (fun _ => le_rfl)
      (fun _ c hc g hg => (fixSubgroup α).mul_mem ((fixSubgroup α).mul_mem hc hg)
        ((fixSubgroup α).inv_mem hc))
      (fun _ => hq) (1 : ↥(fixSubgroup α) →* Unit)
      (fun x _ => Subgroup.mem_iSup_of_mem (ι := Unit) () x.2) K' hK'
    exact hKi
  rw [hcomp K₁ h₁, hcomp K₂ h₂]

theorem compNormal_primeFormP_of_not_dvd (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hpQ : ¬ p ∣ ℓ ^ f + 1) (β : MulAut (primeFormP h (idGram K n))) (hβ : β ^ p = 1) :
    CompNormal β := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, hker1, -, -, -, -, hkerD, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  by_cases hσ : primeFormFieldFactor h hC hn hq β = 1
  · have hβD : β ∈ (primeFormFieldFactor h hC hn hq).ker := hσ
    rw [hkerD, primeFormD, MonoidHom.mem_range] at hβD
    obtain ⟨A, rfl⟩ := hβD
    have h1 : primeFormPsi h hC ⟨A ^ p, 1⟩ = 1 := by
      rw [primeFormPsi_apply, map_pow, hβ, map_one, one_mul]
    obtain ⟨-, c, -, hc⟩ := (hker1 _).1 h1
    exact compNormal_primeFormConjHom_of_not_dvd h hp hpℓ hpQ A
      (by rwa [SubgroupClass.coe_pow] at hc)
  · have : Fact p.Prime := ⟨hp⟩
    have hne : β ≠ 1 := fun h1 => hσ (by rw [h1, map_one])
    have hord : orderOf β = p := orderOf_eq_prime hβ hne
    have hσp : orderOf (primeFormFieldFactor h hC hn hq β) = p :=
      orderOf_eq_prime (by rw [← map_pow, hβ, map_one]) hσ
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hq hp hp2 hpℓ β
        hord _ rfl hσp
    refine CompNormal.of_conj (primeFormConjHom h _ M)⁻¹ ?_
    rw [inv_inv, hM]
    exact compNormal_primeFormFieldHom h hn hp hp2 hσp

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen

end
