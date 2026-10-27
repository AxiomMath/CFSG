module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SUFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.UnitaryAut
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CentralQuotient

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.Classical (subfieldSU exists_subfieldGL_eq_of_fixed mem_gramSU_of_subfieldGL
  subfieldSU_injective fixSubfield_unitaryFieldData fixSubfield_unitaryFieldData_bar
  card_primeFormP_three_two)
open CFSG.LieType.Chevalley (fixSubfield)

section Helpers

variable {ℓ f n : ℕ} {K : Type} [Field K]

private theorem fixSubgroup_primeFormFieldSU_eq_range (h : UnitaryFieldData ℓ f K)
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

private theorem nonempty_statedSU_mulEquiv_fixSubgroup (h : UnitaryFieldData ℓ f K)
    {e : ℕ} {σ : K ≃+* K} (h₀ : UnitaryFieldData ℓ e (fixSubfield σ))
    (hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c)
    (hC : IsPrimeFormGram (1 : GL (Fin n) K)) :
    Nonempty (↥(CFSG.Open.StatedSU n (ℓ ^ e) (fixSubfield σ)) ≃*
      ↥(fixSubgroup (primeFormFieldSU h hC σ))) :=
  ⟨((MulEquiv.subgroupCongr (unitarySU_eq_gramSU h₀ n)).trans
    (MonoidHom.ofInjective (subfieldSU_injective h h₀ hbar n))).trans
    (MulEquiv.subgroupCongr (fixSubgroup_primeFormFieldSU_eq_range h h₀ hbar hC).symm)⟩

private theorem isSolvable_gramSU_three_two {e : ℕ} {k : Type} [Field k]
    (h₀ : UnitaryFieldData ℓ e k) (hq2 : ℓ ^ e = 2) :
    Group.IsSolvable ↥(gramSU h₀ ((1 : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) := by
  have h72 := card_primeFormP_three_two h₀ hq2
  have : Finite (primeFormP h₀ ((1 : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) :=
    Nat.finite_of_card_ne_zero (by rw [h72]; norm_num)
  have hP : Group.IsSolvable (primeFormP h₀ ((1 : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k)) :=
    isSolvable_of_card_primeFactors_le_two (by
      rw [h72, show (72 : ℕ) = 2 ^ 3 * 3 ^ 2 by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
      decide)
  have hZ : Group.IsSolvable ↥(normOneScalars h₀ (gramSU h₀ ((1 : GL (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k)) 3) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subtype.ext (by
      have := Subgroup.mem_center_iff.1 (normOneScalars_le_center h₀ _ 3 a.2) b.1
      exact congrArg Subtype.val this.symm))
  exact Group.isSolvable_of_ker_le_range (normOneScalars h₀ _ 3).subtype
    (QuotientGroup.mk' (normOneScalars h₀ (gramSU h₀ ((1 : GL (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k)) 3))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem unitary_fieldAut_components (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hC : IsPrimeFormGram (1 : GL (Fin n) K)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {σ : K ≃+* K} (hσ : orderOf σ = p)
    (K' : Subgroup (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (hK' : CFSG.Open.IsComponentOf K' (fixSubgroup (primeFormFieldHom h hC σ))) :
    ¬ (n = 3 ∧ ℓ ^ (f / p) = 2) ∧
      ∃ g : ↥(CFSG.Open.StatedSU n (ℓ ^ (f / p)) (fixSubfield σ)) →* ↥K',
        Function.Surjective g ∧ g.ker ≤ Subgroup.center _ := by
  haveI := h.finite
  have h₀ : UnitaryFieldData ℓ (f / p) (fixSubfield σ) :=
    fixSubfield_unitaryFieldData h hp hp2 hσ
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  obtain ⟨e⟩ := nonempty_statedSU_mulEquiv_fixSubgroup h h₀ hbar hC
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
  by_cases hq₀ : n = 3 ∧ ℓ ^ (f / p) = 2
  · exfalso
    obtain ⟨hn3, hq2⟩ := hq₀
    subst hn3
    haveI := isSolvable_gramSU_three_two h₀ hq2
    haveI : Group.IsSolvable ↥(CFSG.Open.StatedSU 3 (ℓ ^ (f / p)) (fixSubfield σ)) :=
      Group.isSolvable_of_surjective
        (f := (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h₀ 3)).symm.toMonoidHom)
        (MulEquiv.surjective _)
    haveI : Group.IsSolvable ↥(fixSubgroup α) :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    obtain ⟨i, -⟩ := components_of_centralQuotient π hπ hker α _ hαβ (fun i : Empty => i.elim)
      (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (MonoidHom.id ↥(fixSubgroup α))
      (fun x hx => by
        have hx1 : x = 1 := hx
        rw [hx1]
        exact Subgroup.one_mem _) K' hK'
    exact i.elim
  · refine ⟨hq₀, ?_⟩
    haveI : Fact ℓ.Prime := ⟨h.prime⟩
    haveI : Finite (fixSubfield σ) := inferInstance
    have hcard : Nat.card (fixSubfield σ) = (ℓ ^ (f / p)) ^ 2 := by
      rw [h₀.card, ← pow_mul, mul_comm]
    have hq : CFSG.IsQuasisimple ↥(fixSubgroup α) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e
        (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hcard hn
          (fun heq => hq₀ ⟨(Prod.mk.inj heq).1, (Prod.mk.inj heq).2⟩)).1
    obtain ⟨-, hKi⟩ := components_of_centralQuotient π hπ hker α _ hαβ
      (fun _ : Unit => fixSubgroup α) (fun _ => le_rfl)
      (fun _ c hc g hg => (fixSubgroup α).mul_mem ((fixSubgroup α).mul_mem hc hg)
        ((fixSubgroup α).inv_mem hc))
      (fun _ => hq) (1 : ↥(fixSubgroup α) →* Unit)
      (fun x _ => Subgroup.mem_iSup_of_mem (ι := Unit) () x.2) K' hK'
    subst hKi
    refine ⟨(π.subgroupMap (fixSubgroup α)).comp e.toMonoidHom,
      (MonoidHom.subgroupMap_surjective _ _).comp e.surjective, fun y hy => ?_⟩
    have h1 : π (e y : ↥X) = 1 := congrArg Subtype.val hy
    have h2 : (e y : ↥X) ∈ Subgroup.center ↥X := hker h1
    rw [Subgroup.mem_center_iff]
    intro y'
    apply e.injective
    rw [map_mul, map_mul]
    exact Subtype.ext (Subgroup.mem_center_iff.1 h2 (e y'))

theorem unitary_fixSubfield_lieFactorData (hSU : SUFactorFacts) (h : UnitaryFieldData ℓ f K)
    (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {σ : K ≃+* K} (hσ : orderOf σ = p) :
    ¬ (n = 3 ∧ ℓ ^ (f / p) = 2) →
      LieFactorData ℓ ↥(CFSG.Open.StatedSU n (ℓ ^ (f / p)) (fixSubfield σ)) := by
  intro hne
  haveI := h.finite
  have h₀ : UnitaryFieldData ℓ (f / p) (fixSubfield σ) :=
    fixSubfield_unitaryFieldData h hp hp2 hσ
  haveI : Fintype (fixSubfield σ) := Fintype.ofFinite _
  have hcard : Fintype.card (fixSubfield σ) = (ℓ ^ (f / p)) ^ 2 := by
    rw [Fintype.card_eq_nat_card, h₀.card, ← pow_mul, mul_comm]
  have hchar : ringChar (fixSubfield σ) = ℓ := by
    haveI := h.charP
    rw [Algebra.ringChar_eq (fixSubfield σ) K]
    exact ringChar.eq K ℓ
  have := hSU (fixSubfield σ) n (ℓ ^ (f / p)) hcard hn
    (fun heq => hne ⟨(Prod.mk.inj heq).1, (Prod.mk.inj heq).2⟩)
  rwa [hchar] at this

end Helpers

theorem lieCompExport_primeFormFieldHom (hSU : SUFactorFacts) (hSU6 : SUAltSixFacts)
    {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hC : IsPrimeFormGram (1 : GL (Fin n) K)) (σ : K ≃+* K) (hσ : orderOf σ = 3) :
    LieCompExport ℓ (primeFormFieldHom h hC σ) := by
  haveI := h.finite
  have h₀ : UnitaryFieldData ℓ (f / 3) (fixSubfield σ) :=
    fixSubfield_unitaryFieldData h Nat.prime_three (by norm_num) hσ
  haveI : Fintype (fixSubfield σ) := Fintype.ofFinite _
  have hcard : Fintype.card (fixSubfield σ) = (ℓ ^ (f / 3)) ^ 2 := by
    rw [Fintype.card_eq_nat_card, h₀.card, ← pow_mul, mul_comm]
  have hLF := unitary_fixSubfield_lieFactorData hSU h hn Nat.prime_three (by norm_num) hσ
  refine ⟨LieSemisimple.perfectInLayer_primeFormFieldHom h hn Nat.prime_three (by norm_num) σ hσ,
    fun K' hK' => ?_, fun ⟨K', hK', ⟨a⟩⟩ => ?_⟩
  · obtain ⟨hne, g, hg, hgk⟩ :=
      unitary_fieldAut_components h hn hC Nat.prime_three (by norm_num) hσ K' hK'
    exact ⟨_, inferInstance, inferInstance, hLF hne, g, hg, hgk⟩
  · exfalso
    obtain ⟨hne, g, hg, hgk⟩ :=
      unitary_fieldAut_components h hn hC Nat.prime_three (by norm_num) hσ K' hK'
    have hX := hLF hne
    obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hX.perfect g hg hgk
    exact (hSU6 (fixSubfield σ) n (ℓ ^ (f / 3)) hcard hn).false (e.trans a)

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
