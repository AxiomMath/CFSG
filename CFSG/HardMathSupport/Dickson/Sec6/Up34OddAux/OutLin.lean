module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Layer
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnFieldAut
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PslBadAux.Layer
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.Sec66T
  CFSG.ComponentClassification.RankTwoClassical
  CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
  CFSG.ComponentClassification.CatLeaf CFSG.HardMathSupport.Dickson.Sec6.I923
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs CFSG.LocalAnalysis.GLTheoremB
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open Matrix CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.Classical CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.Coordinator
open scoped commutatorElement

section PslGood

theorem noL34Layer_fieldAut_psl (hO : LieOrderFormulasInput) {n : ℕ} (hn3 : 3 ≤ n) {K : Type}
    [Field K] [Finite K] {σ : K ≃+* K} (hσ : orderOf σ = 3)
    (hcop : Nat.Coprime 3 (Nat.gcd n (Nat.card K - 1))) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) : NoL34Layer (fieldAut n K σ) := by
  set k := semilinearFixedSubfield σ with hkdef
  have hfixset := fixedSubgroup_fieldAut_eq_range_gen hn3 Nat.prime_three hcop hσ
  have hinj := linearSubfieldInclusion_injective (by omega : 0 < n) k
  have hfix : fixSubgroup (fieldAut n K σ) = (linearSubfieldInclusion n k).range := by
    ext x
    exact Iff.of_eq (congrArg (x ∈ ·) hfixset)
  let eD : ↥(fixSubgroup (fieldAut n K σ)) ≃* projectiveSL n ↥k :=
    (MulEquiv.subgroupCongr hfix).trans (MonoidHom.ofInjective hinj).symm
  haveI : IsSimpleGroup (projectiveSL n ↥k) := KCLinearSubfield.isSimpleGroup_projectiveSL hn3
  have hnabk : ∃ a b : projectiveSL n ↥k, a * b ≠ b * a := by
    have h1 := KCLinearSubfield.not_commutative_projectiveSL (n := n) (K := ↥k) hn3
    push Not at h1
    exact h1
  have hs : IsSimpleGroup ↥(fixSubgroup (fieldAut n K σ)) := eD.isSimpleGroup
  have hnab : ∃ a b : ↥(fixSubgroup (fieldAut n K σ)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabk
    exact ⟨eD.symm a, eD.symm b, fun h => hab (by
      have := congrArg eD h
      simpa using this)⟩
  obtain ⟨h3f, hkcard⟩ := card_semilinearFixedSubfield hp hf hK hσ
  have hf0 : 1 ≤ f / 3 := by
    have : 3 ≤ f := Nat.le_of_dvd (by omega) h3f
    omega
  have hadm : StatedLieAdmissible .PSL n p (f / 3) :=
    ⟨hp, hf0, by omega, fun hc => by have := (Prod.mk.inj hc).1; omega,
      fun hc => by have := (Prod.mk.inj hc).1; omega⟩
  have hmodel : LieModel ↥(fixSubgroup (fieldAut n K σ)) .PSL n p (f / 3) :=
    (lieModel_classical_iff (by decide)).mpr
      ⟨hadm, ↥k, inferInstance, inferInstance, hkcard,
        ⟨eD.trans (statedProjEquiv n ↥k).symm⟩⟩
  exact noL34Layer_of_fixed_equiv _ (MulEquiv.refl _) hs hnab
    (not_isLThreeFour_of_lieModel_odd hO hp2 hmodel)

theorem noL34OuterAt_pslGood (hO : LieOrderFormulasInput) : NoL34OuterAt FamPslGood := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ
  have hp2 : p ≠ 2 := by omega
  obtain ⟨rfl, hn3, hcop⟩ := hF
  have hC : StatedClassicalModel P .PSL n p f := (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  rw [← hK] at hcop
  let e : P ≃* projectiveSL n K := e0.trans (statedProjEquiv n K)
  haveI : Finite (projectiveSL n K) := Finite.of_equiv P e.toEquiv
  refine noL34Layer_congr e ?_
  have hψ3' : (MulAut.congr e ψ) ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hD : MulAut.congr e ψ ∉ linearAutGroup n K := fun hD =>
    hψ ((congr_mem_inner_iff_of_equiv e ψ).mp
      (inner_of_mem_linearAut_of_pow_eq_one hn3 hcop hD hψ3'))
  obtain ⟨σ, hσ, H, hψH⟩ := linear_order_three_field_descent hn3 _ hψ3' hD
  rw [hψH]
  exact noL34Layer_conj _ (noL34Layer_fieldAut_psl hO hn3 hσ hcop hadm.1 hp2 hadm.2.1 hK)

end PslGood

section PslTwo

theorem noL34Layer_of_fixed_solvable_lin {P : Type} [Group P] [Finite P] (ψ : MulAut P)
    (hS : Group.IsSolvable ↥(fixSubgroup ψ)) : NoL34Layer ψ := by
  intro A hA _
  have hAD : A ≤ fixSubgroup ψ := hA.1
  have hperf : ⁅A, A⁆ = A := glaPComponent_perfect hA
  haveI : Group.IsSolvable ↥A :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hAD)
  haveI : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.mpr hperf
  haveI : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr (glaPComponent_ne_bot hA)
  exact Group.IsPerfect.not_isSolvable ↥A inferInstance

theorem isSimpleGroup_of_quasisimple_of_center_bot_lin {X : Type} [Group X]
    (hq : CFSG.Open.IsQuasisimple X) (hz : Subgroup.center X = ⊥) : IsSimpleGroup X := by
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2
  exact ((QuotientGroup.quotientMulEquivOfEq hz).trans
    (QuotientGroup.quotientBot (G := X))).symm.isSimpleGroup

theorem noL34OuterAt_pslTwo (hO : LieOrderFormulasInput) : NoL34OuterAt FamPslTwo := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ
  have hp2 : p ≠ 2 := by omega
  obtain ⟨rfl, rfl⟩ := hF
  have hC : StatedClassicalModel P .PSL 2 p f := (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  haveI : Finite (StatedProj (StatedSL 2 K)) := Finite.of_equiv P e0.toEquiv
  refine noL34Layer_congr e0 ?_
  have hβ3 : (MulAut.congr e0 ψ) ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hβ1 : MulAut.congr e0 ψ ≠ 1 := fun h =>
    hψ ((congr_mem_inner_iff_of_equiv e0 ψ).mp (h ▸ one_mem _))
  rcases Solomon.Coordinator.l2Aut3Classification_holds K _ hβ3 with h | hsol | ⟨σ, φ, γ, hφ, hβ⟩
  · exact absurd h hβ1
  · exact noL34Layer_of_fixed_solvable_lin _ hsol
  · obtain ⟨F₀, hF₀f, hF₀fin, hcard, ⟨ψ0⟩⟩ :=
      Solomon.Coordinator.l2FieldFixed_holds K _ hβ3 hβ1 σ φ γ hφ hβ
    have hdvd : Nat.card F₀ ∣ p ^ f := by
      rw [← hK, hcard]
      exact dvd_pow_self _ (by norm_num)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hadm.1).1 hdvd
    have hj1 : 1 ≤ j := by
      by_contra h0
      have h1 : 1 < Nat.card F₀ := Finite.one_lt_card
      rw [hj, show j = 0 by omega] at h1
      simp at h1
    have h5 : 5 ≤ p ^ j := hp5.trans (Nat.le_self_pow (by omega) p)
    have hadm₀ : StatedLieAdmissible .PSL 2 p j :=
      ⟨hadm.1, hj1, le_rfl, fun hc => by have := (Prod.mk.inj hc).2; omega,
        fun hc => by have := (Prod.mk.inj hc).2; omega⟩
    have hmodel : LieModel (StatedProj (StatedSL 2 F₀)) .PSL 2 p j :=
      (lieModel_classical_iff (by decide)).mpr
        ⟨hadm₀, F₀, inferInstance, inferInstance, hj, ⟨MulEquiv.refl _⟩⟩
    obtain ⟨hq, hz⟩ := Solomon.Coordinator.l2fld_isQuasisimple_psl2 (F := F₀) (by omega)
    haveI : IsSimpleGroup (StatedProj (StatedSL 2 F₀)) :=
      isSimpleGroup_of_quasisimple_of_center_bot_lin hq hz
    exact noL34Layer_of_fixed_equiv _ ψ0 inferInstance (exists_noncomm_of_center_bot hz)
      (not_isLThreeFour_of_lieModel_odd hO hp2 hmodel)

end PslTwo

section PslBad

theorem noL34Layer_fieldAut_psl_gen (hO : LieOrderFormulasInput) {n : ℕ} (hn3 : 3 ≤ n)
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} (hσ : orderOf σ = 3) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) :
    NoL34Layer (fieldAut n K σ) := by
  set k := semilinearFixedSubfield σ with hkdef
  have hk : ∀ x, x ∈ k ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have hinj := linearSubfieldInclusion_injective (by omega : 0 < n) k
  let S : Subgroup (projectiveSL n K) := (linearSubfieldInclusion n k).range
  let eS : ↥S ≃* projectiveSL n ↥k := (MonoidHom.ofInjective hinj).symm
  haveI : IsSimpleGroup (projectiveSL n ↥k) := KCLinearSubfield.isSimpleGroup_projectiveSL hn3
  have hnabk : ∃ a b : projectiveSL n ↥k, a * b ≠ b * a := by
    have h1 := KCLinearSubfield.not_commutative_projectiveSL (n := n) (K := ↥k) hn3
    push Not at h1
    exact h1
  have hs : IsSimpleGroup ↥S := eS.isSimpleGroup
  have hnab : ∃ a b : ↥S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabk
    exact ⟨eS.symm a, eS.symm b, fun h => hab (by
      have := congrArg eS h
      simpa using this)⟩
  have hSle : S ≤ fixSubgroup (fieldAut n K σ) := by
    rintro _ ⟨y, rfl⟩
    exact fieldAut_linearSubfieldInclusion (fun c hc => (hk c).mp hc) y
  have hcomm : ⁅fixSubgroup (fieldAut n K σ), fixSubgroup (fieldAut n K σ)⁆ ≤ S :=
    Subgroup.commutator_le.2 fun a ha b hb => commutator_fixed_mem_range (by omega) ha hb
  obtain ⟨h3f, hkcard⟩ := card_semilinearFixedSubfield hp hf hK hσ
  have hf0 : 1 ≤ f / 3 := by
    have : 3 ≤ f := Nat.le_of_dvd (by omega) h3f
    omega
  have hadm : StatedLieAdmissible .PSL n p (f / 3) :=
    ⟨hp, hf0, by omega, fun hc => by have := (Prod.mk.inj hc).1; omega,
      fun hc => by have := (Prod.mk.inj hc).1; omega⟩
  have hmodel : LieModel ↥S .PSL n p (f / 3) :=
    (lieModel_classical_iff (by decide)).mpr
      ⟨hadm, ↥k, inferInstance, inferInstance, hkcard,
        ⟨eS.trans (statedProjEquiv n ↥k).symm⟩⟩
  exact noL34_of_simple_normal_comm _ S hSle hcomm hs hnab
    (not_isLThreeFour_of_lieModel_odd hO hp2 hmodel)

@[expose] def Up34DiagPsl : Prop :=
  ∀ (n p f : ℕ) (K : Type) [Field K] [Finite K], 3 ≤ n → p.Prime → 5 ≤ p → 1 ≤ f →
    Nat.card K = p ^ f → ∀ ψ : MulAut (projectiveSL n K), ψ ^ 3 = 1 → ψ ∈ linearAutGroup n K →
      ψ ∉ inner (projectiveSL n K) → NoL34Layer ψ

theorem noL34OuterAt_pslBad (hO : LieOrderFormulasInput) (hD : Up34DiagPsl) :
    NoL34OuterAt FamPslBad := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ
  have hp2 : p ≠ 2 := by omega
  obtain ⟨rfl, hn3, hdvd⟩ := hF
  have hC : StatedClassicalModel P .PSL n p f := (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  let e : P ≃* projectiveSL n K := e0.trans (statedProjEquiv n K)
  haveI : Finite (projectiveSL n K) := Finite.of_equiv P e.toEquiv
  refine noL34Layer_congr e ?_
  have hψ3' : (MulAut.congr e ψ) ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  by_cases hDiag : MulAut.congr e ψ ∈ linearAutGroup n K
  · exact hD n p f K hn3 hadm.1 hp5 hadm.2.1 hK _ hψ3' hDiag fun hin =>
      hψ ((congr_mem_inner_iff_of_equiv e ψ).mp hin)
  · obtain ⟨σ, hσ, H, hψH⟩ := linear_order_three_field_descent hn3 _ hψ3' hDiag
    rw [hψH]
    exact noL34Layer_conj _ (noL34Layer_fieldAut_psl_gen hO hn3 hσ hadm.1 hp2 hadm.2.1 hK)

end PslBad

section PsuGood

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem noL34Layer_fieldAut_psu (hO : LieOrderFormulasInput) (h : UnitaryFieldData ℓ f K)
    (hn : 3 ≤ n) (hℓ5 : 5 ≤ ℓ) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    NoL34Layer (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) := by
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
  have hq0 : ¬(n = 3 ∧ ℓ ^ (f / 3) = 2) := fun ⟨_, h2⟩ => by
    have : ℓ ≤ ℓ ^ (f / 3) := Nat.le_self_pow (by omega) ℓ
    omega
  have hGL : Finite (GL (Fin n) K) :=
    Finite.of_injective (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) Units.val_injective
  have hfinT : Finite (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    inferInstance
  set j := primeSubfieldPSU h hp hp2 hσ n with hj
  have hinj : Function.Injective j := subfieldPSU_injective h h₀ hbar n (by omega)
  have hJC : j.range ≤ fixSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) :=
    range_subfieldPSU_le h n h₀ hbar
  have hCC := commutator_fixed_le_range (n := n) h hσ
  let eJ : primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ)) ≃* ↥j.range := MonoidHom.ofInjective hinj
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
  exact noL34_of_simple_normal_comm _ j.range hJC hCC inferInstance hnab
    (not_isLThreeFour_of_lieModel_odd hO (by omega) hmodel)

theorem noL34OuterAt_psuGood (hO : LieOrderFormulasInput) : NoL34OuterAt FamPsuGood := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ
  obtain ⟨rfl, hn3, hdiv⟩ := hF
  obtain ⟨K, _, h, ⟨e0⟩⟩ := exists_psu_model hadm hm
  have hne : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨h1, h2⟩ => hadm.2.2.2 (by rw [h1, h2])
  haveI : Finite (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    Finite.of_equiv P e0.toEquiv
  refine noL34Layer_congr e0 ?_
  have hψ3' : (MulAut.congr e0 ψ) ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  have hσ1 : primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn3 hne
      (MulAut.congr e0 ψ) ≠ 1 := by
    intro hσ1
    have hD : MulAut.congr e0 ψ ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← ker_primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn3 hne]
      exact hσ1
    exact hψ ((congr_mem_inner_iff_of_equiv e0 ψ).mp
      (mem_inner_of_mem_primeFormD h hn3 hne Nat.prime_three hdiv hD hψ3'))
  obtain ⟨σ, u, hσord, hu⟩ := exists_conj_fieldAut_of_factor_ne_one h hn3 hne hψ3' hσ1
  rw [hu]
  exact noL34Layer_conj _ (noL34Layer_fieldAut_psu hO h hn3 hp5 hσord)

end PsuGood

section PsuBad

@[expose] def Up34DiagPsu : Prop :=
  ∀ (n p f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData p f K), 3 ≤ n → 5 ≤ p →
    ∀ ψ : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)), ψ ^ 3 = 1 →
      ψ ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
      ψ ∉ inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) → NoL34Layer ψ

theorem noL34OuterAt_psuBad (hO : LieOrderFormulasInput) (hD : Up34DiagPsu) :
    NoL34OuterAt FamPsuBad := by
  intro P _ _ t n p f hadm ht hF hp5 hm ψ hψ3 hψ
  obtain ⟨rfl, hn3, hdvd⟩ := hF
  obtain ⟨K, _, h, ⟨e0⟩⟩ := exists_psu_model hadm hm
  have hne : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨h1, h2⟩ => hadm.2.2.2 (by rw [h1, h2])
  haveI : Finite (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    Finite.of_equiv P e0.toEquiv
  refine noL34Layer_congr e0 ?_
  have hψ3' : (MulAut.congr e0 ψ) ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
  by_cases hσ : primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn3 hne
      (MulAut.congr e0 ψ) = 1
  · have hDmem : MulAut.congr e0 ψ ∈
        primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← ker_primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn3 hne]
      exact hσ
    exact hD n p f K h hn3 hp5 _ hψ3' hDmem fun hin =>
      hψ ((congr_mem_inner_iff_of_equiv e0 ψ).mp hin)
  · obtain ⟨σ, u, hσord, hu⟩ := exists_conj_fieldAut_of_factor_ne_one h hn3 hne hψ3' hσ
    rw [hu]
    exact noL34Layer_conj _ (noL34Layer_fieldAut_psu hO h hn3 hp5 hσord)

end PsuBad

end CFSG.HardMathSupport.Dickson.Sec6
