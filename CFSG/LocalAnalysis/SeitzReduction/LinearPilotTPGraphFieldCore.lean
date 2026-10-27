module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTPFieldGraph

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.LinearGroups
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatalogueBGraphField
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry CFSG.LieType.Universal.Unitary
open CFSG.ComponentClassification.UnbalancedCatalog (linear_graph_field_full_centralizer_rigidity
  conjAut_eq_conjAut_iff)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect)
open scoped commutatorElement

variable {p e : ℕ} {K : Type} [Field K] {n : ℕ}

variable (p e K n) in
@[expose] noncomputable def unitaryCore : Subgroup (projectiveSL n K) :=
  ((unitarySU p e K n).map (conjAut n K)).comap MulAut.conj

theorem mem_unitaryCore {x : projectiveSL n K} :
    x ∈ unitaryCore p e K n ↔ ∃ g ∈ unitarySU p e K n, conjAut n K g = MulAut.conj x :=
  Iff.rfl

theorem unitarySU_map_le_range_conj (h : UnitaryFieldData p e K) :
    (unitarySU p e K n).map (conjAut n K) ≤
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  rintro _ ⟨g, hg, rfl⟩
  let g' : SpecialLinearGroup (Fin n) K :=
    ⟨(g : Matrix (Fin n) (Fin n) K), ((mem_unitarySU_iff h).1 hg).1⟩
  refine ⟨proj n K g', ?_⟩
  rw [← conjAut_toGL]
  exact congrArg (conjAut n K) (Units.ext rfl)

theorem map_conj_unitaryCore (h : UnitaryFieldData p e K) :
    (unitaryCore p e K n).map MulAut.conj = (unitarySU p e K n).map (conjAut n K) :=
  map_comap_eq_self (unitarySU_map_le_range_conj h)

theorem exists_unitaryCoreEquiv (h : UnitaryFieldData p e K) (hn : 3 ≤ n) (σ : K ≃+* K)
    (hσ : ∀ x, σ x = h.bar x) :
    ∃ E : unitaryPSU h n ≃* unitaryCore p e K n,
      ∀ g, MulAut.conj (E (unitaryProj h n g) : projectiveSL n K) = conjAut n K g := by
  have := h.finite
  obtain ⟨-, ⟨ι, hι⟩, -⟩ := linear_graph_field_full_centralizer_rigidity h hn σ hσ
  have hconj := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.conj_injective_projectiveSL
    (F := K) hn
  let eY := (unitaryCore p e K n).equivMapOfInjective _ hconj
  refine ⟨ι.trans ((MulEquiv.subgroupCongr (map_conj_unitaryCore h)).symm.trans eY.symm),
    fun g => ?_⟩
  have h1 : ((eY (eY.symm ((MulEquiv.subgroupCongr (map_conj_unitaryCore h)).symm
      (ι (unitaryProj h n g)))) : MulAut (projectiveSL n K))) = conjAut n K g := by
    rw [MulEquiv.apply_symm_apply]
    exact hι g
  exact h1

theorem unitaryCore_le_autFixSubgroup (h : UnitaryFieldData p e K) (hn : 3 ≤ n) (σ : K ≃+* K)
    (hσ : ∀ x, σ x = h.bar x) :
    unitaryCore p e K n ≤ autFixSubgroup (fieldAut n K σ * dualAut n K) := by
  have := h.finite
  obtain ⟨-, -, -, -, hcent, -, -⟩ := linear_graph_field_full_centralizer_rigidity h hn σ hσ
  intro x hx
  exact (mem_autFixSubgroup_iff_conj_mem_centralizer hn _ x).2 (hcent hx)

theorem commutator_unitaryCore (h : UnitaryFieldData p e K) (hn : 3 ≤ n)
    (hnq : (n, p ^ e) ≠ (3, 2)) (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) :
    ⁅unitaryCore p e K n, unitaryCore p e K n⁆ = unitaryCore p e K n := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨E, -⟩ := exists_unitaryCoreEquiv h hn σ hσ
  have hSU : Group.IsPerfect (unitarySU p e K n) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (by rw [h.card, ← pow_mul, mul_comm]) hn hnq
  have hPSU : Group.IsPerfect (unitaryPSU h n) :=
    Group.IsPerfect.ofSurjective (f := unitaryProj h n) (unitaryProj_surjective h n)
  have hY : Group.IsPerfect (unitaryCore p e K n) :=
    Group.IsPerfect.ofSurjective (f := E.toMonoidHom) E.surjective
  exact Subgroup.isPerfect_iff.mp hY

omit [Field K] in
theorem graphField_mul_conjAut [Field K] (σ : K ≃+* K) (A : GL (Fin n) K) :
    fieldAut n K σ * dualAut n K * conjAut n K A =
      conjAut n K (GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.inverseTranspose A)) *
        (fieldAut n K σ * dualAut n K) := by
  rw [mul_assoc, dualAut_mul_conjAut, ← mul_assoc, fieldAut_mul_conjAut, mul_assoc]

theorem exists_mem_Uid_of_mem_autFixSubgroup (h : UnitaryFieldData p e K) (hn : 3 ≤ n)
    (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) {x : projectiveSL n K}
    (hx : x ∈ autFixSubgroup (fieldAut n K σ * dualAut n K)) :
    ∃ B ∈ Uid σ n, conjAut n K B = MulAut.conj x := by
  have := h.finite
  have hσσ : ∀ x, σ (σ x) = x := fun x => by rw [hσ, hσ, h.bar_bar]
  have hσ2 : σ ^ 2 = 1 := RingEquiv.ext fun x => by
    rw [pow_two, RingAut.mul_apply, hσσ]
    rfl
  have hσne : σ ≠ 1 := by
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    intro h1
    apply hc
    rw [← hσ, h1]
    rfl
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  have hcx : conjAut n K (SpecialLinearGroup.toGL g) = MulAut.conj (proj n K g) :=
    conjAut_toGL g
  set A := SpecialLinearGroup.toGL g with hA
  have hcomm := (mem_autFixSubgroup_iff_conj_mem_centralizer hn _ _).1 hx
  rw [mem_centralizer_singleton_iff, ← hcx] at hcomm
  have h1 : conjAut n K (GeneralLinearGroup.map (σ : K →+* K)
      (GeneralLinearGroup.inverseTranspose A)) = conjAut n K A := by
    have h2 := graphField_mul_conjAut σ A
    rw [← hcomm] at h2
    exact (mul_right_cancel h2).symm
  obtain ⟨c, hc⟩ := (conjAut_eq_conjAut_iff hn _ _).mp h1
  have hfix : ProjGenLinGroup.mk A ∈ fixedPGL n K σ := by
    change pglGraphFieldAut n K σ (ProjGenLinGroup.mk A) = ProjGenLinGroup.mk A
    rw [pglGraphFieldAut_mk]
    change ProjGenLinGroup.mk (GeneralLinearGroup.map (σ : K →+* K)
      (GeneralLinearGroup.inverseTranspose A)) = _
    rw [hc, map_mul, ProjGenLinGroup.mk_scalar, mul_one]
  rw [fixedPGL_eq_unitary_image n K (by omega) σ hσ2 hσne] at hfix
  obtain ⟨B, hB, hBA⟩ := hfix
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hBA
  refine ⟨B, hB, ?_⟩
  rw [← hcx, ← hu, map_mul, conjAut_scalar, mul_one]

theorem commutator_autFixSubgroup_le_unitaryCore (h : UnitaryFieldData p e K) (hn : 3 ≤ n)
    (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) :
    ⁅autFixSubgroup (fieldAut n K σ * dualAut n K),
      autFixSubgroup (fieldAut n K σ * dualAut n K)⁆ ≤ unitaryCore p e K n := by
  have hmapσ : ∀ M : Matrix (Fin n) (Fin n) K, M.map σ = M.map h.bar := fun M => by
    ext i j
    simp [hσ]
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨B, hB, hBx⟩ := exists_mem_Uid_of_mem_autFixSubgroup h hn σ hσ hx
  obtain ⟨B', hB', hBy⟩ := exists_mem_Uid_of_mem_autFixSubgroup h hn σ hσ hy
  have hU : ⁅B, B'⁆ ∈ Uid σ n := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hB hB') (inv_mem hB)) (inv_mem hB')
  have hdet : ((⁅B, B'⁆ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det ⁅B, B'⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
    have h2 := congrArg Units.val h1
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h2
  refine ⟨⁅B, B'⁆, (mem_unitarySU_iff h).2 ⟨hdet, ?_⟩, ?_⟩
  · have h1 := (mem_Uid_iff σ n _).1 hU
    rwa [conjTr, hmapσ] at h1
  · change conjAut n K ⁅B, B'⁆ = MulAut.conj ⁅x, y⁆
    rw [map_commutatorElement, map_commutatorElement, hBx, hBy]

theorem perfectCore_autFixSubgroup_graphField_le (h : UnitaryFieldData p e K) (hn : 3 ≤ n)
    (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) :
    perfectCore (autFixSubgroup (fieldAut n K σ * dualAut n K)) ≤ unitaryCore p e K n := by
  have h1 := CFSG.Quasithin.perfectCore_le_derivedSeriesOf
    (autFixSubgroup (fieldAut n K σ * dualAut n K)) 1
  rw [CFSG.Quasithin.derivedSeriesOf_succ, CFSG.Quasithin.derivedSeriesOf_zero] at h1
  exact h1.trans (commutator_autFixSubgroup_le_unitaryCore h hn σ hσ)

theorem perfectCore_autFixSubgroup_graphField (h : UnitaryFieldData p e K) (hn : 3 ≤ n)
    (hnq : (n, p ^ e) ≠ (3, 2)) (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) :
    perfectCore (autFixSubgroup (fieldAut n K σ * dualAut n K)) = unitaryCore p e K n := by
  apply le_antisymm (perfectCore_autFixSubgroup_graphField_le h hn σ hσ)
  exact le_perfectCore_of_perfect (unitaryCore_le_autFixSubgroup h hn σ hσ)
      (commutator_unitaryCore h hn hnq σ hσ)

theorem card_unitarySU_and_factorization (h : UnitaryFieldData p e K) (hn : 1 ≤ n) :
    (Nat.card (unitarySU p e K n) : ℤ) = ((p ^ e : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 n, (((p ^ e : ℕ) : ℤ) ^ i - (-1) ^ i) ∧
      p ^ (Nat.card (unitarySU p e K n)).factorization p = (p ^ e) ^ (n * (n - 1) / 2) := by
  have := unitary_full_group_order h (stdHermForm_isSymm h n) (stdHermForm_separatingLeft h n)
    (Module.finrank_fin_fun K) hn
  rw [unitarySU_eq_gramSU h n, card_gramSU, ← stdHermForm_eq_gramForm]
  exact ⟨this.2.1, this.2.2.2.2.2.2⟩

theorem card_unitaryPSU_mul (h : UnitaryFieldData p e K) (hn : 1 ≤ n) :
    Nat.card (unitaryPSU h n) * Nat.gcd n (p ^ e + 1) = Nat.card (unitarySU p e K n) := by
  rw [← card_unitaryScalars h hn]
  exact ((unitaryScalars h n).card_eq_card_quotient_mul_card_subgroup).symm

theorem card_perfectCore_graphField_dvd (h : UnitaryFieldData p e K) (hn : 3 ≤ n) (σ : K ≃+* K)
    (hσ : ∀ x, σ x = h.bar x) :
    Nat.card (perfectCore (autFixSubgroup (fieldAut n K σ * dualAut n K))) ∣
      Nat.card (unitarySU p e K n) := by
  have := h.finite
  obtain ⟨E, -⟩ := exists_unitaryCoreEquiv h hn σ hσ
  refine (Subgroup.card_dvd_of_le (perfectCore_autFixSubgroup_graphField_le h hn σ hσ)).trans ?_
  rw [← Nat.card_congr E.toEquiv, ← card_unitaryPSU_mul h (by omega)]
  exact Dvd.intro _ rfl

theorem card_perfectCore_graphField (h : UnitaryFieldData p e K) (hn : 3 ≤ n)
    (hnq : (n, p ^ e) ≠ (3, 2)) (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) :
    Nat.card (perfectCore (autFixSubgroup (fieldAut n K σ * dualAut n K))) =
      Nat.card (unitaryPSU h n) := by
  rw [perfectCore_autFixSubgroup_graphField h hn hnq σ hσ]
  obtain ⟨E, -⟩ := exists_unitaryCoreEquiv h hn σ hσ
  exact (Nat.card_congr E.toEquiv).symm

theorem card_sylow_perfectCore_graphField (h : UnitaryFieldData p e K) (hn : 3 ≤ n)
    (hnq : (n, p ^ e) ≠ (3, 2)) (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x)
    (S : Sylow p (perfectCore (autFixSubgroup (fieldAut n K σ * dualAut n K)))) :
    Nat.card S = (p ^ e) ^ (n * (n - 1) / 2) := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  rw [Sylow.card_eq_multiplicity, card_perfectCore_graphField h hn hnq σ hσ]
  have hmul := card_unitaryPSU_mul h (n := n) (by omega)
  have hp : ¬ p ∣ Nat.gcd n (p ^ e + 1) := by
    intro hp
    have h1 : p ∣ p ^ e + 1 := hp.trans (Nat.gcd_dvd_right _ _)
    have h2 : p ∣ 1 := (Nat.dvd_add_right (dvd_pow_self p (by have := h.one_le; omega))).mp h1
    exact h.prime.one_lt.ne' (Nat.dvd_one.mp h2)
  have hfact : (Nat.card (unitaryPSU h n)).factorization p =
      (Nat.card (unitarySU p e K n)).factorization p := by
    rw [← hmul, Nat.factorization_mul Nat.card_pos.ne'
      (Nat.gcd_pos_of_pos_right _ (Nat.succ_pos _)).ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hp, add_zero]
  rw [hfact]
  exact (card_unitarySU_and_factorization h (by omega)).2

theorem isSimpleGroup_perfectCore_graphField (h : UnitaryFieldData p e K) (hn : 3 ≤ n)
    (hnq : (n, p ^ e) ≠ (3, 2)) (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) :
    IsSimpleGroup (perfectCore (autFixSubgroup (fieldAut n K σ * dualAut n K))) := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  rw [perfectCore_autFixSubgroup_graphField h hn hnq σ hσ]
  obtain ⟨E, -⟩ := exists_unitaryCoreEquiv h hn σ hσ
  have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p e
    (by rw [h.card, ← pow_mul, mul_comm]) n hn hnq
  exact (E.symm.trans (unitaryPSUEquiv h (by omega))).isSimpleGroup

theorem not_forall_mul_comm_perfectCore_graphField (h : UnitaryFieldData p e K) (hn : 3 ≤ n)
    (hnq : (n, p ^ e) ≠ (3, 2)) (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) :
    ¬ ∀ a ∈ perfectCore (autFixSubgroup (fieldAut n K σ * dualAut n K)),
      ∀ b ∈ perfectCore (autFixSubgroup (fieldAut n K σ * dualAut n K)), a * b = b * a := by
  have := h.finite
  intro hc
  have hs := isSimpleGroup_perfectCore_graphField h hn hnq σ hσ
  have hperf := CFSG.Quasithin.perfectCore_perfect (autFixSubgroup (fieldAut n K σ * dualAut n K))
  have hbot : perfectCore (autFixSubgroup (fieldAut n K σ * dualAut n K)) = ⊥ := by
    rw [← hperf, eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def, hc a ha b hb, mul_inv_cancel_right, mul_inv_cancel, mem_bot]
  have hnt := hs.toNontrivial
  rw [Subgroup.nontrivial_iff_ne_bot] at hnt
  exact hnt hbot

end CFSG.SeitzReduction.LinearPilot
