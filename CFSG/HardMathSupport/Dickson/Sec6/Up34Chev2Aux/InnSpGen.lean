module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnUniBlock
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnUniCore
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnOrbit
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicBlocks

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open Polynomial CFSG CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.ComponentClassification.CatLeaf
open scoped commutatorElement

namespace Up34Chev2

section Derived

variable {X : Type} [Group X]

theorem nonempty_mulEquiv_commutator_ker {G Q : Type*} [Group G] [CommGroup Q] (A : Subgroup X)
    (φ : ↥A ≃* G) (D : G →* Q) (hq : CFSG.IsQuasisimple ↥D.ker) :
    Nonempty (↥⁅A, A⁆ ≃* ↥D.ker) := by
  have hle : commutator G ≤ D.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  have hge : D.ker ≤ commutator G := by
    have h1 := Subgroup.isPerfect_iff.mp hq.1
    calc D.ker = ⁅D.ker, D.ker⁆ := h1.symm
      _ ≤ ⁅(⊤ : Subgroup G), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator G := (_root_.commutator_def G).symm
  have hmap : (commutator ↥A).map φ.toMonoidHom = commutator G := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 φ.surjective]
  have hAA : (commutator ↥A).map A.subtype = ⁅A, A⁆ := Subgroup.map_subtype_commutator A
  exact ⟨((MulEquiv.subgroupCongr hAA.symm).trans
    ((commutator ↥A).equivMapOfInjective A.subtype A.subtype_injective).symm).trans
    (((commutator ↥A).equivMapOfInjective φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr (hmap.trans (le_antisymm hle hge))))⟩

theorem card_commutator_quotient_le (A : Subgroup X) [Finite ↥A] :
    Nat.card (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆) ≤ Nat.card ↥A := by
  haveI : Finite ↥⁅A, A⁆ := Finite.of_injective (Subgroup.inclusion (commutator_le_self_orb A))
    (Subgroup.inclusion_injective _)
  exact (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)).trans
    (Subgroup.card_le_of_le (commutator_le_self_orb A))

theorem false_of_card_lt (A : Subgroup X) [Finite ↥A] (h : Nat.card ↥A < 20160)
    (hL : IsLThreeFour (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆)) : False := by
  have h1 := card_eq_of_isLThreeFour hL
  have h2 := card_commutator_quotient_le A
  omega

theorem false_of_comm (A : Subgroup X) (hcomm : ∀ a b : ↥A, a * b = b * a)
    (hL : IsLThreeFour (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆)) : False := by
  have hbot : ⁅A, A⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
    exact congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩)
  haveI : Subsingleton ↥⁅A, A⁆ := ⟨fun a b => Subtype.ext (by
    have ha : (a : X) ∈ (⊥ : Subgroup X) := hbot ▸ a.2
    have hb : (b : X) ∈ (⊥ : Subgroup X) := hbot ▸ b.2
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb])⟩
  have h1 := card_eq_of_isLThreeFour hL
  have h2 : Nat.card (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆) ≤ Nat.card ↥⁅A, A⁆ :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  rw [Nat.card_of_subsingleton (1 : ↥⁅A, A⁆)] at h2
  omega

end Derived

section Linear


theorem hno_gl_block (hO : LieOrderFormulasInput) {X T : Type} [Group X] [Group T] (π : X →* T)
    (hπ : π.ker = ⊥) (A : Subgroup X) {E W : Type} [Field E] [Finite E] [AddCommGroup W]
    [Module E W] [FiniteDimensional E W] (φ : ↥A ≃* LinearMap.GeneralLinearGroup E W) {e : ℕ}
    (hE : Nat.card E = 2 ^ e) (h4 : 4 ≤ Nat.card E) (hq : CFSG.IsQuasisimple ↥⁅A, A⁆)
    (hL : IsLThreeFour (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆)) :
    ∃ z : X, z ∈ ⁅A, A⁆ ∧ (∀ g ∈ ⁅A, A⁆, g * z = z * g) ∧ z ^ 3 = 1 ∧ π z ≠ 1 := by
  by_cases hm2 : 2 ≤ Module.finrank E W
  swap
  · exfalso
    refine false_of_comm A (fun a b => φ.injective ?_) hL
    rw [map_mul, map_mul]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul]
    exact (CFSG.RankThree.PartOne.KCUnitary.End_commute_of_finrank_le_one (by omega) _ _).eq
  have h4' := CFSG.RankThree.PartOne.KCSpIsotypic.exists_finset_card_four_of_card h4
  have hqk := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_ker_det hm2 (Or.inr h4')
  obtain ⟨eD⟩ := nonempty_mulEquiv_commutator_ker A φ _ hqk
  obtain ⟨e2⟩ := CFSG.RankThree.PartOne.KCUnitary.nonempty_specialLinearGroup_mulEquiv_ker_det
    (E := E) (W := W)
  let e1 : ↥⁅A, A⁆ ≃* Matrix.SpecialLinearGroup (Fin (Module.finrank E W)) E := eD.trans e2.symm
  have h4e : 4 ≤ 2 ^ e := hE ▸ h4
  have he : 1 ≤ e := by
    by_contra hlt
    have : e = 0 := by omega
    subst this
    omega
  have hadm : StatedLieAdmissible .PSL (Module.finrank E W) 2 e :=
    ⟨Nat.prime_two, he, hm2, fun hc => by have := (Prod.mk.inj hc).2; omega,
      fun hc => by have := (Prod.mk.inj hc).2; omega⟩
  obtain ⟨-, -, z, hzc, hz3, hz1⟩ := block_central_of_isLThreeFour hO hE e1 hadm hL
  refine ⟨z.1, z.2, fun g hg => ?_, congrArg Subtype.val hz3, fun h1 => ?_⟩
  · exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hzc ⟨g, hg⟩)
  · have h2 : z.1 ∈ π.ker := h1
    rw [hπ, Subgroup.mem_bot] at h2
    exact hz1 (Subtype.ext h2)

end Linear

section Unitary

theorem not_isLThreeFour_of_equiv_sesqSU (hO : LieOrderFormulasInput) {f' : ℕ} {E : Type}
    [Field E] (hE : UnitaryFieldData 2 f' E) {W : Type} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft) (hm : 2 ≤ Module.finrank E W)
    (hqq : (Module.finrank E W = 2 → 4 ≤ 2 ^ f') ∧ (Module.finrank E W = 3 → 3 ≤ 2 ^ f'))
    {G : Type} [Group G] (e : G ≃* ↥(sesqSpecialUnitaryGroup Hf)) :
    ¬ IsLThreeFour (G ⧸ Subgroup.center G) := by
  haveI := hE.finite
  rcases Nat.lt_or_ge (Module.finrank E W) 3 with hm3 | hm3
  ·
    have hV : Module.finrank E W = 2 := by omega
    obtain ⟨e2⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf
      hHfl hV
    haveI : Finite hE.fixedField := inferInstance
    have h4 : 4 ≤ 2 ^ f' := hqq.1 hV
    have hadm : StatedLieAdmissible .PSL 2 2 f' :=
      ⟨Nat.prime_two, hE.one_le, le_rfl, fun hc => by have := (Prod.mk.inj hc).2; omega,
        fun hc => by have := (Prod.mk.inj hc).2; omega⟩
    have hmodel := lieModel_centerQuotient_of_equiv_SL_c2 hadm hE.card_fixedField (e.trans e2)
    intro hL
    rcases isLThreeFour_cases_psl_two hO hmodel hL with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  ·
    obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis hHf hHfl
    obtain ⟨e2⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
      (G := (1 : Matrix (Fin (Module.finrank E W)) (Fin (Module.finrank E W)) E))
      (fun i j => by rw [hb i j, Matrix.one_apply])
    have hq' : ¬(Module.finrank E W = 3 ∧ 2 ^ f' = 2) := by
      rintro ⟨h3, h2⟩
      have := hqq.2 h3
      omega
    exact not_isLThreeFour_psu_two hO (lieModel_centerQuotient_of_equiv_gramSU hE hm3 hq' (e.trans e2))

theorem false_of_sesqU_block (hO : LieOrderFormulasInput) {X : Type} [Group X] (A : Subgroup X)
    {f' : ℕ} {E : Type} [Field E] (hE : UnitaryFieldData 2 f' E) {W : Type} [AddCommGroup W]
    [Module E W] [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft) (φ : ↥A ≃* ↥(sesqUnitaryGroup Hf))
    (hq : CFSG.IsQuasisimple ↥⁅A, A⁆)
    (hL : IsLThreeFour (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆)) : False := by
  haveI := hE.finite
  haveI : Finite W := Module.finite_of_finite E
  haveI : Finite (LinearMap.GeneralLinearGroup E W) := finite_gl_of_unitaryFieldData hE
  haveI : Finite ↥(sesqUnitaryGroup Hf) := Subtype.finite
  haveI : Finite ↥A := Finite.of_equiv _ φ.symm.toEquiv
  have hf1 := hE.one_le
  by_cases hm : 2 ≤ Module.finrank E W
  swap
  · refine false_of_comm A (fun a b => φ.injective ?_) hL
    refine Subtype.ext (Units.ext ?_)
    rw [map_mul, map_mul]
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact (CFSG.RankThree.PartOne.KCUnitary.End_commute_of_finrank_le_one (by omega) _ _).eq
  obtain ⟨hcard, -, -, -, hker, -⟩ := CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl rfl
    (by omega : 1 ≤ Module.finrank E W)
  by_cases hqq : (Module.finrank E W = 2 → 4 ≤ 2 ^ f') ∧ (Module.finrank E W = 3 → 3 ≤ 2 ^ f')
  · have hquasi : CFSG.IsQuasisimple ↥(CFSG.LinearGroups.unitaryDet Hf).ker := by
      rw [hker]
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).symm
        (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE hHf
          hHfl hm hqq)
    obtain ⟨eD⟩ := nonempty_mulEquiv_commutator_ker A φ (CFSG.LinearGroups.unitaryDet Hf) hquasi
    let e : ↥⁅A, A⁆ ≃* ↥(sesqSpecialUnitaryGroup Hf) :=
      (eD.trans (MulEquiv.subgroupCongr hker)).trans
        (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf))
    exact not_isLThreeFour_of_equiv_sesqSU hO hE hHf hHfl hm hqq e hL
  ·
    refine false_of_card_lt A ?_ hL
    rw [Nat.card_congr φ.toEquiv]
    have hQ2 : 2 ≤ 2 ^ f' :=
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f' := Nat.pow_le_pow_right (by norm_num) hf1
    generalize Module.finrank E W = m at hm hqq hcard
    generalize hQ : 2 ^ f' = Q at hQ2 hqq hcard
    have hexc : (m = 2 ∧ Q = 2) ∨ (m = 2 ∧ Q = 3) ∨ (m = 3 ∧ Q = 2) := by omega
    rcases hexc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have e : ((2 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
          ∏ i ∈ Finset.Icc 1 2, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 18 := by decide +kernel
      have h18 : Nat.card ↥(sesqUnitaryGroup Hf) = 18 := by exact_mod_cast hcard.trans e
      omega
    · have e : ((3 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
          ∏ i ∈ Finset.Icc 1 2, (((3 : ℕ) : ℤ) ^ i - (-1) ^ i) = 96 := by decide +kernel
      have h96 : Nat.card ↥(sesqUnitaryGroup Hf) = 96 := by exact_mod_cast hcard.trans e
      omega
    · have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
          ∏ i ∈ Finset.Icc 1 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 648 := by decide +kernel
      have h648 : Nat.card ↥(sesqUnitaryGroup Hf) = 648 := by exact_mod_cast hcard.trans e
      omega

end Unitary

section Symplectic

theorem card_statedSp_ne_twenty160 {f s : ℕ} (hf : 1 ≤ f) (hs : 1 ≤ s) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ f) : Nat.card (StatedSp s K) ≠ 20160 := by
  intro h
  rw [SymplecticFlag.card_statedSp, hK] at h
  have hodd : Odd (∏ j ∈ Finset.Icc 1 s, ((2 ^ f) ^ (2 * j) - 1)) := by
    refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one (fun j hj => ?_)
    have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hj).1
    have hev : Even ((2 ^ f) ^ (2 * j)) := by
      rw [← pow_mul]
      exact (Nat.even_pow' (by positivity)).2 even_two
    have hpos : 1 ≤ (2 ^ f) ^ (2 * j) := Nat.one_le_pow _ _ (by positivity)
    exact Nat.Even.sub_odd hpos hev odd_one
  have hpow : (2 ^ f) ^ (s ^ 2) = 2 ^ (f * s ^ 2) := (pow_mul 2 f (s ^ 2)).symm
  rw [hpow] at h
  have hne : ∏ j ∈ Finset.Icc 1 s, ((2 ^ f) ^ (2 * j) - 1) ≠ 0 := hodd.pos.ne'
  have h2 : (2 ^ (f * s ^ 2) * ∏ j ∈ Finset.Icc 1 s, ((2 ^ f) ^ (2 * j) - 1)).factorization 2 =
      (20160 : ℕ).factorization 2 := by rw [h]
  rw [Nat.factorization_mul (by positivity) hne, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by simpa [even_iff_two_dvd] using hodd.not_two_dvd_nat),
    factorization_twenty_thousand_two] at h2
  have hfs : f * s ^ 2 = 6 := by omega
  have hs2 : s ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have : 9 ≤ s ^ 2 := by nlinarith
    nlinarith
  interval_cases s
  · have hf6 : f = 6 := by omega
    subst hf6
    norm_num [Finset.Icc_self] at h
  · omega

theorem false_of_statedSp_block {X : Type} [Group X] (A : Subgroup X) {f s : ℕ} (hf : 1 ≤ f)
    (hs : 1 ≤ s) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (E : ↥A ≃* StatedSp s K) (hL : IsLThreeFour (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆)) : False := by
  haveI : Finite ↥A := Finite.of_equiv _ E.symm.toEquiv
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  by_cases hperf : 4 ≤ Nat.card K ∨ (Nat.card K = 2 ∧ 3 ≤ s)
  · have hqs := CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs
      (hperf.elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr (Or.inr h)))
    have hcomm : commutator (StatedSp s K) = ⊤ := Group.isPerfect_def.mp hqs.1
    have h1 : commutator ↥A = ⊤ := by
      have hmap : (commutator ↥A).map E.toMonoidHom = commutator (StatedSp s K) := by
        rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
          ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 E.surjective]
      rw [hcomm, ← Subgroup.map_top_of_surjective E.toMonoidHom E.surjective] at hmap
      exact Subgroup.map_injective E.injective hmap
    have hA : ⁅A, A⁆ = A := by
      rw [← Subgroup.map_subtype_commutator, h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    let eD : ↥⁅A, A⁆ ≃* StatedSp s K := (MulEquiv.subgroupCongr hA).trans E
    have hZ : Nat.card ↥(Subgroup.center ↥⁅A, A⁆) = 1 := by
      rw [Nat.card_congr (Subgroup.centerCongr eD).toEquiv,
        CFSG.LieType.Universal.Symplectic.center_eq,
        CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
      simp
    have hc := card_eq_of_isLThreeFour hL
    have h2 : Nat.card ↥⁅A, A⁆ = Nat.card (↥⁅A, A⁆ ⧸ Subgroup.center ↥⁅A, A⁆) *
        Nat.card ↥(Subgroup.center ↥⁅A, A⁆) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    rw [hZ, mul_one, hc] at h2
    exact card_statedSp_ne_twenty160 hf hs hK ((Nat.card_congr eD.toEquiv).symm.trans h2)
  · push Not at hperf
    have hf1 : f = 1 := by
      by_contra hne
      have : 4 ≤ 2 ^ f :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact absurd (hK ▸ this) (not_le.2 hperf.1)
    subst hf1
    have hK2 : Nat.card K = 2 := by simpa using hK
    have hs2 : s ≤ 2 := by
      by_contra hlt
      exact absurd (hperf.2 hK2) (by omega)
    refine false_of_card_lt A ?_ hL
    rw [Nat.card_congr E.toEquiv]
    interval_cases s
    · rw [SymplecticFlag.card_statedSp, hK2]
      norm_num [Finset.Icc_self]
    · rw [SymplecticFlag.card_statedSp_two, hK2]
      norm_num

end Symplectic

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
