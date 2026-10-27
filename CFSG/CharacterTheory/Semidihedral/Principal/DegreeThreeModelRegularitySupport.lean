module

public import CFSG.CharacterTheory.Wreathed.OddUnitaryThreeCentralizerCore
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.Semidihedral.Principal.DegreeThreeModel

open CFSG.Assembly.LowTwoRank CFSG.Wreathed.OddLinearThreeCentralizerCore

theorem not_dvd_pow_sub_one {p a k : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hk : 1 ≤ k) :
    ¬ p ∣ (p ^ a) ^ k - 1 := by
  intro h
  have h1 : p ∣ (p ^ a) ^ k := by
    rw [← pow_mul]
    exact dvd_pow_self p (by positivity)
  have h2 : 1 ≤ (p ^ a) ^ k := Nat.one_le_pow _ _ (pow_pos hp.pos _)
  have h3 := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self h2] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)

theorem not_dvd_pow_add_one {p a k : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hk : 1 ≤ k) :
    ¬ p ∣ (p ^ a) ^ k + 1 := by
  intro h
  have h1 : p ∣ (p ^ a) ^ k := by
    rw [← pow_mul]
    exact dvd_pow_self p (by positivity)
  exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp h))

theorem padicValNat_pow_mul {p k m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) :
    padicValNat p (p ^ k * m) = k := by
  have : Fact p.Prime := ⟨hp⟩
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  rw [padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hm, add_zero]

theorem padicValNat_ppow_mul {p a k m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) :
    padicValNat p ((p ^ a) ^ k * m) = a * k := by
  rw [← pow_mul, padicValNat_pow_mul hp hm]

theorem padicValNat_mul_of_not_dvd_left {p a b : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) (hb : b ≠ 0) :
    padicValNat p (a * b) = padicValNat p b := by
  have : Fact p.Prime := ⟨hp⟩
  have ha0 : a ≠ 0 := by rintro rfl; exact ha (dvd_zero p)
  rw [padicValNat.mul ha0 hb, padicValNat.eq_zero_of_not_dvd ha, zero_add]

theorem not_dvd_card_scalars_subgroupOf {K : Type} [Field K] [Finite K] {n : ℕ} {p a : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) (hK : Nat.card K = p ^ a) (H : Subgroup (GL (Fin n) K)) :
    ¬ p ∣ Nat.card ((StatedScalars (Fin n) K).subgroupOf H) := by
  intro hdvd
  have h1 : Nat.card ((StatedScalars (Fin n) K).subgroupOf H) ∣
      Nat.card (StatedScalars (Fin n) K) :=
    Subgroup.card_dvd_of_injective
      ((H.subtype.comp ((StatedScalars (Fin n) K).subgroupOf H).subtype).codRestrict _
        fun x => Subgroup.mem_subgroupOf.mp x.2)
      fun x y hxy => by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : StatedScalars (Fin n) K => (z : GL (Fin n) K)) hxy
  have h2 : Nat.card (StatedScalars (Fin n) K) ∣ Nat.card Kˣ := Subgroup.card_range_dvd _
  rw [Nat.card_units, hK] at h2
  have h3 := not_dvd_pow_sub_one (k := 1) hp ha le_rfl
  rw [pow_one] at h3
  exact h3 ((hdvd.trans h1).trans h2)

theorem padicValNat_statedProj {K : Type} [Field K] [Finite K] {n : ℕ} {p a : ℕ}
    (hp : p.Prime) (ha : 1 ≤ a) (hK : Nat.card K = p ^ a) (H : Subgroup (GL (Fin n) K)) :
    padicValNat p (Nat.card (StatedProj H)) = padicValNat p (Nat.card H) := by
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars (Fin n) K).subgroupOf H)
  rw [hcard, mul_comm, padicValNat_mul_of_not_dvd_left hp
    (not_dvd_card_scalars_subgroupOf hp ha hK H) Nat.card_pos.ne']

theorem card_centralizer_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (g : G) :
    Nat.card (Subgroup.centralizer ({e g} : Set G')) =
      Nat.card (Subgroup.centralizer ({g} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨e.symm x, ?_⟩
      invFun := fun y => ⟨e y, ?_⟩
      left_inv := fun x => Subtype.ext (e.apply_symm_apply x)
      right_inv := fun y => Subtype.ext (e.symm_apply_apply y) }
  · have hx := Subgroup.mem_centralizer_singleton_iff.mp x.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, hx]
  · have hy := Subgroup.mem_centralizer_singleton_iff.mp y.2
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hy]

section Linear

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem not_dvd_card_center {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hK : Nat.card K = p ^ a) :
    ¬ p ∣ Nat.card (Subgroup.center (SL3 K)) := by
  intro hdvd
  have h1 : Nat.card (Subgroup.center (SL3 K)) ∣ Nat.card Kˣ := by
    have hinj : Function.Injective (fun g : Subgroup.center (SL3 K) =>
        ((g : SL3 K) : Matrix (Fin 3) (Fin 3) K) 0 0) := by
      intro g g' hgg'
      obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp g.2
      obtain ⟨c', -, hc'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp g'.2
      simp only at hgg'
      rw [← hc, ← hc'] at hgg'
      simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at hgg'
      apply Subtype.ext
      apply Subtype.ext
      rw [← hc, ← hc', hgg']
    let φ : Subgroup.center (SL3 K) →* Kˣ :=
      { toFun := fun g => Units.mk0 (((g : SL3 K) : Matrix (Fin 3) (Fin 3) K) 0 0) (by
          obtain ⟨c, hc3, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp g.2
          rw [← hc]
          simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
          rintro rfl
          simp at hc3)
        map_one' := by ext; simp
        map_mul' := fun g g' => by
          ext
          obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp g.2
          obtain ⟨c', -, hc'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp g'.2
          simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Units.val_mk0,
            Units.val_mul, ← hc, ← hc']
          simp [Matrix.scalar_apply] }
    exact Subgroup.card_dvd_of_injective φ fun g g' h => hinj (congrArg Units.val h)
  rw [Nat.card_units, hK] at h1
  have h3 := not_dvd_pow_sub_one (k := 1) hp ha le_rfl
  rw [pow_one] at h3
  exact h3 (hdvd.trans h1)

theorem padicValNat_card_psl3 {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hK : Nat.card K = p ^ a) :
    padicValNat p (Nat.card (StatedProj (StatedSL 3 K))) = 3 * a := by
  rw [padicValNat_statedProj hp ha hK, CFSG.SectionRank.OddCover.card_statedSL_three, hK,
    mul_assoc, padicValNat_ppow_mul hp, mul_comm]
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
  · exact not_dvd_pow_sub_one hp ha (by norm_num) h1
  · exact not_dvd_pow_sub_one hp ha (by norm_num) h1

theorem padicValNat_centralizer_psl3 {p a : ℕ} (hp : p.Prime) (hpodd : Odd p) (ha : 1 ≤ a)
    (hK : Nat.card K = p ^ a) (t : SL3 K ⧸ Subgroup.center (SL3 K)) (ht : orderOf t = 2) :
    padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set (SL3 K ⧸ Subgroup.center (SL3 K)))))
      = a := by
  have hF : Odd (Nat.card K) := by rw [hK]; exact hpodd.pow
  obtain ⟨z, ⟨hz, hzt⟩, -⟩ := unique_involution_lift K (Subgroup.center (SL3 K)) le_rfl t ht
  have hc := Subgroup.card_ker_mul_card_of_surjective
    (matrixQuotientCentralizer_surjective K hF (Subgroup.center (SL3 K)) le_rfl z hz)
  rw [matrixQuotientKernel_card K hF _ le_rfl z hz,
    CFSG.Wreathed.OddLinearTwoAutomorphisms.card_automorphisms K
      (minusSpace (matrixAction K z).toLinearMap) (matrixAction_finrank K hF z hz).1] at hc
  subst hzt
  have hv := congrArg (padicValNat p) hc
  rw [padicValNat_mul_of_not_dvd_left hp (not_dvd_card_center hp ha hK) Nat.card_pos.ne', hK,
    mul_assoc, ← pow_one (p ^ a), padicValNat_ppow_mul hp, mul_one] at hv
  · exact hv
  · intro h
    simp only [pow_one] at h
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
    · have h2 := not_dvd_pow_sub_one (k := 1) hp ha le_rfl
      rw [pow_one] at h2
      exact h2 (hp.dvd_of_dvd_pow h1)
    · have h2 := not_dvd_pow_add_one (k := 1) hp ha le_rfl
      rw [pow_one] at h2
      exact h2 h1

end Linear

section Unitary

open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBUnitaryIsometry
  CFSG.Wreathed.OddUnitaryThreeCentralizerCore CFSG.LocalAnalysis.ComponentInitial

theorem padicValNat_card_isometryGroup_plane {E : Type*} [Field E] [Finite E] {p f : ℕ}
    [Fact p.Prime] (hE : Nat.card E = (p ^ f) ^ 2) {P : Type*} [AddCommGroup P] [Module E P]
    [FiniteDimensional E P]
    (hP : P →ₛₗ[(CatalogueBUnitaryTwo.unitaryFieldConjugation p f hE).toRingHom] P →ₗ[E] E)
    (hsym : hP.IsSymm) (hnd : hP.Nondegenerate) (hdim : Module.finrank E P = 2) :
    padicValNat p (Nat.card (isometryGroup hP)) = f := by
  let data := originalFieldData p f hE
  have hbar := originalFieldData_bar p f hE
  let B : P →ₛₗ[data.bar] P →ₗ[E] E := LinearMap.mk₂'ₛₗ data.bar (RingHom.id E)
    (fun x y => hP x y) (fun x x' y => LinearMap.map_add₂ _ _ _ _) (fun c x y => by
      rw [LinearMap.map_smulₛₗ₂, ← hbar]) (fun x y y' => map_add _ _ _)
    (fun c x y => map_smul _ _ _)
  have hBapp : ∀ x y, B x y = hP x y := fun x y => rfl
  have hBsym : B.IsSymm := ⟨fun x y => by rw [hBapp, hBapp, ← hbar]; exact hsym.eq x y⟩
  have hBsep : B.SeparatingLeft := fun x hx => hnd.1 x fun y => by rw [← hBapp]; exact hx y
  obtain ⟨-, -, -, -, -, hpow, -⟩ :=
    CFSG.LinearGroups.unitary_full_group_order data hBsym hBsep hdim (by norm_num)
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv E P
  have hmap : (sesqUnitaryGroup B).map e.toMonoidHom = isometryGroup hP := by
    ext g
    constructor
    · rintro ⟨g', hg', rfl⟩ x y
      have := hg' x y
      rw [hBapp, hBapp] at this
      exact this
    · intro hg
      refine ⟨e.symm g, fun x y => ?_, by simp⟩
      rw [hBapp, hBapp]
      exact hg x y
  have hcard : Nat.card (isometryGroup hP) = Nat.card (sesqUnitaryGroup B) := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective e.injective
  rw [hcard, ← Nat.factorization_def _ (Fact.out : p.Prime)]
  have h1 : p ^ (Nat.card (sesqUnitaryGroup B)).factorization p = p ^ f := by
    rw [hpow]
    norm_num
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le h1

variable {K : Type} [Field K]

@[expose] noncomputable def stdHermitian (σ : K ≃+* K) :
    (Fin 3 → K) →ₛₗ[σ.toRingHom] (Fin 3 → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ σ.toRingHom (RingHom.id K) (fun x y => ∑ i, σ (x i) * y i)
    (fun x x' y => by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]
      rfl)
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)

theorem stdHermitian_apply (σ : K ≃+* K) (x y : Fin 3 → K) :
    stdHermitian σ x y = ∑ i, σ (x i) * y i := rfl

theorem stdHermitian_isSymm (σ : K ≃+* K) (hσ : σ ^ 2 = 1) : (stdHermitian σ).IsSymm := by
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    have := congrArg (fun τ : K ≃+* K => τ c) hσ
    simpa [pow_two] using this
  refine ⟨fun x y => ?_⟩
  change σ (∑ i, σ (x i) * y i) = ∑ i, σ (y i) * x i
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hσσ, mul_comm]

theorem stdHermitian_basis (σ : K ≃+* K) (i j : Fin 3) :
    stdHermitian σ (Pi.basisFun K (Fin 3) i) (Pi.basisFun K (Fin 3) j) =
      if i = j then 1 else 0 := by
  rw [stdHermitian_apply, Finset.sum_eq_single i]
  · simp only [Pi.basisFun_apply, Pi.single_eq_same, map_one, one_mul]
    by_cases hij : i = j
    · subst hij
      simp
    · simp only [hij, ite_false]
      exact Pi.single_eq_of_ne hij _
  · intro k _ hk
    simp [Pi.basisFun_apply, Pi.single_eq_of_ne hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem stdHermitian_nondegenerate (σ : K ≃+* K) : (stdHermitian σ).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · funext j
    have h1 := hx (Pi.basisFun K (Fin 3) j)
    rw [stdHermitian_apply, Finset.sum_eq_single j] at h1
    · simp only [Pi.basisFun_apply, Pi.single_eq_same, mul_one] at h1
      exact (map_eq_zero_iff σ σ.injective).mp h1
    · intro k _ hk
      simp [Pi.basisFun_apply, Pi.single_eq_of_ne hk]
    · intro h
      exact absurd (Finset.mem_univ j) h
  · funext j
    have h1 := hy (Pi.basisFun K (Fin 3) j)
    rw [stdHermitian_apply, Finset.sum_eq_single j] at h1
    · simpa [Pi.basisFun_apply] using h1
    · intro k _ hk
      simp [Pi.basisFun_apply, Pi.single_eq_of_ne hk]
    · intro h
      exact absurd (Finset.mem_univ j) h

variable [Finite K] {p f : ℕ} [Fact p.Prime]

@[expose] noncomputable def specialIsometryEquivStatedSU (hK : Nat.card K = (p ^ f) ^ 2) :
    specialIsometry (stdHermitian (CatalogueBUnitaryTwo.unitaryFieldConjugation p f hK)) ≃*
      StatedSU 3 (p ^ f) K :=
  letI : CharP K p := CatalogueBUnitaryTwo.unitaryFieldCharP p f hK
  (specialIsometryMatrixEquiv _ (Pi.basisFun K (Fin 3)) (stdHermitian_basis _)).trans
    (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 3))

theorem specialIsometryEquivStatedSU_val (hK : Nat.card K = (p ^ f) ^ 2)
    (g : specialIsometry (stdHermitian (CatalogueBUnitaryTwo.unitaryFieldConjugation p f hK))) :
    ((specialIsometryEquivStatedSU hK g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      LinearMap.toMatrix (Pi.basisFun K (Fin 3)) (Pi.basisFun K (Fin 3))
        g.val.val.toLinearMap := rfl

theorem mem_scalarCenter_of_scalar (hK : Nat.card K = (p ^ f) ^ 2)
    (g : specialIsometry (stdHermitian (CatalogueBUnitaryTwo.unitaryFieldConjugation p f hK)))
    (c : Kˣ) (hc : (Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) =
      (specialIsometryEquivStatedSU hK g : GL (Fin 3) K)) :
    g ∈ scalarCenter (stdHermitian (CatalogueBUnitaryTwo.unitaryFieldConjugation p f hK))
      (Module.finrank_fin_fun K) := by
  have hmat : LinearMap.toMatrix (Pi.basisFun K (Fin 3)) (Pi.basisFun K (Fin 3))
      g.val.val.toLinearMap = LinearMap.toMatrix (Pi.basisFun K (Fin 3)) (Pi.basisFun K (Fin 3))
        ((c : K) • LinearMap.id) := by
    rw [← specialIsometryEquivStatedSU_val, ← hc, map_smul, LinearMap.toMatrix_id,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]
    rfl
  have hlin := (LinearMap.toMatrix (Pi.basisFun K (Fin 3)) (Pi.basisFun K (Fin 3))).injective hmat
  have hgv : ∀ v, g.val.val v = (c : K) • v := fun v => by
    have := congrArg (fun φ : (Fin 3 → K) →ₗ[K] (Fin 3 → K) => φ v) hlin
    simpa using this
  have hnorm : CatalogueBUnitaryTwo.unitaryFieldConjugation p f hK (c : K) * (c : K) = 1 := by
    have h1 := g.val.property (Pi.basisFun K (Fin 3) 0) (Pi.basisFun K (Fin 3) 0)
    rw [hgv, CatalogueBHermitian.smul_left, map_smul, stdHermitian_basis] at h1
    simpa [mul_assoc] using h1
  have hcube : (c : K) ^ 3 = 1 := by
    have h1 := (mem_specialIsometry_iff _ g.val).mp g.property
    rw [hlin, LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_fin_fun] at h1
    exact h1
  let a : normOneUnits (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f hK) :=
    ⟨c, hnorm⟩
  have ha : a ∈ cubicUnits (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f hK) := by
    rw [cubicUnits, MonoidHom.mem_ker, powMonoidHom_apply]
    exact Subtype.ext (Units.ext (by simpa using hcube))
  refine ⟨⟨a, ha⟩, Subtype.ext (Subtype.ext (LinearEquiv.ext fun v => ?_))⟩
  rw [scalarSpecial_apply, hgv]

@[expose] noncomputable def scalarPullback (hK : Nat.card K = (p ^ f) ^ 2) :
    Subgroup
      (specialIsometry (stdHermitian (CatalogueBUnitaryTwo.unitaryFieldConjugation p f hK))) :=
  ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K)).comap
    (specialIsometryEquivStatedSU hK).toMonoidHom

instance scalarPullback_normal (hK : Nat.card K = (p ^ f) ^ 2) :
    (scalarPullback hK).Normal := by
  unfold scalarPullback
  infer_instance

theorem scalarPullback_le_scalarCenter (hK : Nat.card K = (p ^ f) ^ 2) :
    scalarPullback hK ≤
      scalarCenter (stdHermitian (CatalogueBUnitaryTwo.unitaryFieldConjugation p f hK))
        (Module.finrank_fin_fun K) := by
  intro g hg
  rw [scalarPullback, Subgroup.mem_comap, Subgroup.mem_subgroupOf] at hg
  obtain ⟨c, hc⟩ := hg
  exact mem_scalarCenter_of_scalar hK g c hc

@[expose] noncomputable def quotientEquivStatedProj (hK : Nat.card K = (p ^ f) ^ 2) :
    specialIsometry (stdHermitian (CatalogueBUnitaryTwo.unitaryFieldConjugation p f hK)) ⧸
        scalarPullback hK ≃* StatedProj (StatedSU 3 (p ^ f) K) :=
  QuotientGroup.congr _ _ (specialIsometryEquivStatedSU hK)
    (Subgroup.map_comap_eq_self_of_surjective (specialIsometryEquivStatedSU hK).surjective _)

theorem padicValNat_card_psu3 (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 2) :
    padicValNat p (Nat.card (StatedProj (StatedSU 3 (p ^ f) K))) = 3 * f := by
  have hp : p.Prime := Fact.out
  let : CharP K p := CatalogueBUnitaryTwo.unitaryFieldCharP p f hK
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  rw [padicValNat_statedProj hp (by omega) hK', CFSG.SectionRank.OddCover.card_statedSU_three hK,
    mul_assoc, padicValNat_ppow_mul hp, mul_comm]
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
  · exact not_dvd_pow_sub_one hp hf (by norm_num) h1
  · exact not_dvd_pow_add_one hp hf (by norm_num) h1

theorem padicValNat_centralizer_psu3 (hpodd : Odd p) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (t : StatedProj (StatedSU 3 (p ^ f) K))
    (ht : orderOf t = 2) :
    padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set (StatedProj (StatedSU 3 (p ^ f) K)))))
      = f := by
  have hp : p.Prime := Fact.out
  set σ := CatalogueBUnitaryTwo.unitaryFieldConjugation p f hK
  set h := stdHermitian σ
  have hsigma := (CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f hK).1
  have hsym : h.IsSymm := stdHermitian_isSymm σ hsigma
  have hnd : h.Nondegenerate := stdHermitian_nondegenerate σ
  have hdim : Module.finrank K (Fin 3 → K) = 3 := Module.finrank_fin_fun K
  have : Finite (isometryGroup h) := isometryGroup_finite h
  let φ := quotientEquivStatedProj hK
  have hcard := card_centralizer_mulEquiv φ.symm t
  rw [← hcard]
  have ht' : orderOf (φ.symm t) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact ht
  obtain ⟨z, hz, hzt, -, hPdim, -, hPnd, -, -, -, -, -, hsurj, -, hkercard, -⟩ :=
    odd_unitary_three_involution_centralizer_core p f hpodd hK h hsym hnd hdim
      (scalarPullback hK) (scalarPullback_le_scalarCenter hK) (φ.symm t) ht'
  have hc := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [hkercard] at hc
  have hv := congrArg (padicValNat p) hc
  have hD : ¬ p ∣ Nat.card (scalarPullback hK) := by
    have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
    have h1 : Nat.card (scalarPullback hK) =
        Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K)) := by
      rw [← Subgroup.card_map_of_injective (f := (specialIsometryEquivStatedSU hK).toMonoidHom)
        (specialIsometryEquivStatedSU hK).injective]
      exact congrArg (fun S : Subgroup (StatedSU 3 (p ^ f) K) => Nat.card S)
        (Subgroup.map_comap_eq_self_of_surjective (specialIsometryEquivStatedSU hK).surjective _)
    rw [h1]
    exact not_dvd_card_scalars_subgroupOf hp (by omega) hK' _
  rw [padicValNat_mul_of_not_dvd_left hp hD Nat.card_pos.ne',
    padicValNat_card_isometryGroup_plane hK _ (hsym.domRestrict _) hPnd hPdim] at hv
  exact hv

end Unitary

end CFSG.Semidihedral.Principal.DegreeThreeModel
