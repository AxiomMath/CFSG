module

public import CFSG.CharacterTheory.BrauerLinearThree.LocalCounting
public import CFSG.CharacterTheory.Wreathed.DegreeThreeModelFullCenterProjective
public import CFSG.CharacterTheory.Semidihedral.Local.OddKernelLocalParameterSupport
public import CFSG.CharacterTheory.BrauerLinearThree.CentralizerSylowSemidihedral

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes
open CFSG.Semidihedral.OddLinearNormals (imageSL entrywiseSL entrywiseSL_matrix
  entrywiseSL_injective normal_odd_specialLinear_eq_bot scalar_of_centralizes_entrywiseSL)

section SL

variable {F : Type} [Field F]

theorem mem_imageSL_id_iff (g : GL (Fin 2) F) :
    g ∈ imageSL (RingHom.id F) ↔ (g : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [entrywiseSL_matrix]
    simp
  · intro h
    refine ⟨(⟨(g : Matrix (Fin 2) (Fin 2) F), h⟩ : Matrix.SpecialLinearGroup (Fin 2) F), ?_⟩
    apply Units.ext
    rfl

theorem imageSL_id_normal : (imageSL (RingHom.id F)).Normal := by
  constructor
  intro n hn g
  rw [mem_imageSL_id_iff] at hn ⊢
  have hg : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := (g.isUnit.map Matrix.detMonoidHom).ne_zero
  simp only [Units.val_mul, Matrix.det_mul, Matrix.GeneralLinearGroup.coe_inv,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hn, mul_one]
  exact mul_inv_cancel₀ hg

end SL

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

omit [Finite F] in
theorem centralizerHom_surjective : Function.Surjective (centralizerHom φ) := by
  intro c
  obtain ⟨A, hA⟩ := QuotientGroup.mk_surjective (φ c)
  exact ⟨A, by rw [centralizerHom, MonoidHom.comp_apply]; simp [hA]⟩

@[expose] noncomputable def imageSLC : Subgroup (Subgroup.centralizer ({J} : Set G)) :=
  (imageSL (RingHom.id F)).map (centralizerHom φ)

omit [Finite F] in
theorem imageSLC_normal : (imageSLC φ).Normal :=
  (imageSL_id_normal (F := F)).map _ (centralizerHom_surjective φ)

omit [Finite F] in
include hZ hZodd h2 in
theorem centralizerHom_comp_entrywiseSL_injective :
    Function.Injective ((centralizerHom φ).comp (entrywiseSL (RingHom.id F))) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : linearCentralizerHom φ (entrywiseSL (RingHom.id F) x) = 1 := by
    rw [← coe_centralizerHom]
    exact congrArg Subtype.val hx
  rw [linearCentralizerHom_eq_one_iff] at h1
  have hdet : ((entrywiseSL (RingHom.id F) x : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [entrywiseSL_matrix]
    simp
  have h3 := eq_one_of_mem_odd_of_det h2 hZ hZodd h1 hdet
  exact entrywiseSL_injective (RingHom.id F) Function.injective_id (h3.trans (map_one _).symm)

include hZ hZodd h2 in
theorem disjoint_imageSLC_of_normal_odd (hq3 : 3 ≤ Nat.card F)
    (K : Subgroup (Subgroup.centralizer ({J} : Set G))) (hK : K.Normal)
    (hKodd : Odd (Nat.card K)) : Disjoint K (imageSLC φ) := by
  set f := (centralizerHom φ).comp (entrywiseSL (RingHom.id F)) with hf_def
  have hf := centralizerHom_comp_entrywiseSL_injective φ hZ hZodd h2
  have hFodd : Odd (Nat.card F) := odd_card_F h2
  have hcomap : K.comap f = ⊥ :=
    normal_odd_specialLinear_eq_bot F hFodd hq3 _ (hK.comap f)
      (hKodd.of_dvd_nat (K.card_comap_dvd_of_injective f hf))
  have hrange : imageSLC φ = f.range := by
    rw [imageSLC, imageSL, hf_def, MonoidHom.range_comp]
  rw [Subgroup.disjoint_def]
  intro x hxK hxS
  rw [hrange] at hxS
  obtain ⟨y, rfl⟩ := hxS
  have hy : y ∈ K.comap f := hxK
  rw [hcomap, Subgroup.mem_bot] at hy
  rw [hy, map_one]

include hZ hZodd h2 in
theorem mem_centerSub_of_mem_normal_odd (hq3 : 3 ≤ Nat.card F)
    (K : Subgroup (Subgroup.centralizer ({J} : Set G))) (hK : K.Normal)
    (hKodd : Odd (Nat.card K)) {k : Subgroup.centralizer ({J} : Set G)} (hk : k ∈ K) :
    (k : G) ∈ centerSub φ := by
  have hdisj := disjoint_imageSLC_of_normal_odd φ hZ hZodd h2 hq3 K hK hKodd
  obtain ⟨A, rfl⟩ := centralizerHom_surjective φ k
  have hcomm : ∀ x : Matrix.SpecialLinearGroup (Fin 2) F,
      Commute A (entrywiseSL (RingHom.id F) x) := by
    intro x
    have hx : centralizerHom φ (entrywiseSL (RingHom.id F) x) ∈ imageSLC φ :=
      ⟨_, ⟨x, rfl⟩, rfl⟩
    have h := Subgroup.commute_of_normal_of_disjoint K (imageSLC φ) hK (imageSLC_normal φ) hdisj
      _ _ hk hx
    have h' : linearCentralizerHom φ A * linearCentralizerHom φ (entrywiseSL (RingHom.id F) x) =
        linearCentralizerHom φ (entrywiseSL (RingHom.id F) x) * linearCentralizerHom φ A := by
      have := congrArg Subtype.val h.eq
      simpa only [Subgroup.coe_mul, coe_centralizerHom] using this
    exact commute_of_linearCentralizerHom_commute φ hZ hZodd h2 h'
  obtain ⟨c, hc⟩ := scalar_of_centralizes_entrywiseSL (RingHom.id F) A hcomm
  have hc0 : c ≠ 0 := by
    intro h
    have hdet := (A.isUnit.map Matrix.detMonoidHom).ne_zero
    apply hdet
    change (A : Matrix (Fin 2) (Fin 2) F).det = 0
    rw [← hc, h]
    simp
  rw [mem_centerSub, coe_centralizerHom]
  refine ⟨Units.mk0 c hc0, ?_⟩
  congr 1
  apply Units.ext
  rw [← hc]
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar]

include hZ hZodd h2 in
theorem mem_centerSub_of_mem_pPrimeCore (hq3 : 3 ≤ Nat.card F)
    {x : Subgroup.centralizer ({J} : Set G)}
    (hx : x ∈ CFSG.pPrimeCore 2 (Subgroup.centralizer ({J} : Set G))) :
    (x : G) ∈ centerSub φ := by
  have hle : CFSG.pPrimeCore 2 (Subgroup.centralizer ({J} : Set G)) ≤
      (centerSub φ).subgroupOf (Subgroup.centralizer ({J} : Set G)) := by
    unfold CFSG.pPrimeCore
    apply sSup_le
    rintro K ⟨hKn, hKc⟩ k hk
    rw [Subgroup.mem_subgroupOf]
    exact mem_centerSub_of_mem_normal_odd φ hZ hZodd h2 hq3 K hKn
      (Nat.coprime_two_left.mp hKc) hk
  have := hle hx
  rwa [Subgroup.mem_subgroupOf] at this

omit [Finite F] in
include hZ hZodd h2 hJ in
theorem J_mem_centerSub : J ∈ centerSub φ := by
  rw [mem_centerSub]
  refine ⟨-1, ?_⟩
  have e : Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : Fˣ) = -1 := by
    apply Units.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.one_apply]
  rw [e]
  exact linearCentralizerHom_neg_one φ hZ hZodd h2 hJ

omit [Finite F] in
include hZ hZodd h2 hJ in
theorem eq_one_or_eq_J_of_mem_centerSub {w : G} (hw : w ∈ centerSub φ) (hw2 : w * w = 1) :
    w = 1 ∨ w = J := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hw1, hwJ⟩ := hcon
  have hwC : J * w = w * J := (commute_of_mem_centerSub φ hw (rfl : J * J = J * J)).symm
  obtain ⟨h, hh, hhw⟩ := exists_conj_invJ₁ φ hZ hZodd h2 hJ hwC hw2 hw1 hwJ
  have hwh : w * h = h * w := commute_of_mem_centerSub φ hw hh
  have hJ₁w : invJ₁ φ = w := by
    calc invJ₁ φ = h⁻¹ * (h * invJ₁ φ * h⁻¹) * h := by group
      _ = h⁻¹ * w * h := by rw [hhw]
      _ = w := by rw [mul_assoc, hwh, ← mul_assoc, inv_mul_cancel, one_mul]
  have hx : rootUp φ 1 ∈ rootX₁ φ := (mem_rootX₁ φ).mpr ⟨1, rfl⟩
  have hc : invJ₁ φ * rootUp φ 1 = rootUp φ 1 * invJ₁ φ := by
    rw [hJ₁w]
    exact commute_of_mem_centerSub φ hw (linearCentralizerHom_commute φ _)
  have h1 := inverts_invJ₁_rootX₁ φ _ hx
  rw [hc, mul_inv_cancel_right, ← rootUp_neg] at h1
  have h3 := rootUp_injective φ hZ h1
  apply h2
  linear_combination h3

omit [Finite F] in
include hZ hZodd in
theorem card_centerSub_eq_two_mul_odd (hq : Nat.card F % 4 = 3) :
    ∃ u : ℕ, Odd u ∧ Nat.card (centerSub φ) = 2 * u := by
  have hm : Nat.card (centerSub φ) * Nat.card Z = Nat.card F - 1 := card_scalarImage φ hZ
  obtain ⟨w, hw⟩ : ∃ w, Nat.card F - 1 = 2 * w ∧ Odd w := by
    refine ⟨(Nat.card F - 1) / 2, by omega, ?_⟩
    rw [Nat.odd_iff]
    omega
  have heven : Even (Nat.card (centerSub φ)) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have : Odd (Nat.card F - 1) := by rw [← hm]; exact hodd.mul hZodd
    rw [hw.1] at this
    exact (Nat.not_even_iff_odd.mpr this) (even_two_mul w)
  obtain ⟨u, hu⟩ := heven
  refine ⟨u, ?_, by omega⟩
  have h3 : u * Nat.card Z = w := by
    have : 2 * (u * Nat.card Z) = 2 * w := by rw [← hw.1, ← hm, hu]; ring
    omega
  have hw' : Odd (u * Nat.card Z) := by rw [h3]; exact hw.2
  exact (Nat.odd_mul.mp hw').1

include hZ hZodd h2 hJ in
theorem mem_NZ_of_mem_centerSub (hq : Nat.card F % 4 = 3)
    {c : Subgroup.centralizer ({J} : Set G)} (hc : (c : G) ∈ centerSub φ) :
    c ∈ CFSG.Semidihedral.ActualSimpleLayerLocalPackage.NZ J := by
  classical
  have : Finite (Subgroup.centralizer ({J} : Set G)) := Finite.of_equiv _ φ.symm.toEquiv
  obtain ⟨u, hu, hcard⟩ := card_centerSub_eq_two_mul_odd φ hZ hZodd hq
  let O : Subgroup (Subgroup.centralizer ({J} : Set G)) :=
    { carrier := {z | (z : G) ∈ centerSub φ ∧ z ^ u = 1}
      one_mem' := ⟨(centerSub φ).one_mem, one_pow u⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨(centerSub φ).mul_mem ha hb, ?_⟩
        have hab : Commute a b := Subtype.ext (commute_of_mem_centerSub φ ha
          (Subgroup.mem_centralizer_singleton_iff.mp b.2).symm)
        rw [hab.mul_pow, ha', hb', one_mul]
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨(centerSub φ).inv_mem ha, by rw [inv_pow, ha', inv_one]⟩ }
  have hOn : O.Normal := by
    constructor
    rintro z ⟨hz, hz'⟩ g
    have hzg : g * z * g⁻¹ = z := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← commute_of_mem_centerSub φ hz (Subgroup.mem_centralizer_singleton_iff.mp g.2).symm,
        mul_inv_cancel_right]
    rw [hzg]
    exact ⟨hz, hz'⟩
  have hOodd : Odd (Nat.card O) := by
    by_contra hcon
    rw [Nat.not_odd_iff_even] at hcon
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hcon)
    have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have hxu : x ^ u = 1 := Subtype.ext x.2.2
    have h1 : x = 1 := by
      have := pow_gcd_eq_one.mpr ⟨hx2, hxu⟩
      rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hu), pow_one] at this
    rw [h1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hON : O ≤ CFSG.pPrimeCore 2 (Subgroup.centralizer ({J} : Set G)) := by
    unfold CFSG.pPrimeCore
    exact le_sSup ⟨hOn, Nat.coprime_two_left.mpr hOodd⟩
  have hc2u : c ^ (2 * u) = 1 := by
    have h := pow_card_eq_one' (x := (⟨c, hc⟩ : centerSub φ))
    rw [hcard] at h
    apply Subtype.ext
    simpa using congrArg Subtype.val h
  obtain ⟨k, hk⟩ := hu
  have hcO : c ^ (u + 1) ∈ O := by
    refine ⟨(centerSub φ).pow_mem hc _, ?_⟩
    rw [← pow_mul, show (u + 1) * u = 2 * u * (k + 1) by rw [hk]; ring, pow_mul, hc2u, one_pow]
  have hcZ : (c ^ u)⁻¹ ∈ CFSG.Semidihedral.ActualSimpleLayerLocalPackage.Z J := by
    apply Subgroup.inv_mem
    have hsq : (c : G) ^ u * (c : G) ^ u = 1 := by
      rw [← pow_add, ← two_mul]
      exact congrArg Subtype.val hc2u
    rcases eq_one_or_eq_J_of_mem_centerSub φ hZ hZodd h2 hJ ((centerSub φ).pow_mem hc u) hsq
      with h | h
    · have : c ^ u = 1 := Subtype.ext (by simpa using h)
      rw [this]
      exact Subgroup.one_mem _
    · have : c ^ u = CFSG.Semidihedral.ActualSimpleLayerLocalPackage.tInC J :=
        Subtype.ext (by simpa [CFSG.Semidihedral.ActualSimpleLayerLocalPackage.tInC] using h)
      rw [this]
      exact Subgroup.mem_zpowers _
  have hceq : c = c ^ (u + 1) * (c ^ u)⁻¹ := by
    rw [pow_succ', mul_inv_cancel_right]
  rw [hceq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hON hcO)) (Subgroup.mem_sup_right hcZ)

include hZ hZodd h2 hJ in
theorem NZ_eq_centerSub (hq : Nat.card F % 4 = 3) (hq3 : 3 ≤ Nat.card F) :
    CFSG.Semidihedral.ActualSimpleLayerLocalPackage.NZ J =
      (centerSub φ).subgroupOf (Subgroup.centralizer ({J} : Set G)) := by
  apply le_antisymm
  · apply sup_le
    · intro x hx
      rw [Subgroup.mem_subgroupOf]
      exact mem_centerSub_of_mem_pPrimeCore φ hZ hZodd h2 hq3 hx
    · rw [Subgroup.zpowers_le, Subgroup.mem_subgroupOf]
      exact J_mem_centerSub φ hZ hZodd h2 hJ
  · intro c hc
    rw [Subgroup.mem_subgroupOf] at hc
    exact mem_NZ_of_mem_centerSub φ hZ hZodd h2 hJ hq hc

omit [Finite F] [Z.Normal] in
include hZ in
theorem le_center_GL : Z ≤ Subgroup.center (GL (Fin 2) F) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact hZ

@[expose] noncomputable def toPGL :
    Subgroup.centralizer ({J} : Set G) →* GL (Fin 2) F ⧸ Subgroup.center (GL (Fin 2) F) :=
  (QuotientGroup.map Z (Subgroup.center (GL (Fin 2) F)) (MonoidHom.id _)
    (le_center_GL hZ)).comp φ.toMonoidHom

omit [Finite F] in
theorem toPGL_centralizerHom (A : GL (Fin 2) F) :
    toPGL φ hZ (centralizerHom φ A) = QuotientGroup.mk A := by
  change QuotientGroup.map Z (Subgroup.center (GL (Fin 2) F)) (MonoidHom.id _) (le_center_GL hZ)
    (φ (φ.symm (QuotientGroup.mk' Z A))) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

omit [Finite F] in
theorem toPGL_surjective : Function.Surjective (toPGL φ hZ) := by
  intro x
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨centralizerHom φ A, toPGL_centralizerHom φ hZ A⟩

omit [Finite F] in
theorem ker_toPGL :
    (toPGL φ hZ).ker = (centerSub φ).subgroupOf (Subgroup.centralizer ({J} : Set G)) := by
  ext c
  obtain ⟨A, rfl⟩ := centralizerHom_surjective φ c
  rw [MonoidHom.mem_ker, toPGL_centralizerHom, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    coe_centralizerHom, mem_centerSub, Matrix.GeneralLinearGroup.center_eq_range_scalar]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    have hmem := (linearCentralizerHom_eq_iff φ _ _).mp ha
    have h1 := hZ hmem
    have h3 : (Matrix.GeneralLinearGroup.scalar (Fin 2) a)⁻¹ *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) a * A⁻¹) ∈
        CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ ⟨a, rfl⟩) h1
    rw [inv_mul_cancel_left] at h3
    have h4 := Subgroup.inv_mem _ h3
    rw [inv_inv] at h4
    exact h4

include hZ hZodd h2 hJ in
@[expose] noncomputable def gammaEquiv (hq : Nat.card F % 4 = 3) (hq3 : 3 ≤ Nat.card F) :
    CFSG.Semidihedral.ActualSimpleLayerLocalPackage.Gamma J ≃*
      GL (Fin 2) F ⧸ Subgroup.center (GL (Fin 2) F) :=
  (QuotientGroup.quotientMulEquivOfEq
    ((NZ_eq_centerSub φ hZ hZodd h2 hJ hq hq3).trans (ker_toPGL φ hZ).symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (toPGL_surjective φ hZ))

section Layer

open CFSG.Wreathed.DegreeThreeModelFullCenter (scalarSubgroup
  matrix_overgroup_generalizedFitting_full_conclusions)

omit [Finite F] in
@[expose] noncomputable def pglTopEquiv :
    GL (Fin 2) F ⧸ Subgroup.center (GL (Fin 2) F) ≃*
      (⊤ : Subgroup (GL (Fin 2) F)) ⧸ scalarSubgroup (⊤ : Subgroup (GL (Fin 2) F)) :=
  QuotientGroup.congr _ _ Subgroup.topEquiv.symm (by
    ext x
    simp only [Subgroup.mem_map, scalarSubgroup, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩)

theorem card_top_GL :
    Nat.card (⊤ : Subgroup (GL (Fin 2) F)) =
      Nat.card F * (Nat.card F ^ 2 - 1) *
        Nat.card (scalarSubgroup (⊤ : Subgroup (GL (Fin 2) F))) := by
  let : Fintype F := Fintype.ofFinite F
  have hsc : Nat.card (scalarSubgroup (⊤ : Subgroup (GL (Fin 2) F))) = Nat.card F - 1 := by
    rw [scalarSubgroup, ← card_statedScalars (F := F), CFSG.Assembly.LowTwoRank.StatedScalars,
      ← Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv
  rw [hsc, Subgroup.card_top, Matrix.card_GL_field, Fin.prod_univ_two, Nat.card_eq_fintype_card]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  have h1 : 1 ≤ Fintype.card F ^ 2 := Nat.one_le_pow _ _ hq
  have h3 : Fintype.card F ≤ Fintype.card F ^ 2 := by nlinarith
  zify [h1, h3, hq]
  ring

include φ hZ hZodd h2 hJ in
theorem layer_hypotheses (hq : Nat.card F % 4 = 3) (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hq5 : 5 ≤ Nat.card F) :
    IsSimpleGroup (CFSG.generalizedFitting
        (CFSG.Semidihedral.ActualSimpleLayerLocalPackage.Gamma J)) ∧
      (∃ a b : CFSG.generalizedFitting
        (CFSG.Semidihedral.ActualSimpleLayerLocalPackage.Gamma J), a * b ≠ b * a) ∧
      Subgroup.centralizer (CFSG.generalizedFitting
          (CFSG.Semidihedral.ActualSimpleLayerLocalPackage.Gamma J) :
            Set (CFSG.Semidihedral.ActualSimpleLayerLocalPackage.Gamma J)) = ⊥ ∧
      (∀ U : Sylow 2 (CFSG.generalizedFitting
          (CFSG.Semidihedral.ActualSimpleLayerLocalPackage.Gamma J)), ¬ IsCyclic U) ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (CFSG.generalizedFitting
          (CFSG.Semidihedral.ActualSimpleLayerLocalPackage.Gamma J)) .PSL 2 p f := by
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd' with h | h
    · exfalso
      have hqodd := odd_card_F h2
      rw [hF, h] at hqodd
      exact (Nat.not_even_iff_odd.mpr hqodd) ((Nat.even_pow' (by omega)).mpr even_two)
    · exact h
  have hq3 : 3 ≤ Nat.card F := by omega
  set θ := (gammaEquiv φ hZ hZodd h2 hJ hq hq3).trans (pglTopEquiv (F := F)) with hθ
  obtain ⟨hs, hnab, hcen, -, hmodel, hcardL, -⟩ :=
    matrix_overgroup_generalizedFitting_full_conclusions (F := F) (E := F) p f hp hpodd hf
      (hF ▸ hq5) hF (RingHom.id F) 1 ⊤ le_top (card_top_GL (F := F))
  set L' := CFSG.generalizedFitting ((⊤ : Subgroup (GL (Fin 2) F)) ⧸
    scalarSubgroup (⊤ : Subgroup (GL (Fin 2) F)))
  set LJ := CFSG.generalizedFitting (CFSG.Semidihedral.ActualSimpleLayerLocalPackage.Gamma J)
  have : Finite (Subgroup.centralizer ({J} : Set G)) := Finite.of_equiv _ φ.symm.toEquiv
  have : IsSimpleGroup L' := hs
  have hmap : L'.map θ.symm.toMonoidHom = LJ :=
    CFSG.Semidihedral.Local.OddKernel.generalizedFitting_map_of_mulEquiv θ.symm hnab hcen
  let eL : L' ≃* LJ :=
    (L'.equivMapOfInjective θ.symm.toMonoidHom θ.symm.injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hsJ : IsSimpleGroup LJ := eL.symm.isSimpleGroup
  have hnabJ : ∃ a b : LJ, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨eL a, eL b, fun h => hab (eL.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  have hcenJ : Subgroup.centralizer
      (LJ : Set (CFSG.Semidihedral.ActualSimpleLayerLocalPackage.Gamma J)) = ⊥ := by
    have := CFSG.Semidihedral.Local.OddKernel.centralizer_map_eq_bot_of_mulEquiv θ.symm L' hcen
    rwa [hmap] at this
  refine ⟨hsJ, hnabJ, hcenJ, ?_, ?_⟩
  · intro U
    have : Group.IsPerfect LJ :=
      CFSG.Semidihedral.CoreFreeDihedral.isPerfect_of_simple_nonabelian hnabJ
    have heven : Even (Nat.card LJ) := by
      rw [← Nat.card_congr eL.toEquiv, hcardL, ← hF]
      have hqodd := odd_card_F h2
      obtain ⟨k, hk⟩ := hqodd
      rw [hk]
      refine ⟨k * (2 * k + 1) * (k + 1), ?_⟩
      have e1 : (2 * k + 1) ^ 2 - 1 = 4 * k * (k + 1) := by
        rw [show (2 * k + 1) ^ 2 = 4 * k * (k + 1) + 1 by ring]
        omega
      rw [e1]
      rw [show (2 * k + 1) * (4 * k * (k + 1)) = 2 * (2 * (k * (2 * k + 1) * (k + 1))) by ring,
        Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
      ring
    exact CFSG.TwoRankLowerBound.Helpers.sylow_two_not_isCyclic_of_perfect LJ heven U
  · obtain ⟨hadm, K, hK1, hK2, hKc, ⟨e⟩⟩ := hmodel
    exact ⟨hadm, K, hK1, hK2, hKc, ⟨eL.symm.trans e⟩⟩

end Layer

include φ hZodd h2 in
theorem factorization_two_card (hq : Nat.card F % 4 = 3)
    (hcard : Nat.card G * Nat.card Z =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1)) :
    (Nat.card G).factorization 2 = (Nat.card F + 1).factorization 2 + 2 := by
  have : Finite (Subgroup.centralizer ({J} : Set G)) := Finite.of_equiv _ φ.symm.toEquiv
  obtain ⟨-, -, -, w, hw, hqw⟩ := semidihedral_arith hq
  have hG := card_eq_card_centralizer_mul φ hcard
  have hC := card_centralizer_J φ
  set m := (Nat.card F + 1).factorization 2
  set c := Nat.card (Subgroup.centralizer ({J} : Set G))
  have hqodd : Odd (Nat.card F) := odd_card_F h2
  have hodd2 : Odd (Nat.card F ^ 2 * (Nat.card F ^ 2 + Nat.card F + 1)) :=
    hqodd.pow.mul ((hqodd.pow.add_odd hqodd).add_one)
  have hl : (Nat.card Z).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hZodd)
      (even_iff_two_dvd.mpr h))
  have hw2 : w.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hw)
      (even_iff_two_dvd.mpr h))
  have hodd2' : (Nat.card F ^ 2 * (Nat.card F ^ 2 + Nat.card F + 1)).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hodd2)
      (even_iff_two_dvd.mpr h))
  have hc0 : c ≠ 0 := Nat.card_pos.ne'
  have hl0 : Nat.card Z ≠ 0 := Nat.card_pos.ne'
  have hcv : c.factorization 2 = m + 2 := by
    have h1 : (c * Nat.card Z).factorization 2 = (2 ^ (m + 2) * w).factorization 2 := by
      rw [hC, hqw]
    rw [Nat.factorization_mul hc0 hl0, Nat.factorization_mul (by positivity) hw.pos.ne',
      Finsupp.add_apply, Finsupp.add_apply, hl, hw2, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same] at h1
    omega
  rw [hG, Nat.factorization_mul hc0 hodd2.pos.ne', Finsupp.add_apply, hcv, hodd2']

include φ hZ hZodd h2 hJ in
theorem exists_semidihedral_sylow_presentation [Finite G] (hq : Nat.card F % 4 = 3)
    (hcard : Nat.card G * Nat.card Z =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1)) :
    4 ≤ (Nat.card F + 1).factorization 2 + 2 ∧
      ∃ (S : Sylow 2 G) (e' : CFSG.Open.SemidihedralGroup
          ((Nat.card F + 1).factorization 2 + 2) ≃* (S : Subgroup G)),
        (e' (CFSG.Semidihedral.r _) : G) ^
            (CFSG.Semidihedral.modulus ((Nat.card F + 1).factorization 2 + 2) / 2) = J ∧
          (e' (CFSG.Semidihedral.s _) : G) = invJ₁ φ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set m := (Nat.card F + 1).factorization 2 with hm
  obtain ⟨hm2, h, -, -, hhpow, -, -, hPcard, -, e, he_r, he_s, -, -⟩ :=
    exists_semidihedral_sylow φ hZ hZodd h2 hJ hq hm.symm
  have hv := factorization_two_card φ hZodd h2 hq hcard
  let S : Sylow 2 G := Sylow.ofCard (Subgroup.zpowers h ⊔ Subgroup.zpowers (invJ₁ φ))
    (by rw [hPcard, hv])
  refine ⟨by omega, S, e.trans (MulEquiv.subgroupCongr (Sylow.coe_ofCard _ _).symm), ?_, ?_⟩
  · have hmod : CFSG.Semidihedral.modulus (m + 2) / 2 = 2 ^ m := by
      rw [CFSG.Semidihedral.modulus, show m + 2 - 1 = m + 1 by omega, pow_succ,
        Nat.mul_div_cancel _ (by norm_num)]
    rw [hmod]
    change ((e (CFSG.Semidihedral.r (m + 2)) : G)) ^ 2 ^ m = J
    rw [he_r, hhpow]
  · change ((e (CFSG.Semidihedral.s (m + 2)) : G)) = invJ₁ φ
    exact he_s

end CFSG.BrauerLinearThree
