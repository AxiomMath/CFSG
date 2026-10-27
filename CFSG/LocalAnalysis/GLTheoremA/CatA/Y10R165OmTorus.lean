module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerD4MExt
public import CFSG.LieType.SeitzGeneration.OrthBlocks
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open QuadraticMap CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.SeitzGeneration.OrthBlk
open CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4
open scoped commutatorElement

namespace OmTorus

variable {F W : Type} [Field F] [AddCommGroup W] [Module F W] {Q : QuadraticForm F W}

private noncomputable def hypDiagLin (P : HypPair Q) (a : F) : W →ₗ[F] W :=
  LinearMap.id + (a - 1) • LinearMap.smulRight (polarBilin Q P.f) P.e +
    (a⁻¹ - 1) • LinearMap.smulRight (polarBilin Q P.e) P.f

private theorem hypDiagLin_apply (P : HypPair Q) (a : F) (x : W) :
    hypDiagLin P a x = x + (a - 1) • (polar Q x P.f • P.e) +
      (a⁻¹ - 1) • (polar Q x P.e • P.f) := by
  simp only [hypDiagLin, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, polarBilin_apply_apply]
  rw [polar_comm Q P.f x, polar_comm Q P.e x]

private theorem hypDiagLin_apply_e (P : HypPair Q) (a : F) :
    hypDiagLin P a P.e = a • P.e := by
  rw [hypDiagLin_apply, P.polar_ef, polar_self_eq_zero P.Q_e]
  simp only [mul_zero, zero_smul, smul_zero, add_zero]
  module

private theorem hypDiagLin_apply_f (P : HypPair Q) (a : F) :
    hypDiagLin P a P.f = a⁻¹ • P.f := by
  rw [hypDiagLin_apply, P.polar_ff, P.polar_fe]
  simp only [mul_one, mul_zero, zero_smul, smul_zero, add_zero, zero_add, one_smul]
  module

private theorem hypDiagLin_apply_perp (P : HypPair Q) (a : F) {r : W} (hr : r ∈ P.perp) :
    hypDiagLin P a r = r := by
  rw [hypDiagLin_apply, polar_comm Q r P.f, polar_comm Q r P.e,
    (P.mem_perp.mp hr).2, (P.mem_perp.mp hr).1]
  simp only [mul_zero, zero_smul, smul_zero, add_zero]

private theorem hypDiagLin_apply_decomp (P : HypPair Q) (a α β : F) {r : W}
    (hr : r ∈ P.perp) :
    hypDiagLin P a (α • P.e + β • P.f + r) = (a * α) • P.e + (a⁻¹ * β) • P.f + r := by
  rw [map_add, map_add, map_smul, map_smul, hypDiagLin_apply_e, hypDiagLin_apply_f,
    hypDiagLin_apply_perp P a hr, smul_smul, smul_smul]
  rw [mul_comm a α, mul_comm a⁻¹ β]

private theorem hypDiagLin_inv (P : HypPair Q) {a : F} (ha : a ≠ 0) :
    hypDiagLin P a⁻¹ ∘ₗ hypDiagLin P a = LinearMap.id := by
  ext x
  rw [LinearMap.comp_apply, LinearMap.id_apply]
  conv_lhs => rw [P.eq_add_proj x]
  conv_rhs => rw [P.eq_add_proj x]
  rw [hypDiagLin_apply_decomp P a _ _ (P.proj_mem_perp x)]
  rw [hypDiagLin_apply_decomp P a⁻¹ _ _ (P.proj_mem_perp x)]
  simp only [inv_inv]
  rw [show a⁻¹ * (a * polar Q x P.f) = polar Q x P.f from by
        rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul],
      show a * (a⁻¹ * polar Q x P.e) = polar Q x P.e from by
        rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]]

private theorem hypDiagLin_inv' (P : HypPair Q) {a : F} (ha : a ≠ 0) :
    hypDiagLin P a ∘ₗ hypDiagLin P a⁻¹ = LinearMap.id := by
  have := hypDiagLin_inv P (a := a⁻¹) (by simpa using ha)
  simpa using this

private theorem map_hypDiagLin (P : HypPair Q) {a : F} (ha : a ≠ 0) (x : W) :
    Q (hypDiagLin P a x) = Q x := by
  set al := polar Q x P.f with hal
  set be := polar Q x P.e with hbe
  set r := P.proj x with hr
  have hmem : r ∈ P.perp := P.proj_mem_perp x
  have hx : x = (al • P.e + be • P.f) + r := by
    rw [hr, hal, hbe]; exact P.eq_add_proj x
  have hQplane : ∀ u v : F, Q (u • P.e + v • P.f) = u * v := by
    intro u v
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul Q, QuadraticMap.map_smul Q, P.Q_e, P.Q_f,
      polar_smul_left_eq Q, polar_smul_right_eq Q, P.polar_ef]
    simp
  have horth : ∀ u v : F, polar Q (u • P.e + v • P.f) r = 0 := by
    intro u v
    rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
      (P.mem_perp.mp hmem).1, (P.mem_perp.mp hmem).2]
    simp only [mul_zero, add_zero]
  have hy : hypDiagLin P a x = ((a * al) • P.e + (a⁻¹ * be) • P.f) + r := by
    conv_lhs => rw [hx]
    rw [hypDiagLin_apply_decomp P a al be hmem]
  rw [hy, hx]
  conv_lhs => rw [QuadraticMap.map_add Q]
  conv_rhs => rw [QuadraticMap.map_add Q]
  rw [horth, horth, hQplane, hQplane, add_zero]
  have h : a * al * (a⁻¹ * be) = al * be := by
    calc a * al * (a⁻¹ * be) = (a * a⁻¹) * (al * be) := by ring
      _ = al * be := by rw [mul_inv_cancel₀ ha, one_mul]
  rw [h]
  simp

noncomputable def hypDiag (P : HypPair Q) (a : F) (ha : a ≠ 0) : W ≃ₗ[F] W :=
  LinearEquiv.ofLinear (hypDiagLin P a) (hypDiagLin P a⁻¹) (hypDiagLin_inv' P ha)
    (hypDiagLin_inv P ha)

private theorem hypDiag_apply (P : HypPair Q) (a : F) (ha : a ≠ 0) (x : W) :
    hypDiag P a ha x = hypDiagLin P a x := rfl

theorem hypDiag_apply_formula (P : HypPair Q) (a : F) (ha : a ≠ 0) (x : W) :
    hypDiag P a ha x = x + (a - 1) • (polar Q x P.f • P.e) +
      (a⁻¹ - 1) • (polar Q x P.e • P.f) := by
  rw [hypDiag_apply]
  exact hypDiagLin_apply P a x

theorem hypDiag_mem_orthogonalGroup (P : HypPair Q) (a : F) (ha : a ≠ 0) :
    hypDiag P a ha ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  rw [hypDiag_apply]
  exact map_hypDiagLin P ha x

theorem hypDiag_apply_e (P : HypPair Q) (a : F) (ha : a ≠ 0) :
    hypDiag P a ha P.e = a • P.e := by
  rw [hypDiag_apply]; exact hypDiagLin_apply_e P a

theorem hypDiag_apply_f (P : HypPair Q) (a : F) (ha : a ≠ 0) :
    hypDiag P a ha P.f = a⁻¹ • P.f := by
  rw [hypDiag_apply]; exact hypDiagLin_apply_f P a

theorem hypDiag_apply_perp (P : HypPair Q) (a : F) (ha : a ≠ 0) {r : W} (hr : r ∈ P.perp) :
    hypDiag P a ha r = r := by
  rw [hypDiag_apply]; exact hypDiagLin_apply_perp P a hr

private theorem hypDiag_pow_apply_decomp (P : HypPair Q) (a : F) (ha : a ≠ 0) (m : ℕ)
    (α β : F) {r : W} (hr : r ∈ P.perp) :
    (hypDiag P a ha ^ m) (α • P.e + β • P.f + r) =
      ((a ^ m) * α) • P.e + ((a ^ m)⁻¹ * β) • P.f + r := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, hypDiag_apply,
      hypDiagLin_apply_decomp P a _ _ hr]
    rw [show a * ((a ^ m) * α) = (a ^ (m + 1)) * α by
          rw [pow_succ]; ring,
      show a⁻¹ * (((a ^ m)⁻¹) * β) = ((a ^ (m + 1))⁻¹) * β by
          rw [pow_succ, mul_inv_rev]; ring]

theorem hypDiag_pow_eq_one (P : HypPair Q) (a : F) (ha : a ≠ 0) {r : ℕ} (hr : a ^ r = 1) :
    hypDiag P a ha ^ r = 1 := by
  ext x
  conv_lhs => rw [P.eq_add_proj x]
  conv_rhs => rw [P.eq_add_proj x]
  rw [hypDiag_pow_apply_decomp P a ha r _ _ (P.proj_mem_perp x), hr,
    show ((1 : F))⁻¹ = 1 by rw [inv_one], one_mul, one_mul]
  rfl

theorem hypDiag_pow_apply_e (P : HypPair Q) (a : F) (ha : a ≠ 0) (m : ℕ) :
    (hypDiag P a ha ^ m) P.e = (a ^ m) • P.e := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, hypDiag_apply_e, smul_smul,
      ← pow_succ]

theorem dvd_of_zpow_apply_eq_self {G : Type*} [Group G] [Finite G]
    (act : G →* (W ≃ₗ[F] W)) {t : G}
    {r : ℕ} (hord : orderOf t = r)
    {u : W} (hmove : ∀ m : ℕ, 0 < m → m < r → act (t ^ m) u ≠ u) {a : ℤ}
    (ha : act (t ^ a) u = u) : (r : ℤ) ∣ a := by
  by_contra h
  have hrpos : (0 : ℤ) < r := by
    rw [← hord]
    exact_mod_cast orderOf_pos t
  have hne : a % (r : ℤ) ≠ 0 := fun h0 => h (Int.dvd_iff_emod_eq_zero.mpr h0)
  have hpos : 0 < a % (r : ℤ) :=
    lt_of_le_of_ne (Int.emod_nonneg a hrpos.ne') (Ne.symm hne)
  have hlt : a % (r : ℤ) < (r : ℤ) := Int.emod_lt_of_pos a hrpos
  set m := (a % (r : ℤ)).toNat with hm
  have hcast : ((a % (r : ℤ)).toNat : ℤ) = a % (r : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg a hrpos.ne')
  have hmpos : 0 < m := by
    rw [hm]; omega
  have hmlt : m < r := by
    rw [hm]; omega
  have h1 : t ^ a = t ^ (m : ℤ) := by
    rw [← zpow_mod_orderOf t a, hord]
    congr 1
    rw [hm, Int.toNat_of_nonneg (Int.emod_nonneg a hrpos.ne')]
  have hta : act (t ^ a) u = act (t ^ m) u := by
    conv_lhs => rw [h1]
    rw [zpow_natCast]
  have : act (t ^ m) u = u := by
    rw [← hta]; exact ha
  exact hmove m hmpos hmlt this

structure PlaneFrame (Q : QuadraticForm F W) where
  A : Submodule F W
  u : W
  v : W
  hu : u ∈ A
  hv : v ∈ A
  hQu : Q u = 1
  hbv : polar Q u v ≠ 0
  hirr : ∀ s : F, s ^ 2 + polar Q u v * s + Q v ≠ 0
  hspan : A = Submodule.span F {u, v}

variable [CharP F 2]

theorem PlaneFrame.polarNondegOn (D : PlaneFrame Q) : PolarNondegOn Q D.A := by
  intro x hx hx'
  rw [D.hspan, Submodule.mem_span_pair] at hx
  obtain ⟨α, β, rfl⟩ := hx
  have h1 := hx' D.u D.hu
  have h2 := hx' D.v D.hv
  have huu : polar Q D.u D.u = 0 := by
    rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]
  have hvv : polar Q D.v D.v = 0 := by
    rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]
  have hvu : polar Q D.v D.u = polar Q D.u D.v := polar_comm Q D.v D.u
  rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, huu, hvu] at h1
  rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hvv] at h2
  simp only [mul_zero, add_zero] at h2
  have hα : α = 0 := (mul_eq_zero.mp h2).resolve_right D.hbv
  have hβ : β = 0 := by
    have h : β * polar Q D.u D.v = 0 := by simpa [add_comm] using h1
    exact (mul_eq_zero.mp h).resolve_right D.hbv
  rw [hα, hβ, zero_smul, zero_smul, add_zero]



section CharTwo

variable [CharP F 2]

private noncomputable def hypSwapLin (P : HypPair Q) : W →ₗ[F] W :=
  LinearMap.id + LinearMap.smulRight (polarBilin Q P.e + polarBilin Q P.f) (P.e + P.f)

private theorem add_self_eq_zero_vec (x : W) (h2 : (2 : F) = 0) : x + x = 0 := by
  have h : (2 : F) • x = 0 := by rw [h2, zero_smul]
  rwa [show (2 : F) • x = x + x by rw [← one_add_one_eq_two, add_smul, one_smul]] at h

private theorem hypSwapLin_apply (P : HypPair Q) (x : W) :
    hypSwapLin P x = x + (polar Q x P.e + polar Q x P.f) • (P.e + P.f) := by
  simp only [hypSwapLin, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
    polarBilin_apply_apply, polar_comm Q P.e x, polar_comm Q P.f x]

private theorem hypSwapLin_apply_e (P : HypPair Q) : hypSwapLin P P.e = P.f := by
  rw [hypSwapLin_apply, P.polar_ee, P.polar_ef]
  simp only [zero_add, one_smul]
  rw [← add_assoc, add_self_eq_zero_vec _ (CharTwo.two_eq_zero (R := F)), zero_add]

private theorem hypSwapLin_apply_f (P : HypPair Q) : hypSwapLin P P.f = P.e := by
  rw [hypSwapLin_apply, P.polar_ff, polar_comm Q P.f P.e, P.polar_ef]
  simp only [add_zero, one_smul]
  have h := add_self_eq_zero_vec (P.f) (CharTwo.two_eq_zero (R := F))
  rw [← add_assoc, add_comm P.f P.e, add_assoc, h, add_zero]

private theorem hypSwapLin_apply_perp (P : HypPair Q) {r : W} (hr : r ∈ P.perp) :
    hypSwapLin P r = r := by
  rw [hypSwapLin_apply, polar_comm Q r P.e, polar_comm Q r P.f,
    (P.mem_perp.mp hr).1, (P.mem_perp.mp hr).2, add_zero, zero_smul, add_zero]

private theorem hypSwapLin_apply_decomp (P : HypPair Q) (α β : F) {r : W}
    (hr : r ∈ P.perp) :
    hypSwapLin P (α • P.e + β • P.f + r) = β • P.e + α • P.f + r := by
  rw [map_add, map_add, map_smul, map_smul, hypSwapLin_apply_e, hypSwapLin_apply_f,
    hypSwapLin_apply_perp P hr]
  abel

private theorem hypSwapLin_involutive (P : HypPair Q) :
    hypSwapLin P ∘ₗ hypSwapLin P = LinearMap.id := by
  ext x
  rw [LinearMap.comp_apply, LinearMap.id_apply]
  conv_lhs => rw [P.eq_add_proj x]
  conv_rhs => rw [P.eq_add_proj x]
  rw [hypSwapLin_apply_decomp P _ _ (P.proj_mem_perp x),
    hypSwapLin_apply_decomp P _ _ (P.proj_mem_perp x)]

private theorem map_hypSwapLin (P : HypPair Q) (x : W) : Q (hypSwapLin P x) = Q x := by
  set al := polar Q x P.f with hal
  set be := polar Q x P.e with hbe
  set r := P.proj x with hr
  have hmem : r ∈ P.perp := P.proj_mem_perp x
  have hx : x = (al • P.e + be • P.f) + r := by
    rw [hr, hal, hbe]; exact P.eq_add_proj x
  have hQplane : ∀ u v : F, Q (u • P.e + v • P.f) = u * v := by
    intro u v
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul Q, QuadraticMap.map_smul Q, P.Q_e, P.Q_f,
      polar_smul_left_eq Q, polar_smul_right_eq Q, P.polar_ef]
    simp
  have horth : ∀ u v : F, polar Q (u • P.e + v • P.f) r = 0 := by
    intro u v
    rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
      (P.mem_perp.mp hmem).1, (P.mem_perp.mp hmem).2]
    simp only [mul_zero, add_zero]
  have hy : hypSwapLin P x = ((be • P.e + al • P.f)) + r := by
    conv_lhs => rw [hx]
    rw [hypSwapLin_apply_decomp P al be hmem]
  rw [hy, hx]
  conv_lhs => rw [QuadraticMap.map_add Q]
  conv_rhs => rw [QuadraticMap.map_add Q]
  rw [horth, horth, hQplane, hQplane, add_zero]
  rw [mul_comm, add_zero]

noncomputable def hypSwap (P : HypPair Q) : W ≃ₗ[F] W :=
  LinearEquiv.ofLinear (hypSwapLin P) (hypSwapLin P) (hypSwapLin_involutive P)
    (hypSwapLin_involutive P)

private theorem hypSwap_apply (P : HypPair Q) (x : W) : hypSwap P x = hypSwapLin P x := rfl

theorem hypSwap_mem_orthogonalGroup (P : HypPair Q) :
    hypSwap P ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  rw [hypSwap_apply]
  exact map_hypSwapLin P x

theorem hypSwap_mul_self (P : HypPair Q) : hypSwap P * hypSwap P = 1 := by
  ext x
  rw [LinearEquiv.mul_apply, hypSwap_apply, hypSwap_apply]
  exact LinearMap.congr_fun (hypSwapLin_involutive P) x

private theorem hypDiag_mul_inv (P : HypPair Q) (a : F) (ha : a ≠ 0) :
    hypDiag P a ha * hypDiag P a⁻¹ (inv_ne_zero ha) = 1 := by
  ext x
  conv_lhs => rw [P.eq_add_proj x]
  conv_rhs => rw [P.eq_add_proj x]
  rw [LinearEquiv.mul_apply, hypDiag_apply, hypDiag_apply,
    hypDiagLin_apply_decomp P a⁻¹ _ _ (P.proj_mem_perp x),
    hypDiagLin_apply_decomp P a _ _ (P.proj_mem_perp x), inv_inv]
  rw [show a * (a⁻¹ * polar Q x P.f) = polar Q x P.f from by
        rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul],
      show a⁻¹ * (a * polar Q x P.e) = polar Q x P.e from by
        rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]]
  rfl

private theorem hypDiag_inv (P : HypPair Q) (a : F) (ha : a ≠ 0) :
    (hypDiag P a ha)⁻¹ = hypDiag P a⁻¹ (inv_ne_zero ha) :=
  inv_eq_of_mul_eq_one_right (hypDiag_mul_inv P a ha)

theorem hypSwap_conj_hypDiag (P : HypPair Q) (a : F) (ha : a ≠ 0) :
    hypSwap P * hypDiag P a ha * (hypSwap P)⁻¹ = hypDiag P a⁻¹ (inv_ne_zero ha) := by
  have hinv : (hypSwap P)⁻¹ = hypSwap P := inv_eq_of_mul_eq_one_right (hypSwap_mul_self P)
  ext x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hinv, hypSwap_apply, hypDiag_apply,
    hypSwap_apply, hypDiag_apply]
  conv_lhs => rw [P.eq_add_proj x]
  conv_rhs => rw [P.eq_add_proj x]
  rw [hypSwapLin_apply_decomp P _ _ (P.proj_mem_perp x),
    hypDiagLin_apply_decomp P a _ _ (P.proj_mem_perp x),
    hypSwapLin_apply_decomp P _ _ (P.proj_mem_perp x),
    hypDiagLin_apply_decomp P a⁻¹ _ _ (P.proj_mem_perp x), inv_inv]

theorem hypDiag_mem_orthDerived (P : HypPair Q) (mu : Fˣ) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hord : orderOf mu = r) :
    hypDiag P (mu : F) (Units.ne_zero mu) ∈ orthDerived Q := by
  classical
  have hordF : orderOf ((mu : F)) = r := by rw [orderOf_units, hord]
  have hpr : ((mu : F)) ^ r = 1 := by rw [← hordF]; exact pow_orderOf_eq_one _
  have htr : hypDiag P (mu : F) (Units.ne_zero mu) ^ r = 1 :=
    hypDiag_pow_eq_one P _ _ hpr
  have hz : ⁅hypSwap P, hypDiag P (mu : F) (Units.ne_zero mu)⁆ =
      (hypDiag P (mu : F) (Units.ne_zero mu)) ^ (-2 : ℤ) := by
    rw [commutatorElement_def, hypSwap_conj_hypDiag, ← hypDiag_inv P (mu : F) (Units.ne_zero mu)]
    rw [show (hypDiag P (mu : F) (Units.ne_zero mu))⁻¹ =
      (hypDiag P (mu : F) (Units.ne_zero mu)) ^ (-1 : ℤ) by rw [zpow_neg_one]]
    rw [← zpow_add]
    norm_num
  have hmem : ⁅hypSwap P, hypDiag P (mu : F) (Units.ne_zero mu)⁆ ∈ orthDerived Q :=
    Subgroup.commutator_mem_commutator (hypSwap_mem_orthogonalGroup P)
      (hypDiag_mem_orthogonalGroup P _ _)
  obtain ⟨k, hk⟩ := hr.odd_of_ne_two hr2
  have hkdiv : (r - 1) / 2 = k := by omega
  have hmul : (-2 : ℤ) * (((r - 1) / 2 : ℕ) : ℤ) = 1 - (r : ℤ) := by omega
  have hpow : hypDiag P (mu : F) (Units.ne_zero mu) =
      ⁅hypSwap P, hypDiag P (mu : F) (Units.ne_zero mu)⁆ ^ ((r - 1) / 2) := by
    rw [hz, ← zpow_natCast, ← zpow_mul,
      hmul, zpow_sub, zpow_one, zpow_natCast, htr, inv_one, mul_one]
  rw [hpow]
  exact pow_mem hmem _

end CharTwo


end OmTorus

end CFSG.LocalAnalysis.GLTheoremA.Y10F

end
