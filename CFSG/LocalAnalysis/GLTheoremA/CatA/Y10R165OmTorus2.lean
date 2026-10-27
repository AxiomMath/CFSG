module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmTorus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open QuadraticMap CFSG.Open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.SeitzGeneration.OrthBlk
open CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4
open scoped commutatorElement

namespace OmTorus

variable {F W : Type} [Field F] [AddCommGroup W] [Module F W] {Q : QuadraticForm F W}

variable [Finite F] [CharP F 2] [FiniteDimensional F W]

section PlaneTorus

variable [Finite F] [FiniteDimensional F W] {r : ℕ}

private noncomputable def conjLinearEquiv {X Y : Type*} [AddCommGroup X] [Module F X]
    [AddCommGroup Y] [Module F Y] (e : X ≃ₗ[F] Y) : (X ≃ₗ[F] X) ≃* (Y ≃ₗ[F] Y) where
  toFun g := e.symm.trans (g.trans e)
  invFun g := e.trans (g.trans e.symm)
  left_inv g := by ext x; simp
  right_inv g := by ext y; simp
  map_mul' g h := by ext y; simp [LinearEquiv.trans_apply]

private theorem conjLinearEquiv_apply {X Y : Type*} [AddCommGroup X] [Module F X]
    [AddCommGroup Y] [Module F Y] (e : X ≃ₗ[F] Y) (g : X ≃ₗ[F] X) (y : Y) :
    conjLinearEquiv e g y = e (g (e.symm y)) := rfl

private noncomputable def planeBasisLin (D : PlaneFrame Q) : (Fin 2 → F) →ₗ[F] D.A where
  toFun x := ⟨x 0 • D.u + x 1 • D.v, by
    rw [D.hspan]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span (Set.mem_insert D.u {D.v})
    · exact Submodule.subset_span (Set.mem_insert_of_mem D.u (Set.mem_singleton D.v))⟩
  map_add' x y := by
    ext
    simp only [Submodule.coe_add, Pi.add_apply, add_smul]
    abel
  map_smul' a x := by
    ext
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_add, smul_smul, RingHom.id_apply,
      smul_eq_mul, mul_assoc]

private theorem planeBasis_apply (D : PlaneFrame Q) (x : Fin 2 → F) :
    (planeBasisLin D x : W) = x 0 • D.u + x 1 • D.v := rfl

private theorem planeBasis_injective (D : PlaneFrame Q) : Function.Injective (planeBasisLin D) := by
  intro x y h
  have h' : planeBasisLin D (x - y) = 0 := by rw [map_sub, h, sub_self]
  have h2 : (x - y) 0 • D.u + (x - y) 1 • D.v = 0 := by
    have := congrArg Subtype.val h'
    have h2' : x 0 • D.u + x 1 • D.v - (y 0 • D.u + y 1 • D.v) = 0 := by
      simpa [planeBasis_apply, Pi.sub_apply, sub_smul] using this
    rw [show (x - y) 0 • D.u + (x - y) 1 • D.v =
        x 0 • D.u + x 1 • D.v - (y 0 • D.u + y 1 • D.v) by
      simp only [Pi.sub_apply, sub_smul]
      abel]
    exact h2'
  have h1 : polar Q ((x - y) 0 • D.u + (x - y) 1 • D.v) D.u = 0 := by
    rw [h2]; exact polar_zero_left Q _
  have h3 : polar Q ((x - y) 0 • D.u + (x - y) 1 • D.v) D.v = 0 := by
    rw [h2]; exact polar_zero_left Q _
  have huu : polar Q D.u D.u = 0 := by
    rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]
  have hvv : polar Q D.v D.v = 0 := by
    rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]
  rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, huu,
    polar_comm Q D.v D.u] at h1
  rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hvv] at h3
  simp only [mul_zero, add_zero] at h3
  simp only [mul_zero, zero_add] at h1
  have h0 : (x - y) 0 = 0 := (mul_eq_zero.mp h3).resolve_right D.hbv
  have h1' : (x - y) 1 = 0 := (mul_eq_zero.mp h1).resolve_right D.hbv
  funext i
  fin_cases i
  · exact sub_eq_zero.mp h0
  · exact sub_eq_zero.mp h1'

private theorem planeBasis_surjective (D : PlaneFrame Q) :
    Function.Surjective (planeBasisLin D) := by
  intro x
  have hxmem : (x : W) ∈ Submodule.span F {D.u, D.v} := by
    rw [← D.hspan]; exact x.2
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hxmem
  refine ⟨![α, β], Subtype.ext ?_⟩
  show α • D.u + β • D.v = (x : W)
  simpa using hαβ

private noncomputable def planeBasisEquiv (D : PlaneFrame Q) : (Fin 2 → F) ≃ₗ[F] D.A :=
  LinearEquiv.ofBijective (planeBasisLin D) ⟨planeBasis_injective D, planeBasis_surjective D⟩

private theorem planeBasisEquiv_coe (D : PlaneFrame Q) (x : Fin 2 → F) :
    (planeBasisEquiv D x : W) = x 0 • D.u + x 1 • D.v := rfl

private theorem planeBasisEquiv_e0 (D : PlaneFrame Q) :
    planeBasisEquiv D (Pi.single 0 1) = ⟨D.u, D.hu⟩ := by
  apply Subtype.ext
  rw [planeBasisEquiv_coe]
  simp [Pi.single_apply]

private theorem planeBasisEquiv_isometry (D : PlaneFrame Q) (x : Fin 2 → F) :
    Q (planeBasisEquiv D x : W) =
      CFSG.StandardType.OrthRestTail.binF (polar Q D.u D.v) (Q D.v) x := by
  rw [planeBasisEquiv_coe, CFSG.StandardType.OrthRestTail.binF]
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul Q, QuadraticMap.map_smul Q]
  rw [polar_smul_left_eq Q, polar_smul_right_eq Q]
  simp only [D.hQu, mul_one, smul_eq_mul]
  ring

private noncomputable def matrixToLinear (M : Matrix.SpecialLinearGroup (Fin 2) F) :
    (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 2 → F)
    (Matrix.GeneralLinearGroup.toLin (Matrix.SpecialLinearGroup.toGL M))

private theorem matrixToLinear_pow (M : Matrix.SpecialLinearGroup (Fin 2) F) (m : ℕ) :
    matrixToLinear M ^ m = matrixToLinear (M ^ m) := by
  simp only [matrixToLinear]
  rw [← map_pow, ← map_pow, ← map_pow]

private theorem mulVec_pow_single_ne_of_orderOf_eq {r m : ℕ}
    (M : Matrix.SpecialLinearGroup (Fin 2) F) (hr : r.Prime) (hr2 : r ≠ 2)
    (hM : orderOf M = r) (hm : 0 < m) (hmr : m < r) :
    (((M ^ m : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)).mulVec
      (Pi.single 0 1) ≠ Pi.single 0 1 := by
  intro hNmat
  let Nmat : Matrix (Fin 2) (Fin 2) F := ((M ^ m : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F)
  have h00 : Nmat 0 0 = 1 := by
    have := congrFun hNmat 0
    simpa [Nmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single] using this
  have h10 : Nmat 1 0 = 0 := by
    have := congrFun hNmat 1
    simpa [Nmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single] using this
  have hdet : Nmat.det = 1 := Matrix.SpecialLinearGroup.det_coe _
  have h11 : Nmat 1 1 = 1 := by
    rw [Matrix.det_fin_two] at hdet
    rw [h00, h10] at hdet
    simpa using hdet
  have hN2 : (M ^ m : Matrix.SpecialLinearGroup (Fin 2) F) ^ 2 = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have h00' := h00
    have h10' := h10
    have h11' := h11
    fin_cases i <;> fin_cases j <;>
      simp [Nmat, pow_two, Matrix.mul_apply, Fin.sum_univ_two, h00', h10', h11',
        Matrix.SpecialLinearGroup.coe_one, CharTwo.add_self_eq_zero]
  have hN1 : M ^ m = 1 := by
    have hdvd : orderOf (M ^ m) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hN2
    have hdvd' : orderOf (M ^ m) ∣ r := by
      have : (M ^ m) ^ r = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, ← hM, pow_orderOf_eq_one, one_pow]
      exact orderOf_dvd_iff_pow_eq_one.mpr this
    have hcop : Nat.Coprime 2 r := (Nat.coprime_two_right.mpr (hr.odd_of_ne_two hr2)).symm
    have hgcd : orderOf (M ^ m) ∣ Nat.gcd 2 r := Nat.dvd_gcd hdvd hdvd'
    rw [hcop.gcd_eq_one] at hgcd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
  have hM1 : r ∣ m := by
    rw [← hM]
    exact orderOf_dvd_iff_pow_eq_one.mpr hN1
  obtain ⟨c, hc⟩ := hM1
  rw [hc] at hmr
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0
      omega
    · exact h0
  nlinarith [hr.two_le]

private theorem planeTorus_pair_data (D : PlaneFrame Q) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrdvd : r ∣ Nat.card F + 1) :
    ∃ (M σ : Matrix.SpecialLinearGroup (Fin 2) F) (tA σA : D.A ≃ₗ[F] D.A),
      orderOf M = r ∧
      tA = conjLinearEquiv (planeBasisEquiv D) (matrixToLinear M) ∧
      σA = conjLinearEquiv (planeBasisEquiv D) (matrixToLinear σ) ∧
      tA ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict D.A) ∧
      σA ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict D.A) ∧
      orderOf tA = r ∧ σA * tA * σA⁻¹ = tA⁻¹ := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hK'⟩ := FiniteField.card F 2
  have hK : Nat.card F = 2 ^ (n : ℕ) := by rwa [Fintype.card_eq_nat_card] at hK'
  have hpn : r ∣ 2 ^ (n : ℕ) + 1 := by rwa [hK] at hrdvd
  obtain ⟨M, σ, hMord, hσconj, hMiso, hσiso⟩ :=
    CFSG.StandardType.OrthRestTail.exists_rot hK D.hirr hr hr2 hpn
  have hMlin_ord : orderOf (matrixToLinear M) = r := by
    rw [show matrixToLinear M = LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 2 → F)
        (Matrix.GeneralLinearGroup.toLin (Matrix.SpecialLinearGroup.toGL M)) from rfl,
      MulEquiv.orderOf_eq, MulEquiv.orderOf_eq,
      orderOf_injective Matrix.SpecialLinearGroup.toGL
        Matrix.SpecialLinearGroup.toGL_injective M, hMord]
  let tA : D.A ≃ₗ[F] D.A := conjLinearEquiv (planeBasisEquiv D) (matrixToLinear M)
  let σA : D.A ≃ₗ[F] D.A := conjLinearEquiv (planeBasisEquiv D) (matrixToLinear σ)
  have htA_order : orderOf tA = r := by
    rw [show tA = conjLinearEquiv (planeBasisEquiv D) (matrixToLinear M) from rfl,
      MulEquiv.orderOf_eq, hMlin_ord]
  have htA_iso : tA ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict D.A) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    change Q (tA x : W) = Q (x : W)
    rw [show tA x = planeBasisEquiv D (matrixToLinear M ((planeBasisEquiv D).symm x)) from
      conjLinearEquiv_apply (planeBasisEquiv D) (matrixToLinear M) x]
    have hx : Q (x : W) = CFSG.StandardType.OrthRestTail.binF (polar Q D.u D.v) (Q D.v)
        ((planeBasisEquiv D).symm x) := by
      rw [← planeBasisEquiv_isometry D ((planeBasisEquiv D).symm x),
        LinearEquiv.apply_symm_apply]
    rw [planeBasisEquiv_isometry D, hx]
    exact hMiso _
  have hσA_iso : σA ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict D.A) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    change Q (σA x : W) = Q (x : W)
    rw [show σA x = planeBasisEquiv D (matrixToLinear σ ((planeBasisEquiv D).symm x)) from
      conjLinearEquiv_apply (planeBasisEquiv D) (matrixToLinear σ) x]
    have hx : Q (x : W) = CFSG.StandardType.OrthRestTail.binF (polar Q D.u D.v) (Q D.v)
        ((planeBasisEquiv D).symm x) := by
      rw [← planeBasisEquiv_isometry D ((planeBasisEquiv D).symm x),
        LinearEquiv.apply_symm_apply]
    rw [planeBasisEquiv_isometry D, hx]
    exact hσiso _
  have hσ : matrixToLinear σ * matrixToLinear M * (matrixToLinear σ)⁻¹ =
      (matrixToLinear M)⁻¹ := by
    have h := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 2 → F)
        (Matrix.GeneralLinearGroup.toLin (Matrix.SpecialLinearGroup.toGL A))) hσconj
    simpa [matrixToLinear, map_mul, map_inv] using h
  have hconj : σA * tA * σA⁻¹ = tA⁻¹ := by
    have h := congrArg (conjLinearEquiv (planeBasisEquiv D)) hσ
    simpa [σA, tA, map_mul, map_inv] using h
  exact ⟨M, σ, tA, σA, hMord, rfl, rfl, htA_iso, hσA_iso, htA_order, hconj⟩

theorem planeTorus_data (D : PlaneFrame Q) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrdvd : r ∣ Nat.card F + 1) :
    ∃ (tA σA : D.A ≃ₗ[F] D.A),
      tA ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict D.A) ∧
      σA ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict D.A) ∧
      orderOf tA = r ∧ σA * tA * σA⁻¹ = tA⁻¹ ∧
      (∀ m : ℕ, 0 < m → m < r →
        ((tA ^ m : D.A ≃ₗ[F] D.A) ⟨D.u, D.hu⟩) ≠ ⟨D.u, D.hu⟩) := by
  classical
  obtain ⟨M, σ, tA, σA, hMord, htA_eq, -, htA_iso, hσA_iso, htA_order, hconj⟩ :=
    planeTorus_pair_data D hr hr2 hrdvd
  refine ⟨tA, σA, htA_iso, hσA_iso, htA_order, hconj, ?_⟩
  intro m hm hmr hfix
  have hcoord : (matrixToLinear M ^ m) (Pi.single 0 1) = Pi.single 0 1 := by
    have htApow : tA ^ m = conjLinearEquiv (planeBasisEquiv D) (matrixToLinear M ^ m) := by
      rw [htA_eq, ← map_pow]
    have hφ := congrArg (planeBasisEquiv D).symm hfix
    rw [htApow, conjLinearEquiv_apply, LinearEquiv.symm_apply_apply] at hφ
    rw [show (planeBasisEquiv D).symm ⟨D.u, D.hu⟩ = Pi.single 0 1 from by
      rw [show (⟨D.u, D.hu⟩ : D.A) = planeBasisEquiv D (Pi.single 0 1) from
        (planeBasisEquiv_e0 D).symm]
      exact LinearEquiv.symm_apply_apply _ _] at hφ
    exact hφ
  have hNmat : (((M ^ m : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)).mulVec (Pi.single 0 1) = Pi.single 0 1 := by
    rw [matrixToLinear_pow] at hcoord
    change Matrix.mulVec (((M ^ m : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)) (Pi.single 0 1) = Pi.single 0 1 at hcoord
    simpa [matrixToLinear] using hcoord
  exact mulVec_pow_single_ne_of_orderOf_eq M hr hr2 hMord hm hmr hNmat


section Glue

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {U : Submodule K V}

noncomputable def glueHom (hc : IsCompl U (perp Q U)) : (U ≃ₗ[K] U) →* (V ≃ₗ[K] V) where
  toFun a := CFSG.RankThree.PartOne.KCOrthogonal.glue hc a 1
  map_one' := CFSG.RankThree.PartOne.KCOrthogonal.glue_one hc
  map_mul' a b := by
    simpa using CFSG.RankThree.PartOne.KCOrthogonal.glue_mul hc a b
      (1 : perp Q U ≃ₗ[K] perp Q U) (1 : perp Q U ≃ₗ[K] perp Q U)

private theorem glueHom_apply (hc : IsCompl U (perp Q U)) (a : U ≃ₗ[K] U) :
    glueHom hc a = CFSG.RankThree.PartOne.KCOrthogonal.glue hc a 1 := rfl

private theorem glueHom_injective (hc : IsCompl U (perp Q U)) :
    Function.Injective (glueHom hc) := by
  intro a b h
  ext u
  have h' := congrArg (fun e : V ≃ₗ[K] V => e ((u : V) + (0 : perp Q U))) h
  rw [glueHom_apply, glueHom_apply, CFSG.RankThree.PartOne.KCOrthogonal.glue_apply,
    CFSG.RankThree.PartOne.KCOrthogonal.glue_apply] at h'
  simpa using h'

private theorem glueHom_orderOf (hc : IsCompl U (perp Q U)) (a : U ≃ₗ[K] U) :
    orderOf (glueHom hc a) = orderOf a :=
  orderOf_injective (glueHom hc) (glueHom_injective hc) a

theorem glueHom_mem_orthogonalGroup [FiniteDimensional K V]
    (hc : IsCompl U (perp Q U)) {a : U ≃ₗ[K] U}
    (ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict U)) :
    glueHom hc a ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  obtain ⟨u, r, rfl⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonal.exists_coe_add_of_isCompl hc v
  rw [glueHom_apply, CFSG.RankThree.PartOne.KCOrthogonal.glue_apply]
  have hqu : Q (a u : V) = Q (u : V) := by
    have := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup ha u
    simpa using this
  have hpol : polar Q (a u : V) (r : V) = 0 :=
    mem_perp.mp r.2 (a u) (a u).2
  have hpol2 : polar Q (u : V) (r : V) = 0 := mem_perp.mp r.2 u u.2
  calc Q ((a u : V) + (r : V))
      = Q (a u : V) + Q (r : V) + polar Q (a u) (r : V) := QuadraticMap.map_add Q _ _
    _ = Q (u : V) + Q (r : V) + 0 := by rw [hqu, hpol]
    _ = Q ((u : V) + (r : V)) := by rw [QuadraticMap.map_add Q, hpol2, add_zero]

end Glue

theorem exists_plane_torus (D : PlaneFrame Q) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrdvd : r ∣ Nat.card F + 1) :
    ∃ t : W ≃ₗ[F] W,
      t ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ t ∈ orthDerived Q ∧
      orderOf t = r ∧ (∀ w ∈ perp Q D.A, t w = w) ∧
      (∀ x ∈ D.A, t x ∈ D.A) ∧
      (∀ a : ℤ, (t ^ a) D.u = D.u → (r : ℤ) ∣ a) := by
  classical
  obtain ⟨tA, σA, htA_iso, hσA_iso, htA_order, hconj, hmove⟩ :=
    planeTorus_data D hr hr2 hrdvd
  let hcompl : IsCompl D.A (perp Q D.A) := isCompl_perp D.polarNondegOn
  let t : W ≃ₗ[F] W := glueHom hcompl tA
  let σ : W ≃ₗ[F] W := glueHom hcompl σA
  have ht_iso : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    glueHom_mem_orthogonalGroup hcompl htA_iso
  have hσ_iso : σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    glueHom_mem_orthogonalGroup hcompl hσA_iso
  have ht_order : orderOf t = r := by
    rw [show t = glueHom hcompl tA from rfl, glueHom_orderOf hcompl tA, htA_order]
  have ht_perp : ∀ w ∈ perp Q D.A, t w = w := by
    intro w hw
    have := CFSG.RankThree.PartOne.KCOrthogonal.glue_apply hcompl tA 1 (0 : D.A) ⟨w, hw⟩
    simpa [t, glueHom] using this
  let s0 : D.A ≃ₗ[F] D.A := tA ^ ((r + 1) / 2)
  have hs0_iso : s0 ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict D.A) :=
    Subgroup.pow_mem _ htA_iso _
  have hs0_sq : s0 * s0 = tA := by
    have h2 : 2 * ((r + 1) / 2) = r + 1 := by
      obtain ⟨k, hk⟩ := hr.odd_of_ne_two hr2
      omega
    rw [show s0 = tA ^ ((r + 1) / 2) from rfl, ← pow_add,
      show (r + 1) / 2 + (r + 1) / 2 = r + 1 by omega, pow_succ,
      show tA ^ r = 1 by rw [← htA_order]; exact pow_orderOf_eq_one tA, one_mul]
  have hconj_s0 : σA * s0 * σA⁻¹ = s0⁻¹ := by
    rw [show s0 = tA ^ ((r + 1) / 2) from rfl]
    have h1 : σA * tA ^ ((r + 1) / 2) * σA⁻¹ = (σA * tA * σA⁻¹) ^ ((r + 1) / 2) := by
      rw [← conj_pow]
    rw [h1, hconj, show (tA⁻¹) ^ ((r + 1) / 2) = (tA ^ ((r + 1) / 2))⁻¹ by rw [inv_pow]]
  have hcommA : ⁅σA, s0⁆ = tA⁻¹ := by
    rw [commutatorElement_def, hconj_s0, ← mul_inv_rev, hs0_sq]
  have htA_mem : tA ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (Q.restrict D.A),
      TauCeti.QuadraticMap.orthogonalGroup (Q.restrict D.A)⁆ := by
    have hm : ⁅σA, s0⁆ ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (Q.restrict D.A),
        TauCeti.QuadraticMap.orthogonalGroup (Q.restrict D.A)⁆ :=
      Subgroup.commutator_mem_commutator hσA_iso hs0_iso
    rw [hcommA] at hm
    simpa using Subgroup.inv_mem _ hm
  have ht_inv_mem : t⁻¹ ∈ orthDerived Q := by
    have h1 : t⁻¹ = glueHom hcompl (tA⁻¹) := by
      rw [show t = glueHom hcompl tA from rfl, map_inv]
    rw [h1, show tA⁻¹ = ⁅σA, s0⁆ from hcommA.symm, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator hσ_iso
      (glueHom_mem_orthogonalGroup hcompl hs0_iso)
  have ht_mem : t ∈ orthDerived Q := by
    simpa using Subgroup.inv_mem _ ht_inv_mem
  have ht_maps : ∀ x ∈ D.A, t x ∈ D.A := by
    intro x hx
    have := CFSG.RankThree.PartOne.KCOrthogonal.glue_apply hcompl tA 1 ⟨x, hx⟩ (0 : perp Q D.A)
    have hx' : t x = (tA ⟨x, hx⟩ : W) := by simpa [t, glueHom] using this
    rw [hx']
    exact (tA ⟨x, hx⟩).2
  have ht_move : ∀ a : ℤ, (t ^ a) D.u = D.u → (r : ℤ) ∣ a := by
    intro a ha
    refine dvd_of_zpow_apply_eq_self (act := glueHom hcompl) (t := tA) (u := D.u) htA_order ?_ ?_
    · intro m hm hmr hfix
      apply hmove m hm hmr
      have hgu : glueHom hcompl (tA ^ m) D.u = ((tA ^ m) ⟨D.u, D.hu⟩ : W) := by
        have := CFSG.RankThree.PartOne.KCOrthogonal.glue_apply hcompl (tA ^ m) 1
          ⟨D.u, D.hu⟩ (0 : perp Q D.A)
        simpa [glueHom] using this
      rw [hgu] at hfix
      exact Subtype.ext hfix
    · simpa [show t = glueHom hcompl tA from rfl, map_zpow] using ha
  exact ⟨t, ht_iso, ht_mem, ht_order, ht_perp, ht_maps, ht_move⟩

end PlaneTorus



end OmTorus

end CFSG.LocalAnalysis.GLTheoremA.Y10F

end
