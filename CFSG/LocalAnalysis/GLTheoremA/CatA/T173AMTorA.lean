module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMDefs


public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open Module
open scoped commutatorElement MatrixGroups

open Polynomial in
private lemma finset_sup_ker_aeval_eq_ker_aeval_prod {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] (f : V →ₗ[F] V) {ι : Type*} [DecidableEq ι] (s : Finset ι) (q : ι → F[X])
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (q i) (q j)) :
    s.sup (fun i => LinearMap.ker (aeval f (q i))) =
      LinearMap.ker (aeval f (∏ i ∈ s, q i)) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty, Finset.sup_empty, Polynomial.aeval_one]
    exact (LinearMap.ker_id (R := F) (M := V)).symm
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sup_insert, ih]
    · have hca : IsCoprime (q a) (∏ i ∈ s, q i) := by
        refine IsCoprime.prod_right fun i hi => ?_
        exact hcop a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
          (fun h => ha (h ▸ hi))
      rw [Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hca]
    · intro i hi j hj hij
      exact hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij

open Polynomial in
private lemma sup_eigenspace_eq_top_of_pow_eq_one {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] {p : ℕ} (hp : p.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ p) (f : V →ₗ[F] V)
    (hf : f ^ p = 1) :
    (nthRootsFinset p (1 : F)).sup (fun ω => Module.End.eigenspace f ω) = ⊤ := by
  classical
  have hprod : (nthRootsFinset p (1 : F)).prod (fun ω => (X - C ω : F[X])) = X ^ p - 1 := by
    rw [Polynomial.X_pow_sub_one_eq_prod hp.pos hζ]
  have hcop : ∀ i ∈ nthRootsFinset p (1 : F), ∀ j ∈ nthRootsFinset p (1 : F), i ≠ j →
      IsCoprime (X - C i : F[X]) (X - C j : F[X]) := by
    intro i _ j _ hij
    exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hij).isUnit
  have hsup := finset_sup_ker_aeval_eq_ker_aeval_prod f (nthRootsFinset p (1 : F))
    (fun ω => (X - C ω : F[X])) hcop
  have heig : ∀ ω : F, Module.End.eigenspace f ω =
      LinearMap.ker (aeval f (X - C ω : F[X])) := by
    intro ω
    have h := Module.End.eigenspace_aeval_polynomial_degree_1 f (X - C ω : F[X])
      (degree_X_sub_C ω)
    have harg : -(X - C ω : F[X]).coeff 0 / (X - C ω : F[X]).leadingCoeff = ω := by simp
    rw [harg] at h
    exact h
  simp only [heig]
  rw [hsup, hprod]
  have : aeval f (X ^ p - 1 : F[X]) = f ^ p - 1 := by
    simp [map_sub, map_pow]
  rw [this, hf, sub_self]
  exact LinearMap.ker_zero

private noncomputable def glLinEquiv (n : Type*) [Fintype n] [DecidableEq n] (K : Type*)
    [CommRing K] : GL n K ≃* ((n → K) ≃ₗ[K] (n → K)) :=
  (Matrix.GeneralLinearGroup.toLin (n := n) (R := K)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K))

private theorem glLinEquiv_apply {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [CommRing K]
    (g : GL n K) (v : n → K) : (glLinEquiv n K g) v = (g : Matrix n n K).mulVec v := by
  change (LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K)
      (Matrix.GeneralLinearGroup.toLin (n := n) (R := K) g)) v = _
  rw [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv,
    Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply]

private noncomputable def unitsSmulEquiv {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (a : Kˣ) : V ≃ₗ[K] V where
  toFun v := (a : K) • v
  invFun v := (↑a⁻¹ : K) • v
  left_inv v := by simp
  right_inv v := by simp
  map_add' v w := by simp [smul_add]
  map_smul' c v := smul_comm (a : K) c v

private theorem glLinEquiv_scalar {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]
    (a : Kˣ) : glLinEquiv n K (Matrix.GeneralLinearGroup.scalar n a) = unitsSmulEquiv a := by
  ext v i
  simp [glLinEquiv_apply, Matrix.scalar_apply, Matrix.mulVec_diagonal, unitsSmulEquiv]

private theorem unitsSmulEquiv_inv_mul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (a : Kˣ) : unitsSmulEquiv (V := V) a⁻¹ * unitsSmulEquiv (V := V) a = 1 := by
  ext v
  simp [unitsSmulEquiv, smul_smul]

private theorem unitsSmulEquiv_commute {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (a : Kˣ) (e : V ≃ₗ[K] V) :
    unitsSmulEquiv (V := V) a * e = e * unitsSmulEquiv (V := V) a := by
  ext v
  simp [unitsSmulEquiv]

private theorem trans_unitsSmulEquiv_trans {K M N : Type*} [Field K] [AddCommGroup M]
    [Module K M] [AddCommGroup N] [Module K N] (a : Kˣ) (e : M ≃ₗ[K] N) :
    e.symm.trans ((unitsSmulEquiv (V := M) a).trans e) = unitsSmulEquiv (V := N) a := by
  ext x
  simp [LinearEquiv.trans_apply, unitsSmulEquiv]

private noncomputable def scalarUnit {n : Type} [Fintype n] [DecidableEq n] {K : Type} [Field K]
    (y : LargeEvenScalars n K) : Kˣ :=
  Classical.choose (MonoidHom.mem_range.mp y.2)

private theorem scalarUnit_spec {n : Type} [Fintype n] [DecidableEq n] {K : Type} [Field K]
    (y : LargeEvenScalars n K) :
    Matrix.GeneralLinearGroup.scalar n (scalarUnit y) = y.1 :=
  Classical.choose_spec (MonoidHom.mem_range.mp y.2)

private theorem glScalar_injective {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    {K : Type} [Field K] :
    Function.Injective (Matrix.GeneralLinearGroup.scalar n : Kˣ →* GL n K) := by
  intro a b hab
  have h : Matrix.scalar n (a : K) = Matrix.scalar n (b : K) := by
    simpa using congrArg (fun x : GL n K => (x : Matrix n n K)) hab
  have h2 : (a : K) = (b : K) := Matrix.scalar_inj.mp h
  exact Units.ext h2

private noncomputable def scalarUnitHom {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    {K : Type} [Field K] : LargeEvenScalars n K →* Kˣ where
  toFun := scalarUnit
  map_one' := by
    apply glScalar_injective (n := n)
    simp only [scalarUnit_spec, map_one]
    rfl
  map_mul' := by
    intro y z
    apply glScalar_injective (n := n)
    simp only [scalarUnit_spec, map_mul]
    rfl

private lemma relIndex_le_card_of_le_sup {H : Type*} [Group H] [Finite H] {Z M L : Subgroup H}
    [Finite M] (hZ : Z.Normal) (hL : L ≤ Z ⊔ M) : Z.relIndex L ≤ Nat.card M := by
  haveI : Z.Normal := hZ
  calc Z.relIndex L ≤ Z.relIndex (Z ⊔ M) :=
        Subgroup.relIndex_le_of_le_right hL
          (Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card Z (Z ⊔ M)) Nat.card_pos).ne'
    _ = Z.relIndex M := Subgroup.relIndex_sup_left M Z
    _ ≤ Nat.card M := Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card Z M)

private lemma comap_le_sup_ker {G G' : Type*} [Group G] [Group G'] (ρ : G →* G') {Z : Subgroup G}
    {Z' : Subgroup G'} (hZ' : Z' ≤ Z.map ρ) : Z'.comap ρ ≤ Z ⊔ ρ.ker := by
  intro y hy
  rw [Subgroup.mem_comap] at hy
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp (hZ' hy)
  have h2 : z⁻¹ * y ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hzy, inv_mul_cancel]
  have h3 : z * (z⁻¹ * y) = y := by group
  rw [← h3]
  exact Subgroup.mul_mem_sup hz h2

private noncomputable def restrictLinearEquiv {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (X : V ≃ₗ[K] V) (E : Submodule K V) (hX : ∀ v ∈ E, X v ∈ E)
    (hXinv : ∀ v ∈ E, X.symm v ∈ E) : E ≃ₗ[K] E where
  toFun v := ⟨X v, hX v v.2⟩
  invFun v := ⟨X.symm v, hXinv v v.2⟩
  left_inv v := by ext; simp
  right_inv v := by ext; simp
  map_add' v w := by ext; simp
  map_smul' c v := by ext; simp

theorem tor_lemmaA {p d : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hp : p.Prime)
    (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) {G : Subgroup (GL (Fin d) F)}
    (hZG : LargeEvenScalars (Fin d) F ≤ G) (hel : MElemMod p d F G) {h g : GL (Fin d) F}
    (hh : h ∈ G) (hg : g ∈ G) (hhp : h ^ p = 1) (hζ : ⁅g, h⁆ ≠ 1) :
    p ∣ d ∧ ∃ G' : Subgroup (GL (Fin (d / p)) F), LargeEvenScalars (Fin (d / p)) F ≤ G' ∧
      MElemMod p (d / p) F G' ∧
      (LargeEvenScalars (Fin d) F).relIndex G ≤
        p ^ 2 * (LargeEvenScalars (Fin (d / p)) F).relIndex G' := by
  classical
  have hcomm : ⁅g, h⁆ ∈ LargeEvenScalars (Fin d) F := hel.2 g hg h hh
  rw [largeEvenScalars_def] at hcomm
  obtain ⟨ζ, hζeq⟩ := MonoidHom.mem_range.mp hcomm
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · exfalso
      subst h0
      exact hζ (Subsingleton.elim (⁅g, h⁆) 1)
    · exact hpos
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hconj : g * h * g⁻¹ = h * Matrix.GeneralLinearGroup.scalar (Fin d) ζ := by
    have h1 : g * h * g⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin d) ζ * h := by
      rw [hζeq]
      group
    rw [h1, Matrix.GeneralLinearGroup.scalar_commute]
  have hζp : ζ ^ p = 1 := by
    have hpow : (Matrix.GeneralLinearGroup.scalar (Fin d) ζ) ^ p = 1 := by
      have h1 : (g * h * g⁻¹) ^ p = 1 := by
        rw [conj_pow, hhp, mul_one, mul_inv_cancel]
      have h2 : (h * Matrix.GeneralLinearGroup.scalar (Fin d) ζ) ^ p = 1 := by
        rw [← hconj]; exact h1
      have hcommute : Commute h (Matrix.GeneralLinearGroup.scalar (Fin d) ζ) :=
        (Matrix.GeneralLinearGroup.scalar_commute ζ h).symm
      rw [hcommute.mul_pow, hhp, one_mul] at h2
      exact h2
    have h2 : Matrix.GeneralLinearGroup.scalar (Fin d) (ζ ^ p) = 1 := by
      have h3 : (Matrix.GeneralLinearGroup.scalar (Fin d) ζ) ^ p =
          Matrix.GeneralLinearGroup.scalar (Fin d) (ζ ^ p) := (map_pow _ _ _).symm
      rw [h3] at hpow
      exact hpow
    have hmat : Matrix.scalar (Fin d) (ζ ^ p).1 = (1 : Matrix (Fin d) (Fin d) F) :=
      congrArg (fun x : GL (Fin d) F => (x : Matrix (Fin d) (Fin d) F)) h2
    refine Units.ext ?_
    have h1 : Matrix.scalar (Fin d) (ζ ^ p).1 = Matrix.scalar (Fin d) (1 : F) := by
      rw [hmat]
      exact (map_one (Matrix.scalar (Fin d))).symm
    exact (Matrix.scalar_inj (n := Fin d)).mp h1
  have hζne : ζ ≠ 1 := by
    intro h
    apply hζ
    rw [← hζeq, h, map_one]
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hprimUnit : IsPrimitiveRoot ζ p :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hζp hζne)
  have hprim : IsPrimitiveRoot (ζ : F) p := IsPrimitiveRoot.coe_units_iff.mpr hprimUnit
  let T : (Fin d → F) ≃ₗ[F] (Fin d → F) := glLinEquiv (Fin d) F h
  let S : (Fin d → F) ≃ₗ[F] (Fin d → F) := glLinEquiv (Fin d) F g
  have hST : S * T * S⁻¹ = unitsSmulEquiv ζ * T := by
    have h1 : S * T * S⁻¹ = glLinEquiv (Fin d) F (g * h * g⁻¹) := by
      change glLinEquiv (Fin d) F g * glLinEquiv (Fin d) F h * (glLinEquiv (Fin d) F g)⁻¹ =
        glLinEquiv (Fin d) F (g * h * g⁻¹)
      rw [map_mul, map_mul, map_inv]
    rw [h1, hconj, map_mul, glLinEquiv_scalar, unitsSmulEquiv_commute]
  have hTpe : T ^ p = 1 := by
    rw [show T = glLinEquiv (Fin d) F h from rfl, ← map_pow, hhp, map_one]
  have hTp : (T : Module.End F (Fin d → F)) ^ p = 1 := by
    have hcoepow : ∀ n : ℕ,
        ((T ^ n : (Fin d → F) ≃ₗ[F] (Fin d → F)) : Module.End F (Fin d → F)) =
        (T : Module.End F (Fin d → F)) ^ n := by
      intro n
      induction n with
      | zero => rw [pow_zero, pow_zero]; exact LinearEquiv.coe_toLinearMap_one
      | succ n ih => rw [pow_succ, LinearEquiv.coe_toLinearMap_mul, ih, pow_succ]
    rw [← hcoepow p, hTpe]
    exact LinearEquiv.coe_toLinearMap_one
  have hSTS : S⁻¹ * T * S = unitsSmulEquiv ζ⁻¹ * T := by
    have h1 : T * S⁻¹ = unitsSmulEquiv ζ * S⁻¹ * T := by
      calc T * S⁻¹ = S⁻¹ * (S * T * S⁻¹) := by group
        _ = S⁻¹ * (unitsSmulEquiv ζ * T) := by rw [hST]
        _ = unitsSmulEquiv ζ * S⁻¹ * T := by
              rw [← mul_assoc, ← unitsSmulEquiv_commute ζ S⁻¹, mul_assoc]
    have h2 : T = unitsSmulEquiv ζ * (S⁻¹ * T * S) := by
      calc T = T * S⁻¹ * S := by group
        _ = (unitsSmulEquiv ζ * S⁻¹ * T) * S := by rw [h1]
        _ = unitsSmulEquiv ζ * (S⁻¹ * T * S) := by group
    have h3 : unitsSmulEquiv ζ⁻¹ * T = S⁻¹ * T * S := by
      have h4 := congrArg (fun x => unitsSmulEquiv ζ⁻¹ * x) h2
      rw [← mul_assoc, unitsSmulEquiv_inv_mul, one_mul] at h4
      exact h4
    exact h3.symm
  have hS_mapsTo : ∀ ω : F, Set.MapsTo S
      (Module.End.eigenspace (T : Module.End F (Fin d → F)) ω)
      (Module.End.eigenspace (T : Module.End F (Fin d → F)) (ζ⁻¹ * ω)) := by
    intro ω v hv
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hv
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
    have h := congrArg (fun e : (Fin d → F) ≃ₗ[F] (Fin d → F) => e (S v)) hST
    simp [unitsSmulEquiv] at h
    have h2 : S (T v) = ω • S v := by
      rw [show T v = ω • v from hv, map_smul]
    rw [h2] at h
    have hζ : (ζ : F)⁻¹ * (ζ : F) = 1 := inv_mul_cancel₀ (Units.ne_zero ζ)
    calc T (S v) = ((ζ : F)⁻¹ * (ζ : F)) • T (S v) := by rw [hζ, one_smul]
      _ = (ζ : F)⁻¹ • ((ζ : F) • T (S v)) := by rw [mul_smul]
      _ = (ζ : F)⁻¹ • (ω • S v) := by rw [← h]
      _ = ((ζ : F)⁻¹ * ω) • S v := by rw [mul_smul]
      _ = (ζ⁻¹ * ω) • S v := by rw [Units.val_inv_eq_inv_val]
  have hSinv_mapsTo : ∀ ω : F, Set.MapsTo S.symm
      (Module.End.eigenspace (T : Module.End F (Fin d → F)) ω)
      (Module.End.eigenspace (T : Module.End F (Fin d → F)) (ζ * ω)) := by
    intro ω v hv
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hv
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
    have h := congrArg (fun e : (Fin d → F) ≃ₗ[F] (Fin d → F) => e (S.symm v)) hSTS
    simp [unitsSmulEquiv] at h
    have h2 : S.symm (T v) = ω • S.symm v := by
      rw [show T v = ω • v from hv, map_smul]
    rw [h2] at h
    have hζ : (ζ : F) * (ζ : F)⁻¹ = 1 := mul_inv_cancel₀ (Units.ne_zero ζ)
    calc T (S.symm v) = ((ζ : F) * (ζ : F)⁻¹) • T (S.symm v) := by rw [hζ, one_smul]
      _ = (ζ : F) • ((ζ : F)⁻¹ • T (S.symm v)) := by rw [mul_smul]
      _ = (ζ : F) • (ω • S.symm v) := by rw [← h]
      _ = ((ζ : F) * ω) • S.symm v := by rw [mul_smul]
      _ = (ζ * ω) • S.symm v := rfl
  have hdim : ∀ ω : F, finrank F (Module.End.eigenspace (T : Module.End F (Fin d → F)) (ζ⁻¹ * ω)) =
      finrank F (Module.End.eigenspace (T : Module.End F (Fin d → F)) ω) := by
    intro ω
    refine le_antisymm ?_ ?_
    · have hmap : (Module.End.eigenspace (T : Module.End F (Fin d → F)) (ζ⁻¹ * ω)).map
          (S.symm : (Fin d → F) →ₗ[F] (Fin d → F)) ≤
          Module.End.eigenspace (T : Module.End F (Fin d → F)) ω := by
        rintro _ ⟨v, hv, rfl⟩
        have h := hSinv_mapsTo (ζ⁻¹ * ω) hv
        have hidx : (ζ : F) * (↑ζ⁻¹ * ω) = ω := by
          rw [Units.val_inv_eq_inv_val, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero ζ), one_mul]
        rwa [hidx] at h
      calc finrank F (Module.End.eigenspace (T : Module.End F (Fin d → F)) (ζ⁻¹ * ω))
          = finrank F ((Module.End.eigenspace (T : Module.End F (Fin d → F)) (ζ⁻¹ * ω)).map
              (S.symm : (Fin d → F) →ₗ[F] (Fin d → F))) :=
            (LinearEquiv.finrank_map_eq S.symm _).symm
        _ ≤ finrank F (Module.End.eigenspace (T : Module.End F (Fin d → F)) ω) :=
            Submodule.finrank_mono hmap
    · have hmap : (Module.End.eigenspace (T : Module.End F (Fin d → F)) ω).map
          (S : (Fin d → F) →ₗ[F] (Fin d → F)) ≤
          Module.End.eigenspace (T : Module.End F (Fin d → F)) (ζ⁻¹ * ω) := by
        rintro _ ⟨v, hv, rfl⟩
        exact hS_mapsTo ω hv
      calc finrank F (Module.End.eigenspace (T : Module.End F (Fin d → F)) ω)
          = finrank F ((Module.End.eigenspace (T : Module.End F (Fin d → F)) ω).map
              (S : (Fin d → F) →ₗ[F] (Fin d → F))) :=
            (LinearEquiv.finrank_map_eq S _).symm
        _ ≤ finrank F (Module.End.eigenspace (T : Module.End F (Fin d → F)) (ζ⁻¹ * ω)) :=
            Submodule.finrank_mono hmap
  let t : Finset F := Polynomial.nthRootsFinset p (1 : F)
  have htcard : t.card = p := hprim.card_nthRootsFinset
  have hspan : t.sup (fun ω => Module.End.eigenspace (T : Module.End F (Fin d → F)) ω) = ⊤ :=
    sup_eigenspace_eq_top_of_pow_eq_one hp hprim (T : Module.End F (Fin d → F)) hTp
  have hdim' : ∀ ω : F, finrank F (Module.End.eigenspace (T : Module.End F (Fin d → F)) (ζ * ω)) =
      finrank F (Module.End.eigenspace (T : Module.End F (Fin d → F)) ω) := by
    intro ω
    have h := (hdim (ζ * ω)).symm
    rwa [show ζ⁻¹ * (ζ * ω) = ω by
      rw [Units.val_inv_eq_inv_val]
      exact inv_mul_cancel_left₀ (Units.ne_zero ζ) ω] at h
  have hdim_pow : ∀ i : ℕ,
      finrank F (Module.End.eigenspace (T : Module.End F (Fin d → F)) (ζ ^ i)) =
      finrank F (Module.End.eigenspace (T : Module.End F (Fin d → F)) 1) := by
    intro i
    induction i with
    | zero => rw [pow_zero]
    | succ i ih => rw [pow_succ, mul_comm, hdim' (ζ ^ i), ih]
  have hdim_mem : ∀ ω ∈ t,
      finrank F (Module.End.eigenspace (T : Module.End F (Fin d → F)) ω) =
      finrank F (Module.End.eigenspace (T : Module.End F (Fin d → F)) 1) := by
    intro ω hω
    obtain ⟨i, _, hζi⟩ := hprim.eq_pow_of_pow_eq_one
      ((Polynomial.mem_nthRootsFinset hp.pos (1 : F)).mp hω)
    rw [← hζi]
    exact hdim_pow i
  have hi : iSupIndep (fun ω : {ω // ω ∈ t} =>
      Module.End.eigenspace (T : Module.End F (Fin d → F)) ω) :=
    (Module.End.eigenspaces_iSupIndep (T : Module.End F (Fin d → F))).comp
      Subtype.coe_injective
  have hsup : (⨆ ω : {ω // ω ∈ t},
      Module.End.eigenspace (T : Module.End F (Fin d → F)) ω) = ⊤ := by
    rw [iSup_subtype, ← Finset.sup_eq_iSup]
    exact hspan
  have hInt := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hi hsup
  letI : DirectSum.Decomposition (fun ω : {ω // ω ∈ t} =>
      Module.End.eigenspace (T : Module.End F (Fin d → F)) ω) := hInt.chooseDecomposition
  have hsum : finrank F (Fin d → F) =
      ∑ ω ∈ t, finrank F (Module.End.eigenspace (T : Module.End F (Fin d → F)) ω) := by
    have hfr : finrank F (Fin d → F) = ∑ ω : {ω // ω ∈ t},
        finrank F (Module.End.eigenspace (T : Module.End F (Fin d → F)) ω) := by
      rw [(DirectSum.decomposeLinearEquiv (fun ω : {ω // ω ∈ t} =>
        Module.End.eigenspace (T : Module.End F (Fin d → F)) ω)).finrank_eq,
        Module.finrank_directSum]
    rw [hfr]
    exact Finset.sum_coe_sort t (fun ω : F =>
      finrank F (Module.End.eigenspace (T : Module.End F (Fin d → F)) ω))
  have hsum2 : ∑ ω ∈ t, finrank F (Module.End.eigenspace (T : Module.End F (Fin d → F)) ω) =
      p * finrank F (Module.End.eigenspace (T : Module.End F (Fin d → F)) 1) := by
    rw [Finset.sum_congr rfl (fun ω hω => hdim_mem ω hω), Finset.sum_const, htcard]
    rfl
  have h1 : d = p * finrank F (Module.End.eigenspace (T : Module.End F (Fin d → F)) 1) := by
    have h := hsum
    rw [hsum2] at h
    rwa [Module.finrank_fin_fun] at h
  have hfinrank : finrank F (Module.End.eigenspace (T : Module.End F (Fin d → F)) 1) = d / p := by
    conv_rhs => rw [h1]
    exact (Nat.mul_div_cancel_left _ hp.pos).symm
  have hdvd : p ∣ d := ⟨_, h1⟩
  let E1 : Submodule F (Fin d → F) := Module.End.eigenspace (T : Module.End F (Fin d → F)) 1
  have hE1fin : finrank F E1 = d / p := hfinrank
  let eE1 : E1 ≃ₗ[F] (Fin (d / p) → F) :=
    LinearEquiv.ofFinrankEq E1 (Fin (d / p) → F) (by rw [hE1fin, Module.finrank_fin_fun])
  let Cgl : Subgroup (GL (Fin d) F) := G ⊓ Subgroup.centralizer ({h} : Set (GL (Fin d) F))
  have hpres : ∀ x : Cgl,
      (∀ v ∈ E1, (glLinEquiv (Fin d) F (x : GL (Fin d) F)) v ∈ E1) ∧
      (∀ v ∈ E1, (glLinEquiv (Fin d) F (x : GL (Fin d) F)).symm v ∈ E1) := by
    intro x
    let X : (Fin d → F) ≃ₗ[F] (Fin d → F) := glLinEquiv (Fin d) F (x : GL (Fin d) F)
    have hxh : (x : GL (Fin d) F) * h = h * (x : GL (Fin d) F) :=
      (x.2.2 h (Set.mem_singleton h)).symm
    have hXT : X * T = T * X := by
      change glLinEquiv (Fin d) F (x : GL (Fin d) F) * T =
        T * glLinEquiv (Fin d) F (x : GL (Fin d) F)
      rw [← map_mul, ← map_mul, hxh]
    have hcomm : ∀ v : Fin d → F, (T : Module.End F (Fin d → F)) (X v) =
        X ((T : Module.End F (Fin d → F)) v) := by
      intro v
      have := congrArg (fun e : (Fin d → F) ≃ₗ[F] (Fin d → F) => e v) hXT
      simpa [LinearEquiv.mul_apply] using this.symm
    have hXinvT : T * X.symm = X.symm * T := by
      have h1 : X.symm * T * X = T := by
        rw [mul_assoc, ← hXT, ← mul_assoc,
          show X.symm * X = 1 from by ext v; simp, one_mul]
      conv_lhs => rw [← h1]
      rw [mul_assoc, show X * X.symm = 1 from by ext v; simp, mul_one]
    have hcomm_inv : ∀ v : Fin d → F, (T : Module.End F (Fin d → F)) (X.symm v) =
        X.symm ((T : Module.End F (Fin d → F)) v) := by
      intro v
      have := congrArg (fun e : (Fin d → F) ≃ₗ[F] (Fin d → F) => e v) hXinvT
      simpa [LinearEquiv.mul_apply] using this
    constructor
    · intro v hv
      change v ∈ Module.End.eigenspace (T : Module.End F (Fin d → F)) 1 at hv
      change X v ∈ Module.End.eigenspace (T : Module.End F (Fin d → F)) 1
      rw [Module.End.mem_eigenspace_iff] at hv
      rw [Module.End.mem_eigenspace_iff]
      change (T : Module.End F (Fin d → F)) (X v) = 1 • X v
      rw [hcomm, hv]; simp
    · intro v hv
      change v ∈ Module.End.eigenspace (T : Module.End F (Fin d → F)) 1 at hv
      change X.symm v ∈ Module.End.eigenspace (T : Module.End F (Fin d → F)) 1
      rw [Module.End.mem_eigenspace_iff] at hv
      rw [Module.End.mem_eigenspace_iff]
      change (T : Module.End F (Fin d → F)) (X.symm v) = 1 • X.symm v
      rw [hcomm_inv, hv]; simp
  let ρE : Cgl →* (E1 ≃ₗ[F] E1) :=
    { toFun := fun x => restrictLinearEquiv (glLinEquiv (Fin d) F (x : GL (Fin d) F)) E1
        (hpres x).1 (hpres x).2
      map_one' := by ext v i; simp [restrictLinearEquiv]
      map_mul' := by intro x y; ext v i; simp [restrictLinearEquiv, map_mul] }
  let conjE1 : (E1 ≃ₗ[F] E1) ≃* ((Fin (d / p) → F) ≃ₗ[F] (Fin (d / p) → F)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F E1).symm.trans
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv eE1).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin (d / p) → F)))
  let ρ : Cgl →* GL (Fin (d / p)) F :=
    (glLinEquiv (Fin (d / p)) F).symm.toMonoidHom.comp (conjE1.toMonoidHom.comp ρE)
  let G' : Subgroup (GL (Fin (d / p)) F) := ρ.range
  have hscalar_C : ∀ a : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin d) a ∈ Cgl := by
    intro a
    refine ⟨?_, ?_⟩
    · exact hZG (by rw [largeEvenScalars_def]; exact ⟨a, rfl⟩)
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact (Matrix.GeneralLinearGroup.scalar_commute a h).symm
  have hρE_scalar : ∀ a : Fˣ,
      ρE ⟨Matrix.GeneralLinearGroup.scalar (Fin d) a, hscalar_C a⟩ =
      unitsSmulEquiv (V := E1) a := by
    intro a
    ext v i
    simp only [ρE, MonoidHom.coe_mk, OneHom.coe_mk, restrictLinearEquiv, unitsSmulEquiv,
      LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, glLinEquiv_scalar,
      Submodule.coe_smul]
  have hconj_scalar : ∀ a : Fˣ,
      conjE1 (unitsSmulEquiv (V := E1) a) =
      unitsSmulEquiv (V := Fin (d / p) → F) a := by
    intro a
    rw [show conjE1 (unitsSmulEquiv (V := E1) a) =
        eE1.symm.trans ((unitsSmulEquiv (V := E1) a).trans eE1) from by
      simp only [conjE1, MulEquiv.trans_apply, MulEquiv.coe_toMonoidHom,
        LinearMap.GeneralLinearGroup.congrLinearEquiv_apply]
      rfl]
    exact trans_unitsSmulEquiv_trans a eE1
  have hrho_scalar : ∀ a : Fˣ,
      ρ ⟨Matrix.GeneralLinearGroup.scalar (Fin d) a, hscalar_C a⟩ =
      Matrix.GeneralLinearGroup.scalar (Fin (d / p)) a := by
    intro a
    apply (glLinEquiv (Fin (d / p)) F).injective
    change glLinEquiv (Fin (d / p)) F ((glLinEquiv (Fin (d / p)) F).symm
      (conjE1 (ρE ⟨Matrix.GeneralLinearGroup.scalar (Fin d) a, hscalar_C a⟩))) =
      glLinEquiv (Fin (d / p)) F (Matrix.GeneralLinearGroup.scalar (Fin (d / p)) a)
    rw [MulEquiv.apply_symm_apply, hρE_scalar a, hconj_scalar a, glLinEquiv_scalar]
  have hscalars_le : LargeEvenScalars (Fin (d / p)) F ≤ G' := by
    rw [largeEvenScalars_def]
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨_, hscalar_C a⟩, hrho_scalar a⟩
  have hmelem : MElemMod p (d / p) F G' := by
    constructor
    · rintro g hg
      obtain ⟨x, rfl⟩ := hg
      have hxp : ((x : Cgl) : GL (Fin d) F) ^ p ∈ LargeEvenScalars (Fin d) F := hel.1 _ x.2.1
      rw [largeEvenScalars_def] at hxp
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hxp
      have hxpeq : (x ^ p : Cgl) = ⟨Matrix.GeneralLinearGroup.scalar (Fin d) a, hscalar_C a⟩ := by
        apply Subtype.ext
        simpa [Subgroup.coe_pow] using ha.symm
      rw [← map_pow, hxpeq, hrho_scalar a, largeEvenScalars_def]
      exact ⟨a, rfl⟩
    · rintro g hg k hk
      obtain ⟨x, rfl⟩ := hg
      obtain ⟨y, rfl⟩ := hk
      rw [← map_commutatorElement]
      have hxy : ((⁅x, y⁆ : Cgl) : GL (Fin d) F) ∈ LargeEvenScalars (Fin d) F := by
        change Cgl.subtype ⁅x, y⁆ ∈ LargeEvenScalars (Fin d) F
        rw [map_commutatorElement Cgl.subtype x y]
        exact hel.2 (x : GL (Fin d) F) x.2.1 (y : GL (Fin d) F) y.2.1
      rw [largeEvenScalars_def] at hxy
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hxy
      have hxyeq : (⁅x, y⁆ : Cgl) =
          ⟨Matrix.GeneralLinearGroup.scalar (Fin d) a, hscalar_C a⟩ := by
        apply Subtype.ext
        simpa using ha.symm
      rw [hxyeq, hrho_scalar a, largeEvenScalars_def]
      exact ⟨a, rfl⟩
  let Z : Subgroup (GL (Fin d) F) := LargeEvenScalars (Fin d) F
  let Z' : Subgroup (GL (Fin (d / p)) F) := LargeEvenScalars (Fin (d / p)) F
  have hZ_C : Z ≤ Cgl := by
    rw [show Z = LargeEvenScalars (Fin d) F from rfl, largeEvenScalars_def]
    rintro _ ⟨a, rfl⟩
    exact hscalar_C a
  have hC_G : Cgl ≤ G := inf_le_left
  let Lgl : Subgroup (GL (Fin d) F) := (Z'.comap ρ).map Cgl.subtype
  have hL_C : Lgl ≤ Cgl := Subgroup.map_subtype_le _
  have hZ_L : Z ≤ Lgl := by
    intro z hz
    have hzC : z ∈ Cgl := hZ_C hz
    refine Subgroup.mem_map.mpr ⟨⟨z, hzC⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have hz' : z ∈ LargeEvenScalars (Fin d) F := hz
    rw [largeEvenScalars_def] at hz'
    obtain ⟨a, rfl⟩ := hz'
    rw [show ρ ⟨Matrix.GeneralLinearGroup.scalar (Fin d) a, hzC⟩ =
        Matrix.GeneralLinearGroup.scalar (Fin (d / p)) a from hrho_scalar a]
    change Matrix.GeneralLinearGroup.scalar (Fin (d / p)) a ∈
      LargeEvenScalars (Fin (d / p)) F
    rw [largeEvenScalars_def]
    exact ⟨a, rfl⟩
  have hrel1 : Z.relIndex G = Z.relIndex Cgl * Cgl.relIndex G :=
    (Subgroup.relIndex_mul_relIndex (H := Z) (K := Cgl) (L := G) hZ_C hC_G).symm
  have hrel2 : Z.relIndex Cgl = Z.relIndex Lgl * Lgl.relIndex Cgl :=
    (Subgroup.relIndex_mul_relIndex (H := Z) (K := Lgl) (L := Cgl) hZ_L hL_C).symm
  have hLrel : Lgl.relIndex Cgl = Z'.relIndex G' := by
    have h1 : Lgl.relIndex Cgl = (Z'.comap ρ).relIndex (⊤ : Subgroup Cgl) := by
      have h := Subgroup.relIndex_map_map_of_injective (f := Cgl.subtype) (Z'.comap ρ)
        (⊤ : Subgroup Cgl) (fun a b hab => Subtype.ext hab)
      rwa [Subgroup.map_top, Subgroup.range_subtype] at h
    rw [h1, Subgroup.relIndex_comap]
    rw [show Subgroup.map ρ ⊤ = G' from by rw [Subgroup.map_top]]
  have hmain : Z.relIndex G = Z.relIndex Lgl * Lgl.relIndex Cgl * Cgl.relIndex G := by
    rw [hrel1, hrel2, mul_assoc]
  have hCrel : Cgl.relIndex G ≤ p := by
    let φh : G →* LargeEvenScalars (Fin d) F :=
    { toFun := fun x => ⟨⁅(x : GL (Fin d) F), h⁆, hel.2 _ x.2 _ hh⟩
      map_one' := by
        apply Subtype.ext
        simp [commutatorElement_def]
      map_mul' := by
        intro x y
        apply Subtype.ext
        have hx : ⁅(x : GL (Fin d) F), h⁆ ∈ LargeEvenScalars (Fin d) F := hel.2 _ x.2 _ hh
        have hy : ⁅(y : GL (Fin d) F), h⁆ ∈ LargeEvenScalars (Fin d) F := hel.2 _ y.2 _ hh
        change ⁅(x : GL (Fin d) F) * (y : GL (Fin d) F), h⁆ =
          ⁅(x : GL (Fin d) F), h⁆ * ⁅(y : GL (Fin d) F), h⁆
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hcomm_y : (x : GL (Fin d) F) * ⁅(y : GL (Fin d) F), h⁆ * (x : GL (Fin d) F)⁻¹ =
            ⁅(y : GL (Fin d) F), h⁆ := by
          rw [largeEvenScalars_def] at hy
          obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hy
          rw [← hb]
          have hcx : (x : GL (Fin d) F) * Matrix.GeneralLinearGroup.scalar (Fin d) b =
              Matrix.GeneralLinearGroup.scalar (Fin d) b * (x : GL (Fin d) F) :=
            (Matrix.GeneralLinearGroup.scalar_commute b (x : GL (Fin d) F)).symm
          rw [hcx]; group
        rw [hcomm_y]
        rw [largeEvenScalars_def] at hx hy
        obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hx
        obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hy
        rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm] }
    have hker : Cgl.subgroupOf G = φh.ker := by
      ext x
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      constructor
      · intro hx
        apply Subtype.ext
        change ⁅(x : GL (Fin d) F), h⁆ = 1
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (hx.2 h (Set.mem_singleton h)).symm
      · intro hx
        refine ⟨x.2, ?_⟩
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        have h1 : ⁅(x : GL (Fin d) F), h⁆ = 1 :=
          congrArg Subtype.val hx
        rw [commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1.symm
    have hcard : Nat.card φh.range ≤ p := by
      have hinj : Function.Injective (scalarUnitHom (n := Fin d) (K := F)) := by
        intro y z hyz
        apply Subtype.ext
        rw [← scalarUnit_spec y, ← scalarUnit_spec z]
        exact congrArg (Matrix.GeneralLinearGroup.scalar (Fin d))
          (show scalarUnit y = scalarUnit z from hyz)
      have hle : ∀ y ∈ φh.range,
          (scalarUnitHom (n := Fin d) (K := F) y : Fˣ) ^ p = 1 := by
        rintro _ ⟨x, rfl⟩
        have hxsc : (x : GL (Fin d) F) ^ p ∈ LargeEvenScalars (Fin d) F := hel.1 _ x.2
        have hmem : ⁅(x : GL (Fin d) F), h⁆ ∈ LargeEvenScalars (Fin d) F := hel.2 _ x.2 _ hh
        have hval : scalarUnitHom (n := Fin d) (K := F) (φh x) =
            scalarUnit ⟨⁅(x : GL (Fin d) F), h⁆, hmem⟩ := rfl
        rw [hval]
        apply glScalar_injective (n := Fin d)
        simp only [scalarUnit_spec, map_pow, map_one]
        have hcomm : Commute (x : GL (Fin d) F) ⁅(x : GL (Fin d) F), h⁆ := by
          rw [largeEvenScalars_def] at hmem
          obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hmem
          rw [← ha]
          exact (Matrix.GeneralLinearGroup.scalar_commute a (x : GL (Fin d) F)).symm
        rw [hcomm.commutatorElement_pow_left p]
        rw [largeEvenScalars_def] at hxsc
        obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hxsc
        rw [← ha, commutatorElement_eq_one_iff_mul_comm]
        exact Matrix.GeneralLinearGroup.scalar_commute a h
      have hinj2 : Function.Injective (fun y : φh.range =>
          (⟨scalarUnitHom (n := Fin d) (K := F) y.1, hle y.1 y.2⟩ : rootsOfUnity p F)) := by
        intro y z hyz
        apply Subtype.ext
        exact hinj (Subtype.ext_iff.mp hyz)
      calc Nat.card φh.range ≤ Nat.card (rootsOfUnity p F) :=
            Nat.card_le_card_of_injective _ hinj2
        _ ≤ p := card_rootsOfUnity F p
    rw [Subgroup.relIndex, hker, Subgroup.index_ker]
    exact hcard
  have hZrelL : Z.relIndex Lgl ≤ p := by
    have hSpow : ∀ j : ℕ, ∀ v ∈ Module.End.eigenspace (T : Module.End F (Fin d → F)) (ζ ^ j),
        (S ^ j : (Fin d → F) ≃ₗ[F] (Fin d → F)) v ∈
        Module.End.eigenspace (T : Module.End F (Fin d → F)) 1 := by
      intro j
      induction j with
      | zero => intro v hv; simpa using hv
      | succ j ih =>
        intro v hv
        have h1 : S v ∈ Module.End.eigenspace (T : Module.End F (Fin d → F)) (ζ ^ j) := by
          have h := hS_mapsTo (ζ ^ (j + 1)) hv
          have hidx : (↑ζ⁻¹ : F) * (↑ζ : F) ^ (j + 1) = (↑ζ : F) ^ j := by
            rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
            congr 1
            rw [pow_succ]; group
          rwa [hidx] at h
        have h2 := ih (S v) h1
        simpa [pow_succ] using h2
    have hkey : ∀ (Y : (Fin d → F) ≃ₗ[F] (Fin d → F)) (a : Fˣ),
        Y * T = T * Y → Y * S = S * Y →
        (∀ v ∈ Module.End.eigenspace (T : Module.End F (Fin d → F)) 1, Y v = (a : F) • v) →
        Y = unitsSmulEquiv (V := Fin d → F) a := by
      intro Y a hYT hYS hYfix
      have hle : t.sup (fun ω => Module.End.eigenspace (T : Module.End F (Fin d → F)) ω) ≤
          LinearMap.ker ((Y : (Fin d → F) →ₗ[F] (Fin d → F)) -
            (unitsSmulEquiv (V := Fin d → F) a : (Fin d → F) →ₗ[F] (Fin d → F))) := by
        rw [Finset.sup_le_iff]
        intro ω hω
        obtain ⟨j, -, hζj⟩ := hprim.eq_pow_of_pow_eq_one
          ((Polynomial.mem_nthRootsFinset hp.pos (1 : F)).mp hω)
        subst hζj
        rintro v hv
        rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
        have h1 : (S ^ j) v ∈ Module.End.eigenspace (T : Module.End F (Fin d → F)) 1 :=
          hSpow j v hv
        have h2 : Y ((S ^ j) v) = (a : F) • ((S ^ j) v) := hYfix _ h1
        have h3 : Y ((S ^ j) v) = (S ^ j) (Y v) := by
          have hcomm : Commute Y (S ^ j) := (show Commute Y S from hYS).pow_right j
          have := congrArg (fun e : (Fin d → F) ≃ₗ[F] (Fin d → F) => e v) hcomm.eq
          simpa [LinearEquiv.mul_apply] using this
        rw [h3] at h2
        have h4 : (S ^ j) (Y v) = (S ^ j) ((a : F) • v) := by rw [h2, map_smul]
        exact (S ^ j).injective h4
      have htop : LinearMap.ker ((Y : (Fin d → F) →ₗ[F] (Fin d → F)) -
          (unitsSmulEquiv (V := Fin d → F) a : (Fin d → F) →ₗ[F] (Fin d → F))) = ⊤ :=
        eq_top_iff.mpr (hspan ▸ hle)
      apply LinearEquiv.ext
      intro v
      have hv : v ∈ LinearMap.ker ((Y : (Fin d → F) →ₗ[F] (Fin d → F)) -
          (unitsSmulEquiv (V := Fin d → F) a : (Fin d → F) →ₗ[F] (Fin d → F))) := by
        rw [htop]; trivial
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hv
      exact hv
    have hρ_def : ∀ x : Cgl, ρ x = (glLinEquiv (Fin (d / p)) F).symm (conjE1 (ρE x)) :=
      fun x => rfl
    have hker_eq : ρ.ker = ρE.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      constructor
      · intro hx
        rw [hρ_def x] at hx
        have h := congrArg (glLinEquiv (Fin (d / p)) F) hx
        rw [MulEquiv.apply_symm_apply, map_one] at h
        exact conjE1.injective (by rw [h, map_one])
      · intro hx
        rw [hρ_def x, hx, map_one, map_one]
    have hfix : ∀ x : ρ.ker, ∀ v ∈ E1,
        (glLinEquiv (Fin d) F ((x : Cgl) : GL (Fin d) F)) v = v := by
      intro x v hv
      have hx : (x : Cgl) ∈ ρE.ker := by
        rw [← hker_eq]
        exact x.2
      rw [MonoidHom.mem_ker] at hx
      have h2 := congrArg (fun e : E1 ≃ₗ[F] E1 => ((e ⟨v, hv⟩ : E1) : Fin d → F)) hx
      simpa [ρE, restrictLinearEquiv] using h2
    let φg : Cgl →* LargeEvenScalars (Fin d) F :=
    { toFun := fun x => ⟨⁅(x : GL (Fin d) F), g⁆, hel.2 _ x.2.1 _ hg⟩
      map_one' := by
        apply Subtype.ext
        simp [commutatorElement_def]
      map_mul' := by
        intro x y
        apply Subtype.ext
        have hx : ⁅(x : GL (Fin d) F), g⁆ ∈ LargeEvenScalars (Fin d) F := hel.2 _ x.2.1 _ hg
        have hy : ⁅(y : GL (Fin d) F), g⁆ ∈ LargeEvenScalars (Fin d) F := hel.2 _ y.2.1 _ hg
        change ⁅(x : GL (Fin d) F) * (y : GL (Fin d) F), g⁆ =
          ⁅(x : GL (Fin d) F), g⁆ * ⁅(y : GL (Fin d) F), g⁆
        rw [commutatorElement_mul_left_eq_conj_mul]
        have hcomm_y : (x : GL (Fin d) F) * ⁅(y : GL (Fin d) F), g⁆ * (x : GL (Fin d) F)⁻¹ =
            ⁅(y : GL (Fin d) F), g⁆ := by
          rw [largeEvenScalars_def] at hy
          obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hy
          rw [← hb]
          have hcx : (x : GL (Fin d) F) * Matrix.GeneralLinearGroup.scalar (Fin d) b =
              Matrix.GeneralLinearGroup.scalar (Fin d) b * (x : GL (Fin d) F) :=
            (Matrix.GeneralLinearGroup.scalar_commute b (x : GL (Fin d) F)).symm
          rw [hcx]; group
        rw [hcomm_y]
        rw [largeEvenScalars_def] at hx hy
        obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hx
        obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hy
        rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm] }
    let ψ : Cgl →* Fˣ := (scalarUnitHom (n := Fin d) (K := F)).comp φg
    have hψ_inj : Function.Injective (scalarUnitHom (n := Fin d) (K := F)) := by
      intro y z hyz
      apply Subtype.ext
      rw [← scalarUnit_spec y, ← scalarUnit_spec z]
      exact congrArg (Matrix.GeneralLinearGroup.scalar (Fin d))
        (show scalarUnit y = scalarUnit z from hyz)
    have hψ_one : ∀ x : Cgl, ψ x = 1 → ⁅(x : GL (Fin d) F), g⁆ = 1 := by
      intro x hx
      have h1 : φg x = 1 := hψ_inj (by
        rw [show (scalarUnitHom (n := Fin d) (K := F)) (φg x) = ψ x from rfl, hx, map_one])
      have h2 := congrArg (fun y : LargeEvenScalars (Fin d) F => (y : GL (Fin d) F)) h1
      exact h2
    have hker_card : Nat.card (ρ.ker) ≤ p := by
      have hmem_roots : ∀ x : ρ.ker, ψ (x : Cgl) ∈ rootsOfUnity p F := by
        intro x
        rw [mem_rootsOfUnity]
        have hxsc : ((x : Cgl) : GL (Fin d) F) ^ p ∈ LargeEvenScalars (Fin d) F :=
          hel.1 _ (x : Cgl).2.1
        have hmem : ⁅((x : Cgl) : GL (Fin d) F), g⁆ ∈ LargeEvenScalars (Fin d) F :=
          hel.2 _ (x : Cgl).2.1 _ hg
        have hval : ψ (x : Cgl) = scalarUnit ⟨⁅((x : Cgl) : GL (Fin d) F), g⁆, hmem⟩ := rfl
        rw [hval]
        apply glScalar_injective (n := Fin d)
        simp only [scalarUnit_spec, map_pow, map_one]
        have hcomm : Commute ((x : Cgl) : GL (Fin d) F)
            ⁅((x : Cgl) : GL (Fin d) F), g⁆ := by
          rw [largeEvenScalars_def] at hmem
          obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hmem
          rw [← ha]
          exact (Matrix.GeneralLinearGroup.scalar_commute a
            (((x : Cgl) : GL (Fin d) F))).symm
        rw [hcomm.commutatorElement_pow_left p]
        rw [largeEvenScalars_def] at hxsc
        obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hxsc
        rw [← ha, commutatorElement_eq_one_iff_mul_comm]
        exact Matrix.GeneralLinearGroup.scalar_commute a g
      have hinj : Function.Injective (fun x : ρ.ker =>
          (⟨ψ (x : Cgl), hmem_roots x⟩ : rootsOfUnity p F)) := by
        intro x y hxy
        apply Subtype.ext
        have hxy' : ψ (x : Cgl) = ψ (y : Cgl) := Subtype.ext_iff.mp hxy
        have h1 : ψ ((x : Cgl) * (y : Cgl)⁻¹) = 1 := by
          rw [map_mul, map_inv, hxy', mul_inv_cancel]
        have h2 : ⁅(((x : Cgl) * (y : Cgl)⁻¹ : Cgl) : GL (Fin d) F), g⁆ = 1 := hψ_one _ h1
        have hXT : (glLinEquiv (Fin d) F (((x : Cgl) * (y : Cgl)⁻¹ : Cgl) : GL (Fin d) F)) * T =
            T * glLinEquiv (Fin d) F (((x : Cgl) * (y : Cgl)⁻¹ : Cgl) : GL (Fin d) F) := by
          rw [← map_mul, ← map_mul]
          congr 1
          exact (((x : Cgl) * (y : Cgl)⁻¹ : Cgl).2.2 h (Set.mem_singleton h)).symm
        have hYS : (glLinEquiv (Fin d) F (((x : Cgl) * (y : Cgl)⁻¹ : Cgl) : GL (Fin d) F)) * S =
            S * glLinEquiv (Fin d) F (((x : Cgl) * (y : Cgl)⁻¹ : Cgl) : GL (Fin d) F) := by
          rw [← map_mul, ← map_mul]
          congr 1
          rw [commutatorElement_eq_one_iff_mul_comm] at h2
          exact h2
        have hfix' : ∀ v ∈ Module.End.eigenspace (T : Module.End F (Fin d → F)) 1,
            (glLinEquiv (Fin d) F (((x : Cgl) * (y : Cgl)⁻¹ : Cgl) : GL (Fin d) F)) v =
            (1 : F) • v := by
          intro v hv
          rw [one_smul]
          have hmem : (x : Cgl) * (y : Cgl)⁻¹ ∈ ρ.ker := by
            rw [MonoidHom.mem_ker]
            rw [map_mul, map_inv, MonoidHom.mem_ker.mp x.2, MonoidHom.mem_ker.mp y.2,
              one_mul, inv_one]
          exact hfix ⟨_, hmem⟩ v hv
        have hkey' := hkey _ 1 hXT hYS hfix'
        have hone : unitsSmulEquiv (V := Fin d → F) (1 : Fˣ) = 1 := by
          ext v; simp [unitsSmulEquiv]
        rw [hone] at hkey'
        have h3 : (x : Cgl) * (y : Cgl)⁻¹ = 1 := by
          apply Subtype.ext
          simpa using (glLinEquiv (Fin d) F).injective (hkey'.trans (map_one _).symm)
        rw [mul_inv_eq_one] at h3
        exact h3
      calc Nat.card (ρ.ker) ≤ Nat.card (rootsOfUnity p F) :=
            Nat.card_le_card_of_injective _ hinj
        _ ≤ p := card_rootsOfUnity F p
    have hZ'_le_map : Z' ≤ (Z.subgroupOf Cgl).map ρ := by
      intro w hw
      rw [show Z' = LargeEvenScalars (Fin (d / p)) F from rfl, largeEvenScalars_def] at hw
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hw
      refine Subgroup.mem_map.mpr
        ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin d) a, hscalar_C a⟩, ?_,
          (hrho_scalar a).trans ha⟩
      change Matrix.GeneralLinearGroup.scalar (Fin d) a ∈ Z
      rw [show Z = LargeEvenScalars (Fin d) F from rfl, largeEvenScalars_def]
      exact ⟨a, rfl⟩
    have hZmap : (Z.subgroupOf Cgl).map Cgl.subtype = Z := by
      apply le_antisymm
      · rintro x ⟨z, hz, rfl⟩
        exact Subgroup.mem_subgroupOf.mp hz
      · intro x hx
        exact ⟨⟨x, hZ_C hx⟩, hx, rfl⟩
    have hLgl_sup : Lgl ≤ Z ⊔ ρ.ker.map Cgl.subtype := by
      calc Lgl = (Z'.comap ρ).map Cgl.subtype := rfl
        _ ≤ ((Z.subgroupOf Cgl) ⊔ ρ.ker).map Cgl.subtype :=
              Subgroup.map_mono (comap_le_sup_ker ρ hZ'_le_map)
        _ = (Z.subgroupOf Cgl).map Cgl.subtype ⊔ ρ.ker.map Cgl.subtype :=
              Subgroup.map_sup (Z.subgroupOf Cgl) ρ.ker Cgl.subtype
        _ = Z ⊔ ρ.ker.map Cgl.subtype := by rw [hZmap]
    have hMcard : Nat.card (ρ.ker.map Cgl.subtype) = Nat.card (ρ.ker) :=
      (Nat.card_congr (Subgroup.equivMapOfInjective ρ.ker Cgl.subtype
        (fun a b hab => Subtype.ext hab)).toEquiv).symm
    calc Z.relIndex Lgl ≤ Nat.card (ρ.ker.map Cgl.subtype) :=
          relIndex_le_card_of_le_sup inferInstance hLgl_sup
      _ = Nat.card (ρ.ker) := hMcard
      _ ≤ p := hker_card
  have hfinal : Z.relIndex G ≤ p ^ 2 * Z'.relIndex G' := by
    rw [hmain, hLrel]
    calc Z.relIndex Lgl * Z'.relIndex G' * Cgl.relIndex G
        ≤ p * Z'.relIndex G' * p :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ hZrelL) hCrel
      _ = p ^ 2 * Z'.relIndex G' := by ring
  exact ⟨hdvd, G', hscalars_le, hmelem, hfinal⟩

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
