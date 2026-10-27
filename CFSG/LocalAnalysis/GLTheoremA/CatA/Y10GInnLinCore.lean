module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinMat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinHeld

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

open CFSG.Open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.Held
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup exists_glaPComponent_map_fixSubgroup)
open scoped commutatorElement

section Projection

variable {K : Type} [Field K] {d : ℕ}

theorem mem_statedScalars_iff (x : GL (Fin d) K) :
    x ∈ StatedScalars (Fin d) K ↔ ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin d) c = x :=
  MonoidHom.mem_range

theorem projMk_eq_iff (x y : ↥(StatedSL d K)) :
    LargeEvenProjMk (StatedSL d K) x = LargeEvenProjMk (StatedSL d K) y ↔
      ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin d) c = (x : GL (Fin d) K)⁻¹ * (y : GL (Fin d) K) := by
  rw [LargeEvenProjMk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  have hmem : ((x⁻¹ * y : ↥(StatedSL d K)) : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K ↔
      ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin d) c = (x : GL (Fin d) K)⁻¹ * (y : GL (Fin d) K) := by
    rw [LargeEvenScalars, mem_statedScalars_iff]
    simp
  rw [← hmem]

@[expose] def conjSL (A : GL (Fin d) K) : MulAut ↥(StatedSL d K) where
  toFun h := ⟨A * (h : GL (Fin d) K) * A⁻¹, (statedSL_normal d).conj_mem h.1 h.2 A⟩
  invFun h := ⟨A⁻¹ * (h : GL (Fin d) K) * A⁻¹⁻¹, (statedSL_normal d).conj_mem h.1 h.2 A⁻¹⟩
  left_inv h := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv h := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' x y := by
    apply Subtype.ext
    simp [mul_assoc]

@[simp]
theorem conjSL_apply_val (A : GL (Fin d) K) (h : ↥(StatedSL d K)) :
    ((conjSL A h : ↥(StatedSL d K)) : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ :=
  rfl

theorem pow_projMk (A : GL (Fin d) K)
    (u : MulAut (LargeEvenProj (StatedSL d K)))
    (hu : ∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h')
    (k : ℕ) (h h' : ↥(StatedSL d K)) (hk : (h' : GL (Fin d) K) = A ^ k * (h : GL (Fin d) K) * (A ^ k)⁻¹) :
    (u ^ k) (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h' := by
  induction k generalizing h h' with
  | zero =>
    have : h' = h := by
      apply Subtype.ext
      simpa using hk
    subst this
    simp
  | succ k ih =>
    let h1 : ↥(StatedSL d K) := conjSL A h
    have hh1 : (h1 : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ := rfl
    have step1 : u (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h1 :=
      hu h h1 hh1
    have step2 := ih h1 h' (by rw [hk, hh1, pow_succ]; group)
    rw [pow_succ, MulAut.mul_apply, step1, step2]

end Projection

section Scalars

variable {K : Type} [Field K] {d : ℕ}

theorem val_scalar_gl (c : Kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (c : K) • (1 : Matrix (Fin d) (Fin d) K) := by
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_one_eq_diagonal]

theorem isScalar_of_pow_trivial (h2 : (2 : K) = 0) (A : GL (Fin d) K) (p : ℕ)
    (u : MulAut (LargeEvenProj (StatedSL d K)))
    (hu : ∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h')
    (hpow : u ^ p = 1) :
    ∃ c : K, ((A ^ p : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = c • (1 : Matrix (Fin d) (Fin d) K) := by
  refine gl_isScalar_of_conj_mod_scalar h2 (A ^ p) ?_
  intro g hg
  let h : ↥(StatedSL d K) := ⟨g, hg⟩
  let h' : ↥(StatedSL d K) := conjSL (A ^ p) h
  have hk : (h' : GL (Fin d) K) = A ^ p * (h : GL (Fin d) K) * (A ^ p)⁻¹ := rfl
  have hmk : LargeEvenProjMk (StatedSL d K) h' = LargeEvenProjMk (StatedSL d K) h := by
    have := pow_projMk A u hu p h h' hk
    rw [hpow] at this
    simpa using this.symm
  obtain ⟨c, hc⟩ := (projMk_eq_iff h' h).mp hmk
  have h1 : (h' : GL (Fin d) K) = (h : GL (Fin d) K) * (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ := by
    rw [hc]
    group
  have hGL : A ^ p * (g : GL (Fin d) K) * (A ^ p)⁻¹ =
      (g : GL (Fin d) K) * (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ := by
    rw [← hk, h1]
  refine ⟨(c : K)⁻¹, ?_⟩
  have hM := congrArg (fun X : GL (Fin d) K => ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) hGL
  simp only [Units.val_mul] at hM
  rw [hM, ← map_inv, val_scalar_gl, Units.val_inv_eq_inv_val, Matrix.mul_smul, Matrix.mul_one]

end Scalars

section Orders

variable {K : Type} [Field K] [Finite K]

theorem not_two_dvd_natCard_units (h2 : (2 : K) = 0) : ¬ 2 ∣ Nat.card Kˣ := by
  intro h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx2' : (x : K) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx2, Units.val_one]
  have h3 : ((x : K) - 1) ^ 2 = 0 := by
    linear_combination hx2' + (1 - (x : K)) * h2
  have h4 : (x : K) - 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h3
  have hx1 : x = 1 := Units.ext (sub_eq_zero.mp h4)
  rw [hx1, orderOf_one] at hx
  norm_num at hx

theorem odd_orderOf_of_pow_scalar (h2 : (2 : K) = 0) {d : ℕ} (hd : 1 ≤ d) (A : GL (Fin d) K) {p : ℕ}
    (hp : Odd p) {c : K}
    (hc : ((A ^ p : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = c • (1 : Matrix (Fin d) (Fin d) K)) :
    Odd (orderOf A) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hc0 : c ≠ 0 := by
    intro h0
    have hu : ((A ^ p : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        (((A ^ p)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := Units.mul_inv (A ^ p)
    rw [hc, h0, zero_smul, zero_mul] at hu
    exact one_ne_zero hu.symm
  let z : Kˣ := Units.mk0 c hc0
  have hz : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) z := by
    apply Units.ext
    rw [val_scalar_gl]
    exact hc
  have hdvd : orderOf A ∣ p * orderOf z := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, hz, ← map_pow, pow_orderOf_eq_one, map_one]
  have hodd_card : Odd (Nat.card Kˣ) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (not_two_dvd_natCard_units h2))
  have hodd_z : Odd (orderOf z) := Odd.of_dvd_nat hodd_card (orderOf_dvd_natCard z)
  exact Odd.of_dvd_nat (Odd.mul hp hodd_z) hdvd

theorem cast_orderOf_ne_zero_of_odd (h2 : (2 : K) = 0) {G : Type*} [Group G] (x : G)
    (hx : Odd (orderOf x)) : ((orderOf x : ℕ) : K) ≠ 0 := by
  obtain ⟨k, hk⟩ := hx
  rw [hk]
  push_cast
  rw [h2]
  simp

end Orders

section Centre

variable {G H : Type*} [Group G] [Group H]

open scoped commutatorElement in
theorem mem_center_of_commutator_mem_center (hG : commutator G = ⊤) {g : G}
    (hc : ∀ x : G, ⁅g, x⁆ ∈ Subgroup.center G) : g ∈ Subgroup.center G := by
  have hmul : ∀ x y : G, ⁅g, x * y⁆ = ⁅g, x⁆ * ⁅g, y⁆ := by
    intro x y
    have hxc : x * ⁅g, y⁆ = ⁅g, y⁆ * x := Subgroup.mem_center_iff.mp (hc y) x
    have hcx : ⁅g, y⁆ * x⁻¹ = x⁻¹ * ⁅g, y⁆ := by
      calc ⁅g, y⁆ * x⁻¹ = x⁻¹ * (x * ⁅g, y⁆) * x⁻¹ := by group
        _ = x⁻¹ * (⁅g, y⁆ * x) * x⁻¹ := by rw [hxc]
        _ = x⁻¹ * ⁅g, y⁆ := by group
    rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
    calc g * (x * y) * g⁻¹ * (x * y)⁻¹
        = g * x * (g⁻¹ * (g * y * g⁻¹ * y⁻¹)) * x⁻¹ := by group
      _ = g * x * g⁻¹ * (⁅g, y⁆ * x⁻¹) := by rw [commutatorElement_def]; group
      _ = g * x * g⁻¹ * (x⁻¹ * ⁅g, y⁆) := by rw [hcx]
      _ = g * x * g⁻¹ * x⁻¹ * (g * y * g⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
  have hinv : ∀ u : G, ⁅g, u⁻¹⁆ * ⁅g, u⁆ = 1 := by
    intro u
    have h := hmul u⁻¹ u
    rw [inv_mul_cancel, commutatorElement_one_right] at h
    exact h.symm
  have hpow : ∀ x : G, ⁅g, x⁆ = 1 := by
    intro x
    have hx : x ∈ commutator G := by rw [hG]; exact Subgroup.mem_top x
    change x ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ at hx
    rw [Subgroup.commutator_def] at hx
    induction hx using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, -, b, -, rfl⟩ := hw
      have hp : ⁅g, a⁆ * ⁅g, b⁆ = ⁅g, b⁆ * ⁅g, a⁆ :=
        Subgroup.mem_center_iff.mp (hc b) _
      have hpi : ⁅g, a⁻¹⁆ = ⁅g, a⁆⁻¹ := eq_inv_of_mul_eq_one_left (hinv a)
      have hqi : ⁅g, b⁻¹⁆ = ⁅g, b⁆⁻¹ := eq_inv_of_mul_eq_one_left (hinv b)
      rw [commutatorElement_def a b, hmul, hmul, hmul, hpi, hqi]
      calc ⁅g, a⁆ * ⁅g, b⁆ * ⁅g, a⁆⁻¹ * ⁅g, b⁆⁻¹ = ⁅g, b⁆ * ⁅g, a⁆ * ⁅g, a⁆⁻¹ * ⁅g, b⁆⁻¹ := by
            rw [hp]
        _ = 1 := by group
    | one => simp
    | mul x y _ _ hx hy => rw [hmul, hx, hy, one_mul]
    | inv x _ hx =>
      have := hinv x
      rw [hx, mul_one] at this
      exact this
  refine Subgroup.mem_center_iff.mpr fun x => ?_
  exact (commutatorElement_eq_one_iff_mul_comm.mp (hpow x)).symm

theorem center_quot_equiv_of_surjective (hG : commutator G = ⊤) (f : G →* H)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center G) :
    Nonempty (H ⧸ Subgroup.center H ≃* G ⧸ Subgroup.center G) := by
  let φ : G →* H ⧸ Subgroup.center H := (QuotientGroup.mk' (Subgroup.center H)).comp f
  have hφ : Function.Surjective φ := fun y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨g, rfl⟩ := hf x
    exact ⟨g, rfl⟩
  have hker' : φ.ker = Subgroup.center G := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hfx : f x ∈ Subgroup.center H := by
        have hx' : ((f x : H) : H ⧸ Subgroup.center H) = 1 := hx
        exact (QuotientGroup.eq_one_iff (f x)).mp hx'
      apply mem_center_of_commutator_mem_center hG
      intro y
      apply hker
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hfx (f y)).symm
    · intro hx
      rw [MonoidHom.mem_ker]
      have hfx : f x ∈ Subgroup.center H := by
        refine Subgroup.mem_center_iff.mpr fun h => ?_
        obtain ⟨y, rfl⟩ := hf h
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
      exact (QuotientGroup.eq_one_iff (f x)).mpr hfx
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker')⟩

end Centre

section Core

variable {K : Type} [Field K] [Finite K]

theorem map_fixSubgroup_conjSL {d : ℕ} (A : GL (Fin d) K) :
    (fixSubgroup (conjSL A)).map (StatedSL d K).subtype =
      Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ CFSG.Open.StatedSL d K := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_fixSubgroup,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h := congrArg (fun z : ↥(StatedSL d K) => (z : GL (Fin d) K)) hy
    rw [conjSL_apply_val] at h
    have h' : A * (y : GL (Fin d) K) * A⁻¹ * A = (y : GL (Fin d) K) * A := by rw [h]
    refine ⟨?_, y.2⟩
    simpa [mul_assoc] using h'.symm
  · rintro ⟨hc, hx⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    apply Subtype.ext
    rw [conjSL_apply_val]
    show A * x * A⁻¹ = x
    rw [hc.symm]
    group

theorem ker_projMk_le_center {d : ℕ} :
    (LargeEvenProjMk (StatedSL d K)).ker ≤ Subgroup.center ↥(StatedSL d K) := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hx' : LargeEvenProjMk (StatedSL d K) x = LargeEvenProjMk (StatedSL d K) 1 := by
    rw [hx, map_one]
  obtain ⟨c, hc⟩ := (projMk_eq_iff x 1).mp hx'
  have hxinv : ((x : GL (Fin d) K))⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin d) c := by
    simpa using hc.symm
  have hxG : (x : GL (Fin d) K) = Matrix.GeneralLinearGroup.scalar (Fin d) c⁻¹ := by
    rw [map_inv, ← hxinv, inv_inv]
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [hxG]
  apply Units.ext
  simp only [Units.val_mul, val_scalar_gl, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]

theorem pComponent_psl_fixed (hSL : SLComponentsTrivial) (hP1 : LinPCompIsComp) (h2 : (2 : K) = 0)
    {d : ℕ} (hd : 1 ≤ d) (A : GL (Fin d) K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (u : MulAut (LargeEvenProj (StatedSL d K)))
    (hu : ∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h')
    (hpow : u ^ p = 1)
    (J : Subgroup (LargeEvenProj (StatedSL d K)))
    (hJ : GLAPComponent p (fixSubgroup u) J) :
    ∃ (a : ℕ) (E : Type) (_ : Field E) (_ : Algebra K E) (_ : Finite E), 2 ≤ a ∧
      Nonempty (J ⧸ Subgroup.center J ≃* StatedProj (StatedSL a E)) := by
  obtain ⟨c, hc⟩ := isScalar_of_pow_trivial h2 A p u hu hpow
  have hodd : Odd (orderOf A) := odd_orderOf_of_pow_scalar h2 hd A (hp.odd_of_ne_two hp2) hc
  have hord : ((orderOf A : ℕ) : K) ≠ 0 := cast_orderOf_ne_zero_of_odd h2 A hodd
  obtain ⟨M, hM, hMJ⟩ := exists_glaPComponent_map_fixSubgroup (LargeEvenProjMk (StatedSL d K))
    ker_projMk_le_center (conjSL A) u (fun k => (hu k (conjSL A k) rfl).symm)
    (QuotientGroup.mk_surjective) hp hJ
  have hMinj : Function.Injective (StatedSL d K).subtype := Subtype.val_injective
  have hM' : GLAPComponent p (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ CFSG.Open.StatedSL d K)
      (M.map (StatedSL d K).subtype) := by
    rw [← map_fixSubgroup_conjSL A]
    exact (CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_map_iff hp hMinj).mpr hM
  have hcomp := hP1 K d p hp A hord (M.map (StatedSL d K).subtype) hM'
  obtain ⟨a, E, hEf, hEalg, hEfin, ha, ⟨eM⟩⟩ :=
    held_linear_components_gl hSL A hord (M.map (StatedSL d K).subtype) hcomp
  have hperf : commutator ↥(M.map (StatedSL d K).subtype) = ⊤ := hcomp.2.2.1
  have hmemJ : ∀ x : ↥M, LargeEvenProjMk (StatedSL d K) (x : ↥(StatedSL d K)) ∈ J := fun x => by
    rw [← hMJ]
    exact Subgroup.mem_map_of_mem _ x.2
  let fJ : ↥M →* ↥J := MonoidHom.codRestrict ((LargeEvenProjMk (StatedSL d K)).comp M.subtype) J hmemJ
  have hfJ : Function.Surjective fJ := by
    rintro ⟨y, hy⟩
    rw [← hMJ] at hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨z, hz⟩, rfl⟩
  have hkerJ : fJ.ker ≤ Subgroup.center ↥M := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hπ : LargeEvenProjMk (StatedSL d K) (x : ↥(StatedSL d K)) = 1 := congrArg Subtype.val hx
    have hxc : (x : ↥(StatedSL d K)) ∈ Subgroup.center ↥(StatedSL d K) :=
      ker_projMk_le_center (MonoidHom.mem_ker.mpr hπ)
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact Subgroup.mem_center_iff.mp hxc _
  let e : ↥M ≃* ↥(M.map (StatedSL d K).subtype) := Subgroup.equivMapOfInjective M _ hMinj
  let f' : ↥(M.map (StatedSL d K).subtype) →* ↥J := fJ.comp e.symm.toMonoidHom
  have hsurj' : Function.Surjective f' := hfJ.comp e.symm.surjective
  have hker' : f'.ker ≤ Subgroup.center ↥(M.map (StatedSL d K).subtype) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hw : (e.symm x : ↥M) ∈ fJ.ker := by
      rw [MonoidHom.mem_ker]
      exact hx
    have hwc := hkerJ hw
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    have hx' : x = e (e.symm x) := (e.apply_symm_apply x).symm
    rw [hx', ← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_center_iff.mp hwc z
  obtain ⟨φ⟩ := center_quot_equiv_of_surjective hperf f' hsurj' hker'
  exact ⟨a, E, hEf, hEalg, hEfin, ha, ⟨φ.trans eM⟩⟩

end Core

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

end
