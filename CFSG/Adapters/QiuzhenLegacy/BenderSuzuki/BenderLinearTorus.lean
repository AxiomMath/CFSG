module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
public import Mathlib.LinearAlgebra.Projectivization.Action

public section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Matrix LinearAlgebra.Projectivization

noncomputable section

theorem pgl_standard_pair_torus
    {K : Type*} [Field K] [Finite K]
    [MulAction (Matrix.ProjGenLinGroup (Fin 2) K) (ℙ K (Fin 2 → K))]
    (hrho : ∀ (g : Matrix.ProjGenLinGroup (Fin 2) K)
      (z : ℙ K (Fin 2 → K)) (A : GL (Fin 2) K),
      Matrix.ProjGenLinGroup.mk A = g →
        g • z = (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z) :
    ∃ (a b : ℙ K (Fin 2 → K))
      (w : Matrix.ProjGenLinGroup (Fin 2) K)
      (T : Subgroup (Matrix.ProjGenLinGroup (Fin 2) K)),
      a ≠ b ∧ w • a = b ∧ w • b = a ∧
      (T : Set (Matrix.ProjGenLinGroup (Fin 2) K)) =
        {g | g • a = a ∧ g • b = b} ∧
      IsCyclic T ∧ Nat.card T = Nat.card K - 1 ∧
      ∀ g ∈ T, rightConjugateElem g w = g⁻¹ := by
  classical
  let G := Matrix.ProjGenLinGroup (Fin 2) K
  let Omega := ℙ K (Fin 2 → K)
  let e0 : Fin 2 → K := ![1, 0]
  let e1 : Fin 2 → K := ![0, 1]
  let e01 : Fin 2 → K := ![1, 1]
  have he0 : e0 ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [e0] at this
  have he1 : e1 ≠ 0 := by
    intro h
    have := congrFun h 1
    simp [e1] at this
  have he01 : e01 ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [e01] at this
  let alpha0 : Omega := Projectivization.mk K e0 he0
  let beta0 : Omega := Projectivization.mk K e1 he1
  let gamma0 : Omega := Projectivization.mk K e01 he01
  have halpha0beta0 : alpha0 ≠ beta0 := by
    intro h
    rw [show alpha0 = Projectivization.mk K e0 he0 by rfl,
      show beta0 = Projectivization.mk K e1 he1 by rfl,
      Projectivization.mk_eq_mk_iff] at h
    rcases h with ⟨c, hc⟩
    have h0 := congrFun hc 0
    simp [e0, e1] at h0
  let diagGL (k : Kˣ) : GL (Fin 2) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero
      (Matrix.diagonal ![(k : K), 1]) (by
        simp [Matrix.det_diagonal, Fin.prod_univ_two, k.ne_zero])
  let diagHom : Kˣ →* GL (Fin 2) K :=
    { toFun := diagGL
      map_one' := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [diagGL]
      map_mul' := by
        intro k l
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [diagGL, Matrix.mul_apply, Fin.sum_univ_two] }
  let torus : Kˣ →* G :=
    Matrix.ProjGenLinGroup.mk.comp diagHom
  let wGL : GL (Fin 2) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by
      simp [Matrix.det_fin_two])
  let w : G := Matrix.ProjGenLinGroup.mk wGL
  have hwalpha : w • alpha0 = beta0 := by
    rw [hrho w alpha0 wGL rfl]
    rw [show alpha0 = Projectivization.mk K e0 he0 by rfl,
      Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
    refine ⟨1, ?_⟩
    funext i
    fin_cases i <;>
      simp [wGL, e0, e1, Matrix.mulVec]
  have hwbeta : w • beta0 = alpha0 := by
    rw [hrho w beta0 wGL rfl]
    rw [show beta0 = Projectivization.mk K e1 he1 by rfl,
      Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
    refine ⟨1, ?_⟩
    funext i
    fin_cases i <;>
      simp [wGL, e0, e1, Matrix.mulVec]
  have htorus_alpha (k : Kˣ) : torus k • alpha0 = alpha0 := by
    rw [hrho (torus k) alpha0 (diagHom k) rfl]
    rw [show alpha0 = Projectivization.mk K e0 he0 by rfl,
      Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
    refine ⟨(k : K), ?_⟩
    funext i
    fin_cases i <;>
      simp [diagHom, diagGL, e0, Matrix.mulVec]
  have htorus_beta (k : Kˣ) : torus k • beta0 = beta0 := by
    rw [hrho (torus k) beta0 (diagHom k) rfl]
    rw [show beta0 = Projectivization.mk K e1 he1 by rfl,
      Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
    refine ⟨1, ?_⟩
    funext i
    fin_cases i <;>
      simp [diagHom, diagGL, e1, Matrix.mulVec]
  let H0 : Subgroup G :=
    MulAction.stabilizer G alpha0 ⊓ MulAction.stabilizer G beta0
  have hH0set : (H0 : Set G) =
      {x : G | x • alpha0 = alpha0 ∧ x • beta0 = beta0} := by
    ext x
    constructor
    · intro hx
      exact ⟨MulAction.mem_stabilizer_iff.mp hx.1,
        MulAction.mem_stabilizer_iff.mp hx.2⟩
    · intro hx
      exact ⟨MulAction.mem_stabilizer_iff.mpr hx.1,
        MulAction.mem_stabilizer_iff.mpr hx.2⟩
  have htorus_range_le : torus.range ≤ H0 := by
    rintro _ ⟨k, rfl⟩
    exact ⟨MulAction.mem_stabilizer_iff.mpr (htorus_alpha k),
      MulAction.mem_stabilizer_iff.mpr (htorus_beta k)⟩
  have hH0_le_range : H0 ≤ torus.range := by
    intro g hg
    obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    have hfixalpha :
        (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • alpha0 =
          alpha0 := by
      rw [← hrho g alpha0 A hA]
      exact MulAction.mem_stabilizer_iff.mp hg.1
    have hfixbeta :
        (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • beta0 =
          beta0 := by
      rw [← hrho g beta0 A hA]
      exact MulAction.mem_stabilizer_iff.mp hg.2
    rw [show alpha0 = Projectivization.mk K e0 he0 by rfl,
      Projectivization.smul_mk,
      Projectivization.mk_eq_mk_iff] at hfixalpha
    rw [show beta0 = Projectivization.mk K e1 he1 by rfl,
      Projectivization.smul_mk,
      Projectivization.mk_eq_mk_iff] at hfixbeta
    rcases hfixalpha with ⟨c, hc⟩
    rcases hfixbeta with ⟨d, hd⟩
    change (c : K) • e0 = Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) K) e0 at hc
    change (d : K) • e1 = Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) K) e1 at hd
    have hc0 := congrFun hc 0
    have hc1 := congrFun hc 1
    have hd0 := congrFun hd 0
    have hd1 := congrFun hd 1
    simp [e0, e1, Matrix.mulVec] at hc0 hc1 hd0 hd1
    change (c : K) = (A : Matrix (Fin 2) (Fin 2) K) 0 0 at hc0
    change (0 : K) = (A : Matrix (Fin 2) (Fin 2) K) 1 0 at hc1
    change (0 : K) = (A : Matrix (Fin 2) (Fin 2) K) 0 1 at hd0
    change (d : K) = (A : Matrix (Fin 2) (Fin 2) K) 1 1 at hd1
    have hA00 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = (c : K) := by
      exact hc0.symm
    have hA10 : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
      exact hc1.symm
    have hA01 : (A : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
      exact hd0.symm
    have hA11 : (A : Matrix (Fin 2) (Fin 2) K) 1 1 = (d : K) := by
      exact hd1.symm
    let k : Kˣ := c * d⁻¹
    have hAdiag : A = Matrix.GeneralLinearGroup.scalar (Fin 2) d * diagHom k := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.GeneralLinearGroup.scalar, diagHom, diagGL, k,
          Matrix.mul_apply, Fin.sum_univ_two, hA00, hA01, hA10, hA11,
          mul_left_comm]
    refine ⟨k, ?_⟩
    calc
      torus k = Matrix.ProjGenLinGroup.mk (diagHom k) := rfl
      _ = Matrix.ProjGenLinGroup.mk
          (Matrix.GeneralLinearGroup.scalar (Fin 2) d * diagHom k) := by
            calc
              Matrix.ProjGenLinGroup.mk (diagHom k) =
                  Matrix.ProjGenLinGroup.mk
                    (Matrix.GeneralLinearGroup.scalar (Fin 2) d) *
                      Matrix.ProjGenLinGroup.mk (diagHom k) := by
                        rw [Matrix.ProjGenLinGroup.mk_scalar, one_mul]
              _ = Matrix.ProjGenLinGroup.mk
                    (Matrix.GeneralLinearGroup.scalar (Fin 2) d * diagHom k) := by
                      exact (map_mul Matrix.ProjGenLinGroup.mk
                        (Matrix.GeneralLinearGroup.scalar (Fin 2) d)
                        (diagHom k)).symm
      _ = Matrix.ProjGenLinGroup.mk A := congrArg _ hAdiag.symm
      _ = g := hA
  have hH0eq : H0 = torus.range := le_antisymm hH0_le_range htorus_range_le
  have htorus_gamma (k : Kˣ) :
      torus k • gamma0 =
        Projectivization.mk K ![(k : K), 1] (by simp [k.ne_zero]) := by
    rw [hrho (torus k) gamma0 (diagHom k) rfl]
    rw [show gamma0 = Projectivization.mk K e01 he01 by rfl,
      Projectivization.smul_mk]
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
    refine ⟨1, ?_⟩
    funext i
    fin_cases i <;>
      simp [diagHom, diagGL, e01, Matrix.mulVec]
  have htorus_injective : Function.Injective torus := by
    intro k l hkl
    have hact := congrArg (fun g : G => g • gamma0) hkl
    change torus k • gamma0 = torus l • gamma0 at hact
    rw [htorus_gamma k, htorus_gamma l,
      Projectivization.mk_eq_mk_iff] at hact
    rcases hact with ⟨c, hc⟩
    have hc0 := congrFun hc 0
    have hc1 := congrFun hc 1
    simp at hc0 hc1
    apply Units.ext
    have hc_one : (c : K) = 1 := by
      simpa [Units.smul_def] using hc1
    calc
      (k : K) = (c : K) * (l : K) := hc0.symm
      _ = (l : K) := by rw [hc_one, one_mul]
  have hrangeRestrict_injective :
      Function.Injective torus.rangeRestrict := by
    intro a b hab
    apply htorus_injective
    exact congrArg Subtype.val hab
  let eRange : Kˣ ≃* torus.range :=
    MulEquiv.ofBijective torus.rangeRestrict
      ⟨hrangeRestrict_injective, MonoidHom.rangeRestrict_surjective torus⟩
  let eH0 : H0 ≃* torus.range := MulEquiv.subgroupCongr hH0eq
  have hRangeCyclic : IsCyclic torus.range :=
    eRange.isCyclic.mp (inferInstance : IsCyclic Kˣ)
  have hH0cyclic : IsCyclic H0 := eH0.isCyclic.mpr hRangeCyclic
  have hwGL_sq : wGL * wGL = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [wGL, Matrix.mul_apply, Fin.sum_univ_two]
  have hw_sq : w * w = 1 := by
    change Matrix.ProjGenLinGroup.mk wGL *
        Matrix.ProjGenLinGroup.mk wGL = 1
    rw [← map_mul, hwGL_sq, map_one]
  have hw_inv : w⁻¹ = w := (eq_inv_of_mul_eq_one_right hw_sq).symm
  have hweyl_torus (k : Kˣ) :
      rightConjugateElem (torus k) w = (torus k)⁻¹ := by
    rw [rightConjugateElem, hw_inv]
    have hGL : wGL * diagHom k * wGL =
        Matrix.GeneralLinearGroup.scalar (Fin 2) k * diagHom k⁻¹ := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [wGL, diagHom, diagGL, Matrix.GeneralLinearGroup.scalar,
          Matrix.mul_apply, Matrix.vecMul, Fin.sum_univ_two]
    change Matrix.ProjGenLinGroup.mk wGL *
        Matrix.ProjGenLinGroup.mk (diagHom k) *
          Matrix.ProjGenLinGroup.mk wGL =
        (Matrix.ProjGenLinGroup.mk (diagHom k))⁻¹
    rw [← map_mul, ← map_mul, hGL, map_mul,
      Matrix.ProjGenLinGroup.mk_scalar, one_mul]
    rw [map_inv diagHom k]
    exact map_inv Matrix.ProjGenLinGroup.mk (diagHom k)
  refine ⟨alpha0, beta0, w, H0, halpha0beta0, hwalpha, hwbeta,
    hH0set, hH0cyclic, ?_, ?_⟩
  · calc
      Nat.card H0 = Nat.card torus.range := Nat.card_congr eH0.toEquiv
      _ = Nat.card Kˣ := Nat.card_congr eRange.toEquiv.symm
      _ = Nat.card K - 1 := Nat.card_units K
  · intro x hx
    rw [hH0eq] at hx
    rcases hx with ⟨k, rfl⟩
    exact hweyl_torus k

theorem pgl_twoPointStabilizer_isCyclic
    {K : Type*} [Field K] [Finite K]
    [MulAction (Matrix.ProjGenLinGroup (Fin 2) K) (ℙ K (Fin 2 → K))]
    (hrho : ∀ (g : Matrix.ProjGenLinGroup (Fin 2) K)
      (z : ℙ K (Fin 2 → K)) (A : GL (Fin 2) K),
      Matrix.ProjGenLinGroup.mk A = g →
        g • z = (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z)
    (htwo : MulAction.IsMultiplyPretransitive
      (Matrix.ProjGenLinGroup (Fin 2) K) (ℙ K (Fin 2 → K)) 2)
    (a b : ℙ K (Fin 2 → K)) (hab : a ≠ b) :
    IsCyclic ↥(MulAction.stabilizer (Matrix.ProjGenLinGroup (Fin 2) K) a ⊓
      MulAction.stabilizer (Matrix.ProjGenLinGroup (Fin 2) K) b) := by
  let G := Matrix.ProjGenLinGroup (Fin 2) K
  obtain ⟨a0, b0, _w, T0, hab0, _hwa, _hwb, hTset, hTcyc, _hTcard, _hinv⟩ :=
    pgl_standard_pair_torus hrho
  have hT0 : T0 = MulAction.stabilizer G a0 ⊓ MulAction.stabilizer G b0 := by
    ext x
    have hx : x ∈ T0 ↔ x • a0 = a0 ∧ x • b0 = b0 :=
      Set.ext_iff.mp hTset x
    constructor
    · intro hxT
      exact ⟨MulAction.mem_stabilizer_iff.mpr (hx.mp hxT).1,
        MulAction.mem_stabilizer_iff.mpr (hx.mp hxT).2⟩
    · intro hxS
      exact hx.mpr ⟨MulAction.mem_stabilizer_iff.mp hxS.1,
        MulAction.mem_stabilizer_iff.mp hxS.2⟩
  obtain ⟨g, hga, hgb⟩ := (MulAction.is_two_pretransitive_iff.mp htwo) hab hab0
  let H := MulAction.stabilizer G a ⊓ MulAction.stabilizer G b
  let c := MulAut.conj g
  have hmap : H.map c.toMonoidHom = T0 := by
    dsimp only [H, c]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
      ← MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      ← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hga, hgb]
    exact hT0.symm
  let e : H ≃* T0 :=
    (H.equivMapOfInjective c.toMonoidHom c.injective).trans
      (MulEquiv.subgroupCongr hmap)
  exact e.isCyclic.mpr hTcyc

end

end CFSG.BenderSuzuki
