module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Inner

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup

theorem isOuterDiagonalPSL2_of_equiv {Y Y' : Type} [Group Y] [Group Y'] (ψ : Y ≃* Y')
    {φ : Y ≃* Y} {φ' : Y' ≃* Y'} (hcomm : ∀ y, ψ (φ y) = φ' (ψ y))
    (h : GSThmB.IsOuterDiagonalPSL2 φ') : GSThmB.IsOuterDiagonalPSL2 φ := by
  obtain ⟨⟨F, hF, hFin, e, A, hA⟩, hni⟩ := h
  refine ⟨⟨F, hF, hFin, ψ.trans e, A, fun M N hMN => ?_⟩, fun ⟨g, hg⟩ => hni ⟨ψ g, fun y => ?_⟩⟩
  · rw [MulEquiv.trans_apply, MulEquiv.symm_trans_apply, hcomm, ψ.apply_symm_apply]
    exact hA M N hMN
  · obtain ⟨y₀, rfl⟩ := ψ.surjective y
    rw [← hcomm, hg, map_mul, map_mul, map_inv]

variable {K : Type} [Field K]

theorem gaussEmb_transpose_mul_self (z : Gauss K) :
    (gaussEmb z)ᵀ * gaussEmb z = QuadraticAlgebra.norm z • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [← gaussEmb_star, ← map_mul, mul_comm, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star,
    gaussEmb_algebraMap]

theorem kron_gaussEmb_symplectic {g : Matrix (Fin 2) (Fin 2) K} {z : Gauss K}
    (h : g.det * QuadraticAlgebra.norm z = 1) :
    (kron g (gaussEmb z))ᵀ * formJ 2 K * kron g (gaussEmb z) = formJ 2 K := by
  rw [kron_symplectic_iff, gaussEmb_transpose_mul_self, smul_smul, h, one_smul]

@[expose] def kronSp (g : Matrix (Fin 2) (Fin 2) K) (z : Gauss K)
    (h : g.det * QuadraticAlgebra.norm z = 1) : StatedSp 2 K :=
  toSp (kron g (gaussEmb z)) (kron_gaussEmb_symplectic h)

theorem coe_kronSp {g : Matrix (Fin 2) (Fin 2) K} {z : Gauss K}
    (h : g.det * QuadraticAlgebra.norm z = 1) :
    (((kronSp g z h : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = kron g (gaussEmb z) := rfl

theorem gaussEmb_omega : gaussEmb (QuadraticAlgebra.omega : Gauss K) = J₁ := by
  rw [gaussEmb_apply, QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, zero_smul, one_smul,
    zero_add]

theorem kronSp_mem_centralizer {g : Matrix (Fin 2) (Fin 2) K} {z : Gauss K}
    (h : g.det * QuadraticAlgebra.norm z = 1) : kronSp g z h ∈ centralizer {T2 K} := by
  rw [mem_centralizer_T2_iff, coe_kronSp, kron_mul, kron_mul, Matrix.mul_one, Matrix.one_mul,
    ← gaussEmb_omega, ← map_mul, ← map_mul, mul_comm]

theorem kronSp_pow {g : Matrix (Fin 2) (Fin 2) K} {z : Gauss K}
    (h : g.det * QuadraticAlgebra.norm z = 1) (m : ℕ) :
    kronSp g z h ^ m =
      kronSp (g ^ m) (z ^ m) (by rw [det_pow, map_pow, ← mul_pow, h, one_pow]) := by
  apply sp_ext
  induction m with
  | zero => simp [coe_kronSp, kron_one_one]
  | succ m ih =>
    rw [pow_succ, Subgroup.coe_mul, Units.val_mul, ih, coe_kronSp, coe_kronSp, coe_kronSp,
      kron_mul, ← map_mul, ← pow_succ, ← pow_succ]

theorem proj_kronSp_mem {g : Matrix (Fin 2) (Fin 2) K} {z : Gauss K}
    (h : g.det * QuadraticAlgebra.norm z = 1) :
    proj 2 K (kronSp g z h) ∈ centralizer {u2 K} :=
  map_centralizer_le (T2 K) ⟨_, kronSp_mem_centralizer h, rfl⟩

theorem commutator_Lsub [Finite K] (h4 : 4 ≤ Nat.card K) : ⁅Lsub K, Lsub K⁆ = Lsub K := by
  have hperf := CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := 2) le_rfl
    (Or.inr (exists_finset_card_four h4))
  have htop : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)), ⊤⁆ = ⊤ :=
    Group.isPerfect_def.mp hperf
  have h1 : (diagSL K).range = ⁅(diagSL K).range, (diagSL K).range⁆ := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, htop]
  rw [Lsub, ← Subgroup.map_commutator, ← h1]

theorem conj_mem_Lsub [Finite K] (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K)
    {x : StatedProj (StatedSp 2 K)} (hx : x ∈ centralizer {u2 K}) {l : StatedProj (StatedSp 2 K)}
    (hl : l ∈ Lsub K) : x * l * x⁻¹ ∈ Lsub K := by
  have h2 := two_ne_zero_of_odd_card hodd
  set N := (Lsub K).map (MulAut.conj x).toMonoidHom
  have hN : N ≤ centralizer {u2 K} := by
    rintro _ ⟨l', hl', rfl⟩
    exact mul_mem (mul_mem hx (Lsub_le_centralizer hl')) (inv_mem hx)
  have hNp : ⁅N, N⁆ = N := by
    rw [show N = (Lsub K).map (MulAut.conj x).toMonoidHom from rfl, ← Subgroup.map_commutator,
      commutator_Lsub (by omega)]
  exact perfect_le_L h2 hN hNp ⟨l, hl, rfl⟩

theorem mem_normalizer_Lsub [Finite K] (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K)
    {x : StatedProj (StatedSp 2 K)} (hx : x ∈ centralizer {u2 K}) :
    x ∈ normalizer (Lsub K : Set (StatedProj (StatedSp 2 K))) := by
  rw [mem_normalizer_iff]
  intro l
  constructor
  · exact conj_mem_Lsub hodd h5 hx
  · intro h
    have := conj_mem_Lsub hodd h5 (inv_mem hx) h
    simpa [mul_assoc] using this

theorem neg_kron (X Y : Matrix (Fin 2) (Fin 2) K) : -kron X Y = kron (-X) Y := by
  simp only [kron, fromBlocks_neg, Matrix.neg_apply, neg_smul]

@[expose] def conjSL (g : GL (Fin 2) K) (k : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨(g : Matrix (Fin 2) (Fin 2) K) * k * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), by
    rw [det_mul, det_mul, k.2, mul_one, ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      det_one]⟩

theorem coe_conjSL (g : GL (Fin 2) K) (k : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((conjSL g k : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (g : Matrix (Fin 2) (Fin 2) K) * k * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem kronSp_mul_diagSL (g : GL (Fin 2) K) {z : Gauss K}
    (h : (g : Matrix (Fin 2) (Fin 2) K).det * QuadraticAlgebra.norm z = 1)
    (k : Matrix.SpecialLinearGroup (Fin 2) K) :
    kronSp g z h * diagSL K k = diagSL K (conjSL g k) * kronSp g z h := by
  apply sp_ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_kronSp, coe_diagSL,
    coe_diagSL, coe_conjSL, kron_mul, kron_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
    Units.inv_mul, Matrix.mul_one]

theorem conj_proj_diagSL (g : GL (Fin 2) K) {z : Gauss K}
    (h : (g : Matrix (Fin 2) (Fin 2) K).det * QuadraticAlgebra.norm z = 1)
    (k : Matrix.SpecialLinearGroup (Fin 2) K) :
    proj 2 K (kronSp g z h) * proj 2 K (diagSL K k) * (proj 2 K (kronSp g z h))⁻¹ =
      proj 2 K (diagSL K (conjSL g k)) := by
  rw [← map_mul, kronSp_mul_diagSL, map_mul, mul_inv_cancel_right]

variable (K) in
@[expose] def LtoStated : Lsub K ≃* StatedProj (StatedSL 2 K) :=
  (LEquiv K).symm.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K)

theorem LtoStated_symm_mk (M : StatedSL 2 K) :
    (((LtoStated K).symm (QuotientGroup.mk M) : Lsub K) : StatedProj (StatedSp 2 K)) =
      proj 2 K (diagSL K ((specialLinearGroupEquivStatedSL 2 K).symm M)) := by
  have h1 : (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm (QuotientGroup.mk M) =
      QuotientGroup.mk ((specialLinearGroupEquivStatedSL 2 K).symm M) := by
    apply (projectiveSpecialLinearGroupEquivStatedProj 2 K).injective
    rw [MulEquiv.apply_symm_apply]
    change QuotientGroup.mk M = QuotientGroup.mk (specialLinearGroupEquivStatedSL 2 K _)
    rw [MulEquiv.apply_symm_apply]
  rw [LtoStated, MulEquiv.symm_trans_apply, MulEquiv.symm_symm, h1, LEquiv_mk]

theorem LtoStated_mk (k : Matrix.SpecialLinearGroup (Fin 2) K)
    (hk : proj 2 K (diagSL K k) ∈ Lsub K) :
    LtoStated K ⟨proj 2 K (diagSL K k), hk⟩ =
      QuotientGroup.mk (specialLinearGroupEquivStatedSL 2 K k) := by
  have : (⟨proj 2 K (diagSL K k), hk⟩ : Lsub K) = LEquiv K (QuotientGroup.mk k) :=
    Subtype.ext (LEquiv_mk k).symm
  rw [this, LtoStated, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

theorem trace_transvection_two {i j : Fin 2} (hij : i ≠ j) (c : K) :
    (transvection i j c).trace = 2 := by
  fin_cases i <;> fin_cases j <;> simp_all [transvection, Matrix.trace, Fin.sum_univ_two] <;>
    norm_num

theorem commute_of_conj_eq_pm (h2 : (2 : K) ≠ 0) (x : GL (Fin 2) K)
    {t : Matrix (Fin 2) (Fin 2) K} (htr : t.trace = 2)
    (h : (x : Matrix (Fin 2) (Fin 2) K) * t *
        ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = t ∨
      (x : Matrix (Fin 2) (Fin 2) K) * t *
        ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = -t) :
    Commute t (x : Matrix (Fin 2) (Fin 2) K) := by
  have htr' : ((x : Matrix (Fin 2) (Fin 2) K) * t *
      ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).trace = t.trace := by
    rw [trace_mul_cycle, Units.inv_mul, Matrix.one_mul]
  rcases h with h | h
  · have h1 : (x : Matrix (Fin 2) (Fin 2) K) * t = t * x := by
      calc (x : Matrix (Fin 2) (Fin 2) K) * t =
          (x : Matrix (Fin 2) (Fin 2) K) * t *
            (((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * x) := by
            rw [Units.inv_mul, Matrix.mul_one]
        _ = t * x := by rw [← Matrix.mul_assoc, h]
    exact h1.symm
  · exfalso
    rw [h, trace_neg, htr] at htr'
    have h4 : (2 : K) * 2 = 0 := by linear_combination -htr'
    exact h2 (mul_self_eq_zero.mp h4)

theorem isOuterDiagonalPSL2_kronSp [Finite K] (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K)
    (g : GL (Fin 2) K) {z : Gauss K}
    (h : (g : Matrix (Fin 2) (Fin 2) K).det * QuadraticAlgebra.norm z = 1)
    (hg : ¬ IsSquare (g : Matrix (Fin 2) (Fin 2) K).det) :
    GSThmB.IsOuterDiagonalPSL2 ((Lsub K).normalizerMonoidHom
      ⟨proj 2 K (kronSp g z h), mem_normalizer_Lsub hodd h5 (proj_kronSp_mem h)⟩) := by
  have h2 := two_ne_zero_of_odd_card hodd
  have hact : ∀ (k : Matrix.SpecialLinearGroup (Fin 2) K) (hk : proj 2 K (diagSL K k) ∈ Lsub K),
      (((Lsub K).normalizerMonoidHom ⟨proj 2 K (kronSp g z h),
        mem_normalizer_Lsub hodd h5 (proj_kronSp_mem h)⟩ ⟨proj 2 K (diagSL K k), hk⟩ : Lsub K) :
          StatedProj (StatedSp 2 K)) = proj 2 K (diagSL K (conjSL g k)) :=
    fun k _ => conj_proj_diagSL g h k
  refine ⟨⟨K, inferInstance, inferInstance, LtoStated K, g, fun M N hMN => ?_⟩, ?_⟩
  · set k := (specialLinearGroupEquivStatedSL 2 K).symm M with hkdef
    have key : (((Lsub K).normalizerMonoidHom ⟨proj 2 K (kronSp g z h),
        mem_normalizer_Lsub hodd h5 (proj_kronSp_mem h)⟩ ((LtoStated K).symm
          (QuotientGroup.mk M)) : Lsub K) : StatedProj (StatedSp 2 K)) =
        proj 2 K (diagSL K (conjSL g k)) := by
      change proj 2 K (kronSp g z h) * (((LtoStated K).symm (QuotientGroup.mk M) : Lsub K) :
        StatedProj (StatedSp 2 K)) * (proj 2 K (kronSp g z h))⁻¹ = _
      rw [LtoStated_symm_mk]
      exact conj_proj_diagSL g h k
    rw [show (Lsub K).normalizerMonoidHom ⟨proj 2 K (kronSp g z h),
        mem_normalizer_Lsub hodd h5 (proj_kronSp_mem h)⟩ ((LtoStated K).symm
          (QuotientGroup.mk M)) = ⟨proj 2 K (diagSL K (conjSL g k)), ⟨_, ⟨_, rfl⟩, rfl⟩⟩ from
        Subtype.ext key]
    refine (LtoStated_mk (conjSL g k) _).trans ?_
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [specialLinearGroupEquivStatedSL_coe, coe_conjSL, hMN, Units.val_mul, Units.val_mul]
    congr 2
    change (((specialLinearGroupEquivStatedSL 2 K k : GL (Fin 2) K)) :
      Matrix (Fin 2) (Fin 2) K) = _
    rw [hkdef, MulEquiv.apply_symm_apply]
  · rintro ⟨l, hl⟩
    obtain ⟨_, ⟨m₀, rfl⟩, hm₀⟩ := l.2
    apply hg
    set x : GL (Fin 2) K := Matrix.SpecialLinearGroup.toGL m₀ * g with hx
    have hm₀inv : ((m₀ : Matrix (Fin 2) (Fin 2) K) * ((m₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hm₀inv' : (((m₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        (m₀ : Matrix (Fin 2) (Fin 2) K)) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hxm : (x : Matrix (Fin 2) (Fin 2) K) = (m₀ : Matrix (Fin 2) (Fin 2) K) * g := rfl
    have hxinv : ((x⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
          ((m₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      rw [hx, _root_.mul_inv_rev, Units.val_mul, ← map_inv]
      rfl
    have hcomm : ∀ t : TransvectionStruct (Fin 2) K,
        Commute t.toMatrix (x : Matrix (Fin 2) (Fin 2) K) := by
      intro t
      have hdet : t.toMatrix.det = 1 := by
        rw [TransvectionStruct.toMatrix, det_transvection_of_ne _ _ t.hij]
      let kt : Matrix.SpecialLinearGroup (Fin 2) K := ⟨t.toMatrix, hdet⟩
      have hy0 := congrArg Subtype.val (hl ⟨proj 2 K (diagSL K kt), ⟨_, ⟨kt, rfl⟩, rfl⟩⟩)
      have hy : proj 2 K (diagSL K (conjSL g kt)) = proj 2 K (diagSL K (m₀⁻¹ * kt * m₀)) := by
        change proj 2 K (kronSp g z h) * proj 2 K (diagSL K kt) * (proj 2 K (kronSp g z h))⁻¹ =
          (l : StatedProj (StatedSp 2 K))⁻¹ * proj 2 K (diagSL K kt) * l at hy0
        rw [conj_proj_diagSL, ← hm₀] at hy0
        rw [hy0]
        simp only [map_mul, map_inv]
      have hpm : (m₀ : Matrix (Fin 2) (Fin 2) K) * g * t.toMatrix *
            (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
              ((m₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) =
            t.toMatrix ∨
          (m₀ : Matrix (Fin 2) (Fin 2) K) * g * t.toMatrix *
            (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
              ((m₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) =
            -t.toMatrix := by
        rcases eq_or_eq_neg_of_proj_eq hy with h3 | h3
        · rw [coe_diagSL, coe_diagSL] at h3
          have h4 := kron_one_injective h3
          rw [coe_conjSL, Matrix.SpecialLinearGroup.coe_mul,
            Matrix.SpecialLinearGroup.coe_mul] at h4
          left
          calc (m₀ : Matrix (Fin 2) (Fin 2) K) * g * t.toMatrix *
              (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
                ((m₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) =
              (m₀ : Matrix (Fin 2) (Fin 2) K) * ((g : Matrix (Fin 2) (Fin 2) K) * kt *
                ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
                ((m₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
                simp only [Matrix.mul_assoc]
                rfl
            _ = t.toMatrix := by
                rw [← h4]
                simp only [← Matrix.mul_assoc, hm₀inv, Matrix.one_mul]
                rw [Matrix.mul_assoc, hm₀inv, Matrix.mul_one]
        · rw [coe_diagSL, coe_diagSL, neg_kron] at h3
          have h4 := kron_one_injective h3
          rw [coe_conjSL, Matrix.SpecialLinearGroup.coe_mul,
            Matrix.SpecialLinearGroup.coe_mul] at h4
          right
          calc (m₀ : Matrix (Fin 2) (Fin 2) K) * g * t.toMatrix *
              (((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
                ((m₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) =
              -((m₀ : Matrix (Fin 2) (Fin 2) K) * (-((g : Matrix (Fin 2) (Fin 2) K) * kt *
                ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))) *
                ((m₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
                simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
                rfl
            _ = -t.toMatrix := by
                rw [← h4]
                simp only [← Matrix.mul_assoc, hm₀inv, Matrix.one_mul]
                rw [Matrix.mul_assoc, hm₀inv, Matrix.mul_one]
      refine commute_of_conj_eq_pm h2 x ?_ ?_
      · rw [TransvectionStruct.toMatrix]
        exact trace_transvection_two t.hij t.c
      · rw [hxm, hxinv]
        exact hpm
    obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct hcomm
    have hdx : (x : Matrix (Fin 2) (Fin 2) K).det = c * c := by
      rw [← hc, det_fin_two]
      simp [Matrix.scalar_apply]
    rw [hxm, det_mul, m₀.2, one_mul] at hdx
    exact ⟨c, hdx⟩

theorem exists_conj_mem_sylow {X : Type*} [Group X] [Finite X] {s : X}
    (hs : IsPGroup 2 (zpowers s)) (T : Sylow 2 X) : ∃ x : X, x * s * x⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀, hT₀⟩ := hs.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X T₀ T
  refine ⟨x, ?_⟩
  rw [← hx]
  exact Subgroup.smul_mem_pointwise_smul s (MulAut.conj x) (T₀ : Subgroup X)
    (hT₀ (mem_zpowers s))

theorem not_isSquare_pow {ν : K} (hν : ¬ IsSquare ν) {m : ℕ} (hm : Odd m) :
    ¬ IsSquare (ν ^ m) := by
  rintro ⟨c, hc⟩
  obtain ⟨k, rfl⟩ := hm
  have hν0 : ν ≠ 0 := by
    rintro rfl
    exact hν ⟨0, by ring⟩
  apply hν
  refine ⟨c / ν ^ k, ?_⟩
  field_simp
  calc ν * (ν ^ k) ^ 2 = ν ^ (2 * k + 1) := by ring
    _ = c * c := hc
    _ = c ^ 2 := by ring

theorem exists_outer_two_element [Finite K] (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K) :
    ∃ s ∈ centralizer {u2 K}, IsPGroup 2 (zpowers s) ∧
      ∃ hs : s ∈ normalizer (Lsub K : Set (StatedProj (StatedSp 2 K))),
        GSThmB.IsOuterDiagonalPSL2 ((Lsub K).normalizerMonoidHom ⟨s, hs⟩) := by
  have h2 := two_ne_zero_of_odd_card hodd
  have hc2 : ringChar K ≠ 2 := by
    intro hc
    apply h2
    have := (ringChar.spec K 2).mpr (by rw [hc])
    exact_mod_cast this
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hc2
  have hν0 : ν ≠ 0 := by
    rintro rfl
    exact hν ⟨0, by ring⟩
  obtain ⟨a, b, hab⟩ := exists_sq_add_sq_eq h2 ν⁻¹
  set z₀ : Gauss K := ⟨a, b⟩
  have hz₀ : QuadraticAlgebra.norm z₀ = ν⁻¹ := by
    rw [QuadraticAlgebra.norm_def, ← hab]
    simp only [z₀]
    ring
  set g₀ : GL (Fin 2) K := nonsingInvUnit (diagonal ![ν, 1]) (by
    rw [det_diagonal, Fin.prod_univ_two]
    simpa using hν0)
  have hdet : (g₀ : Matrix (Fin 2) (Fin 2) K).det = ν := by
    change (diagonal ![ν, 1]).det = ν
    rw [det_diagonal, Fin.prod_univ_two]
    simp
  have h : (g₀ : Matrix (Fin 2) (Fin 2) K).det * QuadraticAlgebra.norm z₀ = 1 := by
    rw [hdet, hz₀, mul_inv_cancel₀ hν0]
  set s' := proj 2 K (kronSp g₀ z₀ h)
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos s').ne'
  have hm' : (g₀ ^ m : GL (Fin 2) K).val.det * QuadraticAlgebra.norm (z₀ ^ m) = 1 := by
    rw [Units.val_pow_eq_pow_val, det_pow, map_pow, ← mul_pow, h, one_pow]
  have hs : s' ^ m = proj 2 K (kronSp (g₀ ^ m : GL (Fin 2) K) (z₀ ^ m) hm') := by
    rw [← map_pow, kronSp_pow]
    congr 1
  refine ⟨s' ^ m, pow_mem (proj_kronSp_mem h) m, ?_, ?_⟩
  · have hm0 : m ≠ 0 := by
      rintro rfl
      exact Nat.not_even_iff_odd.mpr hm (by decide)
    apply IsPGroup.of_card (n := k)
    rw [Nat.card_zpowers, orderOf_pow_of_dvd hm0 (Dvd.intro_left _ hkm.symm), hkm,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  · rw [hs]
    refine ⟨mem_normalizer_Lsub hodd h5 (proj_kronSp_mem hm'), ?_⟩
    apply isOuterDiagonalPSL2_kronSp hodd h5
    rw [Units.val_pow_eq_pow_val, det_pow, hdet]
    exact not_isSquare_pow hν hm

theorem isOuterDiagonalPSL2_conj {Y : Type} [Group Y] {M : Subgroup Y} {s x : Y}
    (hs : s ∈ normalizer (M : Set Y)) (hx : x ∈ normalizer (M : Set Y))
    (h : GSThmB.IsOuterDiagonalPSL2 (M.normalizerMonoidHom ⟨s, hs⟩)) :
    GSThmB.IsOuterDiagonalPSL2 (M.normalizerMonoidHom
      ⟨x * s * x⁻¹, mul_mem (mul_mem hx hs) (inv_mem hx)⟩) := by
  refine isOuterDiagonalPSL2_of_equiv (M.normalizerMonoidHom ⟨x, hx⟩).symm (fun y => ?_) h
  apply Subtype.ext
  simp only [normalizerMonoidHom_apply_symm_apply_coe, normalizerMonoidHom_apply_apply_coe]
  group

theorem isOuterDiagonalPSL2_map {Y Y' : Type} [Group Y] [Group Y'] (ψ : Y ≃* Y')
    {M : Subgroup Y} {N : Subgroup Y'} (hMN : M.map ψ.toMonoidHom = N) {s : Y}
    (hs : s ∈ normalizer (M : Set Y)) (hs' : ψ s ∈ normalizer (N : Set Y'))
    (h : GSThmB.IsOuterDiagonalPSL2 (N.normalizerMonoidHom ⟨ψ s, hs'⟩)) :
    GSThmB.IsOuterDiagonalPSL2 (M.normalizerMonoidHom ⟨s, hs⟩) := by
  subst hMN
  refine isOuterDiagonalPSL2_of_equiv (ψ.subgroupMap M) (fun y => ?_) h
  apply Subtype.ext
  simp only [MulEquiv.coe_subgroupMap_apply, normalizerMonoidHom_apply_apply_coe]
  change ψ (s * y * s⁻¹) = ψ s * ψ y * (ψ s)⁻¹
  rw [map_mul, map_mul, map_inv]

theorem mem_normalizer_of_map {Y Y' : Type} [Group Y] [Group Y'] (ψ : Y ≃* Y')
    {M : Subgroup Y} {N : Subgroup Y'} (hMN : M.map ψ.toMonoidHom = N) {s : Y}
    (hs : ψ s ∈ normalizer (N : Set Y')) : s ∈ normalizer (M : Set Y) := by
  subst hMN
  rw [mem_normalizer_iff]
  intro y
  have := (mem_normalizer_iff.mp hs) (ψ y)
  rw [← map_mul, ← map_inv, ← map_mul] at this
  simpa only [mem_map_equiv, MulEquiv.symm_apply_apply] using this

theorem center_ne_bot_of_u1 (h2 : (2 : K) ≠ 0) {M : Subgroup (StatedProj (StatedSp 2 K))}
    (hM : M = E1 K ∨ M = E2 K) : center M ≠ ⊥ := by
  intro hZ
  have hu : u1 K ∈ M := by
    rcases hM with rfl | rfl
    · exact u1_mem_E1
    · exact u1_mem_E2
  have hc : (⟨u1 K, hu⟩ : M) ∈ center M := by
    rw [mem_center_iff]
    rintro ⟨y, hy⟩
    apply Subtype.ext
    change y * u1 K = u1 K * y
    rcases hM with rfl | rfl
    · exact (commute_E1_E2 hy u1_mem_E2)
    · exact (commute_E1_E2 u1_mem_E1 hy).symm
  rw [hZ, mem_bot] at hc
  exact u1_ne_one h2 (congrArg Subtype.val hc)

theorem center_ne_bot_of_map {Y Y' : Type} [Group Y] [Group Y'] (ψ : Y ≃* Y')
    {M : Subgroup Y} (h : center (M.map ψ.toMonoidHom) ≠ ⊥) : center M ≠ ⊥ := by
  intro hZ
  apply h
  rw [eq_bot_iff]
  rintro ⟨y, hy⟩ hyc
  obtain ⟨m, hm, rfl⟩ := hy
  have hmc : (⟨m, hm⟩ : M) ∈ center M := by
    rw [mem_center_iff] at hyc ⊢
    rintro ⟨z, hz⟩
    have := congrArg Subtype.val (hyc ⟨ψ z, mem_map_of_mem _ hz⟩)
    change ψ z * ψ m = ψ m * ψ z at this
    apply Subtype.ext
    change z * m = m * z
    apply ψ.injective
    rw [map_mul, map_mul]
    exact this
  rw [hZ, mem_bot] at hmc
  rw [mem_bot]
  apply Subtype.ext
  change ψ m = 1
  rw [show m = 1 from congrArg Subtype.val hmc, map_one]

theorem cfSp4Outer : GSThmB.CFSp4Outer := by
  intro Y _ _ p f hp hp2 hf hY t ht M hMt hM hZ R hR
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hY
  have hodd := odd_card_of_card_eq hp hp2 hK
  have h2 := two_ne_zero_of_odd_card hodd
  obtain ⟨φ, hφ⟩ := exists_model_conj hodd (u := e t) (by rw [MulEquiv.orderOf_eq, ht])
  set ψ : Y ≃* StatedProj (StatedSp 2 K) := e.trans φ with hψ
  have hψt : ψ t = u1 K ∨ ψ t = u2 K := hφ
  have hM' := isPComponent_map_subgroupOf 2 ψ hMt hM
  have hMX' := Subgroup.map_mono (f := ψ.toMonoidHom) hMt
  rw [map_centralizer_singleton] at hM' hMX'
  rcases hψt with h | h <;> rw [h] at hM' hMX'
  · exact absurd hZ (center_ne_bot_of_map ψ (center_ne_bot_of_u1 h2
      (pComponent_centralizer_u1 hodd hMX' hM').1))
  obtain ⟨hL, h5⟩ := pComponent_centralizer_u2 hodd hMX' hM'
  obtain ⟨s₀, hs₀C, hs₀2, hs₀N, hs₀⟩ := exists_outer_two_element hodd h5
  set s₁ := ψ.symm s₀ with hs₁def
  have hψs₁ : ψ s₁ = s₀ := ψ.apply_symm_apply s₀
  have hs₁C : s₁ ∈ centralizer {t} := by
    rw [mem_centralizer_singleton_iff]
    apply ψ.injective
    rw [map_mul, map_mul, hψs₁, h]
    exact mem_centralizer_singleton_iff.mp hs₀C
  have hNC : ∀ x ∈ centralizer {t}, x ∈ normalizer (M : Set Y) := by
    intro x hx
    apply mem_normalizer_of_map ψ hL
    apply mem_normalizer_Lsub hodd h5
    rw [← h, mem_centralizer_singleton_iff]
    rw [mem_centralizer_singleton_iff] at hx
    rw [← map_mul, ← map_mul, hx]
  have hs₁N := hNC s₁ hs₁C
  have hs₁ : GSThmB.IsOuterDiagonalPSL2 (M.normalizerMonoidHom ⟨s₁, hs₁N⟩) :=
    isOuterDiagonalPSL2_map ψ hL hs₁N (hψs₁ ▸ hs₀N) (by convert hs₀ using 3)
  obtain ⟨hRC, T, hT⟩ := hR
  have h2g : IsPGroup 2 (zpowers (⟨s₁, hs₁C⟩ : centralizer {t})) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hs₀2
    apply IsPGroup.of_card (n := k)
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hs₁def, MulEquiv.orderOf_eq, ← Nat.card_zpowers, hk]
  obtain ⟨⟨x, hxC⟩, hx⟩ := exists_conj_mem_sylow h2g T
  have hx' : _ ∈ (T : Subgroup (centralizer {t})) := hx
  rw [hT, mem_subgroupOf] at hx'
  exact ⟨x * s₁ * x⁻¹, hx', _, isOuterDiagonalPSL2_conj hs₁N (hNC x hxC) hs₁⟩

end CFSG.ComponentClassification.CatFactsSp4
