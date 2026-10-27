module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Three3
public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldDiag
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.RankThree.PartTwo.Sec4.LThreePiMain
public import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofTypeC
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofD4
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusTorus
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.Adapters.LinearCatalog
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergE6Good
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Duality
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTriality2Classes
public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4Geom
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofEvenDesc
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofFus
public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofTools
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof
public import CFSG.RankThree.PartTwo.Sec16.Item16Tail17
public import CFSG.RankThree.PartTwo.Sec16.Item16Tail19
public import CFSG.RankThree.PartTwo.Sec16.Item16TailMore
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Toolkit.M12Local
public import CFSG.RankThree.S4Free.SuzukiEight
public import Certificates.Certificate8166

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3

section Diagonal

open Matrix Polynomial

variable {K : Type} [Field K]

theorem exists_conj_diagonal_of_cube_scalar {ω : K} (hω : IsPrimitiveRoot ω 3)
    (s : Matrix (Fin 3) (Fin 3) K) (hdet : s.det = 1) {c : K}
    (hc : s ^ 3 = Matrix.scalar (Fin 3) c) :
    ∃ (T : GL (Fin 3) K) (d : Fin 3 → K),
      (T : Matrix (Fin 3) (Fin 3) K) * s * ((T⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        diagonal d ∧ ∀ i, d i ^ 3 = c := by
  classical
  by_cases hcube : ∃ a : K, a ^ 3 = c
  · obtain ⟨a, ha⟩ := hcube
    have ha0 : a ≠ 0 := by
      rintro rfl
      have h1 : (s ^ 3).det = 1 := by rw [Matrix.det_pow, hdet, one_pow]
      rw [hc, ← ha, zero_pow (by norm_num), Matrix.scalar_apply, Matrix.det_diagonal] at h1
      simp at h1
    set B := Matrix.scalar (Fin 3) a⁻¹ * s with hB
    have hBs : B ^ 3 = 1 := by
      have hcomm : Commute (Matrix.scalar (Fin 3) a⁻¹) s :=
        Matrix.scalar_commute a⁻¹ (fun _ => Commute.all _ _) s
      rw [hB, hcomm.mul_pow, hc, ← map_pow, ← map_mul, inv_pow, ha,
        inv_mul_cancel₀ (by rw [← ha]; exact pow_ne_zero 3 ha0), map_one]
    obtain ⟨T, d', hTd, hd'⟩ :=
      CFSG.RankThree.PartTwo.Sec4.HeringOF.exists_conj_diagonal_of_pow_three hω B hBs
    refine ⟨T, fun i => a * d' i, ?_, fun i => by rw [mul_pow, ha, hd', mul_one]⟩
    have hsB : s = Matrix.scalar (Fin 3) a * B := by
      rw [hB, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha0, map_one, one_mul]
    have hcommT : (T : Matrix (Fin 3) (Fin 3) K) * Matrix.scalar (Fin 3) a =
        Matrix.scalar (Fin 3) a * (T : Matrix (Fin 3) (Fin 3) K) :=
      ((Matrix.scalar_commute a (fun _ => Commute.all _ _) _).eq).symm
    calc (T : Matrix (Fin 3) (Fin 3) K) * s * ((T⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        Matrix.scalar (Fin 3) a * ((T : Matrix (Fin 3) (Fin 3) K) * B *
          ((T⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
          rw [hsB, show (T : Matrix (Fin 3) (Fin 3) K) * (Matrix.scalar (Fin 3) a * B) =
            Matrix.scalar (Fin 3) a * ((T : Matrix (Fin 3) (Fin 3) K) * B) by
              rw [← mul_assoc, hcommT, mul_assoc]]
          simp only [Matrix.mul_assoc]
      _ = diagonal fun i => a * d' i := by
        rw [hTd, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
  · exfalso
    push Not at hcube
    have hdeg : (X ^ 3 - C c : K[X]).natDegree = 3 := natDegree_X_pow_sub_C
    have hirr : Irreducible (X ^ 3 - C c : K[X]) := by
      refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) ?_
      intro x hx
      apply hcube x
      have := hx.eq_zero
      simp only [eval_sub, eval_pow, eval_X, eval_C] at this
      exact sub_eq_zero.1 this
    have hmon : (X ^ 3 - C c : K[X]).Monic := monic_X_pow_sub_C c (by norm_num)
    have haeval : aeval s (X ^ 3 - C c : K[X]) = 0 := by
      rw [map_sub, map_pow, aeval_X, aeval_C, hc, sub_eq_zero, Matrix.algebraMap_eq_diagonal]
      rfl
    have hmin := minpoly.eq_of_irreducible_of_monic hirr haeval hmon
    have hdvd : (X ^ 3 - C c : K[X]) ∣ s.charpoly := hmin ▸ Matrix.minpoly_dvd_charpoly s
    have hch : s.charpoly = X ^ 3 - C c := by
      refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon (Matrix.charpoly_monic s) hdvd ?_
      rw [Matrix.charpoly_natDegree_eq_dim, hdeg]
      simp
    have hdet' := Matrix.det_eq_sign_charpoly_coeff s
    rw [hch, hdet] at hdet'
    simp only [coeff_sub, coeff_X_pow, coeff_C_zero, Fintype.card_fin] at hdet'
    have hc1 : c = 1 := by
      norm_num at hdet'
      linear_combination -hdet'
    exact hcube 1 (by rw [one_pow, hc1])

end Diagonal

section Escape

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem det_eq_cube_of_mk_mem (hK : Sec4.PiField π p f K) {w : GL (Fin 3) K}
    (hw : w ∈ Sec4.glPi π 3 (p ^ f) K)
    (hmk : Matrix.ProjGenLinGroup.mk w ∈
      CFSG.PGLModel.projImage (Sec4.slPi π 3 (p ^ f) K)) :
    ∃ c : Kˣ, c ∈ rootsOfUnity (Sec4.qSubPi π (p ^ f)) K ∧
      Matrix.GeneralLinearGroup.det w = c ^ 3 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨s', hs', hmk'⟩ := hmk
  have hsc : s'⁻¹ * w ∈ StatedScalars (Fin 3) K := by
    rw [← Sec4.mk_eq_one_iff_mem_statedScalars, map_mul, map_inv]
    change (Matrix.ProjGenLinGroup.mk s')⁻¹ * Matrix.ProjGenLinGroup.mk w = 1
    rw [hmk', inv_mul_cancel]
  obtain ⟨c, hc⟩ := hsc
  have hcG : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ Sec4.glPi π 3 (p ^ f) K := by
    rw [hc]
    exact mul_mem (inv_mem (Sec4.slPi_le_glPi hπ hs')) hw
  refine ⟨c, (Sec4.scalar_mem_glPi_iff hK c).1 hcG, ?_⟩
  have hdet' : Matrix.GeneralLinearGroup.det s' = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    cases π
    · exact ((Sec4.mem_slPi_false (hπ rfl)).1 hs').1
    · exact (Sec4.mem_slPi_true _).1 hs'
  have hw' : w = s' * Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    rw [hc, mul_inv_cancel_left]
  rw [hw', map_mul, hdet', one_mul]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_three, Units.val_pow_eq_pow_val,
    pow_three, mul_assoc]

theorem unitary_conj_diagonal (h : UnitaryFieldData p f K) {t ti : Matrix (Fin 3) (Fin 3) K}
    (htti : t * ti = 1) (hitt : ti * t = 1) {d u : Fin 3 → K}
    (hs : ((ti * diagonal d * t).map h.bar)ᵀ * (ti * diagonal d * t) = 1)
    (hd : ∀ i, h.bar (d i) * d i = 1) (hu : ∀ i, h.bar (u i) * u i = 1)
    (hud : ∀ i j, d i = d j → u i = u j) :
    ((ti * diagonal u * t).map h.bar)ᵀ * (ti * diagonal u * t) = 1 := by
  set σ := h.bar with hσdef
  have hst_mul : ∀ A B : Matrix (Fin 3) (Fin 3) K,
      ((A * B).map σ)ᵀ = (B.map σ)ᵀ * (A.map σ)ᵀ := fun A B => by
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have hst_one : ((1 : Matrix (Fin 3) (Fin 3) K).map σ)ᵀ = 1 := by
    rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have hst_diag : ∀ e : Fin 3 → K, ((diagonal e).map σ)ᵀ = diagonal fun i => σ (e i) :=
    fun e => by rw [Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose]
  set G : Matrix (Fin 3) (Fin 3) K := (ti.map σ)ᵀ * ti with hG
  have hstti : (ti.map σ)ᵀ * (t.map σ)ᵀ = 1 := by rw [← hst_mul, htti, hst_one]
  have hsttt : (t.map σ)ᵀ * (ti.map σ)ᵀ = 1 := by rw [← hst_mul, hitt, hst_one]
  have hkey : ((diagonal d).map σ)ᵀ * G * diagonal d = G := by
    have h1 := hs
    rw [hst_mul, hst_mul] at h1
    calc ((diagonal d).map σ)ᵀ * G * diagonal d =
          ((ti.map σ)ᵀ * (t.map σ)ᵀ) * ((diagonal d).map σ)ᵀ * G * diagonal d * (t * ti) := by
          rw [hstti, htti, Matrix.one_mul, Matrix.mul_one]
      _ = (ti.map σ)ᵀ * ((t.map σ)ᵀ * (((diagonal d).map σ)ᵀ * (ti.map σ)ᵀ) *
            (ti * diagonal d * t)) * ti := by
          simp only [hG, Matrix.mul_assoc]
      _ = G := by rw [h1, Matrix.mul_one]
  have hGd : ∀ i j, G i j ≠ 0 → d j = d i := by
    intro i j hij
    have h1 := congrFun (congrFun hkey i) j
    rw [hst_diag, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    have h2 : σ (d i) * d j = 1 := by
      have h3 : G i j * (σ (d i) * d j) = G i j * 1 := by
        rw [mul_one]
        calc G i j * (σ (d i) * d j) = σ (d i) * G i j * d j := by ring
          _ = G i j := h1
      exact mul_left_cancel₀ hij h3
    calc d j = (σ (d i) * d i) * d j := by rw [hd, one_mul]
      _ = d i * (σ (d i) * d j) := by ring
      _ = d i := by rw [h2, mul_one]
  have hVG : ((diagonal u).map σ)ᵀ * G * diagonal u = G := by
    ext i j
    rw [hst_diag, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : G i j = 0
    · rw [hij, mul_zero, zero_mul]
    · have huj : u j = u i := hud j i (hGd i j hij)
      rw [huj]
      calc σ (u i) * G i j * u i = G i j * (σ (u i) * u i) := by ring
        _ = G i j := by rw [hu, mul_one]
  rw [hst_mul, hst_mul]
  calc _ = (t.map σ)ᵀ * (((diagonal u).map σ)ᵀ * G * diagonal u) * t := by
        simp only [hG, Matrix.mul_assoc]
    _ = (t.map σ)ᵀ * G * t := by rw [hVG]
    _ = ((t.map σ)ᵀ * (ti.map σ)ᵀ) * (ti * t) := by simp only [hG, Matrix.mul_assoc]
    _ = 1 := by rw [hsttt, hitt, Matrix.one_mul]

theorem escape_projImage_slPi (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f))
    {g : Matrix.ProjGenLinGroup (Fin 3) K}
    (hg : g ∈ CFSG.PGLModel.projImage (Sec4.slPi π 3 (p ^ f) K)) (hg3 : g ^ 3 = 1)
    (hg1 : g ≠ 1) :
    ∃ w ∈ CFSG.PGLModel.projImage (Sec4.glPi π 3 (p ^ f) K),
      w ∉ CFSG.PGLModel.projImage (Sec4.slPi π 3 (p ^ f) K) ∧ w * g = g * w := by
  classical
  have := hK.finite
  have : Fintype K := Fintype.ofFinite K
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨τ, hτ3, hτ1⟩ := Sec4.exists_tau hK hq
  have hω : IsPrimitiveRoot τ 3 := by
    rw [← orderOf_eq_prime hτ3 hτ1]
    exact IsPrimitiveRoot.orderOf τ
  set N := Sec4.qSubPi π (p ^ f) with hN
  have hN3 : 3 ∣ N := Sec4.three_dvd_qSubPi hq
  have hNdvd : N ∣ Nat.card K - 1 := Sec4.qSubPi_dvd hK
  have hq2 : 2 ≤ p ^ f := le_trans hK.prime.two_le (Nat.le_self_pow (by have := hK.one_le; omega) p)
  have hN0 : N ≠ 0 := by
    rw [hN]
    cases π
    · show p ^ f + 1 ≠ 0
      omega
    · show p ^ f - 1 ≠ 0
      omega
  haveI : NeZero N := ⟨hN0⟩
  have hcardμ : Nat.card (rootsOfUnity N K) = N :=
    CFSG.RankThree.Chevalley.card_rootsOfUnity_of_dvd_card_sub_one hNdvd
  obtain ⟨ζ₀, hζ₀⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := rootsOfUnity N K)
  set ζ : Kˣ := (ζ₀ : Kˣ) with hζ
  have hζord : orderOf ζ = N := by
    rw [← hcardμ, ← hζ₀, hζ]
    exact Subgroup.orderOf_coe ζ₀
  have hζN : ζ ^ N = 1 := by rw [← hζord]; exact pow_orderOf_eq_one ζ
  obtain ⟨s, hs, rfl⟩ := hg
  have hdet : (s : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    cases π
    · exact ((Sec4.mem_slPi_false (hπ rfl)).1 hs).1
    · exact (Sec4.mem_slPi_true _).1 hs
  have hs3 : s ^ 3 ∈ StatedScalars (Fin 3) K := by
    rw [← Sec4.mk_eq_one_iff_mem_statedScalars, map_pow]
    exact hg3
  obtain ⟨c, hc⟩ := hs3
  have hcM : (s : Matrix (Fin 3) (Fin 3) K) ^ 3 = Matrix.scalar (Fin 3) (c : K) := by
    rw [← Units.val_pow_eq_pow_val, ← hc, Matrix.GeneralLinearGroup.coe_scalar]
  obtain ⟨T, d, hTd, hd3⟩ := exists_conj_diagonal_of_cube_scalar hω _ hdet hcM
  have hc3 : (c : K) ^ 3 = 1 := by
    have h1 : ((s : Matrix (Fin 3) (Fin 3) K) ^ 3).det = 1 := by
      rw [Matrix.det_pow, hdet, one_pow]
    rw [hcM, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_three] at h1
    rw [pow_three, ← mul_assoc]
    exact h1
  have hd9 : ∀ i, d i ^ 9 = 1 := fun i => by
    rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, hd3, hc3]
  set t : Matrix (Fin 3) (Fin 3) K := (T : Matrix (Fin 3) (Fin 3) K) with ht
  set ti : Matrix (Fin 3) (Fin 3) K := ((T⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hti
  have htti : t * ti = 1 := by rw [ht, hti, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hitt : ti * t = 1 := by rw [ht, hti, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hsD : (s : Matrix (Fin 3) (Fin 3) K) = ti * diagonal d * t := by
    rw [← hTd]
    calc (s : Matrix (Fin 3) (Fin 3) K) =
          (ti * t) * (s : Matrix (Fin 3) (Fin 3) K) * (ti * t) := by
          rw [hitt, Matrix.one_mul, Matrix.mul_one]
      _ = ti * (t * (s : Matrix (Fin 3) (Fin 3) K) * ti) * t := by
          simp only [Matrix.mul_assoc]
  have hnc : ∃ i, d i ≠ d 0 := by
    by_contra h
    push Not at h
    apply hg1
    have hd0 : d 0 ≠ 0 := fun h0 => by
      have := hd9 0
      rw [h0, zero_pow (by norm_num)] at this
      exact zero_ne_one this
    have hD : diagonal d = Matrix.scalar (Fin 3) (d 0) := by
      rw [Matrix.scalar_apply]
      congr 1
      funext i
      exact h i
    have hs' : (s : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) (d 0) := by
      rw [hsD, hD, ← (Matrix.scalar_commute (d 0) (fun _ => Commute.all _ _) ti).eq,
        Matrix.mul_assoc, hitt, Matrix.mul_one]
    rw [Sec4.mk_eq_one_iff_mem_statedScalars]
    exact ⟨Units.mk0 (d 0) hd0, Units.ext (by
      rw [Matrix.GeneralLinearGroup.coe_scalar, hs']
      rfl)⟩
  set u : Fin 3 → Kˣ := fun i => if d i = d 0 then ζ else 1 with hu
  set V : GL (Fin 3) K := TauCeti.diagGL u with hV
  have hVc : (V : Matrix (Fin 3) (Fin 3) K) = diagonal fun i => (u i : K) := TauCeti.diagGL_coe u
  set w : GL (Fin 3) K := T⁻¹ * V * T with hw
  have hwc : (w : Matrix (Fin 3) (Fin 3) K) = ti * diagonal (fun i => (u i : K)) * t := by
    rw [hw, Units.val_mul, Units.val_mul, hVc]
  have hwG : w ∈ Sec4.glPi π 3 (p ^ f) K := by
    cases π
    · have hU := hπ rfl
      have hcardK : Fintype.card K = (p ^ f) ^ 2 := by
        rw [← Nat.card_eq_fintype_card, hU.card, ← pow_mul, mul_comm]
      have hq' : (p ^ f) % 3 = 2 := hq
      have hdinv : ∀ i, hU.bar (d i) * d i = 1 := by
        intro i
        have hdi0 : d i ≠ 0 := fun h0 => by
          have := hd9 i
          rw [h0, zero_pow (by norm_num)] at this
          exact zero_ne_one this
        have hcardm : d i ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one _ hdi0
        have hg9 : d i ^ Nat.gcd 9 (Fintype.card K - 1) = 1 := pow_gcd_eq_one.2 ⟨hd9 i, hcardm⟩
        have hgd : Nat.gcd 9 (Fintype.card K - 1) ∣ p ^ f + 1 := by
          have hsplit : Fintype.card K - 1 = (p ^ f - 1) * (p ^ f + 1) := by
            rw [hcardK]
            obtain ⟨m, hm⟩ : ∃ m, p ^ f = m + 1 := ⟨p ^ f - 1, by omega⟩
            rw [hm, Nat.add_sub_cancel]
            ring_nf
            omega
          have hcop : Nat.Coprime (p ^ f - 1) 9 := by
            rw [show (9 : ℕ) = 3 ^ 2 from rfl]
            apply Nat.Coprime.pow_right
            rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
            omega
          rw [hsplit, Nat.Coprime.gcd_mul_left_cancel_right _ hcop]
          exact Nat.gcd_dvd_right _ _
        obtain ⟨k, hk⟩ := hgd
        rw [hU.bar_apply, ← pow_succ, hk, pow_mul, hg9, one_pow]
      have huinv : ∀ i, hU.bar (u i : K) * (u i : K) = 1 := by
        intro i
        by_cases h : d i = d 0
        · simp only [hu, h, if_true]
          rw [hU.bar_apply, ← pow_succ, ← Units.val_pow_eq_pow_val]
          have : ζ ^ (p ^ f + 1) = 1 := hζN
          rw [this, Units.val_one]
        · simp only [hu, h, if_false, Units.val_one, map_one, mul_one]
      refine (Sec4.mem_glPi_false hU).2 ?_
      rw [hwc]
      refine unitary_conj_diagonal hU htti hitt ?_ hdinv huinv ?_
      · rw [← hsD]
        exact ((Sec4.mem_slPi_false hU).1 hs).2
      · intro i j hij
        simp only [hu, hij]
    · exact Sec4.mem_glPi_true _ w
  have hdetw : Matrix.GeneralLinearGroup.det w = ∏ i, u i := by
    have h1 : Matrix.GeneralLinearGroup.det w = Matrix.GeneralLinearGroup.det V := by
      rw [hw, map_mul, map_mul, map_inv, mul_comm _ (Matrix.GeneralLinearGroup.det V), mul_assoc,
        inv_mul_cancel, mul_one]
    rw [h1]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hVc, Matrix.det_diagonal, Units.coe_prod]
  have hdetw' : Matrix.GeneralLinearGroup.det w = ζ ∨ Matrix.GeneralLinearGroup.det w = ζ ^ 2 := by
    rw [hdetw, Fin.prod_univ_three]
    have hu0 : u 0 = ζ := by simp [hu]
    obtain ⟨i, hi⟩ := hnc
    by_cases h1 : d 1 = d 0
    · have h2 : d 2 ≠ d 0 := by
        intro h2
        fin_cases i
        · exact hi rfl
        · exact hi h1
        · exact hi h2
      have hu1 : u 1 = ζ := by simp [hu, h1]
      have hu2 : u 2 = 1 := by simp [hu, h2]
      right
      rw [hu0, hu1, hu2, mul_one, ← pow_two]
    · have hu1 : u 1 = 1 := by simp [hu, h1]
      by_cases h2 : d 2 = d 0
      · have hu2 : u 2 = ζ := by simp [hu, h2]
        right
        rw [hu0, hu1, hu2, mul_one, ← pow_two]
      · have hu2 : u 2 = 1 := by simp [hu, h2]
        left
        rw [hu0, hu1, hu2, mul_one, mul_one]
  have hcomm : w * s = s * w := by
    apply Units.ext
    show (w : Matrix (Fin 3) (Fin 3) K) * (s : Matrix (Fin 3) (Fin 3) K) =
      (s : Matrix (Fin 3) (Fin 3) K) * (w : Matrix (Fin 3) (Fin 3) K)
    rw [hwc, hsD]
    have hDV : diagonal (fun i => (u i : K)) * diagonal d =
        diagonal d * diagonal (fun i => (u i : K)) := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      ring
    calc ti * diagonal (fun i => (u i : K)) * t * (ti * diagonal d * t) =
          ti * (diagonal (fun i => (u i : K)) * (t * ti) * diagonal d) * t := by
          simp only [Matrix.mul_assoc]
      _ = ti * (diagonal d * diagonal (fun i => (u i : K))) * t := by
          rw [htti, Matrix.mul_one, hDV]
      _ = ti * (diagonal d * (t * ti) * diagonal (fun i => (u i : K))) * t := by
          rw [htti, Matrix.mul_one]
      _ = ti * diagonal d * t * (ti * diagonal (fun i => (u i : K)) * t) := by
          simp only [Matrix.mul_assoc]
  refine ⟨Matrix.ProjGenLinGroup.mk w, ⟨w, hwG, rfl⟩, ?_, ?_⟩
  · intro hmk
    obtain ⟨c', hc'μ, hdetc'⟩ := det_eq_cube_of_mk_mem hK hwG hmk
    have hc'N : c' ^ N = 1 := (mem_rootsOfUnity _ _).1 hc'μ
    obtain ⟨M, hM⟩ := hN3
    have hM0 : 0 < M := by
      rcases Nat.eq_zero_or_pos M with h | h
      · rw [h, mul_zero] at hM
        exact absurd hM hN0
      · exact h
    have hpow : (Matrix.GeneralLinearGroup.det w) ^ M = 1 := by
      rw [hdetc', ← pow_mul, ← hM, hc'N]
    rcases hdetw' with h | h
    · rw [h] at hpow
      have hdvd := orderOf_dvd_of_pow_eq_one hpow
      rw [hζord, hM] at hdvd
      have := Nat.le_of_dvd hM0 hdvd
      omega
    · rw [h, ← pow_mul] at hpow
      have hdvd := orderOf_dvd_of_pow_eq_one hpow
      rw [hζord, hM] at hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
  · rw [← map_mul, hcomm, map_mul]

end Escape

section PlanesPGL

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo CFSG.Open

@[expose] def IsPGLPiThree (X : Type) [Group X] (q : ℕ) : Prop :=
  ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K), Sec4.PiField π p f K ∧ p ^ f = q ∧
    Sec4.ModThree π q ∧ Nonempty (X ≃* CFSG.PGLModel.projImage (Sec4.glPi π 3 q K))

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_cat_projImage_slPi (hK : Sec4.PiField π p f K) (hq : Sec4.ModThree π (p ^ f))
    (hq5 : 5 ≤ p ^ f) :
    ∃ d : TauCeti.ValidLieTypeIndex, 3 ≠ d.1.characteristic ∧
      ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1 ∧
      Nonempty (↥(CFSG.PGLModel.projImage (Sec4.slPi π 3 (p ^ f) K)) ≃*
        (TauCeti.CFSGIndex.lie d).Group) := by
  classical
  have := hK.finite
  have : Fact p.Prime := ⟨hK.prime⟩
  set q : TauCeti.PrimePower := ⟨p, f, hK.prime, hK.one_le⟩ with hqdef
  have hqc : q.card = p ^ f := TauCeti.PrimePower.card_def q
  have hp3 : 3 ≠ p := by
    rintro rfl
    have h0 : (3 : ℕ) ^ f % 3 = 0 := by
      rw [Nat.pow_mod]
      simp [Nat.zero_pow hK.one_le]
    cases π
    · have : (3 ^ f) % 3 = 2 := hq
      omega
    · have : (3 ^ f) % 3 = 1 := hq
      omega
  cases π
  ·
    have hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      exact ⟨⟨le_rfl, fun _ => by rw [hqc]; omega⟩, not_false⟩
    refine ⟨⟨.twistedA 2 q, hv⟩, by simpa using hp3, ?_, ?_⟩
    · simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]
    · obtain ⟨-, K', _, _, hK', ⟨e⟩⟩ :=
        CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv (MulEquiv.refl _)
      have : Fintype K := Fintype.ofFinite K
      have : Fintype K' := Fintype.ofFinite K'
      have hcard : Fintype.card K = Fintype.card K' := by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK', hK.card]
        rfl
      let φ : K ≃+* K' := FiniteField.ringEquivOfCardEq hcard
      let e1 := CFSG.Adapters.RankTwoModelTransports.statedProjCongr
        (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 3) φ)
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ 3 (p ^ f))
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
      exact ⟨((CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk
        (Sec4.slPi false 3 (p ^ f) K)).symm.trans e1).trans e.symm⟩
  ·
    have hv : (TauCeti.LieTypeIndex.A 2 q).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      refine ⟨⟨by norm_num, fun h => absurd h (by norm_num)⟩, ?_⟩
      rintro (⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩)
      · exact absurd h (by norm_num)
      · rw [hqc] at h
        omega
      · exact absurd h (by norm_num)
    refine ⟨⟨.A 2 q, hv⟩, by simpa using hp3, ?_, ?_⟩
    · intro h
      simp only [CFSG.AGLEmbeddingD2.IsD2SeitzException] at h
      rcases h with ⟨-, h⟩ | ⟨h, -⟩
      · rcases h with ⟨q', -, -, h⟩ | ⟨q', hq'p, hq'e, h⟩ | ⟨q', -, -, h⟩ | ⟨q', -, -, h | h⟩ | h
        · cases h
        · injection h with _ h
          subst h
          have : p ^ f = 4 := by
            rw [← hqc, TauCeti.PrimePower.card_def, hq'p, hq'e]
            norm_num
          omega
        · cases h
        · cases h
        · cases h
        · cases h
      · exact absurd h (by norm_num)
    · have : Fintype K := Fintype.ofFinite K
      have : Fintype (GaloisField p f) := Fintype.ofFinite _
      have hcard : Fintype.card K = Fintype.card (GaloisField p f) := by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK.card,
          GaloisField.card p f (by have := hK.one_le; omega)]
        rfl
      exact ⟨(((CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk
        (Sec4.slPi true 3 (p ^ f) K)).symm.trans
          (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
          (CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 3)
            (FiniteField.ringEquivOfCardEq hcard))).trans
          (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).symm⟩

theorem closure_centralizers_eq_top_of_isPGLPiThree
    (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) {C : Type} [Group C] {q : ℕ} (hq5 : 5 ≤ q)
    (hC : IsPGLPiThree C q) {Y : Subgroup C} (hY : IsElemAbelian 3 Y)
    (hYc : Nat.card Y = 3 ^ 2) :
    Subgroup.closure {u : C | ∃ y ∈ Y, y ≠ 1 ∧ y * u = u * y} = ⊤ := by
  classical
  obtain ⟨π, p, f, K, _, hK, rfl, hq, ⟨e⟩⟩ := hC
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq2 : 2 < p ^ f := by omega
  set P := CFSG.PGLModel.projImage (Sec4.glPi π 3 (p ^ f) K) with hP
  set S := CFSG.PGLModel.projImage (Sec4.slPi π 3 (p ^ f) K) with hS
  have hSP : S ≤ P := Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
  set M : Subgroup ↥P := S.subgroupOf P with hM
  have hcomm : commutator ↥P = M := Sec13.commutator_projImage_glPi hK hq2
  haveI : M.Normal := by rw [← hcomm]; infer_instance
  haveI hperf : Group.IsPerfect ↥S := Sec13.isPerfect_projImage_slPi hK hq2
  have hfaith : ∀ x : ↥P, (∀ m ∈ M, x * m = m * x) → x = 1 := by
    intro x hx
    obtain ⟨w, hw, hxw⟩ := x.2
    have hscal : ∀ s ∈ Sec4.slPi π 3 (p ^ f) K,
        w * s * w⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K := by
      intro s hs
      rw [← Sec4.mk_eq_one_iff_mem_statedScalars]
      have hm : (⟨Matrix.ProjGenLinGroup.mk s, hSP ⟨s, hs, rfl⟩⟩ : ↥P) ∈ M :=
        Subgroup.mem_subgroupOf.2 ⟨s, hs, rfl⟩
      have h1 := congrArg Subtype.val (hx _ hm)
      simp only [Subgroup.coe_mul] at h1
      rw [← hxw] at h1
      simp only [map_mul, map_inv, MonoidHom.coe_coe]
      rw [h1]
      group
    have hw1 := Sec4.mem_statedScalars_of_comm_mod hK hq hscal
    apply Subtype.ext
    rw [← hxw, Subgroup.coe_one]
    exact Sec4.mk_eq_one_iff_mem_statedScalars.2 hw1
  set Y' : Subgroup ↥P := Y.map e.toMonoidHom with hY'
  have hY'el : IsElemAbelian 3 Y' := CFSG.Open.IsElemAbelian.map hY _
  have hY'c : Nat.card Y' = 3 ^ 2 := by
    rw [hY', Subgroup.card_map_of_injective e.injective, hYc]
  set G₀ : Subgroup ↥P := Subgroup.closure {u : ↥P | ∃ y ∈ Y', y ≠ 1 ∧ y * u = u * y} with hG₀
  set ρ : ↥P →* MulAut ↥M := MulAut.conjNormal with hρ
  have hρinj : Function.Injective ρ := by
    refine (injective_iff_map_eq_one ρ).2 fun x hx => hfaith x fun m hm => ?_
    have h1 := congrArg (fun φ : MulAut ↥M => ((φ ⟨m, hm⟩ : ↥M) : ↥P)) hx
    simp only [hρ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc x * m = (x * m * x⁻¹) * x := by group
      _ = m * x := by rw [h1]
  set Pl : Subgroup (MulAut ↥M) := Y'.map ρ with hPl
  have hPlel : IsElemAbelian 3 Pl := CFSG.Open.IsElemAbelian.map hY'el ρ
  have hPlc : Nat.card Pl = 3 ^ 2 := by
    rw [hPl, Subgroup.card_map_of_injective hρinj, hY'c]
  obtain ⟨d, hpd, hexc, ⟨eS⟩⟩ := exists_cat_projImage_slPi hK hq hq5
  let φ : ↥M ≃* (TauCeti.CFSGIndex.lie d).Group := (Subgroup.subgroupOfEquivOfLe hSP).trans eS
  set Pl' := Pl.map (MulAut.congr φ).toMonoidHom with hPl'
  have hPl'el : IsElemAbelian 3 Pl' := CFSG.Open.IsElemAbelian.map hPlel _
  have hPl'c : Nat.card Pl' = 3 ^ 2 := by
    rw [hPl', Subgroup.card_map_of_injective (MulAut.congr φ).injective, hPlc]
  have hgen := hS2 d 3 Nat.prime_three (by norm_num) hpd hexc Pl' hPl'el hPl'c
  have hgenM : Subgroup.closure {m : ↥M | ∃ g ∈ Pl, g ≠ 1 ∧ g m = m} = ⊤ := by
    rw [eq_top_iff, ← Subgroup.map_top_of_surjective φ.symm.toMonoidHom φ.symm.surjective, ← hgen,
      MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨k, ⟨_, ⟨g, hgP, rfl⟩, hg1, hgk⟩, rfl⟩
    refine ⟨g, hgP, fun h => hg1 (by rw [h, map_one]), ?_⟩
    have h1 : φ (g (φ.symm k)) = k := hgk
    show g (φ.symm k) = φ.symm k
    apply φ.injective
    rw [h1, MulEquiv.apply_symm_apply]
  have hMG₀ : M ≤ G₀ := by
    intro m hm
    have hle : Subgroup.closure {m : ↥M | ∃ g ∈ Pl, g ≠ 1 ∧ g m = m} ≤ G₀.comap M.subtype := by
      rw [Subgroup.closure_le]
      rintro m' ⟨_, ⟨y, hyY, rfl⟩, hg1, hgm⟩
      refine Subgroup.subset_closure ⟨y, hyY, fun h => hg1 (by rw [h, map_one]), ?_⟩
      have h1 := congrArg Subtype.val hgm
      simp only [hρ, MulAut.conjNormal_apply] at h1
      calc y * (m' : ↥P) = (y * m' * y⁻¹) * y := by group
        _ = m' * y := by rw [h1]
    exact hle (hgenM ▸ Subgroup.mem_top (⟨m, hm⟩ : ↥M))
  obtain ⟨u, huG, huM⟩ : ∃ u ∈ G₀, u ∉ M := by
    by_cases hYM : ∃ y ∈ Y', y ∉ M
    · obtain ⟨y, hyY, hyM⟩ := hYM
      exact ⟨y, Subgroup.subset_closure ⟨y, hyY, fun h => hyM (h ▸ one_mem _), rfl⟩, hyM⟩
    · push Not at hYM
      obtain ⟨y, hyY, hy1⟩ : ∃ y ∈ Y', y ≠ 1 := by
        by_contra h
        push Not at h
        have hbot : Y' = ⊥ := (Subgroup.eq_bot_iff_forall _).2 h
        rw [hbot, Subgroup.card_bot] at hY'c
        norm_num at hY'c
      have hyS : (y : Matrix.ProjGenLinGroup (Fin 3) K) ∈ S :=
        Subgroup.mem_subgroupOf.1 (hYM y hyY)
      have hy3 : (y : Matrix.ProjGenLinGroup (Fin 3) K) ^ 3 = 1 := by
        rw [← Subgroup.coe_pow, hY'el.2 y hyY, Subgroup.coe_one]
      have hy1' : (y : Matrix.ProjGenLinGroup (Fin 3) K) ≠ 1 := fun h => hy1 (Subtype.ext h)
      obtain ⟨w, hwP, hwS, hwy⟩ := escape_projImage_slPi hK hq hyS hy3 hy1'
      exact ⟨⟨w, hwP⟩, Subgroup.subset_closure ⟨y, hyY, hy1, Subtype.ext hwy.symm⟩,
        fun h => hwS (Subgroup.mem_subgroupOf.1 h)⟩
  have hcardM : Nat.card ↥M = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSP).toEquiv
  have hcardP : Nat.card ↥P = Nat.card ↥M * 3 := by
    rw [hcardM, hP, Sec16.ProofKSL3Two.card_projImage_glPi hK, Sec13.card_slPi_three hK,
      ← Sec13.card_projImage_slPi_mul_three hK hq]
  have hlt : M < G₀ := lt_of_le_of_ne hMG₀ fun h => huM (h ▸ huG)
  have hG₀top : G₀ = ⊤ := by
    have h1 : Nat.card M ∣ Nat.card G₀ := Subgroup.card_dvd_of_le hMG₀
    have h2 : Nat.card G₀ ∣ Nat.card ↥P := Subgroup.card_subgroup_dvd_card G₀
    have h3 : Nat.card M < Nat.card G₀ := Subgroup.card_lt_of_lt hlt
    have hM0 : 0 < Nat.card M := Nat.card_pos
    obtain ⟨k, hk⟩ := h1
    rw [hk, hcardP] at h2
    rw [hk] at h3
    have hk3 : k ∣ 3 := Nat.dvd_of_mul_dvd_mul_left hM0 h2
    have hk1 : 1 < k := by
      by_contra hk1
      push Not at hk1
      interval_cases k
      · omega
      · omega
    have hk3' : k = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hk3 with h | h
      · omega
      · exact h
    apply Subgroup.eq_top_of_card_eq
    rw [hk, hk3', hcardP]
  rw [eq_top_iff]
  intro c _
  have hc : e c ∈ G₀ := hG₀top ▸ Subgroup.mem_top _
  have hle : G₀ ≤ (Subgroup.closure {u : C | ∃ y ∈ Y, y ≠ 1 ∧ y * u = u * y}).map
      e.toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro u ⟨y, ⟨y₀, hy₀, rfl⟩, hy1, hyu⟩
    refine ⟨e.symm u, Subgroup.subset_closure ⟨y₀, hy₀, fun h => hy1 (by simp [h]), ?_⟩, by simp⟩
    apply e.injective
    simpa using hyu
  obtain ⟨c', hc', hcc'⟩ := hle hc
  have hcc : c' = c := e.injective hcc'
  rw [← hcc]
  exact hc'

end PlanesPGL

section ThreePlanes

open CFSG.RankThree.PartOne.CTP CFSG.Open

@[expose] def ThreePlaneGen (X : Type*) [Group X] : Prop :=
  ∀ Y : Subgroup X, IsElemAbelian 3 Y → Nat.card Y = 3 ^ 2 →
    Subgroup.closure {u : X | ∃ y ∈ Y, y ≠ 1 ∧ y * u = u * y} = ⊤

theorem threePlaneGen_of_mulEquiv {X X' : Type*} [Group X] [Group X'] (e : X ≃* X')
    (h : ThreePlaneGen X') : ThreePlaneGen X := by
  intro Y hY hYc
  have hgen := h (Y.map e.toMonoidHom) (CFSG.Open.IsElemAbelian.map hY _)
    (by rw [Subgroup.card_map_of_injective e.injective, hYc])
  rw [eq_top_iff]
  intro x _
  have hx : e x ∈ Subgroup.closure {u : X' | ∃ y ∈ Y.map e.toMonoidHom, y ≠ 1 ∧ y * u = u * y} :=
    hgen ▸ Subgroup.mem_top _
  have hle : Subgroup.closure {u : X' | ∃ y ∈ Y.map e.toMonoidHom, y ≠ 1 ∧ y * u = u * y} ≤
      (Subgroup.closure {u : X | ∃ y ∈ Y, y ≠ 1 ∧ y * u = u * y}).map e.toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro u ⟨y, ⟨y₀, hy₀, rfl⟩, hy1, hyu⟩
    refine ⟨e.symm u, Subgroup.subset_closure ⟨y₀, hy₀, fun h => hy1 (by simp [h]), ?_⟩, by simp⟩
    apply e.injective
    simpa using hyu
  obtain ⟨x', hx', hxx'⟩ := hle hx
  have hxx : x' = x := e.injective hxx'
  rw [← hxx]
  exact hx'

theorem fixedPlanesAt_of_threePlaneGen {G : Type*} [Group G] {α : MulAut G}
    (h : ThreePlaneGen ↥(fixedSubgroup α)) : FixedPlanesAt α := by
  intro P hP hPc hPα x hx
  have hgen := h (P.subgroupOf (fixedSubgroup α)) (hP.subgroupOf _)
    (by rw [← hPc]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPα).toEquiv)
  have hx' : (⟨x, hx⟩ : ↥(fixedSubgroup α)) ∈ Subgroup.closure
      {u : ↥(fixedSubgroup α) | ∃ y ∈ P.subgroupOf (fixedSubgroup α), y ≠ 1 ∧ y * u = u * y} :=
    hgen ▸ Subgroup.mem_top _
  have hle : Subgroup.closure
      {u : ↥(fixedSubgroup α) | ∃ y ∈ P.subgroupOf (fixedSubgroup α), y ≠ 1 ∧ y * u = u * y} ≤
      (Subgroup.closure {u : G | u ∈ fixedSubgroup α ∧ ∃ e ∈ P, e ≠ 1 ∧ e * u = u * e}).comap
        (fixedSubgroup α).subtype := by
    rw [Subgroup.closure_le]
    rintro u ⟨y, hyP, hy1, hyu⟩
    exact Subgroup.subset_closure ⟨u.2, (y : G), Subgroup.mem_subgroupOf.1 hyP,
      fun h => hy1 (Subtype.ext h), congrArg Subtype.val hyu⟩
  exact hle hx'

theorem threePlaneGen_of_isPGLPiThree (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) {C : Type}
    [Group C] {q : ℕ} (hq5 : 5 ≤ q) (hC : IsPGLPiThree C q) : ThreePlaneGen C :=
  fun _ hY hYc => closure_centralizers_eq_top_of_isPGLPiThree hS2 hq5 hC hY hYc

theorem fixedPlanesAt_of_isPGLPiThree (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) {G : Type}
    [Group G] {α : MulAut G} {q : ℕ} (hq5 : 5 ≤ q) (h : IsPGLPiThree ↥(fixedSubgroup α) q) :
    FixedPlanesAt α :=
  fixedPlanesAt_of_threePlaneGen (threePlaneGen_of_isPGLPiThree hS2 hq5 h)

theorem threePlaneGen_of_cat (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (d : TauCeti.ValidLieTypeIndex) (hpd : 3 ≠ d.1.characteristic)
    (hexc : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1) {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) (φ : X ≃* (TauCeti.CFSGIndex.lie d).Group) : ThreePlaneGen X := by
  intro Y hY hYc
  set ρ : X →* MulAut X := MulAut.conj with hρ
  have hρinj : Function.Injective ρ := by
    refine (injective_iff_map_eq_one ρ).2 fun x hx => ?_
    have hxZ : x ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : x * g * x⁻¹ = g := by
        have := congrArg (fun ψ : MulAut X => ψ g) hx
        simpa [hρ] using this
      calc g * x = (x * g * x⁻¹) * x := by rw [h1]
        _ = x * g := by group
    rw [hZ] at hxZ
    exact Subgroup.mem_bot.1 hxZ
  set Pl : Subgroup (MulAut X) := Y.map ρ with hPl
  have hPlel : IsElemAbelian 3 Pl := CFSG.Open.IsElemAbelian.map hY ρ
  have hPlc : Nat.card Pl = 3 ^ 2 := by
    rw [hPl, Subgroup.card_map_of_injective hρinj, hYc]
  set Pl' := Pl.map (MulAut.congr φ).toMonoidHom with hPl'
  have hPl'el : IsElemAbelian 3 Pl' := CFSG.Open.IsElemAbelian.map hPlel _
  have hPl'c : Nat.card Pl' = 3 ^ 2 := by
    rw [hPl', Subgroup.card_map_of_injective (MulAut.congr φ).injective, hPlc]
  have hgen := hS2 d 3 Nat.prime_three (by norm_num) hpd hexc Pl' hPl'el hPl'c
  have hgenX : Subgroup.closure {x : X | ∃ g ∈ Pl, g ≠ 1 ∧ g x = x} = ⊤ := by
    rw [eq_top_iff, ← Subgroup.map_top_of_surjective φ.symm.toMonoidHom φ.symm.surjective, ← hgen,
      MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨k, ⟨_, ⟨g, hgP, rfl⟩, hg1, hgk⟩, rfl⟩
    refine ⟨g, hgP, fun h => hg1 (by rw [h, map_one]), ?_⟩
    have h1 : φ (g (φ.symm k)) = k := hgk
    show g (φ.symm k) = φ.symm k
    apply φ.injective
    rw [h1, MulEquiv.apply_symm_apply]
  rw [eq_top_iff, ← hgenX, Subgroup.closure_le]
  rintro x ⟨_, ⟨y, hyY, rfl⟩, hg1, hgx⟩
  refine Subgroup.subset_closure ⟨y, hyY, fun h => hg1 (by rw [h, map_one]), ?_⟩
  have h1 : y * x * y⁻¹ = x := hgx
  calc y * x = (y * x * y⁻¹) * y := by group
    _ = x * y := by rw [h1]

end ThreePlanes

section FixIso

set_option linter.unusedSectionVars false

open CFSG.LieType.Seitz CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Open CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

theorem threePlaneGen_adjointGroup_G2 (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) {F : Type}
    [Field F] [Finite F] (hF3 : ringChar F ≠ 3) (hF5 : 5 ≤ Nat.card F) :
    ThreePlaneGen ↥(adjointGroup Tag.G2 F) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card F (ringChar F)
  set q : TauCeti.PrimePower := ⟨ringChar F, n, hℓ, n.pos⟩ with hq
  have hK : Nat.card F = q.card := by
    rw [TauCeti.PrimePower.card_def, Nat.card_eq_fintype_card]
    exact hn
  have hv : (TauCeti.LieTypeIndex.G2 q).Valid := by
    simp only [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨?_, not_false⟩
    rw [← hK]
    omega
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv F hK
  have hZ : Subgroup.center ↥(adjointGroup Tag.G2 F) = ⊥ := center_adjointGroup_eq_bot
  let e₂ : ↥(adjointGroup Tag.G2 F) ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans φ
  have hpd : 3 ≠ (⟨.G2 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.characteristic := by
    simp only [TauCeti.LieTypeIndex.characteristic_G2]
    exact fun h => hF3 h.symm
  have hexc : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3
      (⟨.G2 q, hv⟩ : TauCeti.ValidLieTypeIndex).1 := by
    simp [CFSG.AGLEmbeddingD2.IsD2SeitzException]
  exact threePlaneGen_of_cat hS2 ⟨.G2 q, hv⟩ hpd hexc hZ e₂

end FixIso

section CharTwo

set_option linter.unusedSectionVars false

open CFSG.LieType.Seitz CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Open CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

theorem nonempty_fixedSubgroup_conj_equiv {G : Type*} [Group G] (ψ β : MulAut G) :
    Nonempty (↥(fixedSubgroup β) ≃* ↥(fixedSubgroup (ψ * β * ψ⁻¹))) :=
  ⟨(Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).trans
    (MulEquiv.subgroupCongr (CFSG.RankThree.PartOne.CTP.fixedSubgroup_conj ψ β).symm)⟩

theorem threePlaneGen_fixedSubgroup_gammaP_of_charTwo (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2) (hK5 : 5 ≤ Nat.card K) {B : SL2 K}
    (hB3 : B ^ 3 = 1) : ThreePlaneGen ↥(fixedSubgroup (gammaP K B)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := ringChar.of_eq hK2
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hm1, hK⟩ : ∃ m : ℕ, 1 ≤ m ∧ Nat.card K = 2 ^ m := by
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card]; exact hn⟩
  have hq5 : 5 ≤ 2 ^ m := hK ▸ hK5
  have hα : gammaP K B = MulAut.conj (sl2At K ⟨2, by decide⟩ B) *
      (exactNormalAut Tag.D4 K 1 1 0 * CFSG.HardMathSupport.Lang.D4Three.d4Graph K 1) := by
    rw [CFSG.StandardType.AutSt.exactNormalAut_one_one_zero, one_mul]
    rfl
  obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨e₁⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.exists_dual_fixEquiv
      (ℓ := 2) (f := m) hm1 K hK (gammaP K B) (gammaP_pow_three hB3)
      (sl2At K ⟨2, by decide⟩ B) 1 (Or.inl rfl) hα
  have e₂ : ↥(fixedSubgroup (gammaP K B)) ≃* ↥(fixedSubgroup φ) :=
    ((MulEquiv.subgroupCongr (Subgroup.ext fun _ => Iff.rfl)).trans e₁).trans
      (MulEquiv.subgroupCongr (Subgroup.ext fun _ => Iff.rfl))
  have hφin : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut φ := hφout
  obtain ⟨g', ⟨e₃⟩, h3⟩ : ∃ g' : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom,
      Nonempty (↥(fixedSubgroup φ) ≃*
        ↥(fixedSubgroup (MulAut.conj g' * fieldActor (t := TwistTag.D4) Fr Fr))) ∧
      (MulAut.conj g' * fieldActor (t := TwistTag.D4) Fr Fr) ^ 3 = 1 := by
    obtain ⟨g', hg' | hg'⟩ := CFSG.RankThree.PartTwo.Sec8.Item8ModelProof.exists_conj_mul_sigma
      (n := m) hm1 hK₃ hFr hφ3 hφin
    · subst hg'
      exact ⟨g', ⟨MulEquiv.refl _⟩, hφ3⟩
    · have hinv : φ⁻¹ = MulAut.conj (fieldActor (t := TwistTag.D4) Fr Fr g'⁻¹) *
          fieldActor (t := TwistTag.D4) Fr Fr := by
        rw [hg', CFSG.HardMathSupport.Lang.E6Descent.inv_conj_mul_inv]
      refine ⟨fieldActor (t := TwistTag.D4) Fr Fr g'⁻¹, ⟨MulEquiv.subgroupCongr ?_⟩, ?_⟩
      · rw [← hinv]
        ext x
        change φ x = x ↔ φ⁻¹ x = x
        rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, eq_comm]
      · rw [← hinv, inv_pow, hφ3, inv_one]
  obtain ⟨h, y, hy, hyy⟩ := CFSG.RankThree.PartTwo.Sec8.exists_conj_eq_of_geom
    CFSG.RankThree.PartTwo.Sec8.d4TrialityGeomClasses_holds
    CFSG.RankThree.PartTwo.Sec8.d4DiagramCentIrred_holds
    CFSG.RankThree.PartTwo.Sec8.d4SecondCentIrred_holds hK₃ hFr g' h3
  obtain ⟨e₄⟩ : Nonempty (↥(fixedSubgroup (MulAut.conj y * fieldActor (t := TwistTag.D4) Fr Fr)) ≃*
      ↥(fixedSubgroup (MulAut.conj g' * fieldActor (t := TwistTag.D4) Fr Fr))) := by
    rw [hyy]
    exact nonempty_fixedSubgroup_conj_equiv _ _
  refine threePlaneGen_of_mulEquiv ((e₂.trans e₃).trans e₄.symm) ?_
  rcases hy with hy1 | hy0
  ·
    have hy1' : y = 1 := Subtype.ext hy1
    subst hy1'
    haveI : CharP K₃ 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (k := m * 3) (by omega) (by rw [hK₃, ← pow_mul])
    obtain ⟨eG⟩ := CFSG.RankThree.PartTwo.KFacts.nonempty_fixedPoints_fieldActor_mulEquiv_g2
      (σ := Fr) (ringChar.eq K₃ 2)
    have hfix : fixedSubgroup (MulAut.conj (1 : graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) *
        fieldActor (t := TwistTag.D4) Fr Fr) =
        (fieldActor (t := TwistTag.D4) Fr Fr).toMonoidHom.eqLocus (MonoidHom.id _) := by
      rw [map_one, one_mul]
      exact Subgroup.ext fun _ => Iff.rfl
    have hcard := CFSG.RankThree.PartTwo.KFacts.card_fixSubfield_of_cube hm1 hK₃ hFr
    refine threePlaneGen_of_mulEquiv ((MulEquiv.subgroupCongr hfix).trans eG) ?_
    haveI := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hm1 hcard
    refine threePlaneGen_adjointGroup_G2 hS2 ?_ (hcard ▸ hq5)
    rw [ringChar.eq _ 2]
    norm_num
  ·
    have hy0' : y = CFSG.RankThree.PartTwo.Sec8.d4TrialityY0Elt K₃ Fr := Subtype.ext hy0
    subst hy0'
    refine threePlaneGen_of_isPGLPiThree hS2 hq5 ?_
    rcases Nat.even_or_odd m with hev | hodd
    · have hmod : 2 ^ m % 3 = 1 := by
        obtain ⟨k, hk⟩ := hev
        rw [hk, ← two_mul, pow_mul, Nat.pow_mod]
        norm_num
      obtain ⟨F, _, _, hF, ⟨eP⟩⟩ :=
        CFSG.RankThree.PartTwo.Sec8.kF82D4SecondCentY0Even_holds m hev hm1 K₃ Fr hK₃ hFr
      exact ⟨true, 2, m, F, inferInstance, ⟨Nat.prime_two, hm1, by rw [hF]; rfl⟩, rfl, hmod,
        ⟨(MulEquiv.subgroupCongr (Subgroup.ext fun _ => Iff.rfl)).trans eP⟩⟩
    · have hmod : 2 ^ m % 3 = 2 := by
        obtain ⟨k, hk⟩ := hodd
        have h4 : 4 ^ k % 3 = 1 := by
          rw [Nat.pow_mod]
          norm_num
        have h2 : 2 ^ m = 4 ^ k * 2 := by
          rw [hk, pow_succ, pow_mul]
          norm_num
        rw [h2]
        omega
      obtain ⟨F, _, _, hF, ⟨eP⟩⟩ :=
        CFSG.RankThree.PartTwo.Sec8.kF82D4SecondCentY0_holds m hodd K₃ Fr hK₃ hFr
      exact ⟨false, 2, m, F, inferInstance, ⟨Nat.prime_two, hm1, by rw [hF]; rfl⟩, rfl, hmod,
        ⟨(MulEquiv.subgroupCongr (Subgroup.ext fun _ => Iff.rfl)).trans eP⟩⟩

theorem fixedPlanesAt_gammaP_of_charTwo (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2) (hK5 : 5 ≤ Nat.card K) {B : SL2 K}
    (hB3 : B ^ 3 = 1) : FixedPlanesAt (gammaP K B) :=
  fixedPlanesAt_of_threePlaneGen (threePlaneGen_fixedSubgroup_gammaP_of_charTwo hS2 hK2 hK5 hB3)

@[expose] def D4GraphA2FixIsoOdd : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 2 → ringChar K ≠ 3 → 5 ≤ Nat.card K →
    ∀ B : SL2 K, B ^ 3 = 1 → B ≠ 1 → IsPGLPiThree ↥(fixedSubgroup (gammaP K B)) (Nat.card K)

theorem d4GraphA2FixedPlanes_of_fixIsoOdd (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (h : D4GraphA2FixIsoOdd) : D4GraphA2FixedPlanes := by
  intro K _ _ hK3 hK5 B hB3 hB1
  by_cases hK2 : ringChar K = 2
  · exact fixedPlanesAt_gammaP_of_charTwo hS2 hK2 hK5 hB3
  · exact fixedPlanesAt_of_isPGLPiThree hS2 hK5 (h K hK2 hK3 hK5 B hB3 hB1)

end CharTwo

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh3

end
