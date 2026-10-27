module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmDefs
public import CFSG.RankThree.PartOne.KF.ClsAltOdd
public import CFSG.RankThree.PartOne.S11d.OrthCaseH

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks QuadraticMap Polynomial
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]

namespace OmEngine

theorem exists_threeSingular_of_eight_le [Finite F] [CharP F 2] [FiniteDimensional F V]
    {Q : QuadraticForm F V} (hQ : (polarBilin Q).Nondegenerate) (h8 : 8 ≤ Module.finrank F V) :
    ∃ U : Submodule F V, Module.finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0 := by
  have h2 : (2 : F) = 0 := by
    have := CharP.cast_eq_zero F 2
    simpa using this
  have halt : (polarBilin Q).IsAlt := polarBilin_isAlt h2 Q
  obtain ⟨m, hm⟩ := LinearMap.BilinForm.IsAlt.even_finrank halt hQ
  have hm2 : Module.finrank F V = 2 * m := by omega
  have hm4 : 4 ≤ m := by omega
  exact CFSG.RankThree.PartOne.exists_threeSingular_of_dim Q hQ hm4 hm2

section BlockDim

variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] {p : ℕ}

theorem finrank_blockSpace_dvd_rk2Ord [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hp : p.Prime) (hp2 : p ≠ 2) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) (D : Hyperplane A p)
    (hD : blockSpace A D.1 ≠ ⊥) {n : ℕ} (hn : Nat.card F = 2 ^ n) :
    CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n ∣ Module.finrank F ↥(blockSpace A D.1) := by
  classical
  have hpF : (p : F) ≠ 0 := by
    intro h
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff F 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  set x : V ≃ₗ[F] V := blockEnd A hp hpF hA t ht D with hx
  set U : Submodule F V := blockSpace A D.1 with hU
  have hxpow : x ^ p = 1 := blockEnd_pow A hp hpF hA t ht D
  have hUinv : ∀ v ∈ U, x v ∈ U := by
    intro v hv
    rw [hx, blockEnd_apply_mem A hp hpF hA t ht D hv]
    exact blockSpace_invariant A hp hpF hA hv
  have hUinv' : ∀ v ∈ U, x.symm v ∈ U := by
    intro v hv
    have hxinv : x.symm = x ^ (p - 1) :=
      inv_eq_of_mul_eq_one_right (by
        rw [← pow_succ', Nat.sub_add_cancel hp.one_lt.le, hxpow])
    rw [hxinv]
    have h := blockEnd_pow_apply A hp hpF hA t ht D (p - 1) (u := v) (r := 0) hv (by simp)
    simp only [add_zero] at h
    rw [h]
    exact blockSpace_pow_mem A hp hpF hA (t D) hv
  let g : U ≃ₗ[F] U := LinearEquiv.ofBijective ((x : V →ₗ[F] V).restrict hUinv) ⟨by
    intro a b hab
    refine Subtype.ext (x.injective ?_)
    simpa using congrArg Subtype.val hab
  , by
    intro b
    refine ⟨⟨x.symm (b : V), hUinv' b b.2⟩, Subtype.ext ?_⟩
    simp⟩
  have hgval : ∀ v : U, ((g v : U) : V) = x (v : V) := fun v => rfl
  have hpow : ∀ (k : ℕ) (v : U), (((g ^ k) v : U) : V) = (x ^ k) (v : V) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      calc ((g ^ (k + 1)) v : V)
          = x ((g ^ k) v : U) := by
            rw [pow_succ', LinearEquiv.mul_apply]
            exact hgval _
        _ = x ((x ^ k) (v : V)) := congrArg x (ih v)
        _ = (x ^ (k + 1)) (v : V) := by
            rw [pow_succ', LinearEquiv.mul_apply]
  have hgp : g ^ p = 1 := by
    refine LinearEquiv.ext fun v => Subtype.ext ?_
    rw [hpow, hxpow]
    simp
  have hfree : ∀ v : U, g v = v → v = 0 := by
    intro v hv
    have hxv : ((t D : ↥A) : V ≃ₗ[F] V) (v : V) = (v : V) := by
      rw [← blockEnd_apply_mem A hp hpF hA t ht D v.2]
      rw [← hgval v]
      exact congrArg Subtype.val hv
    exact Subtype.ext (eq_zero_of_fixed_mem_blockSpace A hp hpF hA (ht D) v.2 hxv)
  have hdvd := CFSG.RankThree.PartOne.KFU.pow_sub_one_dvd_of_fixed_point_free hp hgp hfree
  have hpos : 1 ≤ Nat.card F ^ Module.finrank F U := Nat.one_le_pow _ _ Nat.card_pos
  have hcast : ((Nat.card F : ℕ) : ZMod p) ^ Module.finrank F U = 1 := by
    have hzero : ((Nat.card F ^ Module.finrank F U : ℕ) : ZMod p) - 1 = 0 := by
      rw [← Nat.cast_one, ← Nat.cast_sub hpos]
      exact (ZMod.natCast_eq_zero_iff _ p).mpr hdvd
    have h1 : ((Nat.card F ^ Module.finrank F U : ℕ) : ZMod p) = 1 := sub_eq_zero.mp hzero
    simpa using h1
  have hq : ((Nat.card F : ℕ) : ZMod p) = (2 : ZMod p) ^ n := by
    rw [hn]
    push_cast
    ring
  have hord : orderOf ((2 : ZMod p) ^ n) ∣ Module.finrank F U := by
    rw [← hq]
    exact orderOf_dvd_of_pow_eq_one hcast
  simpa [CFSG.LocalAnalysis.GLTheoremA.rk2Ord] using hord

end BlockDim

section OrthDerived

variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] {p : ℕ} {Q : QuadraticForm F V}

theorem blockEnd_mem_orthDerived [Finite F] [FiniteDimensional F V]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hp2 : p ≠ 2) (hA : IsElemAbelian p A)
    (hQ : (polarBilin Q).Nondegenerate)
    (hQinv : ∀ a : ↥A, ∀ v : V, Q ((a : V ≃ₗ[F] V) v) = Q v)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) (D : Hyperplane A p)
    (hT : ∃ U : Submodule F V, Module.finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    blockEnd A hp hpF hA t ht D ∈ orthDerived Q := by
  have hmem : blockEnd A hp hpF hA t ht D ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    exact blockEnd_quadratic A hp hpF hA Q hQinv t ht D
  exact CFSG.LieType.SeitzGeneration.mem_orthDerived_of_odd_pow hQ hT
    (hp.odd_of_ne_two hp2) hmem (blockEnd_pow A hp hpF hA t ht D)

end OrthDerived

section Supported

variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A] {p : ℕ} {Q : QuadraticForm F V}

theorem blockEnd_mem_supportedFixedDerived [Finite F] [CharP F 2] [FiniteDimensional F V]
    (hp : p.Prime) (hpF : (p : F) ≠ 0) (hp2 : p ≠ 2) (hA : IsElemAbelian p A)
    (hQinv : ∀ a : ↥A, ∀ v : V, Q ((a : V ≃ₗ[F] V) v) = Q v)
    (hQ : (polarBilin Q).Nondegenerate)
    (hB : ∀ a : ↥A, ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = polarBilin Q u v)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) {D E : Hyperplane A p} (hDE : D ≠ E)
    (h8 : 8 ≤ Module.finrank F ↥(fixedSpace (blockEnd A hp hpF hA t ht D))) :
    blockEnd A hp hpF hA t ht E ∈
      supportedFixedDerived Q (blockEnd A hp hpF hA t ht D) := by
  classical
  set x : V ≃ₗ[F] V := blockEnd A hp hpF hA t ht D with hx
  set y : V ≃ₗ[F] V := blockEnd A hp hpF hA t ht E with hy
  have hxodd : OddOrderIsometry Q p x :=
    blockEnd_oddOrderIsometry A hp hpF hA hQ hQinv t ht D
  have hoth : othersSpace x.toLinearMap (X - 1) = blockSpace A D.1 := by
    set K : Submodule F V := LinearMap.ker (projBlock A hp hpF hA D) with hK
    have hKfix : K = fixedSpace x := (fixedSpace_blockEnd_eq_ker_projBlock A hp hpF hA t ht D).symm
    have hKnd : (polarBilin (Q.comp K.subtype)).Nondegenerate := by
      rw [hKfix]
      exact hxodd.polarBilin_fixed_nondegenerate
    have hcompl := CFSG.RankThree.PartOne.KCOrthogonal.isCompl_orthPerp hKnd
    have hdim : Module.finrank F ↥(orthPerp Q K) = Module.finrank F ↥(blockSpace A D.1) := by
      have h1 := Submodule.finrank_add_eq_of_isCompl hcompl
      have h2 := finrank_ker_projBlock_add_finrank_blockSpace A hp hpF hA D
      exact Nat.add_left_cancel (h1.trans h2.symm)
    have hle : blockSpace A D.1 ≤ orthPerp Q K := by
      intro v hv
      rw [mem_orthPerp]
      intro r hr
      rw [QuadraticMap.polar_comm]
      exact blockSpace_ker_orthogonal A hp hpF hA (polarBilin Q) hB D hv hr
    have hOK : orthPerp Q K = blockSpace A D.1 :=
      (Submodule.eq_of_le_of_finrank_eq hle hdim.symm).symm
    rw [← CFSG.RankThree.PartOne.KCOrthogonalD4.orthPerp_fixedSpace hxodd, ← hKfix]
    exact hOK
  have hcent : y ∈ isometryCentralizer Q x := by
    refine mem_isometryCentralizer.mpr ⟨fun v => blockEnd_quadratic A hp hpF hA Q hQinv t ht E v,
      fun v => ?_⟩
    have hcomm : Commute x y :=
      blockEndOf_commute A hp hpF hA (t D) (t E) (Ne.symm hDE)
    exact LinearEquiv.congr_fun hcomm.eq.symm v
  have hfix : ∀ v ∈ othersSpace x.toLinearMap (X - 1), y v = v := by
    intro v hv
    rw [hoth] at hv
    exact blockEnd_apply_of_mem_block A hp hpF hA t ht hDE hv
  have hT : ∃ U' : Submodule F ↥(fixedSpace x), Module.finrank F U' = 3 ∧
      ∀ u ∈ U', (Q.comp (fixedSpace x).subtype) u = 0 :=
    exists_threeSingular_of_eight_le hxodd.polarBilin_fixed_nondegenerate h8
  exact hxodd.mem_supportedFixedDerived_of_odd_pow hT
    (mem_supportedBlock.mpr ⟨hcent, hfix⟩) (hp.odd_of_ne_two hp2)
    (blockEnd_pow A hp hpF hA t ht E)

end Supported

end OmEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F
