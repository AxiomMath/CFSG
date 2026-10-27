module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6LComb
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6LDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6LFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA7Field
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA7Rank
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.PiTensorProduct

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

open Matrix Finset

open scoped Classical

theorem one_add_add_sq_eq_zero {L : Type} [Field L] {ζ : L} (hζ : IsPrimitiveRoot ζ 3) :
    1 + ζ + ζ ^ 2 = 0 := by
  have h := hζ.geom_sum_eq_zero (by norm_num : 1 < 3)
  simpa [Finset.sum_range_succ] using h

theorem proj_val {L : Type} [Field L] {ζ : L} (hζ : IsPrimitiveRoot ζ 3) (h3 : (3 : L) ≠ 0)
    {u : L} (hu : u ^ 3 = 1) :
    (3 : L)⁻¹ * (1 + u + u ^ 2) = if u = 1 then 1 else 0 := by
  rcases mu3_cases hζ hu with h | h | h
  · subst h
    rw [if_pos rfl]
    have : (1 : L) + 1 + 1 ^ 2 = 3 := by norm_num
    rw [this, inv_mul_cancel₀ h3]
  · subst h
    rw [if_neg (hζ.ne_one (by norm_num)), one_add_add_sq_eq_zero hζ, mul_zero]
  · subst h
    have h4 : (ζ ^ 2) ^ 2 = ζ := by
      have h3' : ζ ^ 3 = 1 := hζ.pow_eq_one
      linear_combination ζ * h3'
    rw [if_neg (sq_ne_one_of_prim hζ), h4]
    have : 1 + ζ ^ 2 + ζ = 0 := by linear_combination one_add_add_sq_eq_zero hζ
    rw [this, mul_zero]

theorem conj_pow {L : Type} [Field L] (A : Matrix.GeneralLinearGroup (Fin 6) L)
    (B : Matrix (Fin 6) (Fin 6) L) (n : ℕ) :
    (A : Matrix (Fin 6) (Fin 6) L) * B ^ n * ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) L) :
      Matrix (Fin 6) (Fin 6) L) =
      ((A : Matrix (Fin 6) (Fin 6) L) * B * ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) L) :
        Matrix (Fin 6) (Fin 6) L)) ^ n := by
  have hA' : ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) L) : Matrix (Fin 6) (Fin 6) L) *
      (A : Matrix (Fin 6) (Fin 6) L) = 1 := Units.inv_mul A
  have hA : (A : Matrix (Fin 6) (Fin 6) L) *
      ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) L) : Matrix (Fin 6) (Fin 6) L) = 1 :=
    Units.mul_inv A
  induction n with
  | zero => simp [hA]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih]
    rw [show (A : Matrix (Fin 6) (Fin 6) L) * B ^ n *
        ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) L) : Matrix (Fin 6) (Fin 6) L) *
        ((A : Matrix (Fin 6) (Fin 6) L) * B *
          ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) L) : Matrix (Fin 6) (Fin 6) L)) =
        (A : Matrix (Fin 6) (Fin 6) L) * B ^ n *
        (((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) L) : Matrix (Fin 6) (Fin 6) L) *
          (A : Matrix (Fin 6) (Fin 6) L)) * B *
          ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) L) : Matrix (Fin 6) (Fin 6) L) by
      simp only [Matrix.mul_assoc], hA']
    simp only [Matrix.mul_one, Matrix.mul_assoc]

section Fixed

variable {K L : Type} [Field K] [Field L] [Algebra K L]

theorem Dm_mulVec_fixed (A : Matrix.GeneralLinearGroup (Fin 6) L)
    (x : Matrix.SpecialLinearGroup (Fin 6) K) (v : Fin 6 → K)
    (hxv : (x : Matrix (Fin 6) (Fin 6) K) *ᵥ v = v) :
    Dm A x *ᵥ ((A : Matrix (Fin 6) (Fin 6) L) *ᵥ fun i => algebraMap K L (v i)) =
      (A : Matrix (Fin 6) (Fin 6) L) *ᵥ fun i => algebraMap K L (v i) := by
  unfold Dm
  rw [Matrix.mulVec_mulVec]
  have hA : (A : Matrix (Fin 6) (Fin 6) L) * ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) L) :
      Matrix (Fin 6) (Fin 6) L) = 1 := Units.mul_inv A
  have hA' : ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) L) : Matrix (Fin 6) (Fin 6) L) *
      (A : Matrix (Fin 6) (Fin 6) L) = 1 := Units.inv_mul A
  rw [Matrix.mul_assoc, hA', Matrix.mul_one, ← Matrix.mulVec_mulVec]
  congr 1
  have hw : xL (L := L) x *ᵥ (fun i => algebraMap K L (v i)) =
      fun i => algebraMap K L (v i) := by
    funext i
    have := congrFun hxv i
    unfold xL
    rw [← this]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    simp [map_sum, map_mul]
  exact hw

end Fixed

theorem quad_monic (K : Type) [Field K] : (KA7.quad K).Monic := by
  unfold KA7.quad
  monicity!

@[expose] def emat {K : Type} [Field K] (g : Matrix (Fin 6) (Fin 6) K) : Matrix (Fin 6) (Fin 6) K :=
  (3 : K)⁻¹ • (1 + g + g ^ 2)

theorem diag_proj {L : Type} [Field L] {ζ : L} (hζ : IsPrimitiveRoot ζ 3) (h3 : (3 : L) ≠ 0)
    (u : Fin 6 → L) (hu : ∀ i, u i ^ 3 = 1) :
    (3 : L)⁻¹ • (1 + Matrix.diagonal u + (Matrix.diagonal u) ^ 2) =
      Matrix.diagonal (fun i => if u i = 1 then (1 : L) else 0) := by
  have hsq : (Matrix.diagonal u) ^ 2 = Matrix.diagonal (fun i => u i ^ 2) := by
    rw [sq, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  rw [hsq]
  ext i j
  by_cases h : i = j
  · subst h
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq,
      smul_eq_mul]
    rw [← proj_val hζ h3 (hu i)]
  · simp [Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h]

theorem bridge_frame (K : Type) [Field K] [Finite K] (hnr : ∀ r : K, r ^ 2 + r + 1 ≠ 0)
    (P : Subgroup (Matrix.SpecialLinearGroup (Fin 6) K)) [Fintype P]
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hpow : ∀ x ∈ P, x ^ 3 = 1)
    (hcard : Fintype.card P = 27) :
    ∃ g t : P, g ≠ 1 ∧
      (∀ k : ℕ, (t : Matrix.SpecialLinearGroup (Fin 6) K) ≠
        (g : Matrix.SpecialLinearGroup (Fin 6) K) ^ k) ∧
      ∃ S : Matrix.GeneralLinearGroup (Fin 6) K, ∃ G T2 : Matrix (Fin 2) (Fin 2) K,
        ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
          ((g : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
          (S : Matrix (Fin 6) (Fin 6) K) = blk6 1 G ∧
        ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
          ((t : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
          (S : Matrix (Fin 6) (Fin 6) K) = blk6 (D4 K) T2 ∧
        ((S⁻¹ : Matrix.GeneralLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
          emat ((g : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
          (S : Matrix (Fin 6) (Fin 6) K) = blk6 1 0 := by
  classical
  haveI : Fact (Irreducible (KA7.quad K)) := ⟨KA7.quad_irreducible hnr⟩
  haveI : Module.Finite K (AdjoinRoot (KA7.quad K)) :=
    Polynomial.Monic.finite_adjoinRoot (quad_monic K)
  haveI : Finite (AdjoinRoot (KA7.quad K)) := Module.finite_of_finite K
  have hζ : IsPrimitiveRoot (AdjoinRoot.root (KA7.quad K)) 3 := KA7.prim_root_quad hnr
  obtain ⟨A, hoff, hmul, hcube, hsymm, hfaithful⟩ :=
    diag_eigen hζ (KA7.sigmaQuad K) (KA7.sigmaQuad_zeta K) (KA7.sigmaQuad_sigmaQuad K) P hcomm hpow
  set d : Fin 6 → P → AdjoinRoot (KA7.quad K) := fun i x =>
    Dm A (x : Matrix.SpecialLinearGroup (Fin 6) K) i i with hd
  have hdmul : ∀ i (x y : P), d i (x * y) = d i x * d i y := fun i x y => hmul i x y
  have hdpow : ∀ i (x : P), d i x ^ 3 = 1 := fun i x => hcube i x
  have hfaith : ∀ x : P, (∀ i, d i x = 1) → x = 1 := hfaithful
  have hsy : ∀ z : P, (univ.filter fun i => d i z = AdjoinRoot.root (KA7.quad K)).card =
      (univ.filter fun i => d i z = AdjoinRoot.root (KA7.quad K) ^ 2).card := hsymm
  obtain ⟨g, t, hg1, hcard4, hgt⟩ := exists_gt hζ (d := d) hdmul hdpow hfaith hcard hsy
  have hpowd : ∀ i (x : P) (k : ℕ), d i (x ^ k) = d i x ^ k := by
    intro i x k
    induction k with
    | zero =>
      simp only [pow_zero]
      show Dm A ((1 : P) : Matrix.SpecialLinearGroup (Fin 6) K) i i = 1
      rw [Subgroup.coe_one, Dm_one, Matrix.one_apply_eq]
    | succ k ih => rw [pow_succ, hdmul, ih, pow_succ]
  set gm : Matrix (Fin 6) (Fin 6) K :=
    ((g : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) with hgm
  set tm : Matrix (Fin 6) (Fin 6) K :=
    ((t : Matrix.SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) with htm
  have hg3 : gm ^ 3 = 1 := by
    have h := hpow g g.2
    rw [hgm, ← Matrix.SpecialLinearGroup.coe_pow, h, Matrix.SpecialLinearGroup.coe_one]
  have ht3 : tm ^ 3 = 1 := by
    have h := hpow t t.2
    rw [htm, ← Matrix.SpecialLinearGroup.coe_pow, h, Matrix.SpecialLinearGroup.coe_one]
  have hgt' : Commute gm tm := by
    have h := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 6) K =>
      (x : Matrix (Fin 6) (Fin 6) K)) (hcomm _ g.2 _ t.2)
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h
    exact h
  have h3K : (3 : K) ≠ 0 := fun h => hnr 1 (by linear_combination h)
  have hp : (1 + gm + gm ^ 2) * (1 + gm + gm ^ 2) = (3 : K) • (1 + gm + gm ^ 2) := by
    have h4 : gm ^ 4 = gm := by rw [pow_succ, hg3, one_mul]
    calc (1 + gm + gm ^ 2) * (1 + gm + gm ^ 2)
        = 1 + gm + gm ^ 2 + gm + gm ^ 2 + gm ^ 3 + gm ^ 2 + gm ^ 3 + gm ^ 4 := by noncomm_ring
      _ = (3 : K) • (1 + gm + gm ^ 2) := by
        rw [hg3, h4]
        module
  have hem : emat gm * emat gm = emat gm := by
    have hs : (3 : K)⁻¹ * (3 : K)⁻¹ * 3 = (3 : K)⁻¹ := by
      rw [mul_assoc, inv_mul_cancel₀ h3K, mul_one]
    unfold emat
    rw [Matrix.smul_mul, Matrix.mul_smul, hp, smul_smul, smul_smul, hs]
  have hpgm : gm * (1 + gm + gm ^ 2) = 1 + gm + gm ^ 2 := by
    calc gm * (1 + gm + gm ^ 2) = gm + gm ^ 2 + gm ^ 3 := by noncomm_ring
      _ = 1 + gm + gm ^ 2 := by rw [hg3]; abel
  have hpgm' : (1 + gm + gm ^ 2) * gm = 1 + gm + gm ^ 2 := by
    calc (1 + gm + gm ^ 2) * gm = gm + gm ^ 2 + gm ^ 3 := by noncomm_ring
      _ = 1 + gm + gm ^ 2 := by rw [hg3]; abel
  have hge : gm * emat gm = emat gm := by
    unfold emat; rw [Matrix.mul_smul, hpgm]
  have heg : emat gm * gm = emat gm := by
    unfold emat; rw [Matrix.smul_mul, hpgm']
  have hte : tm * emat gm = emat gm * tm := by
    have hc : Commute tm (1 + gm + gm ^ 2) :=
      ((Commute.one_right tm).add_right hgt'.symm).add_right (hgt'.symm.pow_right 2)
    unfold emat
    rw [Matrix.mul_smul, Matrix.smul_mul, hc.eq]

  have hdiagD : ∀ x : P, Dm A (x : Matrix.SpecialLinearGroup (Fin 6) K) =
      Matrix.diagonal (fun i => d i x) := by
    intro x
    ext i j
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ h]
      exact hoff x i j h
  have hmap : (emat gm).map (algebraMap K (AdjoinRoot (KA7.quad K))) =
      (3 : AdjoinRoot (KA7.quad K))⁻¹ • (1 + gm.map (algebraMap K (AdjoinRoot (KA7.quad K))) +
        (gm.map (algebraMap K (AdjoinRoot (KA7.quad K)))) ^ 2) := by
    ext i j
    simp only [emat, Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply,
      pow_two, Matrix.mul_apply, Fin.sum_univ_six, smul_eq_mul, map_mul, map_add, map_sum,
      map_inv₀, map_ofNat]
    simp [Matrix.one_apply, apply_ite]
  have h3L : (3 : AdjoinRoot (KA7.quad K)) ≠ 0 := by
    intro h
    apply h3K
    exact (algebraMap K (AdjoinRoot (KA7.quad K))).injective
      ((map_ofNat _ 3).trans (h.trans (map_zero _).symm))
  have hconj : (A : Matrix (Fin 6) (Fin 6) (AdjoinRoot (KA7.quad K))) *
      ((emat gm).map (algebraMap K (AdjoinRoot (KA7.quad K)))) *
      ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) (AdjoinRoot (KA7.quad K))) :
        Matrix (Fin 6) (Fin 6) (AdjoinRoot (KA7.quad K))) =
      Matrix.diagonal (fun i => if d i g = 1 then (1 : AdjoinRoot (KA7.quad K)) else 0) := by
    rw [hmap]
    have hA : (A : Matrix (Fin 6) (Fin 6) (AdjoinRoot (KA7.quad K))) *
        ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) (AdjoinRoot (KA7.quad K))) :
          Matrix (Fin 6) (Fin 6) (AdjoinRoot (KA7.quad K))) = 1 := Units.mul_inv A
    have hM : Dm A (g : Matrix.SpecialLinearGroup (Fin 6) K) =
        (A : Matrix (Fin 6) (Fin 6) (AdjoinRoot (KA7.quad K))) *
          (gm.map (algebraMap K (AdjoinRoot (KA7.quad K)))) *
          ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) (AdjoinRoot (KA7.quad K))) :
            Matrix (Fin 6) (Fin 6) (AdjoinRoot (KA7.quad K))) := rfl
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul,
      Matrix.add_mul, Matrix.mul_one, hA, conj_pow, ← hM, hdiagD g, diag_proj hζ
        h3L (fun i => d i g) (fun i => hdpow i g)]
  have hrank : (emat gm).rank = 4 := by
    have h1 := KA7.rank_map_field (algebraMap K (AdjoinRoot (KA7.quad K))) (emat gm)
    have h2 := KA7.rank_conj (A : Matrix (Fin 6) (Fin 6) (AdjoinRoot (KA7.quad K)))
      ((emat gm).map (algebraMap K (AdjoinRoot (KA7.quad K))))
      ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) (AdjoinRoot (KA7.quad K))) :
        Matrix (Fin 6) (Fin 6) (AdjoinRoot (KA7.quad K))) (Units.mul_inv A)
    rw [hconj, Matrix.rank_diagonal] at h2
    have hfc : (univ.filter fun i : Fin 6 =>
        (if d i g = 1 then (1 : AdjoinRoot (KA7.quad K)) else 0) ≠ 0) =
        univ.filter fun i => d i g = 1 := by
      apply Finset.filter_congr
      intro i _
      by_cases h : d i g = 1 <;> simp [h]
    rw [← h1, ← h2, Fintype.card_subtype, hfc, hcard4]
  have hfix : ∀ v : Fin 6 → K, emat gm *ᵥ v = v → tm *ᵥ v = v → v = 0 := by
    intro v hev htv
    have hgv : gm *ᵥ v = v := by
      have h1 : gm *ᵥ (emat gm *ᵥ v) = emat gm *ᵥ v := by
        rw [Matrix.mulVec_mulVec, hge]
      rwa [hev] at h1
    set w : Fin 6 → AdjoinRoot (KA7.quad K) := fun i => algebraMap K (AdjoinRoot (KA7.quad K)) (v i)
      with hw
    set u : Fin 6 → AdjoinRoot (KA7.quad K) :=
      (A : Matrix (Fin 6) (Fin 6) (AdjoinRoot (KA7.quad K))) *ᵥ w with hu
    have hgu : Dm A (g : Matrix.SpecialLinearGroup (Fin 6) K) *ᵥ u = u :=
      Dm_mulVec_fixed A (g : Matrix.SpecialLinearGroup (Fin 6) K) v hgv
    have htu : Dm A (t : Matrix.SpecialLinearGroup (Fin 6) K) *ᵥ u = u :=
      Dm_mulVec_fixed A (t : Matrix.SpecialLinearGroup (Fin 6) K) v htv
    have hz : ∀ i, u i = 0 := by
      intro i
      by_contra hne
      have h1 := congrFun hgu i
      have h2 := congrFun htu i
      rw [hdiagD g, Matrix.mulVec_diagonal] at h1
      rw [hdiagD t, Matrix.mulVec_diagonal] at h2
      have hg1' : d i g = 1 := by
        have : (d i g - 1) * u i = 0 := by linear_combination h1
        rcases mul_eq_zero.mp this with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hne
      have ht1' : d i t = 1 := by
        have : (d i t - 1) * u i = 0 := by linear_combination h2
        rcases mul_eq_zero.mp this with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hne
      exact hgt i hg1' ht1'
    have hu0 : u = 0 := funext hz
    have hw0 : w = 0 := by
      have hwu : w = ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) (AdjoinRoot (KA7.quad K))) :
          Matrix (Fin 6) (Fin 6) (AdjoinRoot (KA7.quad K))) *ᵥ u := by
        rw [hu, Matrix.mulVec_mulVec]
        have hA' : ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 6) (AdjoinRoot (KA7.quad K))) :
            Matrix (Fin 6) (Fin 6) (AdjoinRoot (KA7.quad K))) *
            (A : Matrix (Fin 6) (Fin 6) (AdjoinRoot (KA7.quad K))) = 1 := Units.inv_mul A
        rw [hA', Matrix.one_mulVec]
      rw [hwu, hu0, Matrix.mulVec_zero]
    funext i
    have hi := congrFun hw0 i
    simpa [hw] using hi
  obtain ⟨S, G, T2, e1, e2, e3⟩ := frame6 hnr gm tm (emat gm) hem hrank hge heg hte ht3 hfix
  refine ⟨g, t, hg1, ?_, S, G, T2, e1, e2, e3⟩
  intro k hk
  have hpos : 0 < (univ.filter fun i => d i g = 1).card := by rw [hcard4]; norm_num
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  have htk : t = g ^ k := Subtype.ext (by simpa using hk)
  have hdk : d i t = d i g ^ k := by rw [htk, hpowd]
  rw [(Finset.mem_filter.mp hi).2, one_pow] at hdk
  exact hgt i (Finset.mem_filter.mp hi).2 hdk

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

end
