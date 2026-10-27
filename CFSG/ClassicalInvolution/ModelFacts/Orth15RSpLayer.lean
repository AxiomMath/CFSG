module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSpStd
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSpAlg
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSpPhi

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp

open QuadraticAlgebra CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Sp
open CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4 (QE r0 coe_r0 exists_conj_r0 sl2_sq_cases
  mem_sup_of_comm isQuasisimple_sl2 sup_le_normalizer_of_comm exists_sq_add_sq)
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]

section Iota

variable {lam : QE F}

theorem iota_symplectic (h2 : (2 : F) ≠ 0) (hlam : star lam * lam = -1) (B : SL(2, F)) :
    (PhiS (Xm lam (B : Matrix (Fin 2) (Fin 2) F)))ᵀ * gram F 2 *
      PhiS (Xm lam (B : Matrix (Fin 2) (Fin 2) F)) = gram F 2 :=
  (PhiS_symplectic_iff _).2 (Xm_unitary h2 hlam B.2)

@[expose] noncomputable def iota (h2 : (2 : F) ≠ 0) (hlam : star lam * lam = -1) :
    SL(2, F) →* StatedSp 2 F where
  toFun B := ofSymplecticMat (PhiS (Xm lam (B : Matrix (Fin 2) (Fin 2) F)))
    (iota_symplectic h2 hlam B)
  map_one' := by
    apply mat_injective
    rw [mat_ofSymplecticMat, Matrix.SpecialLinearGroup.coe_one, Xm_one h2 hlam, map_one, map_one]
  map_mul' B B' := by
    apply mat_injective
    rw [mat_ofSymplecticMat, map_mul, mat_ofSymplecticMat, mat_ofSymplecticMat,
      Matrix.SpecialLinearGroup.coe_mul, Xm_mul h2 hlam, map_mul]

theorem mat_iota (h2 : (2 : F) ≠ 0) (hlam : star lam * lam = -1) (B : SL(2, F)) :
    mat 2 F (iota h2 hlam B) = PhiS (Xm lam (B : Matrix (Fin 2) (Fin 2) F)) := rfl

theorem iota_injective (h2 : (2 : F) ≠ 0) (hlam : star lam * lam = -1) :
    Function.Injective (iota h2 hlam) := by
  intro B B' h
  have h1 := congrArg (mat 2 F) h
  rw [mat_iota, mat_iota] at h1
  exact Subtype.ext (Xm_injective h2 hlam (PhiS_injective h1))

theorem iota_comm_u0 (h2 : (2 : F) ≠ 0) (hlam : star lam * lam = -1) (B : SL(2, F)) :
    iota h2 hlam B * u0 F = u0 F * iota h2 hlam B := by
  apply mat_injective
  rw [map_mul, map_mul, mat_iota, mat_u0, gram_mul_PhiS]


theorem exists_unitary_of_comm (g : StatedSp 2 F) (hg : g * u0 F = u0 F * g) :
    ∃ N, mat 2 F g = PhiS N ∧ Nᴴ * N = 1 := by
  have hgc : mat 2 F g * gram F 2 = gram F 2 * mat 2 F g := by
    have := congrArg (mat 2 F) hg
    rwa [map_mul, map_mul, mat_u0] at this
  obtain ⟨N, hN⟩ := exists_PhiS_of_comm hgc
  refine ⟨N, hN.symm, ?_⟩
  have hsp := mat_transpose_mul_gram_mul g
  rw [← hN] at hsp
  exact (PhiS_symplectic_iff N).1 hsp

theorem mem_range_iota_iff (h2 : (2 : F) ≠ 0) (hlam : star lam * lam = -1) (g : StatedSp 2 F) :
    g ∈ (iota h2 hlam).range ↔
      g * u0 F = u0 F * g ∧ ∃ N, mat 2 F g = PhiS N ∧ N.det = 1 := by
  constructor
  · rintro ⟨B, rfl⟩
    exact ⟨iota_comm_u0 h2 hlam B, Xm lam B, mat_iota h2 hlam B, Xm_det h2 hlam B.2⟩
  · rintro ⟨hc, N, hN, hdet⟩
    obtain ⟨N₁, hN₁, hNN⟩ := exists_unitary_of_comm g hc
    have : N₁ = N := PhiS_injective (hN₁.symm.trans hN)
    subst this
    obtain ⟨B, hB⟩ := exists_rat_of_unitary h2 hlam hNN hdet
    exact ⟨B, mat_injective (by rw [mat_iota, hN, hB]; rfl)⟩

theorem iota_conj_of_comm (h2 : (2 : F) ≠ 0) (hlam : star lam * lam = -1) {g : StatedSp 2 F}
    (hg : g * u0 F = u0 F * g) (q : StatedSp 2 F) (hq : q ∈ (iota h2 hlam).range) :
    g * q * g⁻¹ ∈ (iota h2 hlam).range := by
  obtain ⟨hqc, N, hN, hdet⟩ := (mem_range_iota_iff h2 hlam q).1 hq
  have hg' : g⁻¹ * u0 F = u0 F * g⁻¹ := by
    have := (Commute.inv_left (show Commute g (u0 F) from hg)).eq
    exact this
  rw [mem_range_iota_iff h2 hlam]
  refine ⟨?_, ?_⟩
  · calc g * q * g⁻¹ * u0 F = g * q * (u0 F * g⁻¹) := by rw [mul_assoc, hg', ← mul_assoc]
      _ = g * (q * u0 F) * g⁻¹ := by group
      _ = g * (u0 F * q) * g⁻¹ := by rw [hqc]
      _ = (g * u0 F) * q * g⁻¹ := by group
      _ = (u0 F * g) * q * g⁻¹ := by rw [hg]
      _ = u0 F * (g * q * g⁻¹) := by group
  · obtain ⟨Ng, hNg, -⟩ := exists_unitary_of_comm g hg
    obtain ⟨Ng', hNg', -⟩ := exists_unitary_of_comm g⁻¹ hg'
    have hone : Ng * Ng' = 1 := by
      apply PhiS_injective
      rw [map_mul, ← hNg, ← hNg', ← map_mul, mul_inv_cancel, map_one, map_one]
    refine ⟨Ng * N * Ng', ?_, ?_⟩
    · rw [map_mul, map_mul, hNg, hN, hNg', map_mul, map_mul]
    · have h1 : Ng.det * Ng'.det = 1 := by rw [← Matrix.det_mul, hone, Matrix.det_one]
      rw [Matrix.det_mul, Matrix.det_mul, hdet]
      linear_combination h1

end Iota


section Inverter

@[expose] noncomputable def hInv (a b : F) (hab : a * a + b * b = -1) : SL(2, F) :=
  ⟨!![a, b; b, -a], by rw [Matrix.det_fin_two_of]; linear_combination (-1 : F) * hab⟩

theorem hInv_mul_r0 (a b : F) (hab : a * a + b * b = -1) :
    hInv a b hab * r0 = -r0 * hInv a b hab := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_neg, coe_r0]
  show !![a, b; b, -a] * !![0, 1; -1, 0] = -(!![0, 1; -1, 0]) * !![a, b; b, -a]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem hInv_conj_r0 (a b : F) (hab : a * a + b * b = -1) :
    hInv a b hab * r0 * (hInv a b hab)⁻¹ = -r0 := by
  rw [mul_inv_eq_iff_eq_mul, hInv_mul_r0]

theorem neg_one_mul_sl2 (A : SL(2, F)) : (-1 : SL(2, F)) * A = -A := by
  apply Subtype.ext
  simp

theorem c1_conj_u0 (a b : F) (hab : a * a + b * b = -1) :
    blk F (hInv a b hab) (hInv a b hab) * u0 F * (blk F (hInv a b hab) (hInv a b hab))⁻¹ =
      zneg F * u0 F := by
  rw [u0_eq_blk, zneg_eq_blk, blk_inv, blk_mul, blk_mul, hInv_conj_r0, blk_mul, neg_one_mul_sl2]

theorem mat_c1_mul_PhiS (a b : F) (hab : a * a + b * b = -1)
    (N : Matrix (Fin 2) (Fin 2) (QE F)) :
    mat 2 F (blk F (hInv a b hab) (hInv a b hab)) * PhiS N =
      PhiS (N.map star) * mat 2 F (blk F (hInv a b hab) (hInv a b hab)) := by
  rw [mat_blk]
  ext x y
  rcases x with k | k <;> rcases y with l | l <;> fin_cases k <;> fin_cases l <;>
    simp [hInv, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, PhiS_apply, PhiFun,
      Matrix.fromBlocks, Matrix.diagonal_apply] <;> ring


theorem star_det_one {N : Matrix (Fin 2) (Fin 2) (QE F)} (h : N.det = 1) :
    (N.map star).det = 1 := by
  rw [star_det, h, star_one]

end Inverter

section Layer

variable {lam : QE F}

theorem iota_conj_c1 (h2 : (2 : F) ≠ 0) (hlam : star lam * lam = -1) (a b : F)
    (hab : a * a + b * b = -1) (q : StatedSp 2 F) (hq : q ∈ (iota h2 hlam).range) :
    blk F (hInv a b hab) (hInv a b hab) * q * (blk F (hInv a b hab) (hInv a b hab))⁻¹ ∈
      (iota h2 hlam).range := by
  set c := blk F (hInv a b hab) (hInv a b hab) with hc
  obtain ⟨hqc, N, hN, hdet⟩ := (mem_range_iota_iff h2 hlam q).1 hq
  have hcu : c * u0 F * c⁻¹ = zneg F * u0 F := c1_conj_u0 a b hab
  have hz : ∀ y : StatedSp 2 F, y * zneg F = zneg F * y := fun y =>
    (Subgroup.mem_center_iff.mp zneg_mem_center y)
  have hcu' : c⁻¹ * u0 F = zneg F * u0 F * c⁻¹ := by
    have h1 : c⁻¹ * (c * u0 F * c⁻¹) * c = u0 F := by group
    rw [hcu] at h1
    have h2' : c⁻¹ * (zneg F * u0 F) * c = zneg F * (c⁻¹ * u0 F * c) := by
      calc c⁻¹ * (zneg F * u0 F) * c = (c⁻¹ * zneg F) * u0 F * c := by group
        _ = (zneg F * c⁻¹) * u0 F * c := by rw [← hz c⁻¹]
        _ = zneg F * (c⁻¹ * u0 F * c) := by group
    rw [h2'] at h1
    have h3 : c⁻¹ * u0 F * c = zneg F * u0 F := by
      have := congrArg (fun y => zneg F * y) h1
      simpa [← mul_assoc, zneg_mul_self] using this
    calc c⁻¹ * u0 F = (c⁻¹ * u0 F * c) * c⁻¹ := by group
      _ = zneg F * u0 F * c⁻¹ := by rw [h3]
  rw [mem_range_iota_iff h2 hlam]
  refine ⟨?_, ?_⟩
  · calc c * q * c⁻¹ * u0 F = c * q * (c⁻¹ * u0 F) := by group
      _ = c * q * (zneg F * u0 F * c⁻¹) := by rw [hcu']
      _ = zneg F * (c * (q * u0 F) * c⁻¹) := by
        calc c * q * (zneg F * u0 F * c⁻¹) = c * (q * zneg F) * u0 F * c⁻¹ := by group
          _ = c * (zneg F * q) * u0 F * c⁻¹ := by rw [hz q]
          _ = zneg F * (c * q * u0 F * c⁻¹) := by
            calc c * (zneg F * q) * u0 F * c⁻¹ = (c * zneg F) * q * u0 F * c⁻¹ := by group
              _ = (zneg F * c) * q * u0 F * c⁻¹ := by rw [hz c]
              _ = zneg F * (c * q * u0 F * c⁻¹) := by group
          _ = zneg F * (c * (q * u0 F) * c⁻¹) := by group
      _ = zneg F * (c * (u0 F * q) * c⁻¹) := by rw [hqc]
      _ = zneg F * ((c * u0 F * c⁻¹) * (c * q * c⁻¹)) := by group
      _ = zneg F * (zneg F * u0 F * (c * q * c⁻¹)) := by rw [hcu]
      _ = (zneg F * zneg F) * u0 F * (c * q * c⁻¹) := by group
      _ = u0 F * (c * q * c⁻¹) := by rw [zneg_mul_self, one_mul]
  · refine ⟨N.map star, ?_, star_det_one hdet⟩
    have hrel := mat_c1_mul_PhiS a b hab N
    have hone : mat 2 F c * mat 2 F c⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    calc mat 2 F (c * q * c⁻¹) = mat 2 F c * PhiS N * mat 2 F c⁻¹ := by
          rw [map_mul, map_mul, hN]
      _ = PhiS (N.map star) * (mat 2 F c * mat 2 F c⁻¹) := by rw [hrel, Matrix.mul_assoc]
      _ = PhiS (N.map star) := by rw [hone, Matrix.mul_one]


theorem c1_inv_conj_u0 (a b : F) (hab : a * a + b * b = -1) :
    (blk F (hInv a b hab) (hInv a b hab))⁻¹ * u0 F * blk F (hInv a b hab) (hInv a b hab) =
      zneg F * u0 F := by
  rw [u0_eq_blk, zneg_eq_blk, blk_inv, blk_mul, blk_mul]
  have h1 : (hInv a b hab)⁻¹ * r0 * hInv a b hab = -r0 := by
    have : r0 * hInv a b hab = hInv a b hab * (-r0) := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_neg, coe_r0]
      show !![0, 1; -1, 0] * !![a, b; b, -a] = !![a, b; b, -a] * (-(!![0, 1; -1, 0]))
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [mul_assoc, this, inv_mul_cancel_left]
  rw [h1, blk_mul, neg_one_mul_sl2]

theorem t0_mem_range (h2 : (2 : F) ≠ 0) (hlam : star lam * lam = -1) :
    t0 F ∈ (iota h2 hlam).range := by
  rw [mem_range_iota_iff h2 hlam]
  refine ⟨?_, !![omE, 0; 0, -omE], ?_, ?_⟩
  · calc t0 F * u0 F = x0 F * u0 F * u0 F := rfl
      _ = u0 F * x0 F * u0 F := by rw [x0_mul_u0]
      _ = u0 F * t0 F := by rw [t0]; group
  · rw [t0_eq_blk, mat_blk]
    ext x y
    rcases x with k | k <;> rcases y with l | l <;> fin_cases k <;> fin_cases l <;>
      simp [PhiS_apply, PhiFun, omE, coe_r0, Matrix.fromBlocks, Matrix.diagonal_apply]
  · rw [Matrix.det_fin_two_of]
    have := omE_mul_self (F := F)
    linear_combination (-1 : QE F) * this


theorem slayer_u0 [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    (hlam : star lam * lam = -1) : SLayer (u0 F) (iota h2 hlam).range := by
  have hq : CFSG.IsQuasisimple SL(2, F) := isQuasisimple_sl2 h4
  have hperf : Group.IsPerfect (iota h2 hlam).range := by
    have : Group.IsPerfect SL(2, F) := hq.1
    exact Group.IsPerfect.range (iota h2 hlam)
  obtain ⟨a, b, hab⟩ := exists_sq_add_sq h2 (-1 : F)
  refine ⟨fun p hp => ((mem_range_iota_iff h2 hlam p).1 hp).1, ?_,
    (Subgroup.commutator_eq_self (H := (iota h2 hlam).range)).symm.le, ?_⟩
  · intro g hg p hp
    rcases conj_cases (u0 F) g (zneg F) u0_mul_self (Or.inr rfl) hg with h | h
    · exact iota_conj_of_comm h2 hlam (mul_inv_eq_iff_eq_mul.mp h) p hp
    · set c := blk F (hInv a b hab) (hInv a b hab) with hc
      have hcu : c⁻¹ * u0 F * c = zneg F * u0 F := c1_inv_conj_u0 a b hab
      have hz : ∀ y : StatedSp 2 F, y * zneg F = zneg F * y := fun y =>
        (Subgroup.mem_center_iff.mp zneg_mem_center y)
      have hg' : (c⁻¹ * g) * u0 F = u0 F * (c⁻¹ * g) := by
        have h1 : g * u0 F = zneg F * u0 F * g := by
          have := mul_inv_eq_iff_eq_mul.mp h
          exact this
        calc c⁻¹ * g * u0 F = c⁻¹ * (zneg F * u0 F * g) := by rw [mul_assoc, h1, mul_assoc]
          _ = (c⁻¹ * zneg F) * u0 F * g := by group
          _ = (zneg F * c⁻¹) * u0 F * g := by rw [← hz c⁻¹]
          _ = zneg F * (c⁻¹ * u0 F) * g := by group
          _ = zneg F * (c⁻¹ * u0 F * c) * c⁻¹ * g := by group
          _ = zneg F * (zneg F * u0 F) * c⁻¹ * g := by rw [hcu]
          _ = u0 F * (c⁻¹ * g) := by
            calc zneg F * (zneg F * u0 F) * c⁻¹ * g = (zneg F * zneg F) * u0 F * (c⁻¹ * g) := by
                  group
              _ = u0 F * (c⁻¹ * g) := by rw [zneg_mul_self, one_mul]
      have h1 := iota_conj_of_comm h2 hlam hg' p hp
      have h2' := iota_conj_c1 h2 hlam a b hab _ h1
      have e : c * (c⁻¹ * g * p * (c⁻¹ * g)⁻¹) * c⁻¹ = g * p * g⁻¹ := by group
      rwa [e] at h2'
  · refine ⟨{(iota h2 hlam).range}, ?_, ?_⟩
    · intro H hH
      rw [Set.mem_singleton_iff] at hH
      subst hH
      refine ⟨le_rfl,
        isQuasisimple_of_equiv (MonoidHom.ofInjective (iota_injective h2 hlam)) hq, ?_⟩
      intro p hp h hh
      exact (iota h2 hlam).range.mul_mem ((iota h2 hlam).range.mul_mem hp hh)
        ((iota h2 hlam).range.inv_mem hp)
    · exact le_iSup₂_of_le _ rfl le_rfl

theorem exists_layer_u0 [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) :
    ∃ Q : Subgroup (StatedSp 2 F), SLayer (u0 F) Q ∧ t0 F ∈ Q := by
  obtain ⟨lam, hlam⟩ := exists_lam h2
  exact ⟨_, slayer_u0 h2 h4 hlam, t0_mem_range h2 hlam⟩

end Layer


end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp
