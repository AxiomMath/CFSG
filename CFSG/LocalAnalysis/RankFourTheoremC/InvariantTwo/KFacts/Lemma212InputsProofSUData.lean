module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryIsometry

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Subgroup Matrix CFSG.Open
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)
open CFSG.LieType.Universal.Unitary (conjTr conjTr_mul conjTr_one SUid mem_SUid)
open CFSG.ComponentClassification.CatalogueBUnitaryIsometry (Uid mem_Uid_iff)

section Unitary

variable {n r f : ℕ} [Fact r.Prime] {K : Type} [Field K] [Finite K] [CharP K r]

theorem l212in_conjTr_conjTr (hK : Nat.card K = (r ^ f) ^ 2) (A : Matrix (Fin n) (Fin n) K) :
    conjTr (unitaryInvolution K r f) (conjTr (unitaryInvolution K r f) A) = A := by
  ext i j
  simp only [conjTr, transpose_apply, map_apply]
  exact unitaryInvolution_involutive hK (A i j)

theorem l212in_inv_eq_conjTr {B : GL (Fin n) K}
    (hB : conjTr (unitaryInvolution K r f) (B : Matrix (Fin n) (Fin n) K) *
      (B : Matrix (Fin n) (Fin n) K) = 1) :
    ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      conjTr (unitaryInvolution K r f) (B : Matrix (Fin n) (Fin n) K) := by
  have h1 : (B : Matrix (Fin n) (Fin n) K) *
      conjTr (unitaryInvolution K r f) (B : Matrix (Fin n) (Fin n) K) = 1 :=
    mul_eq_one_comm.1 hB
  calc ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((B : Matrix (Fin n) (Fin n) K) *
          conjTr (unitaryInvolution K r f) (B : Matrix (Fin n) (Fin n) K)) := by
        rw [h1, Matrix.mul_one]
    _ = conjTr (unitaryInvolution K r f) (B : Matrix (Fin n) (Fin n) K) := by
        rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem l212in_conj_mem_statedSU (hK : Nat.card K = (r ^ f) ^ 2) {B : GL (Fin n) K}
    (hB : B ∈ Uid (unitaryInvolution K r f) n) {g : GL (Fin n) K}
    (hg : g ∈ StatedSU n (r ^ f) K) : B * g * B⁻¹ ∈ StatedSU n (r ^ f) K := by
  rw [mem_Uid_iff] at hB
  rw [← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK n] at hg ⊢
  obtain ⟨hdet, hiso⟩ := mem_SUid.1 hg
  have hBinv := l212in_inv_eq_conjTr hB
  have hBB' : conjTr (unitaryInvolution K r f) ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) := by
    rw [hBinv]
    exact l212in_conjTr_conjTr hK _
  have hinvB : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (B : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hBinvB : (B : Matrix (Fin n) (Fin n) K) *
      ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine mem_SUid.2 ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdet, mul_one,
      ← Matrix.det_mul, hBinvB, Matrix.det_one]
  · rw [Units.val_mul, Units.val_mul, conjTr_mul, conjTr_mul, hBB', ← hBinv]
    calc (B : Matrix (Fin n) (Fin n) K) *
          (conjTr (unitaryInvolution K r f) (g : Matrix (Fin n) (Fin n) K) *
            ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
          ((B : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) *
            ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        = (B : Matrix (Fin n) (Fin n) K) *
          (conjTr (unitaryInvolution K r f) (g : Matrix (Fin n) (Fin n) K) *
            (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (B : Matrix (Fin n) (Fin n) K)) * (g : Matrix (Fin n) (Fin n) K)) *
          ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hinvB, Matrix.mul_one, hiso, Matrix.mul_one, hBinvB]

@[expose] def l212in_suConj (hK : Nat.card K = (r ^ f) ^ 2)
    (B : Uid (unitaryInvolution K r f) n) : MulAut (StatedSU n (r ^ f) K) where
  toFun g := ⟨(B : GL (Fin n) K) * g * (B : GL (Fin n) K)⁻¹,
    l212in_conj_mem_statedSU hK B.2 g.2⟩
  invFun g := ⟨(B : GL (Fin n) K)⁻¹ * g * (B : GL (Fin n) K)⁻¹⁻¹, by
    have := l212in_conj_mem_statedSU hK (B⁻¹).2 g.2
    simpa using this⟩
  left_inv g := Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  right_inv g := Subtype.ext (by simp only [Subgroup.coe_mul]; group)
  map_mul' g h := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem l212in_suConj_coe (hK : Nat.card K = (r ^ f) ^ 2) (B : Uid (unitaryInvolution K r f) n)
    (g : StatedSU n (r ^ f) K) :
    ((l212in_suConj hK B g : StatedSU n (r ^ f) K) : GL (Fin n) K) =
      (B : GL (Fin n) K) * g * (B : GL (Fin n) K)⁻¹ := rfl

theorem l212in_conj_scalar (B : GL (Fin n) K) (c : Kˣ) :
    B * GeneralLinearGroup.scalar (Fin n) c * B⁻¹ = GeneralLinearGroup.scalar (Fin n) c := by
  have h : GeneralLinearGroup.scalar (Fin n) c ∈ Subgroup.center (GL (Fin n) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  rw [Subgroup.mem_center_iff.1 h B, mul_inv_cancel_right]

theorem l212in_suConj_map (hK : Nat.card K = (r ^ f) ^ 2) (B : Uid (unitaryInvolution K r f) n) :
    ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (r ^ f) K)).map
      (l212in_suConj hK B : StatedSU n (r ^ f) K →* StatedSU n (r ^ f) K) =
    (StatedScalars (Fin n) K).subgroupOf (StatedSU n (r ^ f) K) := by
  have hfix : ∀ g ∈ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (r ^ f) K),
      l212in_suConj hK B g = g := by
    intro g hg
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hg
    apply Subtype.ext
    rw [l212in_suConj_coe, ← hc, l212in_conj_scalar]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hfix y hy).symm ▸ hy
  · intro hx
    exact ⟨x, hx, hfix x hx⟩

@[expose] def l212in_suPhi (hK : Nat.card K = (r ^ f) ^ 2) :
    Uid (unitaryInvolution K r f) n →*
      MulAut (StatedProj (StatedSU n (r ^ f) K)) where
  toFun B := QuotientGroup.congr _ _ (l212in_suConj hK B) (l212in_suConj_map hK B)
  map_one' := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [QuotientGroup.congr_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext (by simp [l212in_suConj_coe]))
  map_mul' B B' := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk, QuotientGroup.congr_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext (by
      simp only [l212in_suConj_coe, Subgroup.coe_mul, _root_.mul_inv_rev]
      group))

theorem l212in_suPhi_mk (hK : Nat.card K = (r ^ f) ^ 2) (B : Uid (unitaryInvolution K r f) n)
    (g : StatedSU n (r ^ f) K) :
    l212in_suPhi hK B (QuotientGroup.mk g) = QuotientGroup.mk (l212in_suConj hK B g) :=
  QuotientGroup.congr_mk _ _ _ (l212in_suConj_map hK B) g

theorem l212in_det_unitary (B : Uid (unitaryInvolution K r f) n) :
    GeneralLinearGroup.det (B : GL (Fin n) K) ^ (r ^ f + 1) = 1 := by
  have h1 := congrArg Matrix.det ((mem_Uid_iff _ _ _).1 B.2)
  rw [Matrix.det_mul, Matrix.det_one] at h1
  have h2 : Matrix.det (conjTr (unitaryInvolution K r f) (B : GL (Fin n) K).val) =
      unitaryInvolution K r f (Matrix.det (B : GL (Fin n) K).val) := by
    rw [conjTr, Matrix.det_transpose]
    exact ((unitaryInvolution K r f : K →+* K).map_det _).symm
  rw [h2, unitaryInvolution_apply] at h1
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ]
  simpa [GeneralLinearGroup.val_det_apply] using h1

@[expose] def l212in_detU :
    Uid (unitaryInvolution K r f) n →* rootsOfUnity (r ^ f + 1) K where
  toFun B := ⟨GeneralLinearGroup.det (B : GL (Fin n) K),
    (mem_rootsOfUnity _ _).2 (l212in_det_unitary B)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' B B' := Subtype.ext (by simp)

theorem l212in_scalar_mem_Uid_iff (hn : 1 ≤ n) (c : Kˣ) :
    GeneralLinearGroup.scalar (Fin n) c ∈ Uid (unitaryInvolution K r f) n ↔
      c ^ (r ^ f + 1) = 1 := by
  rw [mem_Uid_iff]
  have hscal : ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal (fun _ => (c : K)) := by
    rw [GeneralLinearGroup.coe_scalar, scalar_apply]
  have key : ∀ a : Kˣ, (diagonal (fun _ : Fin n => (a : K)) : Matrix (Fin n) (Fin n) K) = 1 ↔
      a = 1 := by
    intro a
    constructor
    · intro h
      have h1 := congrFun (congrFun h ⟨0, hn⟩) ⟨0, hn⟩
      rw [diagonal_apply_eq, one_apply_eq] at h1
      exact Units.ext h1
    · rintro rfl
      simp
  have hm : conjTr (unitaryInvolution K r f)
      ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal (fun _ => ((c ^ (r ^ f + 1) : Kˣ) : K)) := by
    rw [hscal, conjTr, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [unitaryInvolution_apply, Units.val_pow_eq_pow_val, pow_succ]
  rw [hm]
  exact key _

theorem l212in_scalar_unitary (hn : 1 ≤ n) {c : Kˣ}
    (h : GeneralLinearGroup.scalar (Fin n) c ∈ Uid (unitaryInvolution K r f) n) :
    c ^ (r ^ f + 1) = 1 := (l212in_scalar_mem_Uid_iff hn c).1 h

end Unitary

end CFSG.LocalAnalysis.RankFourTheoremC
