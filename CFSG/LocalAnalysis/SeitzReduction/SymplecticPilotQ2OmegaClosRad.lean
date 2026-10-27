module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaClosAut
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaClosFix

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (upperUnipotentSp)

variable {K : Type} [Field K] {N j : ℕ}

theorem upperUnipotentSp_inj_lag {X Y : Matrix (Fin N) (Fin N) K} (hX : Xᵀ = X) (hY : Yᵀ = Y)
    (h : upperUnipotentSp N K hX = upperUnipotentSp N K hY) : X = Y := by
  have h1 := congrArg (mat N K) h
  rw [mat_upperUnipotentSp, mat_upperUnipotentSp, fromBlocks_inj] at h1
  exact h1.2.1

section Theta

variable (θ : centralizer ({spARep N j} : Set (StatedSp N K)) ≃*
    centralizer ({spARep N j} : Set (StatedSp N K)))

open Classical in
@[expose] noncomputable def lagRadMap (X : Matrix (Fin N) (Fin N) K) :
    Matrix (Fin N) (Fin N) K :=
  if hX : Xᵀ = X then
    (mat N K (θ ⟨upperUnipotentSp N K hX, upperUnipotentSp_mem_centralizer_spARep hX⟩ :
      StatedSp N K)).toBlocks₁₂
  else 0

theorem lagRadMap_eq {X : Matrix (Fin N) (Fin N) K} (hX : Xᵀ = X) :
    lagRadMap θ X = (mat N K (θ ⟨upperUnipotentSp N K hX,
      upperUnipotentSp_mem_centralizer_spARep hX⟩ : StatedSp N K)).toBlocks₁₂ := by
  rw [lagRadMap, dite_eq_left hX]

variable [CharP K 2] (hjN : 2 * j = N) (hθπ : ∀ g, spLagProj hjN (θ g) = spLagProj hjN g)
include hθπ

theorem lagTheta_mem_spARadical {g : centralizer ({spARep N j} : Set (StatedSp N K))}
    (hg : (g : StatedSp N K) ∈ spARadical K N j hjN.le) :
    (θ g : StatedSp N K) ∈ spARadical K N j hjN.le := by
  rw [← spLagProj_eq_one_iff hjN, hθπ, spLagProj_eq_one_iff hjN]
  exact hg

theorem lagTheta_mul_inv_mem_spARadical (g : centralizer ({spARep N j} : Set (StatedSp N K))) :
    ((θ g * g⁻¹ : centralizer ({spARep N j} : Set (StatedSp N K))) : StatedSp N K) ∈
      spARadical K N j hjN.le := by
  rw [← spLagProj_eq_one_iff hjN, map_mul, map_inv, hθπ, mul_inv_cancel]

theorem lagTheta_conj_eq (g r : centralizer ({spARep N j} : Set (StatedSp N K)))
    (hr : (r : StatedSp N K) ∈ spARadical K N j hjN.le) :
    θ (g * r * g⁻¹) = g * θ r * g⁻¹ := by
  set q := θ g * g⁻¹ with hq
  have hqR := lagTheta_mul_inv_mem_spARadical θ hjN hθπ g
  have hgr : ((g * θ r * g⁻¹ : centralizer ({spARep N j} : Set (StatedSp N K))) :
      StatedSp N K) ∈ spARadical K N j hjN.le := by
    rw [← spLagProj_eq_one_iff hjN, map_mul, map_mul, map_inv, hθπ,
      (spLagProj_eq_one_iff hjN r).2 hr, mul_one, mul_inv_cancel]
  have hcomm : q * (g * θ r * g⁻¹) = (g * θ r * g⁻¹) * q :=
    Subtype.ext (spARadical_commute hjN hqR hgr)
  have hθg : θ g = q * g := by rw [hq, inv_mul_cancel_right]
  rw [map_mul, map_mul, map_inv, hθg]
  calc q * g * θ r * (q * g)⁻¹ = (q * (g * θ r * g⁻¹)) * q⁻¹ := by group
    _ = g * θ r * g⁻¹ := by rw [hcomm]; group

theorem lagRadMap_spec {X : Matrix (Fin N) (Fin N) K} (hX : Xᵀ = X) :
    ∃ hY : (lagRadMap θ X)ᵀ = lagRadMap θ X,
      (θ ⟨upperUnipotentSp N K hX, upperUnipotentSp_mem_centralizer_spARep hX⟩ :
        StatedSp N K) = upperUnipotentSp N K hY := by
  have hmem := lagTheta_mem_spARadical θ hjN hθπ
    (g := ⟨upperUnipotentSp N K hX, upperUnipotentSp_mem_centralizer_spARep hX⟩)
    (upperUnipotentSp_mem_spARadical hjN hX)
  obtain ⟨Y, hY, hYe⟩ := (mem_spARadical_iff_eq_upperUnipotentSp hjN).1 hmem
  have hF : lagRadMap θ X = Y := by
    rw [lagRadMap_eq θ hX, hYe, mat_upperUnipotentSp, toBlocks_fromBlocks₁₂]
  subst hF
  exact ⟨hY, hYe⟩

theorem lagRadMap_transpose {X : Matrix (Fin N) (Fin N) K} (hX : Xᵀ = X) :
    (lagRadMap θ X)ᵀ = lagRadMap θ X :=
  (lagRadMap_spec θ hjN hθπ hX).1

theorem lagRadMap_add {X Y : Matrix (Fin N) (Fin N) K} (hX : Xᵀ = X) (hY : Yᵀ = Y) :
    lagRadMap θ (X + Y) = lagRadMap θ X + lagRadMap θ Y := by
  have hXY : (X + Y)ᵀ = X + Y := by rw [transpose_add, hX, hY]
  obtain ⟨h1, e1⟩ := lagRadMap_spec θ hjN hθπ hX
  obtain ⟨h2, e2⟩ := lagRadMap_spec θ hjN hθπ hY
  obtain ⟨h3, e3⟩ := lagRadMap_spec θ hjN hθπ hXY
  have hmul : (⟨upperUnipotentSp N K hXY, upperUnipotentSp_mem_centralizer_spARep hXY⟩ :
      centralizer ({spARep N j} : Set (StatedSp N K))) =
      ⟨upperUnipotentSp N K hX, upperUnipotentSp_mem_centralizer_spARep hX⟩ *
        ⟨upperUnipotentSp N K hY, upperUnipotentSp_mem_centralizer_spARep hY⟩ :=
    Subtype.ext (upperUnipotentSp_mul hX hY).symm
  rw [hmul, map_mul, Subgroup.coe_mul, e1, e2, upperUnipotentSp_mul] at e3
  exact upperUnipotentSp_inj_lag h3 _ e3.symm

theorem lagRadMap_eq_zero {X : Matrix (Fin N) (Fin N) K} (hX : Xᵀ = X)
    (h : lagRadMap θ X = 0) : X = 0 := by
  obtain ⟨h1, e1⟩ := lagRadMap_spec θ hjN hθπ hX
  have e2 : upperUnipotentSp N K h1 = upperUnipotentSp N K (C := 0) transpose_zero :=
    upperUnipotentSp_congr _ _ h
  rw [upperUnipotentSp_zero] at e2
  rw [e2] at e1
  have e3 : (⟨upperUnipotentSp N K hX, upperUnipotentSp_mem_centralizer_spARep hX⟩ :
      centralizer ({spARep N j} : Set (StatedSp N K))) = 1 :=
    θ.injective (by rw [map_one]; exact Subtype.ext e1)
  have e4 : upperUnipotentSp N K hX = upperUnipotentSp N K (C := 0) transpose_zero := by
    rw [upperUnipotentSp_zero]
    exact congrArg Subtype.val e3
  exact upperUnipotentSp_inj_lag hX _ e4

theorem lagRadMap_spARepMat
    (hθa : θ ⟨spARep N j, mem_centralizer_singleton_iff.2 rfl⟩ =
      ⟨spARep N j, mem_centralizer_singleton_iff.2 rfl⟩) :
    lagRadMap θ (spARepMat N j) = spARepMat N j := by
  obtain ⟨h1, e1⟩ := lagRadMap_spec θ hjN hθπ (spARepMat_transpose (K := K) N j)
  have e2 : (⟨upperUnipotentSp N K (spARepMat_transpose (K := K) N j),
      upperUnipotentSp_mem_centralizer_spARep (spARepMat_transpose (K := K) N j)⟩ :
        centralizer ({spARep N j} : Set (StatedSp N K))) =
      ⟨spARep N j, mem_centralizer_singleton_iff.2 rfl⟩ := rfl
  rw [e2, hθa] at e1
  exact (upperUnipotentSp_inj_lag h1 _ e1.symm)

theorem lagRadMap_conj (T : GL (Fin N) K)
    (hT : (T : Matrix (Fin N) (Fin N) K) * spARepMat N j * (T : Matrix (Fin N) (Fin N) K)ᵀ =
      spARepMat N j)
    {X : Matrix (Fin N) (Fin N) K} (hX : Xᵀ = X) :
    lagRadMap θ ((T : Matrix (Fin N) (Fin N) K) * X * (T : Matrix (Fin N) (Fin N) K)ᵀ) =
      (T : Matrix (Fin N) (Fin N) K) * lagRadMap θ X * (T : Matrix (Fin N) (Fin N) K)ᵀ := by
  have hℓ := leviEmbedGL_mem_centralizer_spARep hT
  set ℓ : centralizer ({spARep N j} : Set (StatedSp N K)) := ⟨leviEmbedGL K N T, hℓ⟩
  have hTX := transpose_mul_mul_transpose (T : Matrix (Fin N) (Fin N) K) hX
  obtain ⟨h1, e1⟩ := lagRadMap_spec θ hjN hθπ hX
  obtain ⟨h2, e2⟩ := lagRadMap_spec θ hjN hθπ hTX
  have hconj : (⟨upperUnipotentSp N K hTX, upperUnipotentSp_mem_centralizer_spARep hTX⟩ :
      centralizer ({spARep N j} : Set (StatedSp N K))) =
      ℓ * ⟨upperUnipotentSp N K hX, upperUnipotentSp_mem_centralizer_spARep hX⟩ * ℓ⁻¹ :=
    Subtype.ext (leviEmbedGL_conj_upperUnipotentSp T hX).symm
  rw [hconj, lagTheta_conj_eq θ hjN hθπ _ _ (upperUnipotentSp_mem_spARadical hjN hX),
    Subgroup.coe_mul, Subgroup.coe_mul, e1, Subgroup.coe_inv,
    leviEmbedGL_conj_upperUnipotentSp] at e2
  exact upperUnipotentSp_inj_lag h2 _ e2.symm

theorem lagTheta_upperUnipotentSp_plane (hK : Nat.card K = 2)
    (hθa : θ ⟨spARep N j, mem_centralizer_singleton_iff.2 rfl⟩ =
      ⟨spARep N j, mem_centralizer_singleton_iff.2 rfl⟩)
    (i0 : Fin N) {x y : Fin N → K} (hx : x (spAPar i0) = 0) (hy : y (spAPar i0) = 0)
    (hP : (vecMulVec x y + vecMulVec y x)ᵀ = vecMulVec x y + vecMulVec y x) :
    θ ⟨upperUnipotentSp N K hP, upperUnipotentSp_mem_centralizer_spARep hP⟩ =
      ⟨upperUnipotentSp N K hP, upperUnipotentSp_mem_centralizer_spARep hP⟩ := by
  have hF := lagModule_eq hjN hK i0 (lagRadMap θ) (fun X hX => lagRadMap_transpose θ hjN hθπ hX)
    (fun X Y hX hY => lagRadMap_add θ hjN hθπ hX hY)
    (fun X hX h => lagRadMap_eq_zero θ hjN hθπ hX h) (lagRadMap_spARepMat θ hjN hθπ hθa)
    (fun w X hX => lagRadMap_conj θ hjN hθπ (lagTvUnit hjN w) (lagTv_conj_spARepMat hjN w) hX)
    hx hy
  obtain ⟨h1, e1⟩ := lagRadMap_spec θ hjN hθπ hP
  exact Subtype.ext (e1.trans (upperUnipotentSp_congr _ _ hF))

end Theta

end CFSG.SeitzReduction.SymplecticPilot
