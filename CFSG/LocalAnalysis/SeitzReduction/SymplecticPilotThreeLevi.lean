module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeModel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_elt elt E)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp coe_fieldSp)

variable {K : Type} [Field K]

theorem fieldSp_diagSp_const {n : ℕ} (σ : K ≃+* K) (r : Kˣ) :
    fieldSp n K σ (diagSp K n fun _ => r) = diagSp K n fun _ => Units.map (σ : K →* K) r := by
  apply mat_injective
  change (mat n K (diagSp K n fun _ => r)).map σ = _
  rw [mat_diagSp, mat_diagSp, diagonal_map (map_zero σ)]
  congr 1
  funext a
  rcases a with i | i
  · simp [diagSpEntry]
  · simp [diagSpEntry, map_inv₀]

section F5

variable [Finite K] [CharP K 2]

theorem exists_conj_fieldSp_of_inv_mul_mem
    (β : (transvRadical K (1 : Fin 3) ⊔ complSp K (1 : Fin 3) : Subgroup (StatedSp 3 K)) ≃*
      (transvRadical K (1 : Fin 3) ⊔ complSp K (1 : Fin 3) : Subgroup (StatedSp 3 K)))
    (hβ : ((transvRadical K (1 : Fin 3)).subgroupOf
      (transvRadical K (1 : Fin 3) ⊔ complSp K (1 : Fin 3))).map β.toMonoidHom =
        (transvRadical K (1 : Fin 3)).subgroupOf
          (transvRadical K (1 : Fin 3) ⊔ complSp K (1 : Fin 3)))
    (ι : complSp K (1 : Fin 3) ≃* complSp K (1 : Fin 3))
    (hι : ∀ m : complSp K (1 : Fin 3), ((ι m : complSp K (1 : Fin 3)) : StatedSp 3 K)⁻¹ *
      (β (inclusion le_sup_right m) : StatedSp 3 K) ∈ transvRadical K (1 : Fin 3)) :
    ∃ (s : StatedSp 2 K) (σ : K ≃+* K), ∀ g : StatedSp 2 K,
      ι (complSpEquiv (K := K) (m := 2) 1 g) =
        complSpEquiv (K := K) (m := 2) 1 (s * fieldSp 2 K σ g * s⁻¹) := by
  obtain ⟨α, hαdef⟩ : ∃ α : MulAut (StatedSp 2 K),
      α = (complSpEquiv (K := K) (m := 2) 1).trans
        (ι.trans (complSpEquiv (K := K) (m := 2) 1).symm) :=
    ⟨_, rfl⟩
  have hιE : ∀ (m : complSp K (1 : Fin 3)) (g : StatedSp 2 K),
      (m : StatedSp 3 K) = (complSpEquiv (K := K) (m := 2) 1 g : StatedSp 3 K) →
      (ι m : StatedSp 3 K) = (complSpEquiv (K := K) (m := 2) 1 (α g) : StatedSp 3 K) := by
    intro m g hmg
    have hm : m = complSpEquiv (K := K) (m := 2) 1 g := Subtype.ext hmg
    subst hm
    rw [hαdef, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  have hs : (1 : Fin 3).succAbove (0 : Fin 2) = 0 := by decide
  have hJE : ∀ x : StatedSp 3 K, x ∈ longRootSp2 K 3 0 ↔
      ∃ g ∈ longRootSp2 K 2 0, (complSpEquiv (K := K) (m := 2) 1 g : StatedSp 3 K) = x := by
    intro x
    have h0 := map_complSpEquiv_longRootSp2 (K := K) (m := 2) 1 0
    rw [hs] at h0
    rw [← h0]
    constructor
    · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  obtain ⟨s, σ, h | h⟩ := F4Pilot.exists_eq_conj_mul_fieldSp_tauSp α
  · refine ⟨s, σ, fun g => Subtype.ext ?_⟩
    rw [hιE _ g rfl, h g]
  ·
    exfalso
    have hq₀Q := siegPair_one_two_mem_transvRadical (K := K)
    obtain ⟨qq, hqq⟩ : ∃ qq : (transvRadical K (1 : Fin 3) ⊔ complSp K (1 : Fin 3) :
        Subgroup (StatedSp 3 K)), (qq : StatedSp 3 K) = siegPair K (1 : Fin 3) 2 1 :=
      ⟨⟨_, mem_sup_left hq₀Q⟩, rfl⟩
    obtain ⟨X, hX⟩ : ∃ X : StatedSp 3 K, X = (β qq : StatedSp 3 K) := ⟨_, rfl⟩
    have hXQ : X ∈ transvRadical K (1 : Fin 3) := by
      rw [hX]
      exact (EPilot.coe_mem_iff_of_map_eq hβ qq).2 (by rw [hqq]; exact hq₀Q)
    have key : ∀ g ∈ longRootSp2 K 2 0, bRowT X = Matrix.vecMul (bRowT X) (mat 2 K (α g)) := by
      intro g hg
      obtain ⟨jm, hjm⟩ : ∃ jm : complSp K (1 : Fin 3),
          (jm : StatedSp 3 K) = (complSpEquiv (K := K) (m := 2) 1 g : StatedSp 3 K) :=
        ⟨_, rfl⟩
      have hjJ : (jm : StatedSp 3 K) ∈ longRootSp2 K 3 0 := (hJE _).2 ⟨g, hg, hjm.symm⟩
      obtain ⟨B, hB⟩ : ∃ B : StatedSp 3 K,
          B = (β (inclusion le_sup_right jm) : StatedSp 3 K) := ⟨_, rfl⟩
      have hβc : B * X = X * B := by
        have hcomm : inclusion le_sup_right jm * qq = qq * inclusion le_sup_right jm := by
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inclusion, hqq]
          exact commute_siegPair_one_two hjJ
        rw [hB, hX, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hcomm]
      obtain ⟨A, hA⟩ : ∃ A : StatedSp 3 K, A = (ι jm : StatedSp 3 K) := ⟨_, rfl⟩
      have hdQ : A⁻¹ * B ∈ transvRadical K (1 : Fin 3) := by
        rw [hA, hB]
        exact hι jm
      have hrel : A * ((A⁻¹ * B) * X * (A⁻¹ * B)⁻¹) = X * A := by
        calc A * ((A⁻¹ * B) * X * (A⁻¹ * B)⁻¹) = (B * X) * B⁻¹ * A := by group
          _ = X * A := by rw [hβc]; group
      have hAS : A ∈ complSp K (1 : Fin 3) := by
        rw [hA]
        exact (ι jm).2
      have h1 := bRowT_mul_left hAS ((A⁻¹ * B) * X * (A⁻¹ * B)⁻¹)
      have h2 := bRowT_conj hdQ hXQ
      have h3 : bRowT (X * A) = Matrix.vecMul (bRowT X) (mat 2 K (α g)) := by
        rw [hA, hιE jm g hjm, coe_complSpEquiv_apply]
        exact bRowT_mul_spEmbed X (α g)
      calc bRowT X = bRowT ((A⁻¹ * B) * X * (A⁻¹ * B)⁻¹) := h2.symm
        _ = bRowT (A * ((A⁻¹ * B) * X * (A⁻¹ * B)⁻¹)) := h1.symm
        _ = bRowT (X * A) := by rw [hrel]
        _ = Matrix.vecMul (bRowT X) (mat 2 K (α g)) := h3
    have hfix : bRowT X = 0 := by
      have hA := key _ (elt_positiveLong_mem_longRootSp2 0 1)
      have hB := key _ (elt_negativeLong_mem_longRootSp2 0 1)
      rw [h, F4Pilot.tauSp_elt, F4Pilot.fieldSp_elt, one_pow, map_one] at hA hB
      have hτA : F4Pilot.tauIdx (.positiveLong (0 : Fin 2)) = .positiveSum 0 1 (by decide) := rfl
      have hτB : F4Pilot.tauIdx (.negativeLong (0 : Fin 2)) = .negativeSum 0 1 (by decide) := rfl
      rw [hτA] at hA
      rw [hτB] at hB
      have hw0 := eq_zero_of_vecMul_elt_sum (vecMul_mat_conj hA) (vecMul_mat_conj hB)
      have hs2 : mat 2 K s * mat 2 K s⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      calc bRowT X = Matrix.vecMul (bRowT X) (mat 2 K s * mat 2 K s⁻¹) := by
            rw [hs2, Matrix.vecMul_one]
        _ = Matrix.vecMul (Matrix.vecMul (bRowT X) (mat 2 K s)) (mat 2 K s⁻¹) := by
            rw [Matrix.vecMul_vecMul]
        _ = 0 := by rw [hw0, Matrix.zero_vecMul]
    have hXZ := eq_siegDiag_of_bRowT_eq_zero hXQ hfix
    have hΛC : transvRadical K (1 : Fin 3) ⊔ complSp K (1 : Fin 3) ≤
        centralizer ({siegDiag K (1 : Fin 3) 1} : Set (StatedSp 3 K)) :=
      sup_le transvRadical_le_centralizer complSp_le_centralizer_siegDiag
    have hcen : ∀ y : (transvRadical K (1 : Fin 3) ⊔ complSp K (1 : Fin 3) :
        Subgroup (StatedSp 3 K)), qq * y = y * qq := by
      intro y
      apply β.injective
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, ← hX, hXZ]
      exact (commute_siegDiag_of_mem_centralizer (hΛC (β y).2) _).symm
    have hrow : ∀ g : StatedSp 2 K, bRowT (siegPair K (1 : Fin 3) 2 1) =
        Matrix.vecMul (bRowT (siegPair K (1 : Fin 3) 2 1)) (mat 2 K g) := by
      intro g
      have hEg := (complSpEquiv (K := K) (m := 2) 1 g).2
      have hc : siegPair K (1 : Fin 3) 2 1 *
          (complSpEquiv (K := K) (m := 2) 1 g : StatedSp 3 K) =
          (complSpEquiv (K := K) (m := 2) 1 g : StatedSp 3 K) * siegPair K (1 : Fin 3) 2 1 := by
        have h' := congrArg Subtype.val (hcen ⟨_, mem_sup_right hEg⟩)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hqq] at h'
        exact h'
      calc bRowT (siegPair K (1 : Fin 3) 2 1) =
          bRowT ((complSpEquiv (K := K) (m := 2) 1 g : StatedSp 3 K) *
            siegPair K (1 : Fin 3) 2 1) := (bRowT_mul_left hEg _).symm
        _ = bRowT (siegPair K (1 : Fin 3) 2 1 *
            (complSpEquiv (K := K) (m := 2) 1 g : StatedSp 3 K)) := by rw [hc]
        _ = Matrix.vecMul (bRowT (siegPair K (1 : Fin 3) 2 1)) (mat 2 K g) := by
            rw [coe_complSpEquiv_apply]
            exact bRowT_mul_spEmbed _ g
    have h0 := eq_zero_of_vecMul_elt_sum (hrow _).symm (hrow _).symm
    have h1 := congrFun h0 (Sum.inr 1)
    rw [bRowT_siegPair_one_two, Pi.zero_apply] at h1
    exact one_ne_zero h1

theorem exists_mem_complSp_conj_threeTorus
    (β : (transvRadical K (1 : Fin 3) ⊔ complSp K (1 : Fin 3) : Subgroup (StatedSp 3 K)) ≃*
      (transvRadical K (1 : Fin 3) ⊔ complSp K (1 : Fin 3) : Subgroup (StatedSp 3 K)))
    (hβ : ((transvRadical K (1 : Fin 3)).subgroupOf
      (transvRadical K (1 : Fin 3) ⊔ complSp K (1 : Fin 3))).map β.toMonoidHom =
        (transvRadical K (1 : Fin 3)).subgroupOf
          (transvRadical K (1 : Fin 3) ⊔ complSp K (1 : Fin 3)))
    (ι : complSp K (1 : Fin 3) ≃* complSp K (1 : Fin 3))
    (hι : ∀ m : complSp K (1 : Fin 3), ((ι m : complSp K (1 : Fin 3)) : StatedSp 3 K)⁻¹ *
      (β (inclusion le_sup_right m) : StatedSp 3 K) ∈ transvRadical K (1 : Fin 3)) :
    ∃ c ∈ complSp K (1 : Fin 3), ∀ m : complSp K (1 : Fin 3), (m : StatedSp 3 K) ∈ threeTorus K →
      c⁻¹ * (ι m : StatedSp 3 K) * c ∈ threeTorus K := by
  obtain ⟨s, σ, hsσ⟩ := exists_conj_fieldSp_of_inv_mul_mem β hβ ι hι
  refine ⟨(complSpEquiv (K := K) (m := 2) 1 s : StatedSp 3 K),
    (complSpEquiv (K := K) (m := 2) 1 s).2, fun m hm => ?_⟩
  obtain ⟨_, ⟨d, ⟨r, rfl⟩, rfl⟩, hdm⟩ := hm
  have hm' : m = complSpEquiv (K := K) (m := 2) 1 (diagSp K 2 fun _ => r) := Subtype.ext hdm.symm
  have e1 : (ι m : StatedSp 3 K) = (complSpEquiv (K := K) (m := 2) 1 s : StatedSp 3 K) *
      (complSpEquiv (K := K) (m := 2) 1 (fieldSp 2 K σ (diagSp K 2 fun _ => r)) :
        StatedSp 3 K) * (complSpEquiv (K := K) (m := 2) 1 s : StatedSp 3 K)⁻¹ := by
    rw [hm', hsσ, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv]
  rw [e1, fieldSp_diagSp_const]
  have e2 : (complSpEquiv (K := K) (m := 2) 1 s : StatedSp 3 K)⁻¹ *
      ((complSpEquiv (K := K) (m := 2) 1 s : StatedSp 3 K) *
        (complSpEquiv (K := K) (m := 2) 1 (diagSp K 2 fun _ => Units.map (σ : K →* K) r) :
          StatedSp 3 K) * (complSpEquiv (K := K) (m := 2) 1 s : StatedSp 3 K)⁻¹) *
      (complSpEquiv (K := K) (m := 2) 1 s : StatedSp 3 K) =
      (complSpEquiv (K := K) (m := 2) 1 (diagSp K 2 fun _ => Units.map (σ : K →* K) r) :
        StatedSp 3 K) := by group
  rw [e2]
  exact ⟨_, ⟨_, ⟨Units.map (σ : K →* K) r, rfl⟩, rfl⟩, rfl⟩

end F5

end CFSG.SeitzReduction.SymplecticPilot
