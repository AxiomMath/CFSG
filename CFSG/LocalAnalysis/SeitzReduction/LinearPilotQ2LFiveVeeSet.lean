module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveUniNorm
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveZetAut
import all CFSG.Fischer.F4
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveVeeField

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.Fischer

section Transport

variable {X : Type} [Group X]

theorem exists_mulEquiv_specialLinear_F4_of_lieModel_four_four {K : Type} [Field K]
    (hK : Nat.card K = 2) {s : X} (hs : orderOf s = 2) {Lb : Subgroup X}
    (hLs : Lb ≤ centralizer ({s} : Set X)) (hLq : CFSG.Open.IsQuasisimple Lb)
    (hLZ : center Lb = ⊥) (hCs : centralizer ({s} : Set X) ≤ Lb ⊔ zpowers s) {Ks : Subgroup X}
    (hsN : s ∈ normalizer (Ks : Set X)) (hsK : s ∉ Ks) (hLK : Lb ≤ Ks)
    (hKm : LieModel Ks .PSL 4 2 2) (φ : SpecialLinearGroup (Fin 4) K →* X) (hφ : φ.range = Lb) :
    ∃ ψ : Ks ≃* SpecialLinearGroup (Fin 4) F4,
      (∀ k : Ks, ψ (Ks.normalizerMonoidHom ⟨s, hsN⟩ k) = veeFrob (ψ k)) ∧
        ∀ x, veeFrob x = x → ((ψ.symm x : Ks) : X) ∈ Lb := by
  classical
  have hs2 : s * s = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  obtain ⟨F, _, _, _, ι, σ, ψ₀, hF4, hσ1, hσσ, hσι, hψL, hψθ⟩ :=
    exists_normalized_mulEquiv_of_lieModel_four_four hK hs hLs hLq hLZ hCs hsN hsK hLK hKm φ hφ
  have hσsq : ∀ y, σ y = y * y := by
    rcases ringEquiv_eq_id_or_sq_of_card_four hF4 σ with h | h
    · exact absurd (RingEquiv.ext h) hσ1
    · intro y
      rw [h, sq]
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card F4 := by
    rw [F4.card, ← Nat.card_eq_fintype_card, hF4]
  set ι₄ : F ≃+* F4 := FiniteField.ringEquivOfCardEq hcard with hι₄
  let ΦSL : SpecialLinearGroup (Fin 4) F ≃* SpecialLinearGroup (Fin 4) F4 :=
    { toFun := Matrix.SpecialLinearGroup.map ι₄.toRingHom
      invFun := Matrix.SpecialLinearGroup.map ι₄.symm.toRingHom
      left_inv := fun M => by
        ext i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      right_inv := fun M => by
        ext i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      map_mul' := fun M N => map_mul _ M N }
  have hΦSL : ∀ (M : SpecialLinearGroup (Fin 4) F) i j, (ΦSL M) i j = ι₄ (M i j) :=
    fun M i j => by simp [ΦSL, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  have : CharP F 2 := SeitzQ2.charTwo_of_natCard_eq_two_pow (f := 2) (by rw [hF4]; norm_num)
  let Φ : projectiveSL 4 F ≃* SpecialLinearGroup (Fin 4) F4 :=
    (LinearCover.projectiveSLFourEquivSL F).trans ΦSL
  have hΦproj : ∀ A : SpecialLinearGroup (Fin 4) F, Φ (proj 4 F A) = ΦSL A := fun A => rfl
  refine ⟨ψ₀.trans Φ, fun k => ?_, fun x hx => ?_⟩
  ·
    change Φ (ψ₀ _) = veeFrob (Φ (ψ₀ k))
    rw [hψθ]
    obtain ⟨A, hA⟩ := proj_surjective (n := 4) (K := F) (ψ₀ k)
    rw [← hA, fieldAut_proj, hΦproj, hΦproj]
    ext i j
    rw [hΦSL, coe_veeFrob, Matrix.map_apply, hΦSL]
    change ι₄ (σ (A i j)) = ι₄ (A i j) * ι₄ (A i j)
    rw [hσsq, map_mul]
  ·
    set k := (ψ₀.trans Φ).symm x with hk
    have hθk : Ks.normalizerMonoidHom ⟨s, hsN⟩ k = k := by
      apply (ψ₀.trans Φ).injective
      change Φ (ψ₀ _) = Φ (ψ₀ k)
      rw [hψθ]
      obtain ⟨A, hA⟩ := proj_surjective (n := 4) (K := F) (ψ₀ k)
      rw [← hA, fieldAut_proj, hΦproj, hΦproj]
      have hx' : veeFrob (Φ (ψ₀ k)) = Φ (ψ₀ k) := by
        change veeFrob ((ψ₀.trans Φ) k) = (ψ₀.trans Φ) k
        rw [hk, MulEquiv.apply_symm_apply]
        exact hx
      rw [← hA, hΦproj] at hx'
      ext i j
      rw [hΦSL, ← hx', coe_veeFrob, Matrix.map_apply, hΦSL]
      change ι₄ (σ (A i j)) = ι₄ (A i j) * ι₄ (A i j)
      rw [hσsq, map_mul]
    have hks : (k : X) ∈ centralizer ({s} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      have h1 := congrArg Subtype.val hθk
      rw [F4Pilot.coe_normalizerMonoidHom_mk_apply Ks hsN] at h1
      have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
      calc (k : X) * s = s * k * s⁻¹ * s := by rw [h1]
        _ = s * k := by group
    rcases mem_or_mul_mem_of_centralizer_le_sup hs2 hLs hCs hks with h | h
    · exact h
    · exfalso
      apply hsK
      have h1 : (k : X)⁻¹ * (k * s) = s := by group
      rw [← h1]
      exact mul_mem (inv_mem k.2) (hLK h)

end Transport

section Singer

@[expose] def veeMatS : Matrix (Fin 4) (Fin 4) F4 :=
  !![0, 0, 0, 1; 0, 0, 1, 1; 1, 0, 0, 1; 0, 1, 1, 1]

@[expose] def veeS : SpecialLinearGroup (Fin 4) F4 := ⟨veeMatS, by decide +kernel⟩

theorem veeS_pow_five : veeS ^ 5 = veeC := Subtype.ext (by decide +kernel)
theorem veeS_pow_fifteen : veeS ^ 15 = 1 := Subtype.ext (by decide +kernel)
theorem veeS_pow_three_ne_one : veeS ^ 3 ≠ 1 := fun h => by
  have h' := congrArg Subtype.val h
  revert h'
  decide +kernel
theorem veeC_ne_one : veeC ≠ 1 := fun h => by
  have h' := congrArg Subtype.val h
  revert h'
  decide +kernel
theorem veeB_ne_one : veeB ≠ 1 := fun h => by
  have h' := congrArg Subtype.val h
  revert h'
  decide +kernel
theorem veeB_pow_three : veeB ^ 3 = 1 := Subtype.ext (by decide +kernel)
theorem veeFrob_veeS : veeFrob veeS = veeS := Subtype.ext (by decide +kernel)
theorem veeFrob_veeB : veeFrob veeB = veeB := Subtype.ext (by decide +kernel)

end Singer

end CFSG.SeitzReduction.LinearPilot
