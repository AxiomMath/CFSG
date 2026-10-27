module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2Sp
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.LieType.RootSystem TauCeti.GLSymplecticFin
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.QuasithinUnique.Lin2.Five (tauSp)

section Sandwich

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

theorem single_mul_mul_single_eq_smul (a b : ι) (M : Matrix ι ι K) :
    single a b (1 : K) * M * single a b 1 = M b a • single a b 1 := by
  rw [single_mul_mul_single, one_mul, mul_one, smul_single, smul_eq_mul, mul_one]

theorem exists_mul_mul_eq_smul_of_mul_eq_mul {A B S S' : Matrix ι ι K} (hS'S : S' * S = 1)
    (hAB : A * S = S * B)
    (hA : ∀ M : Matrix ι ι K, ∃ c : K, A * M * A = c • A) (M : Matrix ι ι K) :
    ∃ c : K, B * M * B = c • B := by
  have hB : B = S' * A * S := by
    rw [Matrix.mul_assoc, hAB, ← Matrix.mul_assoc, hS'S, Matrix.one_mul]
  obtain ⟨c, hc⟩ := hA (S * M * S')
  refine ⟨c, ?_⟩
  calc B * M * B = S' * (A * (S * M * S') * A) * S := by
        rw [hB]
        simp only [Matrix.mul_assoc]
    _ = c • B := by
        rw [hc, Matrix.mul_smul, Matrix.smul_mul, hB, Matrix.mul_assoc]

end Sandwich

section RootElements

variable {K : Type} [Field K]

theorem statedSpMap_elt {k : Type} [Field k] (ι : k →+* K) {n : ℕ} (r : RootSubgroupIndex n)
    (c : k) : statedSpMap ι n (elt r c) = elt r (ι c) := by
  obtain ⟨γ, -, hγ⟩ := CFSG.LieType.Steinberg.Sp.exists_root_of_stdVec r
  rw [← CFSG.LieType.Steinberg.Sp.x_eq hγ.symm, statedSpMap_x,
    CFSG.LieType.Steinberg.Sp.x_eq hγ.symm]

abbrev rLong0 : RootSubgroupIndex 2 := .positiveLong 0

abbrev rSum01 : RootSubgroupIndex 2 := .positiveSum 0 1 (by decide)

theorem not_forall_exists_E_positiveSum_mul_mul_eq_smul :
    ¬ ∀ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K, ∃ c : K,
      E K rSum01 * M * E K rSum01 = c • E K rSum01 := by
  intro h
  obtain ⟨c, hc⟩ := h (single (Sum.inr 1) (Sum.inl 1) 1)
  have h1 := congrFun (congrFun hc (Sum.inl 0)) (Sum.inr 0)
  simp [E, Matrix.mul_apply, Matrix.add_mul, Matrix.single_apply] at h1

end RootElements

section Scalar

variable {K : Type} [Field K]

theorem commute_single_of_forall_commute_E {S : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hS : ∀ r : RootSubgroupIndex 2, Commute (E K r) S) :
    Pairwise fun a b => Commute (single a b (1 : K)) S := by
  have hL : ∀ i : Fin 2, Commute (single (Sum.inl i) (Sum.inr i) (1 : K)) S :=
    fun i => hS (.positiveLong i)
  have hN : ∀ i : Fin 2, Commute (single (Sum.inr i) (Sum.inl i) (1 : K)) S :=
    fun i => hS (.negativeLong i)
  have hD01 : Commute (single (Sum.inl 0) (Sum.inl 1) (1 : K) -
      single (Sum.inr 1) (Sum.inr 0) 1) S := hS (.difference 0 1 (by decide))
  have hD10 : Commute (single (Sum.inl 1) (Sum.inl 0) (1 : K) -
      single (Sum.inr 0) (Sum.inr 1) 1) S := hS (.difference 1 0 (by decide))
  have hDiag : ∀ i : Fin 2, Commute (single (Sum.inl i) (Sum.inl i) (1 : K)) S := fun i => by
    have h := (hL i).mul_left (hN i)
    rwa [single_mul_single_same, mul_one] at h
  have h01 : Commute (single (Sum.inl 0) (Sum.inl 1) (1 : K)) S := by
    have h := (hDiag 0).mul_left hD01
    have h0 : (single (Sum.inl 0) (Sum.inl 0) 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (single (Sum.inr 1) (Sum.inr 0) 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 0 :=
      single_mul_single_of_ne _ _ _ _ Sum.inl_ne_inr _
    rwa [Matrix.mul_sub, single_mul_single_same, h0, sub_zero, mul_one] at h
  have h10 : Commute (single (Sum.inl 1) (Sum.inl 0) (1 : K)) S := by
    have h := (hDiag 1).mul_left hD10
    have h0 : (single (Sum.inl 1) (Sum.inl 1) 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (single (Sum.inr 0) (Sum.inr 1) 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 0 :=
      single_mul_single_of_ne _ _ _ _ Sum.inl_ne_inr _
    rwa [Matrix.mul_sub, single_mul_single_same, h0, sub_zero, mul_one] at h
  have hR10 : Commute (single (Sum.inr 1) (Sum.inr 0) (1 : K)) S := by
    have h := h01.sub_left hD01
    rwa [sub_sub_cancel] at h
  have hR01 : Commute (single (Sum.inr 0) (Sum.inr 1) (1 : K)) S := by
    have h := h10.sub_left hD10
    rwa [sub_sub_cancel] at h
  have hX01 : Commute (single (Sum.inl 0) (Sum.inr 1) (1 : K)) S := by
    have h := h01.mul_left (hL 1)
    rwa [single_mul_single_same, mul_one] at h
  have hX10 : Commute (single (Sum.inl 1) (Sum.inr 0) (1 : K)) S := by
    have h := h10.mul_left (hL 0)
    rwa [single_mul_single_same, mul_one] at h
  have hY01 : Commute (single (Sum.inr 0) (Sum.inl 1) (1 : K)) S := by
    have h := (hN 0).mul_left h01
    rwa [single_mul_single_same, mul_one] at h
  have hY10 : Commute (single (Sum.inr 1) (Sum.inl 0) (1 : K)) S := by
    have h := (hN 1).mul_left h10
    rwa [single_mul_single_same, mul_one] at h
  have hL0 := hL 0
  have hL1 := hL 1
  have hN0 := hN 0
  have hN1 := hN 1
  intro a b hab
  match a, b, hab with
  | .inl 0, .inl 0, hab => exact absurd rfl hab
  | .inl 0, .inl 1, _ => exact h01
  | .inl 1, .inl 0, _ => exact h10
  | .inl 1, .inl 1, hab => exact absurd rfl hab
  | .inl 0, .inr 0, _ => exact hL0
  | .inl 0, .inr 1, _ => exact hX01
  | .inl 1, .inr 0, _ => exact hX10
  | .inl 1, .inr 1, _ => exact hL1
  | .inr 0, .inl 0, _ => exact hN0
  | .inr 0, .inl 1, _ => exact hY01
  | .inr 1, .inl 0, _ => exact hY10
  | .inr 1, .inl 1, _ => exact hN1
  | .inr 0, .inr 0, hab => exact absurd rfl hab
  | .inr 0, .inr 1, _ => exact hR01
  | .inr 1, .inr 0, _ => exact hR10
  | .inr 1, .inr 1, hab => exact absurd rfl hab

theorem eq_one_of_forall_mul_elt_one_eq [CharP K 2] {s : StatedSp 2 K}
    (hs : ∀ r : RootSubgroupIndex 2, s * elt r 1 = elt r 1 * s) : s = 1 := by
  have hE : ∀ r : RootSubgroupIndex 2, Commute (E K r) (mat 2 K s) := fun r => by
    have h := congrArg (mat 2 K) (hs r)
    rw [map_mul, map_mul, mat_elt, one_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul] at h
    exact (add_left_cancel h).symm
  obtain ⟨c, hc⟩ := mem_range_scalar_of_commute_single (commute_single_of_forall_commute_E hE)
  have hcen : s ∈ center (StatedSp 2 K) := by
    rw [mem_center_iff]
    intro g
    apply mat_injective
    rw [map_mul, map_mul, ← hc]
    exact (scalar_commute c (fun _ => Commute.all _ _) (mat 2 K g)).eq.symm
  rw [center_statedSp_eq_bot_of_charTwo] at hcen
  exact mem_bot.1 hcen

end Scalar

section Twist

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_ringEquiv_eq_fieldSp_of_forall_statedSpMap {k : Type} [Field k] (ι : k →+* K)
    (α : MulAut (StatedSp 2 K))
    (hα : ∀ g : StatedSp 2 k, α (statedSpMap ι 2 g) = statedSpMap ι 2 g) :
    ∃ ρ : K ≃+* K, (∀ c, ρ (ι c) = ι c) ∧ ∀ g, α g = fieldSp 2 K ρ g := by
  have h1 : ∀ r : RootSubgroupIndex 2, α (elt r 1) = elt r 1 := fun r => by
    have h := hα (elt r 1)
    rwa [statedSpMap_elt, map_one] at h
  obtain ⟨s, ρ, hcase | hcase⟩ := exists_eq_conj_mul_fieldSp_tauSp α
  · have hs : s = 1 := eq_one_of_forall_mul_elt_one_eq fun r => by
      have h := h1 r
      rw [hcase, fieldSp_elt, map_one] at h
      calc s * elt r 1 = s * elt r 1 * s⁻¹ * s := by group
        _ = elt r 1 * s := by rw [h]
    refine ⟨ρ, fun c => ?_, fun g => by rw [hcase g, hs, one_mul, inv_one, mul_one]⟩
    have h := hα (elt rLong0 c)
    rw [statedSpMap_elt, hcase, hs, one_mul, inv_one, mul_one, fieldSp_elt] at h
    exact elt_injective _ h
  · exfalso
    have h := h1 rLong0
    have hτ : tauIdx rLong0 = rSum01 := rfl
    rw [hcase, tauSp_elt, hτ, show tauExp rLong0 = 1 from rfl, one_pow, fieldSp_elt,
      map_one] at h
    have h2 : elt rLong0 (1 : K) * s = s * elt rSum01 1 := by
      rw [← h]
      group
    have hmat := congrArg (mat 2 K) h2
    rw [map_mul, map_mul, mat_elt, mat_elt, one_smul, one_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one] at hmat
    have hAB : E K rLong0 * mat 2 K s = mat 2 K s * E K rSum01 := add_left_cancel hmat
    have hS'S : mat 2 K s⁻¹ * mat 2 K s = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have hA : ∀ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K, ∃ c : K,
        E K rLong0 * M * E K rLong0 = c • E K rLong0 :=
      fun M => ⟨M (Sum.inr 0) (Sum.inl 0), single_mul_mul_single_eq_smul _ _ M⟩
    exact not_forall_exists_E_positiveSum_mul_mul_eq_smul
      (exists_mul_mul_eq_smul_of_mul_eq_mul hS'S hAB hA)

end Twist


end CFSG.SeitzReduction.F4Pilot
