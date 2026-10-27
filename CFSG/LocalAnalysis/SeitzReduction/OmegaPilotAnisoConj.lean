module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoRot
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotF6Conj

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.Quasithin (perfectCore)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a a' : Fin d} {b c : K}

omit [Finite K] [CharP K 2] in
theorem linearIndependent_of_polar_eq {x x' : Fin d → K} (hb : b ≠ 0) (hx : Q x = 1)
    (hxx : polar Q x x = 0) (hxx' : polar Q x x' = b) : LinearIndependent K ![x, x'] := by
  rw [LinearIndependent.pair_iff]
  intro α β hαβ
  have h1 := congrArg (polar Q x) hαβ
  rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hxx, hxx', polar_zero_right] at h1
  have hβ : β = 0 := by
    have : β * b = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_right hb
  rw [hβ, zero_smul, add_zero, smul_eq_zero] at hαβ
  refine ⟨hαβ.resolve_right ?_, hβ⟩
  rintro rfl
  rw [QuadraticMap.map_zero] at hx
  exact zero_ne_one hx

theorem IsAnisoCoord.exists_mulAut_eq_map_anisoTorusOf (h : IsAnisoCoord Q a a' b c)
    (hQ : (polarBilin Q).Nondegenerate) {Y : Subgroup (matrixProjectiveDerived Q)}
    {e e' : Fin d → K} (he : Q e = 1) (he' : Q e' = c) (hee' : polar Q e e' = b)
    (hY : ∀ g : orthDerived Q, projHom Q g ∈ Y →
      ∀ x, polar Q x e = 0 → polar Q x e' = 0 → (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) x = x)
    (hcard : Nat.card Y = Nat.card (anisoTorusOf Q h.ne b c)) :
    ∃ α : MulAut (matrixProjectiveDerived Q), Y = (anisoTorusOf Q h.ne b c).map α.toMonoidHom := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hb := h.b_ne_zero
  have hodd : Odd (Nat.card Y) := hcard ▸ h.odd_card_anisoTorusOf
  have hsq : ∀ x : Fin d → K, polar Q x x = 0 := fun x => by
    rw [polar_self_eq_two_mul, h2, zero_mul]
  have hab : polar Q (Pi.single a 1) (Pi.single a' 1) = b := by
    rw [h.polar_left, Pi.single_eq_same, mul_one]
  have hba : polar Q (Pi.single a' 1) (Pi.single a 1) = b := by rw [polar_comm, hab]
  have he'e : polar Q e' e = b := by rw [polar_comm, hee']
  obtain ⟨A, hA, hAuv⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    hQ ![Pi.single a 1, Pi.single a' 1] ![e, e']
    (linearIndependent_of_polar_eq hb h.map_left (hsq _) hab)
    (linearIndependent_of_polar_eq hb he (hsq _) hee')
    (by
      intro i
      fin_cases i
      · simp [he, h.map_left]
      · simp [he', h.map_right])
    (by
      intro i j
      fin_cases i <;> fin_cases j
      · simp [hsq]
      · simp [hee', hab]
      · simp [he'e, hba]
      · simp [hsq])
  have hAe : A (Pi.single a 1) = e := hAuv 0
  have hAe' : A (Pi.single a' 1) = e' := hAuv 1
  set α := conjProj h.exists_ne_zero hA with hα
  refine ⟨α, ?_⟩
  have hle : Y ≤ (anisoTorusOf Q h.ne b c).map α.toMonoidHom := by
    intro y hy
    obtain ⟨g, rfl⟩ := projHom_surjective Q y
    obtain ⟨t, ht⟩ : ∃ t, t = conjOrthDerived (inv_mem hA) g := ⟨_, rfl⟩
    have htg : (t : (Fin d → K) ≃ₗ[K] (Fin d → K)) = A⁻¹ * g * A := by
      rw [ht, coe_conjOrthDerived, inv_inv]
    have htU : ∀ w ∈ perpSub K a a', (t : (Fin d → K) ≃ₗ[K] (Fin d → K)) w = w := by
      intro w hw
      have h1 : polar Q (A w) e = 0 := by
        rw [← hAe, polar_map_of_mem hA, polar_comm, h.polar_left, hw.2, mul_zero]
      have h3 : polar Q (A w) e' = 0 := by
        rw [← hAe', polar_map_of_mem hA, polar_comm, h.polar_right, hw.1, mul_zero]
      rw [htg, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hY g hy _ h1 h3,
        LinearEquiv.inv_apply_apply']
    have htodd : Odd (orderOf (t : (Fin d → K) ≃ₗ[K] (Fin d → K))) := by
      have e1 : orderOf (t : (Fin d → K) ≃ₗ[K] (Fin d → K)) = orderOf g := by
        rw [Subgroup.orderOf_coe, ht, MulEquiv.orderOf_eq]
      have e2 : orderOf (⟨projHom Q g, hy⟩ : Y) = orderOf g := by
        rw [Subgroup.orderOf_mk]
        exact orderOf_injective (projHom Q) (projHom_injective h.exists_ne_zero) g
      rw [e1, ← e2]
      exact hodd.of_dvd_nat (orderOf_dvd_natCard _)
    have htrot := h.mem_anisoRotSub_of_odd hQ (Subgroup.commutator_le_self _ t.2) htU htodd
    refine ⟨projHom Q t, ⟨t, mem_subgroupOf.mpr htrot, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, hα, conjProj_projHom]
    congr 1
    apply Subtype.ext
    rw [coe_conjOrthDerived, htg]
    group
  refine eq_of_le_of_card_ge hle ?_
  rw [card_map_of_injective α.injective, hcard]

theorem IsAnisoCoord.perfectCore_centralizer_anisoTorusOf (h : IsAnisoCoord Q a a' b c)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hD : ⁅pairPerpOf Q a a', pairPerpOf Q a a'⁆ = pairPerpOf Q a a') :
    perfectCore (centralizer (anisoTorusOf Q h.ne b c : Set (matrixProjectiveDerived Q))) =
      pairPerpOf Q a a' := by
  rw [h.centralizer_anisoTorusOf hQ hT]
  exact F4Pilot.perfectCore_sup_eq_of_le_centralizer h.anisoTorusOf_le_centralizer_self
    h.anisoTorusOf_le_centralizer_pairPerpOf hD

theorem IsAnisoCoord.nonempty_perfectCore_centralizer_mulEquiv_pairPerpOf
    (h : IsAnisoCoord Q a a' b c) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hD : ⁅pairPerpOf Q a a', pairPerpOf Q a a'⁆ = pairPerpOf Q a a')
    {Y : Subgroup (matrixProjectiveDerived Q)} {e e' : Fin d → K} (he : Q e = 1)
    (he' : Q e' = c) (hee' : polar Q e e' = b)
    (hY : ∀ g : orthDerived Q, projHom Q g ∈ Y →
      ∀ x, polar Q x e = 0 → polar Q x e' = 0 → (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) x = x)
    (hcard : Nat.card Y = Nat.card (anisoTorusOf Q h.ne b c)) :
    Nonempty (perfectCore (centralizer (Y : Set (matrixProjectiveDerived Q))) ≃*
      pairPerpOf Q a a') := by
  obtain ⟨α, rfl⟩ := h.exists_mulAut_eq_map_anisoTorusOf hQ he he' hee' hY hcard
  obtain ⟨φ⟩ := F4Pilot.nonempty_perfectCore_centralizer_map_mulAut α (anisoTorusOf Q h.ne b c)
  rw [h.perfectCore_centralizer_anisoTorusOf hQ hT hD] at φ
  exact ⟨φ⟩

end CFSG.SeitzReduction.OmegaPilot
