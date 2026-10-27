module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CASwap1
public import CFSG.Sporadic.Recognition.HeMultiplier

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] {ρ : Γ →* MulAut M}
  {t : Γ} {J Q P M6 M7 K : Subgroup Γ}

theorem y7c_phi_ker_central (hcomm : ∀ a ∈ K, ∀ b ∈ conjSub t K, a * b = b * a) (k : ↥K)
    (hk : y7cPhi t K hcomm k = 1) : ∀ k' ∈ K, (k : Γ) * k' = k' * (k : Γ) := by
  have hat : t * (k : Γ) * t⁻¹ ∈ conjSub t K := y7c_mul_mem_conjSub (g := t) k.2
  have hkK : (k : Γ) ∈ conjSub t K := by
    have h : (k : Γ) * (t * (k : Γ) * t⁻¹) = 1 := by
      simpa only [y7cPhi_apply] using hk
    rw [eq_inv_of_mul_eq_one_left h]
    exact Subgroup.inv_mem _ hat
  intro k' hk'
  exact (hcomm k' hk' (k : Γ) hkK).symm

theorem y7c_center_phi_eq_one (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) (hne : conjSub t K ≠ K)
    (hcomm : ∀ a ∈ K, ∀ b ∈ conjSub t K, a * b = b * a) (k : ↥K)
    (hk : ∀ k' ∈ K, (k : Γ) * k' = k' * (k : Γ)) : y7cPhi t K hcomm k = 1 := by
  apply y7c_J_center c (y7c_phi_mem_J c hK hcomm k)
  intro y hy
  obtain ⟨k₁, hk₁⟩ := y7c_J_le_phi c hK hJK hne hcomm hy
  rw [← hk₁, y7cPhi_apply, y7cPhi_apply]
  have hAB : Commute (k : Γ) (k₁ : Γ) := hk (k₁ : Γ) k₁.2
  have hat : t * (k : Γ) * t⁻¹ ∈ conjSub t K := y7c_mul_mem_conjSub (g := t) k.2
  have hbt : t * (k₁ : Γ) * t⁻¹ ∈ conjSub t K :=
    y7c_mul_mem_conjSub (g := t) k₁.2
  have hAtB : Commute (t * (k : Γ) * t⁻¹) (k₁ : Γ) :=
    (hcomm (k₁ : Γ) k₁.2 (t * (k : Γ) * t⁻¹) hat).symm
  have hABt : Commute (k : Γ) (t * (k₁ : Γ) * t⁻¹) :=
    hcomm (k : Γ) k.2 (t * (k₁ : Γ) * t⁻¹) hbt
  have hAtBt : Commute (t * (k : Γ) * t⁻¹) (t * (k₁ : Γ) * t⁻¹) := hAB.conj t
  exact (hAB.mul_left hAtB).mul_right (hABt.mul_left hAtBt)

theorem y7c_swap_quot_equiv (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) (hne : conjSub t K ≠ K) :
    Nonempty (↥K ⧸ Subgroup.center ↥K ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := by
  have hcomm : ∀ a ∈ K, ∀ b ∈ conjSub t K, a * b = b * a :=
    y7c_comm_of_components hK (y7c_isComponent_conjSub hK t) hne.symm
  let ψ : ↥K →* ↥J := (y7cPhi t K hcomm).codRestrict J
    (fun k => y7c_phi_mem_J c hK hcomm k)
  have hψ : Function.Surjective ψ := by
    intro j
    obtain ⟨k, hk⟩ := y7c_J_le_phi c hK hJK hne hcomm j.2
    exact ⟨k, Subtype.ext hk⟩
  have hker : ψ.ker = Subgroup.center ↥K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro hk k'
      have hkφ : y7cPhi t K hcomm k = 1 := congrArg Subtype.val hk
      have h := (y7c_phi_ker_central hcomm k hkφ (k' : Γ) k'.2).symm
      apply Subtype.ext
      simpa only [Subgroup.coe_mul] using h
    · intro hk
      exact Subtype.ext (y7c_center_phi_eq_one c hK hJK hne hcomm k
        (fun k' hk' => by
          have h := (hk ⟨k', hk'⟩).symm
          simpa only [Subgroup.coe_mul] using congrArg Subtype.val h))
  obtain ⟨eJ⟩ := c.J_iso
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (G := ↥K) hker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective ψ hψ).trans eJ)⟩

theorem y7c_swap_card_K (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) (hne : conjSub t K ≠ K) :
    Nat.card ↥K = 168 * Nat.card ↥(Subgroup.center ↥K) := by
  obtain ⟨e⟩ := y7c_swap_quot_equiv c hK hJK hne
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥K),
    Nat.card_congr e.toEquiv, CFSG.ComponentClassification.GHarris.card_GL32_gh]

theorem y7c_swap_center_card (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) (hne : conjSub t K ≠ K)
    (hSM : Nat.card (CFSG.Open.griessHopfMultiplier
      (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) ∣ 2) :
    Nat.card ↥(Subgroup.center ↥K) ∣ 2 := by
  have hperf : Group.IsPerfect ↥K := hK.1.1
  obtain ⟨e⟩ := y7c_swap_quot_equiv c hK hJK hne
  exact dvd_trans
    (CFSG.Sporadic.Recognition.HeMultiplier.card_center_dvd_griess
      (S := Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) hperf e) hSM

end CFSG.OddStandard.HigherRank.YamadaG23
