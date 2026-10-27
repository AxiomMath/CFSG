module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGALift
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGA8Quat
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGADich

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fj_simAct_eq_of_odd (hQ : Q.Nondegenerate) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    (hpos : 0 < Module.finrank (ZMod 3) V) (ρ : simGroup Q) {g : omegaGroup hQ}
    (hodd : Odd (orderOf g))
    (hfix : ffSimOmegaAct hQ h2 (QuotientGroup.mk ρ : ProjSim Q) (omegaToProj hQ g) =
      omegaToProj hQ g) : simAct Q ρ (g : OGroup Q) = (g : OGroup Q) := by
  obtain ⟨g', hg'val⟩ : ∃ g' : omegaGroup hQ, (g' : OGroup Q) = simAct Q ρ (g : OGroup Q) :=
    ⟨⟨_, ff_simAct_mem_omegaGroup hQ h2 ρ g.2⟩, rfl⟩
  have hg' : omegaToProj hQ g' = omegaToProj hQ g := by
    calc omegaToProj hQ g' = ffSimOmegaAct hQ h2 (QuotientGroup.mk ρ : ProjSim Q)
          (omegaToProj hQ g) := by
          apply Subtype.ext
          rw [coe_ffSimOmegaAct, coe_omegaToProj, coe_omegaToProj, projSimAct_mk,
            projActAux_toProj, hg'val]
      _ = omegaToProj hQ g := hfix
  rcases omegaToProj_eq_iff hQ hg' with h | h
  · rw [← hg'val]
    exact h.symm
  · exfalso
    have hS : simAct Q ρ (g : OGroup Q) = piOrth Q * (g : OGroup Q) := by
      rw [← hg'val]
      calc (g' : OGroup Q) = (piOrth Q * piOrth Q) * g' := by rw [piOrth_mul_self, one_mul]
        _ = piOrth Q * (piOrth Q * g') := mul_assoc _ _ _
        _ = piOrth Q * g := by rw [← h]
    obtain ⟨k, hk⟩ := hodd
    have hordG : orderOf (g : OGroup Q) = orderOf g := Subgroup.orderOf_coe g
    have hG1 : (g : OGroup Q) ^ (2 * k + 1) = 1 := by
      rw [← hk, ← hordG]
      exact pow_orderOf_eq_one _
    have hS1 : (simAct Q ρ (g : OGroup Q)) ^ (2 * k + 1) = 1 := by
      rw [← map_pow, hG1, map_one]
    have hπodd : piOrth Q ^ (2 * k + 1) = piOrth Q := by
      rw [pow_succ, pow_mul, show piOrth Q ^ 2 = 1 by rw [pow_two]; exact piOrth_mul_self,
        one_pow, one_mul]
    have hcomm : Commute (piOrth Q) (g : OGroup Q) := (mul_piOrth_comm _).symm
    rw [hS, hcomm.mul_pow, hπodd, hG1, mul_one] at hS1
    exact piOrth_ne_one hpos hS1

theorem fj_comm_of_simAct_fix {ρ : simGroup Q} {g : OGroup Q} (h : simAct Q ρ g = g) (v : V) :
    (ρ : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) v) =
      (g : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) := by
  have h1 : (ρ : V ≃ₗ[ZMod 3] V) * (g : V ≃ₗ[ZMod 3] V) * (ρ : V ≃ₗ[ZMod 3] V)⁻¹ =
      (g : V ≃ₗ[ZMod 3] V) := by
    have := congrArg (fun t : OGroup Q => (t : V ≃ₗ[ZMod 3] V)) h
    rwa [coe_simAct] at this
  have h2 : (ρ : V ≃ₗ[ZMod 3] V) * (g : V ≃ₗ[ZMod 3] V) =
      (g : V ≃ₗ[ZMod 3] V) * (ρ : V ≃ₗ[ZMod 3] V) := by
    calc (ρ : V ≃ₗ[ZMod 3] V) * (g : V ≃ₗ[ZMod 3] V)
        = ((ρ : V ≃ₗ[ZMod 3] V) * (g : V ≃ₗ[ZMod 3] V) * (ρ : V ≃ₗ[ZMod 3] V)⁻¹) *
          (ρ : V ≃ₗ[ZMod 3] V) := by group
      _ = (g : V ≃ₗ[ZMod 3] V) * (ρ : V ≃ₗ[ZMod 3] V) := by rw [h1]
  exact congrArg (fun e : V ≃ₗ[ZMod 3] V => e v) h2

theorem fj_no_pocket_negsim (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 8)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) {ρ : ↥(simGroup Q)}
    (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v)
    {y : omegaProj hQ} {B : Subgroup (omegaProj hQ)} (hy : orderOf y = 2)
    (hB : Sl23PocketIn ⊤ y B)
    (hfix : ∀ b ∈ B, ffSimOmegaAct hQ h2 (QuotientGroup.mk ρ : ProjSim Q) b = b) : False := by
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  haveI : Finite (omegaGroup hQ) := Subtype.finite
  obtain ⟨z, hzy, hz2, hzK⟩ := fj_lift_pocket_omega hQ hy hB
  have hKfix : ∀ k ∈ l34g_oddHull (omegaToProj hQ) B,
      simAct Q ρ (k : OGroup Q) = (k : OGroup Q) := by
    intro k hk
    have hle : l34g_oddHull (omegaToProj hQ) B ≤
        (fixSub (simAct Q ρ)).comap (omegaGroup hQ).subtype := by
      rw [l34g_oddHull, Subgroup.closure_le]
      rintro g ⟨hgB, hodd⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, mem_fixSub_iff]
      exact fj_simAct_eq_of_odd hQ h2 (by omega) ρ hodd (hfix _ hgB)
    exact mem_fixSub_iff.mp (Subgroup.mem_comap.mp (hle hk))
  obtain ⟨q, r, hqK, hrK, hqq, hrr, hrq⟩ := fj_exists_quaternion_pair hzK.2.2.2 hzK.1 hz2
  have hzz : z * z = 1 := by
    rw [← pow_two]
    exact hz2 ▸ pow_orderOf_eq_one z
  have hz1 : (z : OGroup Q) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz2
    exact absurd hz2 (by decide)
  have hzπ : (z : OGroup Q) ≠ piOrth Q := by
    intro h
    have h1 : omegaToProj hQ z = 1 := (omegaToProj_eq_one_iff hQ z).mpr (Or.inr h)
    rw [h1] at hzy
    rw [← hzy, orderOf_one] at hy
    exact absurd hy (by decide)
  have hq2 : (q : OGroup Q) * q = z := congrArg Subtype.val hqq
  have hr2 : (r : OGroup Q) * r = z := congrArg Subtype.val hrr
  exact fj_no_quaternion_comm_negsim hQ hdim (q := (q : OGroup Q)) (r := (r : OGroup Q))
    (hq2.trans hr2.symm) (by rw [hq2]; exact congrArg Subtype.val hzz)
    (congrArg Subtype.val hrq) (by rw [hq2]; exact hz1) (by rw [hq2]; exact hzπ) hρ hρρ
    (fj_comm_of_simAct_fix (hKfix q hqK)) (fj_comm_of_simAct_fix (hKfix r hrK))

end CFSG.OddStandard.SmallF3.Omega
