module

public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.TypeIIIIVChiefData
import CFSG.FeitThompson.Local.ComplementFixedFreeSpecialization
import CFSG.FeitThompson.Local.ElementaryAbelianCubeInvariantPlane
import CFSG.FeitThompson.OddOrder.SemidirectReassociation
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
import CFSG.FeitThompson.Foundations.SolvableSubgroupSolvable
public import Mathlib.Topology.Sheaves.Presheaf

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup CFSG.FeitThompson.Prep05

variable {G : Type*} [Group G] [Finite G]

theorem commutator_eq_bot_of_isFixedPointFreeOn {U W H₀ : Subgroup G}
    (hsd : FreeCore.IsInternalSemidirectProduct (U ⊔ W) U W)
    (hnorm : U ⊔ W ≤ normalizer ((H₀ : Subgroup G) : Set G))
    (hsolvA : Group.IsSolvable ↥(U ⊔ W)) (hsolvH₀ : Group.IsSolvable ↥H₀)
    (hcop : (Nat.card ↥(U ⊔ W)).Coprime (Nat.card ↥H₀))
    (hfpf : IsFixedPointFreeOn U W) (hcent : centralizerIn H₀ W = ⊥) :
    ⁅U, H₀⁆ = ⊥ := by
  have hUA : U ≤ U ⊔ W := le_sup_left
  have hWA : W ≤ U ⊔ W := le_sup_right
  have hC : ∀ w ∈ W.subgroupOf (U ⊔ W), w ≠ 1 →
      U.subgroupOf (U ⊔ W) ⊓ Subgroup.centralizer {w} = ⊥ := by
    intro w hw hw1
    have hwW : (w : G) ∈ W := Subgroup.mem_subgroupOf.1 hw
    have hw1' : (w : G) ≠ 1 := fun h => hw1 (Subtype.ext h)
    have hbot : U ⊓ Subgroup.centralizer ({(w : G)} : Set G) = ⊥ := by
      have h := hfpf (w : G) hwW hw1'
      rwa [centralizerIn_eq, centralizer_coe_eq_centralizer_singleton
        (rfl : Subgroup.zpowers (w : G) = Subgroup.zpowers (w : G))] at h
    refine le_antisymm (fun x hx => ?_) bot_le
    obtain ⟨hxU, hxc⟩ := Subgroup.mem_inf.1 hx
    have hxU' : (x : G) ∈ U := Subgroup.mem_subgroupOf.1 hxU
    have hxc' : (x : G) ∈ Subgroup.centralizer ({(w : G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hxc))
    exact Subgroup.mem_bot.2
      (Subtype.ext (Subgroup.mem_bot.1 (hbot ▸ Subgroup.mem_inf.2 ⟨hxU', hxc'⟩)))
  have hCK : ∀ v : ↥H₀, (∀ w ∈ W.subgroupOf (U ⊔ W),
      conjOnNormalized H₀ hnorm w v = v) → v = 1 := by
    intro v hv
    have hvcent : (v : G) ∈ Subgroup.centralizer (W : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := hv ⟨y, hWA hy⟩ (Subgroup.mem_subgroupOf.2 hy)
      have h2 : y * (v : G) * y⁻¹ = (v : G) := by
        have h3 := congrArg (fun z : ↥H₀ => (z : G)) h1
        rwa [conjOnNormalized_apply_coe] at h3
      calc y * (v : G) = (y * (v : G) * y⁻¹) * y := by group
        _ = (v : G) * y := by rw [h2]
    exact Subtype.ext
      (Subgroup.mem_bot.1 (hcent ▸ Subgroup.mem_inf.2 ⟨v.2, hvcent⟩ : (v : G) ∈ (⊥ : Subgroup G)))
  have hker := le_ker_of_forall_fixedPoints_eq_one (conjOnNormalized H₀ hnorm) hcop
    hsd.normal_subgroupOf
    (isComplement'_subgroupOf_sup hsd.right_le_normalizer hsd.disjoint) hC hCK
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hk := hker
    (Subgroup.mem_subgroupOf.2 hu : (⟨u, hUA hu⟩ : ↥(U ⊔ W)) ∈ U.subgroupOf (U ⊔ W))
  rw [MonoidHom.mem_ker] at hk
  have h2 : u * h * u⁻¹ = h := by
    have h3 : conjOnNormalized H₀ hnorm ⟨u, hUA hu⟩ ⟨h, hh⟩ = ⟨h, hh⟩ := by rw [hk]; rfl
    have h4 := congrArg (fun z : ↥H₀ => (z : G)) h3
    rwa [conjOnNormalized_apply_coe] at h4
  calc h * u = (u * h * u⁻¹) * u := by rw [h2]
    _ = u * h := by group

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.Prep05

universe u

theorem FPF_type_iii_iv_chief_kernel_centralized
    (hprime : Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    Statements.FPF_type_iii_iv_chief_kernel_centralized.{u} := by
  intro G _ _ hG M U W₁ W₂ hM htype hc H₀ hH₀ hlayer
  obtain ⟨-, -, -, -, -, -, -, hsd, hcopH, hfpf, hcentW₁, -, -, -, -, hlayers⟩ :=
    FPF_type_iii_iv_chief_data hprime G hG M U W₁ W₂ hM htype hc _ _ rfl rfl
  obtain ⟨-, hH₀W₂, -, -, -, -, -⟩ := hlayers H₀ hH₀ hlayer
  have hsolvM : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  have hAleM : U ⊔ W₁ ≤ M := sup_le hc.le_M_E hc.le_M_W₁
  have hHle : hallCoreOf M ≤ M := hallCoreOf_le M
  have hH₀le : H₀ ≤ hallCoreOf M := hlayer.2.1.le
  have hAnorm : U ⊔ W₁ ≤ normalizer ((H₀ : Subgroup G) : Set G) := hAleM.trans hlayer.1
  have hcent : centralizerIn H₀ W₁ = ⊥ := by
    rw [centralizerIn_eq, ← hH₀W₂, ← hcentW₁, centralizerIn_eq, ← inf_assoc,
      inf_eq_left.2 hH₀le]
  exact commutator_eq_bot_of_isFixedPointFreeOn hsd hAnorm (isSolvable_of_le hAleM)
    (isSolvable_of_le (hH₀le.trans hHle))
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hH₀le) hcopH.symm) hfpf hcent

end CFSG.FeitThompson.Proofs

end
