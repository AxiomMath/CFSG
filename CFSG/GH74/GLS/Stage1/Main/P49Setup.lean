module

public import CFSG.GH74.GLS.Stage1.Main.P49Ctx
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Final46
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9Glue1
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9Rest2

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K F U : Subgroup G} {x y : G}

theorem setup9_of_ctx49 (hc : Closed49) (h : Ctx49 G z S K F U x y) :
    ∃ u₁ u₂ : G, R1.Setup9 G z S (S ⊓ K) (S ⊓ cSec K) (fun s => InducesFAut s K) U x u₁ u₂ := by
  classical
  obtain ⟨hII, hq, hdiag, h19, hsd, hsdq, hqc, hrn⟩ := hc
  obtain ⟨h, hQF, hquat, hUR, hU4, hUn, -, hxW, hxU, hxz, hcard, hidx, -, -, -, -⟩ := h
  have hcfg := cfg1K_Q hII hq hdiag h19 hsd hsdq hqc hrn h hQF
  have hF := h.F_eq hQF
  obtain ⟨nQ, hnQ⟩ : ∃ n, IVK.IsQuaternionTwoGroup ↥(S ⊓ cSec K) n := hF ▸ hquat
  obtain ⟨nP, hnP⟩ := h.P_quat hq
  have hzQ := h.z_mem_Q hII
  have hz2 := h.z_sq
  have hz1 := h.z_ne
  have hRP : Rz S z = (S ⊓ K) ⊔ (S ⊓ cSec K) := h.Rz_eq
  have hUR' : U ≤ (S ⊓ K) ⊔ (S ⊓ cSec K) := hRP ▸ hUR
  have hU4' : R1.Four U := Std4r1.four_of U hU4
  have hQinv := R1.quat_invol_sub hnQ hzQ hz2 hz1
  obtain ⟨u, huU, hu1, huz⟩ : ∃ u ∈ U, u ≠ 1 ∧ u ≠ z := by
    by_contra hcon
    push Not at hcon
    have hsub : ∀ e ∈ U, e ∈ ({1, z} : Finset G) := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases he1 : e = 1
      · exact Or.inl he1
      · exact Or.inr (hcon e he he1)
    have h1 := B.card_subgroup_le_finset U _ hsub
    have h2 : ({1, z} : Finset G).card ≤ 2 := Finset.card_le_two
    have h3 := hU4'.2
    omega
  obtain ⟨u₁, hu₁P, u₂, hu₂Q, hu, hu₁sq, hu₂sq⟩ :=
    hcfg.toCfg1.decomp_four' hQinv (hUR' huU) (hU4'.1 u huU) hu1 huz
  have hnorm := fun (s : G) (hs : s ∈ S) =>
    hcfg.toCfg1.conj_comp hUR' hU4' hUn huU hu1 huz hu₁P hu₂Q hu hs
  obtain ⟨V₁, hV₁eq, hV₁c, hV₁i⟩ :=
    hcfg.toCfg1.P_centr u₁ hu₁P hu₁sq (fun s hs => (hnorm s hs).1)
  obtain ⟨hV₂c, hV₂i⟩ := hqc G (S ⊓ cSec K) z u₂ nQ hnQ hzQ hz2 hz1 hu₂Q hu₂sq
    (fun q hq => (hnorm q hq.1).2)
  have c9 : R1.Setup9 G z S (S ⊓ K) (S ⊓ cSec K) (fun s => InducesFAut s K) U x u₁ u₂ :=
    { cfg := hcfg.toCfg1
      quatP := ⟨nP, hnP⟩
      quatQ := ⟨nQ, hnQ⟩
      card_eq := by rw [← h.Pz_eq, ← h.Qz_eq]; exact hcard
      idx := by rw [← hRP]; exact hidx
      U_le := hUR'
      U_four := hU4'
      U_norm := hUn
      u₁_mem := hu₁P
      u₂_mem := hu₂Q
      u₁_sq := hu₁sq
      u₂_sq := hu₂sq
      u_mem := hu ▸ huU
      V₁_cyc := by rw [← hV₁eq]; exact hV₁c
      V₁_idx := by rw [← hV₁eq]; exact hV₁i
      V₂_cyc := hV₂c
      V₂_idx := hV₂i
      x_W := Subgroup.mem_normalizer_iff.1 hxW
      x_U := fun v hv => (Subgroup.mem_normalizer_iff.1 hxU v).1 hv
      x_z := hxz }
  exact ⟨u₁, u₂, c9⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
