module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9Glue2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9Glue1

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K F : Subgroup G}

theorem step1_std (hII : II4_4_4_center) (hq : II4_4_quat) (hdiag : IVK_diag_unique)
    (h19 : IVK_1_9_outer) (hsd : SD_facts) (hsdq : SD_sq_not_z) (hqc : Quat_centr) (hrn : Rnormal4)
    (hlift : II4_ord4_lift) (h : Std4r1 G z S K F) (hQF : Qz S z = F)
    (hquat : ∃ n, IVK.IsQuaternionTwoGroup ↥F n) (hcase : ∃ t ∈ Rz S z, t ≠ z ∧ IsConj z t) :
    ∃ U : Subgroup G, U ≤ (S ⊓ K) ⊔ (S ⊓ cSec K) ∧ R1.Four U ∧
      (∀ s ∈ S, ∀ v ∈ U, s * v * s⁻¹ ∈ U) ∧ ∃ u ∈ U, u ≠ 1 ∧ u ≠ z ∧ IsConj z u ∧
        ∃ u₁ ∈ S ⊓ K, ∃ u₂ ∈ S ⊓ cSec K, u = u₁ * u₂ ∧ u₁ * u₁ = z ∧ u₂ * u₂ = z := by
  classical
  have hF := h.F_eq hQF
  have hcfg := cfg1K_Q hII hq hdiag h19 hsd hsdq hqc hrn h hQF
  obtain ⟨nQ, hnQ⟩ : ∃ n, IVK.IsQuaternionTwoGroup ↥(S ⊓ cSec K) n := hF ▸ hquat
  have hzQ : z ∈ S ⊓ cSec K := h.z_mem_Q hII
  have hz2 := h.z_sq
  have hz1 := h.z_ne
  have hQinv := R1.quat_invol_sub hnQ hzQ hz2 hz1
  have hQne : S ⊓ cSec K ≠ zpowers z := by
    intro hQz
    have h8 := R1.card_ge_of_quat hnQ
    have : Nat.card ↥(S ⊓ cSec K) = 2 := by
      rw [hQz, Nat.card_zpowers]
      exact R1.orderOf_two_of_sq_one hz2 hz1
    omega
  obtain ⟨U, hUR, hU4, hUn⟩ := hcfg.rn4 hQne
  have hUS : U ≤ S := hUR.trans (sup_le hcfg.P_le hcfg.Q_le)
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
    have h3 := hU4.2
    omega
  obtain ⟨u₁, hu₁P, u₂, hu₂Q, hu, hu₁sq, hu₂sq⟩ :=
    hcfg.toCfg1.decomp_four' hQinv (hUR huU) (hU4.1 u huU) hu1 huz
  have hnorm₂ : ∀ s ∈ S, s * u₂ * s⁻¹ = u₂ ∨ s * u₂ * s⁻¹ = u₂ * z := fun s hs =>
    (hcfg.toCfg1.conj_comp hUR hU4 hUn huU hu1 huz hu₁P hu₂Q hu hs).2
  refine ⟨U, hUR, hU4, hUn, ?_⟩
  by_cases hPX : ∃ t : G, IsConj z t ∧ t ∈ (S ⊓ K) ⊔ ((S ⊓ cSec K) ⊓ centralizer ({u₂} : Set G)) ∧
      t ≠ z
  · obtain ⟨t, hzt, htPX, htz⟩ := hPX
    obtain ⟨hXc, -⟩ := hqc G (S ⊓ cSec K) z u₂ nQ hnQ hzQ hz2 hz1 hu₂Q hu₂sq
      (fun q hq => hnorm₂ q hq.1)
    obtain ⟨p, hp, x, hx, htpx⟩ := M.mem_sup_of_commute (A := S ⊓ K)
      (B := (S ⊓ cSec K) ⊓ centralizer ({u₂} : Set G))
      (fun a ha b hb => hcfg.PQ_comm a ha b hb.1) htPX
    have hxQ : x ∈ S ⊓ cSec K := hx.1
    obtain ⟨hzt2, hzt1⟩ : t * t = 1 ∧ t ≠ 1 := by
      obtain ⟨c, hc⟩ := isConj_iff.1 hzt
      refine ⟨?_, ?_⟩
      · rw [← hc]
        calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
          _ = 1 := by rw [hz2]; group
      · intro e
        apply hz1
        calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
          _ = 1 := by rw [hc, e]; group
    obtain ⟨hpsq, hxsq⟩ := hcfg.toCfg1.sq_of_pq hQinv hp hxQ (by rw [← htpx]; exact hzt2)
      (by rw [← htpx]; exact hzt1) (by rw [← htpx]; exact htz)
    have hxu : x = u₂ ∨ x = u₂ * z := by
      have hu₂X : u₂ ∈ (S ⊓ cSec K) ⊓ centralizer ({u₂} : Set G) :=
        ⟨hu₂Q, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
      have hzX : z ∈ (S ⊓ cSec K) ⊓ centralizer ({u₂} : Set G) :=
        ⟨hzQ, Subgroup.mem_centralizer_singleton_iff.2 (h.z_cent hu₂Q.1)⟩
      have hcomm : x * u₂ = u₂ * x := R1.comm_of_cyclic hXc hx hu₂X
      have hwX : x * u₂⁻¹ ∈ (S ⊓ cSec K) ⊓ centralizer ({u₂} : Set G) :=
        mul_mem hx (inv_mem hu₂X)
      have hu₂inv : u₂⁻¹ = u₂ * z := hcfg.toCfg1.inv_eq_mul_z hu₂sq
      have hw2 : (x * u₂⁻¹) * (x * u₂⁻¹) = 1 := by
        have hzc : z * u₂ = u₂ * z := h.z_cent hu₂Q.1
        rw [hu₂inv]
        calc x * (u₂ * z) * (x * (u₂ * z)) = (x * u₂) * z * (x * u₂) * z := by group
          _ = (u₂ * x) * z * (u₂ * x) * z := by rw [hcomm]
          _ = u₂ * (x * z * u₂ * x) * z := by group
          _ = u₂ * (x * (z * u₂) * x) * z := by group
          _ = u₂ * (x * (u₂ * z) * x) * z := by rw [hzc]
          _ = (u₂ * x * u₂) * (z * x) * z := by group
          _ = (u₂ * x * u₂) * (x * z) * z := by rw [h.z_cent hxQ.1]
          _ = u₂ * (x * u₂ * x) * (z * z) := by group
          _ = u₂ * (u₂ * x * x) * (z * z) := by rw [hcomm]
          _ = (u₂ * u₂) * (x * x) * (z * z) := by group
          _ = 1 := by rw [hu₂sq, hxsq, hz2]; simp
      by_cases hw1 : x * u₂⁻¹ = 1
      · left
        calc x = (x * u₂⁻¹) * u₂ := by group
          _ = u₂ := by rw [hw1, one_mul]
      · right
        have := B.cyclic_invol_unique hXc hwX hzX hw2 hz2 hw1 hz1
        calc x = (x * u₂⁻¹) * u₂ := by group
          _ = z * u₂ := by rw [this]
          _ = u₂ * z := h.z_cent hu₂Q.1
    have hu₁K : u₁ ∈ S ⊓ K := hu₁P
    have hconj := kconj_step hlift h hp hu₁K hxQ hpsq hu₁sq hxsq htpx hzt
    have hzU : z ∈ U := hcfg.toCfg1.z_mem_four hU4 hUS hUn
    rcases hxu with e | e
    · refine ⟨u, huU, hu1, huz, ?_, u₁, hu₁P, u₂, hu₂Q, hu, hu₁sq, hu₂sq⟩
      rw [hu, ← e]; exact hconj
    · refine ⟨u * z, mul_mem huU hzU, ?_, ?_, ?_, u₁, hu₁P, u₂ * z, mul_mem hu₂Q hzQ, by rw [hu]; group,
        hu₁sq, ?_⟩
      · intro e'
        apply huz
        calc u = u * z * z := by rw [mul_assoc, hz2, mul_one]
          _ = z := by rw [e', one_mul]
      · intro e'
        apply hu1
        calc u = u * z * z⁻¹ := by group
          _ = z * z⁻¹ := by rw [e']
          _ = 1 := by group
      · have : u₁ * (u₂ * z) = u * z := by rw [hu]; group
        rw [e] at hconj
        rw [← this]; exact hconj
      · have hzc : z * u₂ = u₂ * z := h.z_cent hu₂Q.1
        calc u₂ * z * (u₂ * z) = u₂ * (z * u₂) * z := by group
          _ = u₂ * (u₂ * z) * z := by rw [hzc]
          _ = (u₂ * u₂) * (z * z) := by group
          _ = z := by rw [hu₂sq, hz2, mul_one]
  · exfalso
    push Not at hPX
    refine hcfg.step1b hQinv hu₂Q hnorm₂ ?_ (fun t hzt htPX => ?_)
    · obtain ⟨t, htR, htz, hzt⟩ := hcase
      refine ⟨t, ?_, htz, hzt⟩
      rw [h.Rz_eq] at htR; exact htR
    · exact hPX t hzt htPX

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
