module

public import CFSG.ClassicalInvolution.Q3.Sec13EndHyp

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

@[expose] def Perp9 (Ω : Set (Subgroup G)) : Prop :=
  ∀ K ∈ Ω, ∀ J ∈ Ω, Commutes K J → ∀ z j : G, IsUniqueInvolution K z →
    IsUniqueInvolution J j → z = j

namespace EndHyp

variable {Ω : Set (Subgroup G)} (h : EndHyp Ω)
include h

theorem commute_z_of_le (h9 : Perp9 Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {P : Subgroup G} (hP : IsPGroup 2 P) (hKP : K ≤ P) {s : G}
    (hs : s ∈ P) : s * z = z * s := by
  have hΩ := h.thmD.hyp
  have hL : conjSub s K ∈ Ω := hΩ.conjInvariant s K hK
  have hLP : conjSub s K ≤ P := (conjSub_mono hKP).trans (conjSub_eq_self_of_mem hs).le
  have hzs : z = s * z * s⁻¹ := by
    by_cases hLK : conjSub s K = K
    · have h1 := hz.conj s
      rw [hLK] at h1
      exact hz.eq h1
    · obtain ⟨S, hPS⟩ := hP.exists_le_sylow
      have hc : Commutes K (conjSub s K) :=
        Q3CP.l67Gen G Ω hΩ S K (TC.mem_RSet_of_isPGroup hK (h.thmD.two K hK)) (conjSub s K)
          (TC.mem_RSet_of_isPGroup hL (h.thmD.two _ hL)) (hKP.trans hPS) (hLP.trans hPS)
          (fun e => hLK e.symm)
      exact h9 K hK (conjSub s K) hL hc z (s * z * s⁻¹) hz (hz.conj s)
  calc s * z = s * z * s⁻¹ * s := by group
    _ = z * s := by rw [← hzs]

private theorem pCore_comm_zGroup (h9 : Perp9 Ω) {q : G} (hq : q ∈ pCore 2 G) :
    ∀ x ∈ zGroup Ω, x * q = q * x := by
  have hle : zGroup Ω ≤ Subgroup.centralizer ({q} : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro u ⟨L, hL, hu⟩
    obtain ⟨S, hLS⟩ := (h.thmD.two L hL).exists_le_sylow
    have hqS : q ∈ (S : Subgroup G) := CFSG.pCore_isPGroup.le_sylow_of_normal S hq
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (h.commute_z_of_le h9 hL hu S.isPGroup' hLS hqS).symm
  exact fun x hx => Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

theorem zGroup_comm (h9 : Perp9 Ω) : ∀ a ∈ zGroup Ω, ∀ b ∈ zGroup Ω, a * b = b * a :=
  fun a ha b hb => h.pCore_comm_zGroup h9 (h.zGroup_le_pCore hb) a ha

theorem zGroup_mul_self (h9 : Perp9 Ω) : ∀ a ∈ zGroup Ω, a * a = 1 := by
  intro a ha
  have ha' : a ∈ Subgroup.closure {u : G | ∃ L ∈ Ω, IsUniqueInvolution L u} := ha
  clear ha
  induction ha' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨L, -, hu⟩ := hx
    exact hu.sq
  | one => exact one_mul 1
  | mul x y hx hy hxx hyy =>
    have hc : x * y = y * x := h.zGroup_comm h9 x hx y hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hc]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hxx, hyy, one_mul]
  | inv x hx hxx =>
    rw [← mul_inv_rev, hxx, inv_one]

theorem pCore_le_centralizer_zGroup (h9 : Perp9 Ω) :
    pCore 2 G ≤ Subgroup.centralizer (zGroup Ω : Set G) := by
  intro q hq
  exact Subgroup.mem_centralizer_iff.mpr fun x hx => h.pCore_comm_zGroup h9 hq x hx

end EndHyp

end CFSG.ClassicalInvolution.Q3.Sec13
