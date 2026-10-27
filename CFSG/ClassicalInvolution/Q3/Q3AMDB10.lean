module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadPsp

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP
open scoped MatrixGroups commutatorElement

section Act

variable {G : Type} [Group G] {M : Subgroup G} {m : G}

@[expose] noncomputable def centAct (e : ↥M ⧸ classicalInvolutionOddCore ↥M ≃* SL(2, ZMod 3))
    (hCN : Subgroup.centralizer ({m} : Set G) ≤ Subgroup.normalizer (M : Set G)) :
    ↥(Subgroup.centralizer ({m} : Set G)) →* MulAut SL(2, ZMod 3) :=
  (Q3T6.normalizerToAutSL3 e).comp (Subgroup.inclusion hCN)

variable (e : ↥M ⧸ classicalInvolutionOddCore ↥M ≃* SL(2, ZMod 3))
  (hCN : Subgroup.centralizer ({m} : Set G) ≤ Subgroup.normalizer (M : Set G))

theorem centAct_eq_one_iff (g : ↥(Subgroup.centralizer ({m} : Set G))) :
    centAct e hCN g = 1 ↔ ∀ x ∈ M, ⁅(g : G), x⁆ ∈ oddCoreOf M :=
  Q3T6.normalizerToAutSL3_eq_one_iff e ⟨(g : G), hCN g.2⟩

theorem odd_orderOf_centAct (x : ↥(Subgroup.centralizer ({m} : Set G)))
    (hx : Odd (orderOf (x : G))) : Odd (orderOf (centAct e hCN x)) := by
  have h1 : orderOf (centAct e hCN x) ∣ orderOf x := orderOf_map_dvd _ x
  have h2 : orderOf (x : G) = orderOf x := Subgroup.orderOf_coe x
  exact Odd.of_dvd_nat (h2 ▸ hx) h1

theorem exists_sylow_centralized_of_centAct_eq_one [Finite G]
    (g : ↥(Subgroup.centralizer ({m} : Set G))) (hg : (g : G) * g = 1)
    (h : centAct e hCN g = 1) :
    ∃ P : Subgroup G, IsSylow2In P M ∧ P ≤ Subgroup.centralizer ({(g : G)} : Set G) := by
  by_cases hg1 : (g : G) = 1
  · obtain ⟨P, hP⟩ := exists_isSylow2In M
    refine ⟨P, hP, fun x _ => ?_⟩
    rw [hg1, Subgroup.mem_centralizer_singleton_iff]
    simp
  · have hW : IsPGroup 2 (Subgroup.zpowers (g : G)) := isPGroup_zpowers_of_mul_self_eq_one hg hg1
    have hWN : Subgroup.zpowers (g : G) ≤ Subgroup.normalizer (M : Set G) :=
      Subgroup.zpowers_le.mpr (hCN g.2)
    obtain ⟨R, hR, hRinv⟩ := AscL62.exists_sylow_normalized hW hWN
    have hgR : conjSub (g : G) R = R := hRinv _ (Subgroup.mem_zpowers _)
    refine ⟨R, hR, fun x hx => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxM : x ∈ M := hR.1 hx
    have hc1 : ⁅(g : G), x⁆ ∈ oddCoreOf M := (centAct_eq_one_iff e hCN g).mp h x hxM
    have hc2 : ⁅(g : G), x⁆ ∈ R := by
      have h1 : (g : G) * x * (g : G)⁻¹ ∈ R := by
        have := conj_mem_conjSub (n := (g : G)) hx
        rwa [hgR] at this
      have e1 : ⁅(g : G), x⁆ = ((g : G) * x * (g : G)⁻¹) * x⁻¹ := by
        simp only [commutatorElement_def]
      rw [e1]
      exact R.mul_mem h1 (R.inv_mem hx)
    have hc3 : ⁅(g : G), x⁆ = 1 :=
      eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard M) hc1
        (hR.2.1.to_le (Subgroup.zpowers_le.mpr hc2))
    simp only [commutatorElement_def] at hc3
    have h4 : (g : G) * x * (g : G)⁻¹ = x := mul_inv_eq_one.mp hc3
    exact (mul_inv_eq_iff_eq_mul.mp h4).symm

theorem centAct_eq_one_of_commute_sylow [Finite G] {P : Subgroup G} (hP : IsSylow2In P M)
    (g : ↥(Subgroup.centralizer ({m} : Set G))) (hc : ∀ x ∈ P, x * (g : G) = (g : G) * x) :
    centAct e hCN g = 1 := by
  refine (centAct_eq_one_iff e hCN g).mpr ?_
  have hV : ∀ y ∈ Subgroup.zpowers (g : G), conjSub y M = M := fun y hy =>
    mem_normalizer_iff_conjSub_eq.mp (Subgroup.zpowers_le.mpr (hCN g.2) hy)
  have key := badEdge_centSylow_three_modOdd (V := Subgroup.zpowers (g : G)) e hP hV (by
    intro r hr v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hcomm : Commute r ((g : G) ^ k) :=
      ((Commute.zpow_right (show Commute r (g : G) from hc r hr)) k)
    have : ⁅(g : G) ^ k, r⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr hcomm.symm
    rw [this]
    exact (oddCoreOf M).one_mem)
  exact fun x hx => key x hx (g : G) (Subgroup.mem_zpowers _)

end Act

section Member


variable {G : Type} [Group G] [Finite G]

theorem PspSetting.exists_iso_of_mem {Ω : Set (Subgroup G)} {K J K' : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hset : PspSetting Ω K J S R T W z t K') {M : Subgroup G} (hM : M ∈ Ω) :
    Nonempty (↥M ⧸ classicalInvolutionOddCore ↥M ≃* SL(2, ZMod 3)) := by
  obtain ⟨m, hm⟩ := hset.bad.std.stand.modU.classical M hM
  exact Q3T6.nonempty_equiv_of_memberU hm

theorem PspSetting.noTwins_all {Ω : Set (Subgroup G)} {K J K' : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hset : PspSetting Ω K J S R T W z t K') {M : Subgroup G} (hM : M ∈ Ω) :
    ∀ M' ∈ twinSet Ω M, M' = M :=
  T8.noTwins_of_mem hset.bad.std.stand.hyp.conjInvariant hset.bad.std.stand.trans
    hset.bad.std.noTwins hM

theorem PspSetting.centralizer_le_normalizer_of_mem {Ω : Set (Subgroup G)}
    {K J K' : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hset : PspSetting Ω K J S R T W z t K') {M : Subgroup G} (hM : M ∈ Ω) {m : G}
    (hm : IsUniqueInvolution M m) :
    Subgroup.centralizer ({m} : Set G) ≤ Subgroup.normalizer (M : Set G) :=
  T8.centralizer_le_normalizer_of_noTwins hset.bad.std.stand.hyp.conjInvariant hM
    (hset.noTwins_all hM) hm

end Member

end CFSG.ClassicalInvolution.Q3.Q3AM
