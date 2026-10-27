module

public import CFSG.ClassicalInvolution.Q3.Q3TCCtx
public import CFSG.ClassicalInvolution.Q3.Q3TLKLink

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TC

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups


theorem exists_involution_of_fund_psl4 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {M : Subgroup G} {y : G} (c : TCtx3 .PSL 4 Ω M y) {L : Subgroup G} {w : G}
    (hL : IsClassicalMember3 L w) (hLy : L ∈ centralizingMembers Ω {y})
    {R : Subgroup (modelUniv .PSL 4 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 3 1 Nat.prime_three).D)
    (hLR : locImg Ω y L = R.map c.d.ψ) :
    ∃ k ∈ R, orderOf k = 2 ∧ c.d.ψ k = locMk Ω y ⟨w, le_centralizingLayer hLy hL.mem⟩ := by
  have hwY : w ∈ locLayer Ω y := le_centralizingLayer hLy hL.mem
  have hmw : locMk Ω y ⟨w, hwY⟩ ∈ locImg Ω y L :=
    ⟨_, Subgroup.mem_subgroupOf.mpr hL.mem, rfl⟩
  rw [hLR] at hmw
  obtain ⟨k, hkR, hk⟩ := hmw
  have hsq : locMk Ω y ⟨w, hwY⟩ * locMk Ω y ⟨w, hwY⟩ = 1 := by
    rw [← map_mul]
    have : (⟨w, hwY⟩ : ↥(locLayer Ω y)) * ⟨w, hwY⟩ = 1 :=
      Subtype.ext (Q3TLK.mul_self_eq_one_of_orderOf_eq_two3 hL.orderOf_eq_two)
    rw [this, map_one]
  have hk2 : k * k = 1 := by
    have hker : k * k ∈ c.d.ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, hk]
      exact hsq
    exact c.hY.central R hR (k * k) (R.mul_mem hkR hkR) (c.d.ker_le hker)
  have hk1 : k ≠ 1 := by
    intro h
    exact Q3TLK.locMk_involution_ne_one3 hLy hL (by rw [← hk, h, map_one])
  exact ⟨k, hkR, orderOf_eq_prime (by rw [pow_two]; exact hk2) hk1, hk⟩

theorem stdPair_of_normalizing_involution3
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {M : Subgroup G} {y : G}
    (c : TCtx3 .PSL 4 Ω M y) {K N : Subgroup G} {z w : G}
    (hK : IsClassicalMember3 K z) (hN : IsClassicalMember3 N w)
    (hKy : K ∈ centralizingMembers Ω {y}) (hNy : N ∈ centralizingMembers Ω {y})
    (hKM : K ≠ M) (hNM : N ≠ M) (hKN : K ≠ N) (hnorm : conjSub z N = N)
    (hnc : ¬ Commutes K N) :
    ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K N := by
  classical
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have hKQ : ¬ locImg Ω y K ≤ c.d.Q₁ := fun h => hnc (c.commutes_T_of_ne hKy h hNy hKN.symm)
  have hNQ : ¬ locImg Ω y N ≤ c.d.Q₁ := fun h => hnc (c.commutes_T_of_ne hNy h hKy hKN).symm
  obtain ⟨RK, hRK, hKR⟩ := c.exists_fund_of_ne hKy hKM hKQ
  obtain ⟨RN, hRN, hNR⟩ := c.exists_fund_of_ne hNy hNM hNQ
  have hncR : ¬ Commutes RK RN := fun h => hnc ((c.commutes_iff_fund hKy hNy hRK hKR hNR).mpr h)
  obtain ⟨kK, hkK, hkK2, hkKz⟩ := exists_involution_of_fund_psl4 c hK hKy hRK hKR
  obtain ⟨kN, hkN, hkN2, hkNw⟩ := exists_involution_of_fund_psl4 c hN hNy hRN hNR
  obtain ⟨iK, hiK⟩ : RK ∈ Models.longRootSet (K := GaloisField 3 1) (by norm_num : 2 ≤ 3 + 1) :=
    fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hRK
  obtain ⟨iN, hiN⟩ : RN ∈ Models.longRootSet (K := GaloisField 3 1) (by norm_num : 2 ≤ 3 + 1) :=
    fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hRN
  have ekK : kK = iK := hiK.eq_of_orderOf_eq_two h2 hkK hkK2
  have ekN : kN = iN := hiN.eq_of_orderOf_eq_two h2 hkN hkN2
  have hzY : z ∈ locLayer Ω y := le_centralizingLayer hKy hK.mem
  have himg : (RN.map (MulAut.conj kK).toMonoidHom).map c.d.ψ = RN.map c.d.ψ := by
    rw [Subgroup.map_map]
    have e1 : c.d.ψ.comp (MulAut.conj kK).toMonoidHom =
        (MulAut.conj (c.d.ψ kK)).toMonoidHom.comp c.d.ψ := by
      ext r
      simp [MulAut.conj_apply]
    rw [e1, ← Subgroup.map_map, ← hNR, hkKz, ← locImg_conjSub_layer N ⟨z, hzY⟩]
    show locImg Ω y (conjSub z N) = locImg Ω y N
    rw [hnorm]
  have hRNeq : RN.map (MulAut.conj kK).toMonoidHom = RN :=
    eq_of_map_eq_of_pow3 c.d.ψ c.d.ker_le c.ker_cop ((c.hY.pow3 RN hRN).map _)
      (c.hY.pow3 RN hRN) himg
  have hconjmem : kK * kN * kK⁻¹ ∈ RN := by
    have : kK * kN * kK⁻¹ ∈ RN.map (MulAut.conj kK).toMonoidHom :=
      ⟨kN, hkN, by simp [MulAut.conj_apply]⟩
    rwa [hRNeq] at this
  have hconjord : orderOf (kK * kN * kK⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj kK) kN
    simpa [MulAut.conj_apply, hkN2] using this
  have hcommk : kK * kN = kN * kK := by
    have h3 : kK * kN * kK⁻¹ = iN := hiN.eq_of_orderOf_eq_two h2 hconjmem hconjord
    rw [← ekN] at h3
    calc kK * kN = kK * kN * kK⁻¹ * kK := by group
      _ = kN * kK := by rw [h3]
  have hne : iK ≠ iN := by
    intro h
    apply hKN
    have hRKN : RK = RN := by
      rw [hiK.eq_longRootGroup h2, hiN.eq_longRootGroup h2, h]
    exact c.eq_of_locImg_eq hKy hNy (by rw [hKR, hNR, hRKN])
  have hcomm' : Commute iK iN := by
    rw [← ekK, ← ekN]
    exact hcommk
  rcases Models.commute_or_linearBlockStandardPair h2 (by norm_num : 3 ≤ 4) hiK hiN hcomm' hne
    with h | ⟨-, hW⟩
  · exact absurd h hncR
  · exact c.stdPair_of_fund hKy hNy hW hKR hNR

end CFSG.ClassicalInvolution.Q3.Q3TC
