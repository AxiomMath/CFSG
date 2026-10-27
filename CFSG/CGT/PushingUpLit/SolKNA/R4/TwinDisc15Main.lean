module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDisc15Lift
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDisc15Chain
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDisc15D2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDisc15Glue
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscSecConn

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Disc15

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

section Main

theorem involution_eq_of_secImg_eq {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}
    (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {J J₂ : Subgroup G} {t t₂ : G}
    (hJ : J ∈ tqMembers3 Ω c) (hJ₂ : J₂ ∈ tqMembers3 Ω c) (ht : IsUniqueInvolution J t)
    (ht₂ : IsUniqueInvolution J₂ t₂) (heq : secImg Ω c J₂ = secImg Ω c J)
    (hcomm : ∀ x ∈ oddCoreOf (Subgroup.centralizer ({c} : Set G)), x * t = t * x) : t₂ = t := by
  obtain ⟨htC, htY, hU⟩ := isUniqueInvolution_secImg hΩ hc2 hJ ht
  obtain ⟨htC₂, htY₂, hU₂⟩ := isUniqueInvolution_secImg hΩ hc2 hJ₂ ht₂
  rw [heq] at hU₂
  have hmk := hU.eq hU₂
  have hmem := QuotientGroup.eq.mp hmk
  have h1 := oddCore_coreHull_le hΩ hc2 hmem
  have hx : t⁻¹ * t₂ ∈ oddCoreOf (Subgroup.centralizer ({c} : Set G)) := h1
  set x : G := t⁻¹ * t₂ with hxdef
  have hc : x * t = t * x := hcomm x hx
  have htx : t * x = t₂ := by rw [hxdef]; group
  have hxx : x * x = 1 := by
    have e1 : t * x * (t * x) = (t * t) * (x * x) := by
      calc t * x * (t * x) = t * (x * t) * x := by group
        _ = t * (t * x) * x := by rw [hc]
        _ = (t * t) * (x * x) := by group
    rw [htx, ht₂.sq, ht.sq, one_mul] at e1
    exact e1.symm
  have hord : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hxx)
  have hodd : Odd (orderOf x) :=
    (oddCoreOf_odd_natCard (Subgroup.centralizer ({c} : Set G))).of_dvd_nat
      (Subgroup.orderOf_dvd_natCard _ hx)
  have h1' : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have hx1 : x = 1 := orderOf_eq_one_iff.mp h1'
  rw [hx1, mul_one] at htx
  exact htx.symm

variable {r n : ℕ}

theorem twoGroupR_of (hr : 4 ≤ r) (hB : TwinDiscBaseR r n) (h4 : Thm4RTwinBelow r n)
    (hT : Thm1RTwinInO2 r n) : TwoGroupR r n := by
  intro Y _ _ R S t₀ K K' z u J t W s hα hD J₂ hJ₂ t₂ ht₂ hne
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩ : HypOmegaGen Ω := s.core.hyp
  have hf := s.data.frame
  have hK : K ∈ Ω := hf.mem
  have hz : IsUniqueInvolution K z := hf.hz
  have hc2 : IsPGroup 2 (Subgroup.zpowers z) := isPGroup_zpowers_of_uniqueInvolution hz
  have hs := alphaStepsR hB s
  have hαzt : alphaOf (Subgroup.closure ({z, t} : Set Y)) = ⊥ := by
    rw [hs.alpha_zt hf]
    exact hα
  have hcomm := oddCore_comm_of_alpha_zt hz hαzt
  have hJtq := tq_of_mem_omegaOfSet s hf.hJ
  have hJ₂tq := tq_of_mem_omegaOfSet s hJ₂
  by_cases hsame : secImg Ω z J₂ = secImg Ω z J
  · exact absurd (involution_eq_of_secImg_eq hΩ hc2 hJtq hJ₂tq hf.ht ht₂ hsame hcomm) hne
  have hadj := sec_omegaStarNbr hr h4 hT s hJtq hJ₂tq hsame
  obtain ⟨o, ho, U, hU, hUJ₂, hUN⟩ := exists_core_adj_of_sec hΩ hc2 hJtq hJ₂tq hadj
  have hoC : o ∈ Subgroup.centralizer ({z} : Set Y) := oddCoreOf_le_self _ ho
  have hM₃ := conjSub_mem_omegaOfSet_of_cent hΩ.conjInvariant hz hf.hJ hoC
  have hz₃ := isUniqueInvolution_conj_of_comm hf.ht (hcomm o ho)
  have hM₃tq : conjSub o J ∈ tqMembers3 Ω z := conjSub_mem_tqMembers3 hΩ.conjInvariant hoC hJtq
  obtain ⟨B, hB2, c₁, c₂, c₃, c₄⟩ := exists_twoGroup_of_core_adj hΩ hK hz hf.hK' hf.hne hJ₂ hM₃
    hJ₂tq hM₃tq hU hUJ₂ hUN
  exact ⟨B, K, K', conjSub o J, J₂, hB2, mem_twinSet_self hK hz, hf.hK', hf.hne, hM₃, hz₃, hJ₂,
    ht₂, c₁, c₂, c₄, c₃⟩

theorem disc15R_of_inputs (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4RTwinBelow r n) :
    Disc15R r n := by
  intro Y _ _ R S t₀ h hdisc K K' z u J t W d huW hα hD M hM
  have hT : Thm1RTwinInO2 r n := thm1RTwinInO2_of_below hr hNo h.twinBelow
  have hB : TwinDiscBaseR r n := twinDiscBaseR_of h4 hT
  have hTq : DiscTqTzR r n :=
    discTqTz_of_connR hB (discSecConnTzR_of h4 (dstarConnectedTwinR_of hr hT))
  exact disc15R_of_twoGroup hTq (twoGroupR_of hr hB h4 hT) Y R S t₀ h hdisc K K' z u J t W d huW
    hα hD M hM

theorem disc15R_of_supply (hr : 4 ≤ r) (hNo : NoQ16E4) (h4 : Thm4TwinSupplyR r n) :
    Disc15R r n :=
  fun Y _ _ R S t₀ h => disc15R_of_inputs hr hNo (h4 h.below h.tbelow h.twinBelow) Y R S t₀ h

theorem disc15R_all (hNo : NoQ16E4) (h4 : ∀ r : ℕ, 4 ≤ r → ∀ n, Thm4TwinSupplyR r n) :
    ∀ r : ℕ, 4 ≤ r → ∀ n, Disc15R r n :=
  fun r hr n => disc15R_of_supply hr hNo (h4 r hr n)

end Main

end CFSG.CGT.PushingUpLit.SolKNA.R4.Disc15
