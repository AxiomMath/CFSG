module

public import CFSG.ClassicalInvolution.SmallCases.NDB5dLift
public import CFSG.ClassicalInvolution.SmallCases.NDB5dAct
public import CFSG.ClassicalInvolution.SmallCases.NDBC1
import CFSG.ClassicalInvolution.Asc77.WP3SCSModel
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.Q3.TL3Lift
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieModelDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public section

namespace CFSG.ClassicalInvolution.NDB.WC

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer

theorem eq_or_eq_of_card_two {n : ℕ} (hn : n = 2) {a b : Fin n} (hab : a ≠ b) (i : Fin n) :
    i = a ∨ i = b := by
  subst hn
  have h1 : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have := a.2
  have := b.2
  have := i.2
  by_cases h : i.val = a.val
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext (by omega))

section Group

variable {G : Type} [Group G]

theorem mem_normalizer_of_conjSub_eq {g : G} {K : Subgroup G} (h : conjSub g K = K) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
  have e : g * x * g⁻¹ ∈ K ↔ g⁻¹ * (g * x * g⁻¹) * g ∈ K := by
    conv_lhs => rw [← h]
    exact mem_conjSub_iff
  rw [e, show g⁻¹ * (g * x * g⁻¹) * g = x by group]

theorem commute_of_comm_mem_oddCoreIn {s a b : G} (ha : a ∈ Subgroup.centralizer ({s} : Set G))
    (hb : b ∈ Subgroup.centralizer ({s} : Set G))
    (h : a⁻¹ * b⁻¹ * a * b ∈ oddCoreIn (Subgroup.centralizer ({s} : Set G))) :
    oddQuotMk s ⟨a, ha⟩ * oddQuotMk s ⟨b, hb⟩ = oddQuotMk s ⟨b, hb⟩ * oddQuotMk s ⟨a, ha⟩ := by
  set C := Subgroup.centralizer ({s} : Set G)
  have hC : a⁻¹ * b⁻¹ * a * b ∈ C :=
    C.mul_mem (C.mul_mem (C.mul_mem (C.inv_mem ha) (C.inv_mem hb)) ha) hb
  have h1 := oddQuotMk_eq_one_of_mem_oddCoreIn h hC
  have e : (⟨a⁻¹ * b⁻¹ * a * b, hC⟩ : C) = (⟨a, ha⟩ : C)⁻¹ * (⟨b, hb⟩ : C)⁻¹ * ⟨a, ha⟩ * ⟨b, hb⟩ :=
    rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  calc oddQuotMk s ⟨a, ha⟩ * oddQuotMk s ⟨b, hb⟩
      = oddQuotMk s ⟨b, hb⟩ * oddQuotMk s ⟨a, ha⟩ * ((oddQuotMk s ⟨a, ha⟩)⁻¹ *
        (oddQuotMk s ⟨b, hb⟩)⁻¹ * oddQuotMk s ⟨a, ha⟩ * oddQuotMk s ⟨b, hb⟩) := by group
    _ = oddQuotMk s ⟨b, hb⟩ * oddQuotMk s ⟨a, ha⟩ := by rw [h1, mul_one]

theorem comm_mem_oddCoreIn {s a b : G} (ha : a ∈ Subgroup.centralizer ({s} : Set G))
    (hb : b ∈ Subgroup.centralizer ({s} : Set G))
    (h : oddQuotMk s ⟨a, ha⟩ * oddQuotMk s ⟨b, hb⟩ = oddQuotMk s ⟨b, hb⟩ * oddQuotMk s ⟨a, ha⟩) :
    a⁻¹ * b⁻¹ * a * b ∈ oddCoreIn (Subgroup.centralizer ({s} : Set G)) := by
  set A : ↥(Subgroup.centralizer ({s} : Set G)) := ⟨a, ha⟩
  set B : ↥(Subgroup.centralizer ({s} : Set G)) := ⟨b, hb⟩
  have h1 : oddQuotMk s (A⁻¹ * B⁻¹ * A * B) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc _ (oddQuotMk s A), h]
    group
  exact ⟨_, oddQuotMk_eq_one_iff.mp h1, rfl⟩

theorem commutator_modOdd {s : G} {M : Subgroup G} (hMs : M ≤ Subgroup.centralizer ({s} : Set G))
    (hM : ⁅M, M⁆ = M) : ⁅modOdd s M, modOdd s M⁆ = modOdd s M := by
  set C := Subgroup.centralizer ({s} : Set G)
  have hsub : ⁅M.subgroupOf C, M.subgroupOf C⁆ = M.subgroupOf C := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hMs, hM]
  rw [modOdd, ← Subgroup.map_commutator, hsub]

theorem le_map_derivedSeries {X Y : Type*} [Group X] [Group Y] (ψ : X →* Y) {R : Subgroup Y}
    (hR : R ≤ ψ.range) (hRp : ⁅R, R⁆ = R) (n : ℕ) : R ≤ (derivedSeries X n).map ψ := by
  induction n with
  | zero => rwa [derivedSeries_zero, ← MonoidHom.range_eq_map]
  | succ n ih =>
    rw [derivedSeries_succ, Subgroup.map_commutator, ← hRp]
    exact Subgroup.commutator_mono ih ih

end Group

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem conjSub_eq_of_psp (C : Asc77.XCtx p f Ω z) (hcard : C.D.card = 2)
    {i₀ i₁ : Fin C.D.card} (hi₀₁ : i₀ ≠ i₁) (hK₀ : modOdd z C.K = (C.psi i₀).range)
    (hi₁ : ¬ (C.D.tag i₁ = .PSL ∧ C.D.rank i₁ = 2)) {g : G}
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) : conjSub g C.K = C.K := by
  have hgz : g * z * g⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hg]
    group
  have hT : IsClassicalMember p f (conjSub g C.K) z := by
    have h := C.K_cl.conj g
    rwa [hgz] at h
  obtain ⟨j, hj, hjT⟩ := C.exists_A1_of_member (C.hΩ.conjInvariant g C.K C.hK) hT
  rcases eq_or_eq_of_card_two hcard hi₀₁ j with rfl | rfl
  · exact Cover.eq_of_modOdd_eq hT C.K_cl (hjT.trans hK₀.symm)
  · exact absurd hj hi₁

theorem mem_range_of_tq (C : Asc77.XCtx p f Ω z) (hcard : C.D.card = 2)
    {i₀ i₁ : Fin C.D.card} (hi₀₁ : i₀ ≠ i₁) (hi₀ : C.D.tag i₀ = .PSL ∧ C.D.rank i₀ = 2)
    (hK₀ : modOdd z C.K = (C.psi i₀).range) {N : Subgroup G} (hN : N ∈ tqMembers Ω z) {n : G}
    (hn : IsClassicalMember p f N n) (hnz : n ≠ z) :
    oddQuotMk z ⟨n, C.involution_mem_centralizer hN hn⟩ ∈ (C.psi i₁).range := by
  obtain ⟨j, R, hR, hRN⟩ := C.exists_fund_of_mem hN
  have hnN := oddQuotMk_mem_modOdd (C.involution_mem_exactCore hN hn)
    (C.involution_mem_centralizer hN hn)
  rcases eq_or_eq_of_card_two hcard hi₀₁ j with rfl | rfl
  · exfalso
    rw [C.fund_eq_top j hi₀ hR, Subgroup.map_top] at hRN
    have hzR : oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ ∈ (C.psi j).range := by
      rw [← hK₀]
      exact oddQuotMk_mem_modOdd C.K_cl.mem _
    exact hnz (C.classical_of_range hN hn hRN.symm hzR)
  · rw [← hRN] at hnN
    exact Subgroup.map_le_range _ _ hnN

end CFSG.ClassicalInvolution.NDB.WC
