module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.F1Loc
public import CFSG.CGT.PushingUpLit.SolKNA.R4.PMStd

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

namespace TightSylowDataTR

variable (hd : TightSylowDataTR r K z S W L t V)
include hd

theorem inf_le_inf_core : K ⊓ W ≤ (S : Subgroup G) ⊓ K := fun a ha => ⟨hd.hWS ha.2, ha.1⟩

theorem isCyclic_inf : IsCyclic ↥(K ⊓ W) := by
  obtain ⟨-, -, -, -, -, -, hUc, -, -⟩ :=
    Sec6Gen.exists_data_of_mem_USet hd.tight.hypGen hd.toTightSylowDataR.inf_mem_USet
  exact hUc

theorem relIndex_inf : (K ⊓ W).relIndex ((S : Subgroup G) ⊓ K) = 2 := by
  have hd0 := hd.toTightSylowDataR
  set R : Subgroup G := (S : Subgroup G) ⊓ K with hRdef
  have hRR : R ∈ RSet (CoreAssembly.conjClass K) := hd0.inf_mem_rSet
  have hUR : K ⊓ W ≤ R := hd.inf_le_inf_core
  obtain ⟨R', hR', hUR', -, hidx⟩ := hd0.inf_mem_USet
  have h1 := Subgroup.relIndex_mul_card (H := K ⊓ W) (K := R')
  have h2 := Subgroup.relIndex_mul_card (H := K ⊓ W) (K := R)
  rw [inf_eq_left.mpr hUR', hidx] at h1
  rw [inf_eq_left.mpr hUR] at h2
  have hpos : 0 < Nat.card ↥(K ⊓ W) := Nat.card_pos
  have h3 : (K ⊓ W).relIndex R * Nat.card ↥(K ⊓ W) = 2 * Nat.card ↥(K ⊓ W) := by
    rw [h2, hd.tight.natCard_rSet hRR, ← hd.tight.natCard_rSet hR', ← h1]
  exact Nat.eq_of_mul_eq_mul_right hpos h3

theorem natCard_inf_W : Nat.card ↥(K ⊓ W) = 2 ^ (r - 1) := by
  have h1 := hd.toTightSylowDataR.card_inf_eq
  rw [hd.toTightSylowDataR.natCard_inf] at h1
  have h3 := hd.tight.three_le
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [pow_succ, mul_comm] at h1
  rw [Nat.add_sub_cancel]
  exact (Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h1).symm

theorem natCard_V : Nat.card ↥V = 2 ^ (r - 1) := by
  rw [← hd.card_inf_eq_card]
  exact hd.natCard_inf_W

theorem exists_quat_inf :
    Nonempty (↥((S : Subgroup G) ⊓ K) ≃* QuaternionGroup (2 ^ (r - 2))) :=
  hd.exists_quat_of_mem_RSet hd.toTightSylowDataR.inf_mem_rSet

theorem le_normalizer_inf_W (hr : 4 ≤ r) :
    (S : Subgroup G) ≤ Subgroup.normalizer ((K ⊓ W : Subgroup G) : Set G) := by
  obtain ⟨e⟩ := hd.exists_quat_inf
  exact hd.toTightSylowDataR.le_normalizer_inf.trans
    (le_normalizer_of_isCyclic_of_relIndex_eq_two hr e hd.inf_le_inf_core hd.isCyclic_inf
      hd.relIndex_inf)

theorem inf_core_le_pm (hr : 4 ≤ r) : (S : Subgroup G) ⊓ K ≤ pmSubgroup (K ⊓ W) := by
  obtain ⟨e⟩ := hd.exists_quat_inf
  exact le_pmSubgroup_of_quat hr e hd.inf_le_inf_core hd.isCyclic_inf hd.relIndex_inf

theorem W_le_centralizer_inf : W ≤ Subgroup.centralizer ((K ⊓ W : Subgroup G) : Set G) := by
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact hd.toTightSylowDataR.comm_of_mem u hu.2 w hw

theorem W_le_pm : W ≤ pmSubgroup (K ⊓ W) := fun _ hw =>
  centralizer_le_pmSubgroup _ (hd.W_le_centralizer_inf hw)

theorem V_le_pm : V ≤ pmSubgroup (K ⊓ W) := hd.leW.trans hd.W_le_pm

theorem conjSub_V_le_pm (hr : 4 ≤ r) {r₀ : G} (hr₀ : r₀ ∈ (S : Subgroup G) ⊓ K) :
    conjSub r₀ V ≤ pmSubgroup (K ⊓ W) := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  have hr₀N : r₀ ∈ Subgroup.normalizer ((K ⊓ W : Subgroup G) : Set G) :=
    hd.le_normalizer_inf_W hr hr₀.1
  refine centralizer_le_pmSubgroup _ (Subgroup.mem_centralizer_iff.mpr fun u hu => ?_)
  have hv : r₀⁻¹ * x * r₀ ∈ W := hd.leW hx
  have hu' : r₀⁻¹ * u * r₀ ∈ K ⊓ W := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hr₀N) u).mp hu
    simpa using this
  have hcomm := hd.toTightSylowDataR.comm_of_mem _ hv _ hu'.2
  have h1 : r₀ * ((r₀⁻¹ * x * r₀) * (r₀⁻¹ * u * r₀)) * r₀⁻¹ =
      r₀ * ((r₀⁻¹ * u * r₀) * (r₀⁻¹ * x * r₀)) * r₀⁻¹ := by rw [hcomm]
  have e1 : r₀ * ((r₀⁻¹ * x * r₀) * (r₀⁻¹ * u * r₀)) * r₀⁻¹ = x * u := by group
  have e2 : r₀ * ((r₀⁻¹ * u * r₀) * (r₀⁻¹ * x * r₀)) * r₀⁻¹ = u * x := by group
  rw [e1, e2] at h1
  exact h1.symm

theorem actsPM_conj_iff (hr : 4 ≤ r) {D₁ D₂ : Subgroup G} (hD₁ : D₁ ≤ K) (hD₂ : D₂ ≤ K)
    (hc₁ : IsCyclic ↥D₁) (hc₂ : IsCyclic ↥D₂) (hn₁ : Nat.card ↥D₁ = 2 ^ (r - 1))
    (hn₂ : Nat.card ↥D₂ = 2 ^ (r - 1)) {g y : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G))
    (hy : y ∈ Subgroup.centralizer ({z} : Set G)) (hyD₁ : y ∈ Subgroup.normalizer (D₁ : Set G))
    (hyD₂ : g⁻¹ * y * g ∈ Subgroup.normalizer (D₂ : Set G)) :
    ActsPM D₁ y ↔ ActsPM D₂ (g⁻¹ * y * g) := by
  obtain ⟨e⟩ := hd.exists_quat_inf
  rw [← hd.tight.normEq] at hg hy
  exact actsPM_conj_iff_of_sylow hr hd.toTightSylowDataR.isSylow2In_inf e hD₁ hD₂ hc₁ hc₂ hn₁ hn₂ hg hy hyD₁
    hyD₂

theorem actsPM_conj_iff_inf (hr : 4 ≤ r) {g y : G} (hg : g ∈ Subgroup.centralizer ({z} : Set G))
    (hy : y ∈ Subgroup.centralizer ({z} : Set G))
    (hyU : y ∈ Subgroup.normalizer ((K ⊓ W : Subgroup G) : Set G))
    (hyU' : g⁻¹ * y * g ∈ Subgroup.normalizer ((K ⊓ W : Subgroup G) : Set G)) :
    ActsPM (K ⊓ W) y ↔ ActsPM (K ⊓ W) (g⁻¹ * y * g) :=
  hd.actsPM_conj_iff hr inf_le_left inf_le_left hd.isCyclic_inf hd.isCyclic_inf hd.natCard_inf_W
    hd.natCard_inf_W hg hy hyU hyU'

end TightSylowDataTR

end CFSG.CGT.PushingUpLit.SolKNA.R4
