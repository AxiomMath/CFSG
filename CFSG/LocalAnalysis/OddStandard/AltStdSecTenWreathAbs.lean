module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenWreathCentral
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapThompson

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup Equiv Equiv.Perm

private theorem subgroupOf_map_subtype_self {G : Type*} [Group G] (C : Subgroup G)
    (B : Subgroup ↥C) : (B.map C.subtype).subgroupOf C = B := by
  rw [← Subgroup.comap_subtype (B.map C.subtype) C]
  exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective B

private theorem mem_map_subtype_iff {G : Type*} [Group G] {C : Subgroup G} (B : Subgroup ↥C) {g : G}
    (hg : g ∈ C) : g ∈ B.map C.subtype ↔ (⟨g, hg⟩ : ↥C) ∈ B := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨b, hb, hbg⟩
    have : b = ⟨g, hg⟩ := Subtype.ext hbg
    rwa [this] at hb
  · rintro hb
    exact ⟨⟨g, hg⟩, hb, rfl⟩

private theorem mul_mem_iff_of_relIndex_eq_two {G : Type*} [Group G] {C B : Subgroup G}
    (hB : B.relIndex C = 2) {a b : G} (ha : a ∈ C) (hb : b ∈ C) :
    b * a ∈ B ↔ (b ∈ B ↔ a ∈ B) := by
  have h := Subgroup.mul_mem_iff_of_index_two (H := B.subgroupOf C) hB
    (a := (⟨b, hb⟩ : ↥C)) (b := (⟨a, ha⟩ : ↥C))
  simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] using h

theorem relIndex_inf_eq_two {G : Type*} [Group G] {C T B : Subgroup G} (hTC : T ≤ C) (hBC : B ≤ C)
    (hB : B.relIndex C = 2) (hT : ¬ T ≤ B) : (T ⊓ B).relIndex T = 2 := by
  have hBT : B.relIndex T = 2 := by
    obtain ⟨a, haT, haB⟩ := Set.not_subset.1 hT
    refine (Subgroup.relIndex_eq_two_iff (H := B) (K := T)).2 ⟨a, haT, ?_⟩
    intro b hbT
    rw [xor_iff_iff_not, mul_mem_iff_of_relIndex_eq_two hB (hTC haT) (hTC hbT)]
    tauto
  rw [Subgroup.inf_relIndex_left]
  exact hBT

variable {G : Type} [Group G] [Finite G] {z : G} {ι : Perm (Fin 10) →* G} {x : G}

theorem false_of_wreath_abstract [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hC : CentData z ι) (hN : NoSwapConj z ι) (hx : x = ι τ₀)
    (hO : CFSG.oddCore (TwoSec x) = ⊥) {K : Subgroup (TwoSec x)}
    (hE : ExactShape (zbar hC hx) (diagSub (ι := ι) hx) 8)
    (hK : WreathK (zbar hC hx) (diagSub (ι := ι) hx) K) : False := by
  have hzCg : z ∈ centralizer ({x} : Set G) := z_mem_centralizer_of_eq hC hx
  have ht2 : zbar hC hx * zbar hC hx = 1 := by
    have hzsq : (⟨z, hzCg⟩ : ↥(centralizer ({x} : Set G))) * ⟨z, hzCg⟩ = 1 :=
      Subtype.ext hC.mul_self
    rw [zbar, ← QuotientGroup.mk_mul, hzsq, QuotientGroup.mk_one]
  obtain ⟨T, hTp, hTidx, hTx, hzT⟩ := exists_sylow_central hC hN hx hO hE hK
  set ψ : ↥(centralizer ({x} : Set G)) →* TwoSec x :=
    QuotientGroup.mk' (zpowers (selfC x)) with hψ
  set Nn : Subgroup (TwoSec x) := normalizer (K : Set (TwoSec x)) with hNn
  set B : Subgroup ↥(centralizer ({x} : Set G)) := Nn.comap ψ with hB
  set B' : Subgroup G := B.map (centralizer ({x} : Set G)).subtype with hB'
  set U : Subgroup G := T ⊓ B' with hU
  have hψsurj : Function.Surjective ψ := by
    rw [hψ]
    exact QuotientGroup.mk'_surjective _
  have hBidx : B.index = 2 := by
    rw [hB, Subgroup.index_comap_of_surjective Nn hψsurj, hNn]
    exact hK.index_normalizer ht2
  have hB'C : B' ≤ centralizer ({x} : Set G) := by
    rw [hB']
    exact Subgroup.map_subtype_le B
  have hB'idx : B'.relIndex (centralizer ({x} : Set G)) = 2 := by
    have hsub : B'.subgroupOf (centralizer ({x} : Set G)) = B := by
      rw [hB']
      exact subgroupOf_map_subtype_self (centralizer ({x} : Set G)) B
    change (B'.subgroupOf (centralizer ({x} : Set G))).index = 2
    rw [hsub]
    exact hBidx
  have hψz : ψ ⟨z, hzCg⟩ = zbar hC hx :=
    congrArg QuotientGroup.mk (Subtype.ext rfl)
  have hzB : (⟨z, hzCg⟩ : ↥(centralizer ({x} : Set G))) ∉ B := by
    rw [hB]
    intro hmem
    have hmem' : ψ ⟨z, hzCg⟩ ∈ Nn := Subgroup.mem_comap.1 hmem
    rw [hψz] at hmem'
    exact hK.t_notMem_normalizer hmem'
  have hzB' : z ∉ B' := by
    rw [hB']
    exact fun hmem => hzB ((mem_map_subtype_iff B hzCg).1 hmem)
  have hTB' : ¬ T ≤ B' := fun hle => hzB' (hle hzT)
  have hUT : U ≤ T := by
    rw [hU]
    exact inf_le_left
  have hUidx : U.relIndex T = 2 := by
    rw [hU]
    exact relIndex_inf_eq_two hTx hB'C hB'idx hTB'
  have hzU : z ∉ U := by
    rw [hU]
    exact fun hmem => hzB' hmem.2
  have hconj : ∀ g : G, g⁻¹ * z * g ∉ U := by
    intro g hmem
    rw [hU, hB'] at hmem
    have hg : g⁻¹ * z * g ∈ centralizer ({x} : Set G) := Subgroup.map_subtype_le B hmem.2
    have hnot := (mk_conj_notMem_normalizer hC hN hx hO hE hK g hg).1
    apply hnot
    have hmemB : (⟨g⁻¹ * z * g, hg⟩ : ↥(centralizer ({x} : Set G))) ∈ B :=
      (mem_map_subtype_iff B hg).1 hmem.2
    have hmemN : ψ ⟨g⁻¹ * z * g, hg⟩ ∈ Nn := Subgroup.mem_comap.1 hmemB
    rw [hψ, QuotientGroup.mk'_apply] at hmemN
    exact hmemN
  exact false_of_thompson_involution (z := z) hnonab hTp hTidx hUT hUidx hC.order hzT hzU hconj

end CFSG.OddStandard.AltStdSec.SwapPattern
