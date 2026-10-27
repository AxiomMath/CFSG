module

public import CFSG.ClassicalInvolution.Q3.Q3WALoc
public import CFSG.ClassicalInvolution.RouteD.TWZAct
public import CFSG.ClassicalInvolution.RouteD.TWZLayer

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TLK

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TWZ
  CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.Open (classicalInvolutionOddCore)


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem conjSub_mem_and_image3 (hΩ : InClass3 Ω) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {x}) (y : ↥(locLayer Ω x)) :
    conjSub (y : G) N ∈ centralizingMembers Ω {x} ∧
      ∀ n ∈ conjSub (y : G) N, ∃ (k : G) (hk : k ∈ N) (hn : n ∈ locLayer Ω x),
        locMk Ω x ⟨n, hn⟩ =
          locMk Ω x y * locMk Ω x ⟨k, le_centralizingLayer hN hk⟩ * (locMk Ω x y)⁻¹ := by
  have hyx : (y : G) * x = x * y :=
    Subgroup.mem_centralizer_singleton_iff.mp (centralizingLayer_le_centralizer Ω {x} y.2)
  have hyx' : (y : G) * x * (y : G)⁻¹ = x := by rw [hyx]; group
  have hN' : conjSub (y : G) N ∈ centralizingMembers Ω {x} := by
    have := centralizingMembers_conj hΩ.conjInvariant (y : G) x
    rw [hyx'] at this
    rw [this]
    exact ⟨N, hN, rfl⟩
  refine ⟨hN', fun n hn => ?_⟩
  have hk : (y : G)⁻¹ * n * (y : G) ∈ N := mem_conjSub_iff.mp hn
  refine ⟨(y : G)⁻¹ * n * (y : G), hk, le_centralizingLayer hN' hn, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show n = (y : G) * ((y : G)⁻¹ * n * (y : G)) * (y : G)⁻¹
  group

theorem centralizes_of_actX_fix3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x) {c : G} (hcx : c * x = x * c)
    (hc : c ∈ Subgroup.normalizer (locLayer Ω x : Set G)) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {x})
    (hfix : ∀ (n : G) (hn : n ∈ N), actX c hc (locMk Ω x ⟨n, le_centralizingLayer hN hn⟩) =
      locMk Ω x ⟨n, le_centralizingLayer hN hn⟩) :
    N ≤ Subgroup.centralizer ({c} : Set G) := by
  have hcx' : c * x * c⁻¹ = x := by rw [hcx]; group
  have hN' : conjSub c N ∈ centralizingMembers Ω {x} := by
    have := centralizingMembers_conj hΩ.conjInvariant c x
    rw [hcx'] at this
    rw [this]
    exact ⟨N, hN, rfl⟩
  have hmk : ∀ (n : G) (hn : n ∈ N),
      locMk Ω x ⟨c * n * c⁻¹, le_centralizingLayer hN' (conj_mem_conjSub hn)⟩ =
        locMk Ω x ⟨n, le_centralizingLayer hN hn⟩ := fun n hn => hfix n hn
  have himg : locImg Ω x (conjSub c N) = locImg Ω x N := by
    ext q
    constructor
    · rintro ⟨⟨m, hmY⟩, hm, rfl⟩
      have hm' : m ∈ conjSub c N := Subgroup.mem_subgroupOf.mp hm
      have hn : c⁻¹ * m * c ∈ N := mem_conjSub_iff.mp hm'
      have hme : m = c * (c⁻¹ * m * c) * c⁻¹ := by group
      refine ⟨⟨c⁻¹ * m * c, le_centralizingLayer hN hn⟩, Subgroup.mem_subgroupOf.mpr hn, ?_⟩
      show locMk Ω x ⟨c⁻¹ * m * c, _⟩ = locMk Ω x ⟨m, hmY⟩
      have h2 := hmk (c⁻¹ * m * c) hn
      rw [← h2]
      congr 1
      apply Subtype.ext
      exact hme.symm
    · rintro ⟨⟨n, hnY⟩, hn, rfl⟩
      have hn' : n ∈ N := Subgroup.mem_subgroupOf.mp hn
      refine ⟨⟨c * n * c⁻¹, le_centralizingLayer hN' (conj_mem_conjSub hn')⟩,
        Subgroup.mem_subgroupOf.mpr (conj_mem_conjSub hn'), ?_⟩
      exact hmk n hn'
  have hNeq : conjSub c N = N := locImg_injOn3 hΩ hex hP1 hO3 hN' hN himg
  intro n hn
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hcn : c * n * c⁻¹ ∈ N := hNeq ▸ conj_mem_conjSub hn
  have hnY := le_centralizingLayer hN hn
  have hkernel : (⟨n⁻¹ * (c * n * c⁻¹), N.mul_mem (N.inv_mem hn) hcn |>
        fun h => le_centralizingLayer hN h⟩ : ↥(locLayer Ω x)) ∈
      N.subgroupOf (locLayer Ω x) ⊓ classicalInvolutionOddCore ↥(locLayer Ω x) := by
    refine ⟨Subgroup.mem_subgroupOf.mpr (N.mul_mem (N.inv_mem hn) hcn), ?_⟩
    refine (QuotientGroup.eq_one_iff _).mp ?_
    show locMk Ω x ⟨n⁻¹ * (c * n * c⁻¹), _⟩ = 1
    have h2 := hmk n hn
    have e : (⟨n⁻¹ * (c * n * c⁻¹), _⟩ : ↥(locLayer Ω x)) =
        (⟨n, hnY⟩ : ↥(locLayer Ω x))⁻¹ *
          ⟨c * n * c⁻¹, le_centralizingLayer hN' (conj_mem_conjSub hn)⟩ := rfl
    rw [e, map_mul, map_inv, h2, inv_mul_cancel]
  rw [TWZ.subgroupOf_inf_oddCore_eq_bot hex hN, Subgroup.mem_bot] at hkernel
  have h3 : n⁻¹ * (c * n * c⁻¹) = 1 := congrArg Subtype.val hkernel
  have h4 : c * n * c⁻¹ = n := by
    have := congrArg (fun w => n * w) h3
    simpa using this
  calc n * c = c * n * c⁻¹ * c := by rw [h4]
    _ = c * n := by group

end CFSG.ClassicalInvolution.Q3.Q3TLK
