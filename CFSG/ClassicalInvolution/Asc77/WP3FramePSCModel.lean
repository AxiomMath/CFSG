module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Std
public import CFSG.ClassicalInvolution.Asc77.WP3FrameP1Shape

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.RouteD
open CFSG.Assembly.LowTwoRank

theorem no_commuting_fund_three {p : ℕ} [Fact p.Prime]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n e : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p e) (ht : t = .PSL ∨ t = .PSU) (hn : n = 3)
    {R S : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hS : S ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) (hne : R ≠ S)
    (hc : Commutes R S) : False := by
  subst hn
  rcases ht with rfl | rfl
  · have := four_le_of_commutes_psl hp2 le_rfl hR hS hne hc
    omega
  · have := four_le_of_commutes_psu hp2 hadm hR hS hne hc
    omega

section Lemmas

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem eq_of_modOdd_eq_of_localOddCentral (hΩ : InClass p f Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) {M N : Subgroup G} (hM : M ∈ centMembers Ω x)
    (hN : N ∈ centMembers Ω x) (h : modOdd x M = modOdd x N) : M = N := by
  have hθ := layerQuotientHom_injective (a := x) hΩ.conjInvariant
  have key : ∀ L ∈ centMembers Ω x,
      modOdd x L = (locImg Ω x L).map (layerQuotientHom hΩ.conjInvariant x) := by
    intro L hL
    have h1 := map_layerToOddQuot_subgroupOf (Ω := Ω) (a := x) (le_centLayer hL)
    change modOdd x L = ((L.subgroupOf (centLayer Ω x)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(centLayer Ω x)))).map
        (layerQuotientHom hΩ.conjInvariant x)
    rw [Subgroup.map_map]
    refine h1.symm.trans ?_
    congr 1
  exact locImg_injOn hΩ hP1 hM hN
    (Subgroup.map_injective hθ ((key M hM).symm.trans (h.trans (key N hN))))

omit [Fact p.Prime] [Finite G] in
theorem commutes_modOdd {x : G} {A B : Subgroup G} (h : Commutes A B) :
    Commutes (modOdd x A) (modOdd x B) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (h a ha b hb)

end Lemmas

section Chain

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  (C : ChainCtx p f Ω z)

namespace ChainCtx

include C

theorem exists_fund_i₁_of_ne (hex : ExactMembers Ω) (hp1 : LocalOddCentral Ω {z})
    (hT : ∀ J ∈ twinSet Ω C.K, J = C.K) {N : Subgroup G} (hN : N ∈ centMembers Ω z)
    (hNK : N ≠ C.K) :
    ∃ R ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D,
      R.map (C.psi C.i₁) = modOdd z N := by
  obtain ⟨n, hn⟩ := C.hΩ.classical N hN.1
  have hzn : z ≠ n := by
    intro h
    apply hNK
    refine hT N ⟨hN.1, z, C.hKz, ?_⟩
    rw [h]
    exact ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq hn
  obtain ⟨R, hR, hmod⟩ := C.exists_fund_i₁ hex hp1 (centMembers_subset_tqMembers hN) hn hzn
  refine ⟨R, hR, ?_⟩
  rw [hmod, exactCore_eq_self_of_mem_centMembers C.hΩ.classical hN]

theorem not_commutes_pair (h3 : C.D.rank C.i₁ = 3) (hIn : InClass p f Ω) (hex : ExactMembers Ω)
    (hp1 : LocalOddCentral Ω {z}) (hT : ∀ J ∈ twinSet Ω C.K, J = C.K) {M N : Subgroup G}
    (hM : M ∈ centMembers Ω z) (hN : N ∈ centMembers Ω z) (hMK : M ≠ C.K) (hNK : N ≠ C.K)
    (hMN : M ≠ N) (hc : Commutes M N) : False := by
  obtain ⟨R, hR, hRM⟩ := C.exists_fund_i₁_of_ne hex hp1 hT hM hMK
  obtain ⟨S, hS, hSN⟩ := C.exists_fund_i₁_of_ne hex hp1 hT hN hNK
  have hcomm : Commutes (R.map (C.psi C.i₁)) (S.map (C.psi C.i₁)) := by
    rw [hRM, hSN]
    exact commutes_modOdd hc
  have hperf : R ≤ ⁅R, R⁆ := (C.fund_perfect C.i₁ C.tag₁ hR).ge
  have hRS : Commutes R S :=
    ih8_commutes_of_commutes_map (C.psi C.i₁) (C.psi_ker C.i₁) hperf hcomm
  by_cases hRSeq : R = S
  · apply hMN
    refine eq_of_modOdd_eq_of_localOddCentral hIn hp1 hM hN ?_
    rw [← hRM, ← hSN, hRSeq]
  · exact no_commuting_fund_three C.hp (C.D.admissible C.i₁) C.tag₁ h3 hR hS hRSeq hRS

end ChainCtx

end Chain

end CFSG.ClassicalInvolution.Asc77
