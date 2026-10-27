module

public import CFSG.ClassicalInvolution.Asc77.AscT8W2
public import CFSG.ClassicalInvolution.Asc77.AscT8W3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace T8W

section ZStar

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem exists_zStar_conj [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hE : MuIsoE4 Ω W) (h1 : C26_1 p f)
    {S₂ : Sylow 2 G} (hRS₂ : R ≤ (S₂ : Subgroup G)) (hTS₂ : T ≤ (S₂ : Subgroup G))
    (hS₂X : IsSylow2In ((S₂ : Subgroup G) ⊓ omegaNbrGen Ω K) (omegaNbrGen Ω K)) :
    ∃ g ∈ omegaNbrGen Ω K, g⁻¹ * t * g ∈ (S₂ : Subgroup G) ∧ g⁻¹ * t * g ≠ t := by
  classical
  by_contra hcon
  push Not at hcon
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hKX : ¬ K ≤ omegaNbrGen Ω K :=
    T8S2.not_le_omegaNbrGen hs (s26XProper_E4 hs hdisc)
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hJX : J ≤ X := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hs.hJ
  have htJ : t ∈ J := hs.ht.mem
  have htX : t ∈ X := hJX htJ
  have htT : t ∈ (S₂ : Subgroup G) := by
    have hTsyl : IsSylow2In T J :=
      T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.hJ.1 hs.hT.1 hs.hT.2.1
    have h8 : 8 ≤ Nat.card T := hΩ.eight_le_of_mem_RSet hp hs.hT.1
    exact hTS₂ (T3.mem_of_isPGroup hs.ht hs.hT.2.1 hTsyl.2.1 (by omega))
  let SH : Sylow 2 ↥X := AscP1Nine3.sylowOfIsSylow2In₉ hS₂X
  have hSH : (SH : Subgroup ↥X) = ((S₂ : Subgroup G) ⊓ X).subgroupOf X := rfl
  have htSH : (⟨t, htX⟩ : ↥X) ∈ (SH : Subgroup ↥X) := by
    rw [hSH, Subgroup.mem_subgroupOf]
    exact ⟨htT, htX⟩
  let zt : ↥(SH : Subgroup ↥X) := ⟨⟨t, htX⟩, htSH⟩
  have hzZ : zt ∈ Subgroup.center ↥(SH : Subgroup ↥X) := by
    rw [Subgroup.mem_center_iff]
    intro s
    have hsmem : (s : ↥X) ∈ ((S₂ : Subgroup G) ⊓ X).subgroupOf X := s.2
    rw [Subgroup.mem_subgroupOf] at hsmem
    have h := sX_centralizes_t hs hE hRS₂ hTS₂ hKX hsmem.1 hsmem.2
    apply Subtype.ext
    apply Subtype.ext
    show (s : ↥X).1 * t = t * (s : ↥X).1
    calc (s : ↥X).1 * t = ((s : ↥X).1 * t * (s : ↥X).1⁻¹) * (s : ↥X).1 := by group
      _ = t * (s : ↥X).1 := by rw [h]
  have ht2 : t * t = 1 := hs.ht.sq
  have hzo : orderOf zt = 2 := by
    have h2 : orderOf (t : G) = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) hs.ht.ne_one
    have h3 : orderOf (⟨t, htX⟩ : ↥X) = 2 := (Subgroup.orderOf_mk t htX).trans h2
    exact (Subgroup.orderOf_mk _ htSH).trans h3
  have hwc : ∀ g : ↥X, g⁻¹ * (zt : ↥X) * g ∈ (SH : Subgroup ↥X) → g⁻¹ * (zt : ↥X) * g = zt := by
    intro g hg
    have hg' : g⁻¹ * (zt : ↥X) * g ∈ ((S₂ : Subgroup G) ⊓ X).subgroupOf X := hg
    rw [Subgroup.mem_subgroupOf] at hg'
    have := hcon g.1 g.2 hg'.1
    apply Subtype.ext
    show g.1⁻¹ * t * g.1 = t
    exact this
  obtain ⟨-, hcen⟩ := CFSG.Adapters.glauberman_zStar SH zt hzZ hzo hwc
  set N : Subgroup ↥X := classicalInvolutionOddCore ↥X with hNdef
  have hNodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥X
  set π := QuotientGroup.mk' N with hπ
  have hcen' : π ⟨t, htX⟩ ∈ Subgroup.center (↥X ⧸ N) := hcen
  have hGen := s26_genSection_omegaNbrGen (K := K) hp hq hΩ hs.stand.aEmpty
  have hDE := s26XEdgeless_E4 hs hdisc hE
  have htop : (⊤ : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X)) ∉
      oddQuotientFamily (restrictFamily Ω X) := s26_top_notMem_of_c26_1 h1 hs hdisc
  have hJΦ : (J.subgroupOf X).map π ∈ oddQuotientFamily (restrictFamily Ω X) :=
    ⟨_, ⟨J, hs.hJ.1, hJX, rfl⟩, rfl⟩
  have hzJ := isUniqueInvolution_subgroupOf hs.ht hJX
  have hzJb := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hNodd (J.subgroupOf X)) hzJ
  have hall : ∀ M ∈ oddQuotientFamily (restrictFamily Ω X), M = (J.subgroupOf X).map π := by
    intro M hM
    by_contra hne
    have hc : M ≤ Subgroup.centralizer ({π ⟨t, htX⟩} : Set (↥X ⧸ N)) := by
      intro m _
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_center_iff.mp hcen' m)
    have hnbr := AscE186.mem_omegaNbr_of_le_centralizer hp hq hGen.hyp hJΦ hM hne hzJb hc
    exact hDE _ hJΦ _ hM (Or.inl hnbr)
  apply htop
  have hgen := hGen.gen
  have : omegaGen (oddQuotientFamily (restrictFamily Ω X)) = (J.subgroupOf X).map π := by
    refine le_antisymm (iSup₂_le fun L hL => ?_) (le_omegaGen hJΦ)
    rw [hall L hL]
  rw [← hgen, this]
  exact hJΦ

end ZStar

end T8W

end CFSG.ClassicalInvolution.Asc77
