module

public import CFSG.CGT.PushingUpLit.BHS6.SixTwelveC

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E : Subgroup Γ}

theorem isBTBlock_conjSub_of_nonCentral (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hE : E ∈ btBlocksG G T) (hsub : CFSG.Open.IsSubnormal E G) {x : Γ} (hx : x ∈ G)
    (hz : ⁅E, omegaOneCenterOf (A1b.conjSub x T)⁆ ≠ ⊥) :
    IsBTBlock G (A1b.conjSub x T) E := by
  obtain ⟨g, hg, hE₀⟩ := hE
  have hT' : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  have hT₀' : IsSylowTwoOf (A1b.conjSub g T) G := isSylowTwoOf_conjSub_of_mem hT' hg
  have hT₀ : IsSylowOf 2 (A1b.conjSub g T) G := isSylowOf_of_isSylowTwoOf hT₀'
  set T₀ : Subgroup Γ := A1b.conjSub g T with hT₀def
  have hy : x * g⁻¹ ∈ G := G.mul_mem hx (G.inv_mem hg)
  have hxy : A1b.conjSub x T = A1b.conjSub (x * g⁻¹) T₀ := by
    rw [hT₀def, ← A1b.conjSub_mul, mul_assoc, inv_mul_cancel, mul_one]
  rw [hxy] at hz ⊢
  set S : Subgroup Γ := A1b.conjSub (x * g⁻¹) T₀ with hSdef
  have hS' : IsSylowTwoOf S G := isSylowTwoOf_conjSub_of_mem hT₀' hy
  obtain ⟨-, hBN⟩ := six_twelve_a hG hT₀ (mem_btBlocksG_of_isBTBlock hE₀) hsub
  have hB1 : baum T₀ ≤ baumG G T₀ := by
    have := baum_conjSub_le_baumG (G := G) (T := T₀) (x := 1) G.one_mem
    rwa [A1b.conjSub_one] at this
  obtain ⟨c, hc, hcb⟩ := exists_conj_baum_of_le_of_le (N := baumG G T₀) hT₀' hS'
    (baumG_le hT₀') hB1 (baum_conjSub_le_baumG hy)
  have hcG : c ∈ G := baumG_le hT₀' hc
  have hcE : A1b.conjSub c E = E := BHS.conjSub_eq_of_mem_normalizer (hBN hc)
  have hE₁ : IsBTBlock G (A1b.conjSub c T₀) E := by
    have := isBTBlock_conj c hE₀
    rwa [BHS.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hcG), hcE] at this
  have hb : baum S = baum (A1b.conjSub c T₀) := by
    rw [hcb, baum_conjSub c T₀]
  exact isBTBlock_of_baum_eq hE₁ hb hz

theorem six_twelve_b_of_not_le_cStar (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hE : E ∈ btBlocksG G T) (hsub : CFSG.Open.IsSubnormal E G) {x : Γ} (hx : x ∈ G)
    (hEC : ¬ E ≤ cStarIn G (A1b.conjSub x T)) : IsBTBlock G (A1b.conjSub x T) E := by
  refine isBTBlock_conjSub_of_nonCentral hG hT hE hsub hx fun h => hEC ?_
  obtain ⟨g, hg, hE₀⟩ := hE
  have hEG : E ≤ G := hE₀.le
  have hEc : E ≤ G ⊓ Subgroup.centralizer (omegaOneCenterOf (A1b.conjSub x T) : Set Γ) := by
    intro e he
    refine Subgroup.mem_inf.mpr ⟨hEG he, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 : ⁅e, z⁆ ∈ (⁅E, omegaOneCenterOf (A1b.conjSub x T)⁆ : Subgroup Γ) :=
      Subgroup.commutator_mem_commutator he hz
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  exact hEc.trans (centralizer_le_cStarIn G (A1b.conjSub x T))

end CFSG.CGT.PushingUpLit.BHS6
