module

public import CFSG.CGT.PushingUpLit.BHS6.NestedLinearSym

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E F : Subgroup Γ}

theorem six_seven_one (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    (hF : F ∈ btBlocksG G T) (hFE : F ≤ E) :
    F = E ∨ ∃ g ∈ E, baum (A1b.conjSub g T) ≤ Subgroup.normalizer (F : Set Γ) := by
  obtain ⟨s, hs, hFs⟩ := hF
  rcases hE.type with ⟨n, hn2, hn⟩ | ⟨m, hm, hn⟩
  · exact Or.inl (eq_of_le_linear hG hT hE hn2 hn ⟨s, hs, hFs⟩ hFE)
  · rcases hFs.type with ⟨k, hk2, hk⟩ | ⟨r, hr, hr'⟩
    · exact (false_of_linear_le_symm hG hT hE hm hn ⟨s, hs, hFs⟩ hFE hk2 hk).elim
    · exact Or.inr (exists_conj_baum_le_normalizer_of_symm hG hT hE hm hn ⟨s, hs, hFs⟩ hFE hr
        hr')

theorem six_nine (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    (hmax : ∀ F : Subgroup Γ, IsBTBlock G T F → E ≤ F → F = E) : E ∈ btBlocksMax G T := by
  classical
  refine ⟨mem_btBlocksG_of_isBTBlock hE, fun L hL hEL => ?_⟩
  obtain ⟨s, hs, hLs⟩ := hL
  have hT' : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  have hS' : IsSylowTwoOf (A1b.conjSub s T) G := isSylowTwoOf_conjSub_of_mem hT' hs
  have hS : IsSylowOf 2 (A1b.conjSub s T) G := isSylowOf_of_isSylowTwoOf hS'
  have hEG : E ∈ btBlocksG G (A1b.conjSub s T) := by
    rw [btBlocksG_conjSub' hs]
    exact mem_btBlocksG_of_isBTBlock hE
  rcases six_seven_one hG hS hLs hEG hEL with h | ⟨g, hgL, hgN⟩
  · exact h.symm
  · have hgG : g ∈ G := hLs.le hgL
    have hS₂ : IsSylowTwoOf (A1b.conjSub g (A1b.conjSub s T)) G :=
      isSylowTwoOf_conjSub_of_mem hS' hgG
    set N : Subgroup Γ := G ⊓ Subgroup.normalizer (E : Set Γ) with hN
    have h₁ : baum (A1b.conjSub g (A1b.conjSub s T)) ≤ N :=
      le_inf ((inf_le_left : baum (A1b.conjSub g (A1b.conjSub s T)) ≤
        A1b.conjSub g (A1b.conjSub s T)).trans hS₂.1) hgN
    have h₂ : baum T ≤ N :=
      le_inf ((inf_le_left : baum T ≤ T).trans hT'.1) (baum_le_normalizer_of_isBTBlock hE)
    obtain ⟨n, hnN, hbn⟩ := exists_conj_baum_of_le_of_le hS₂ hT' inf_le_left h₁ h₂
    have hnG : n ∈ G := (Subgroup.mem_inf.mp hnN).1
    have hnE : n ∈ Subgroup.normalizer (E : Set Γ) := (Subgroup.mem_inf.mp hnN).2
    have hgNL : g ∈ Subgroup.normalizer (L : Set Γ) := Subgroup.le_normalizer hgL
    have hL₁ : IsBTBlock G (A1b.conjSub n (A1b.conjSub g (A1b.conjSub s T)))
        (A1b.conjSub n L) := by
      have h1 := isBTBlock_conj g hLs
      rw [BHS.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hgG),
        BHS.conjSub_eq_of_mem_normalizer hgNL] at h1
      have h2 := isBTBlock_conj n h1
      rwa [BHS.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hnG)] at h2
    have hb : baum T = baum (A1b.conjSub n (A1b.conjSub g (A1b.conjSub s T))) := by
      rw [baum_conjSub]
      exact hbn
    have hEL₁ : E ≤ A1b.conjSub n L := by
      have := A1b.conjSub_mono n hEL
      rwa [BHS.conjSub_eq_of_mem_normalizer hnE] at this
    have hz : ⁅A1b.conjSub n L, omegaOneCenterOf T⁆ ≠ ⊥ := fun h =>
      hE.nonCentral (le_bot_iff.mp (h ▸ Subgroup.commutator_mono hEL₁ le_rfl))
    have hL₁T : IsBTBlock G T (A1b.conjSub n L) := isBTBlock_of_baum_eq hL₁ hb hz
    have hEq : A1b.conjSub n L = E := hmax _ hL₁T hEL₁
    refine (Subgroup.eq_of_le_of_card_ge hEL ?_).symm
    have hc : Nat.card (A1b.conjSub n L) = Nat.card L :=
      Subgroup.card_map_of_injective (MulAut.conj n).injective
    rw [← hc, hEq]

end CFSG.CGT.PushingUpLit.BHS6
