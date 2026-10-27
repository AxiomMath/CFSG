module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8Beta
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Blk

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem beta_eq_pair' {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8) (hB : TwinThinPf10.AEBlocks' n)
    (J : AEIdent (fam K (conjSub g (piGen π))) n) {α : Finset (Fin n)} {h : α.card = 4}
    {b : Bool}
    (hlab : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ = AE.memBar α h b) :
    betaOf (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) π = {K, K'} := by
  set β := betaOf (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) π with hβ
  have hk : IsPGroup 2 J.φ.ker := J.isPGroup_ker S.hOdd
  have hlab' := S.map_twin_eq hn hn8 J hlab
  have hfamΩ : fam K (conjSub g (piGen π)) ⊆ CoreAssembly.conjClass K₀ := fun L hL => S.fam_mem hL
  set B : Set (Subgroup (AE.AEQ n)) :=
    {M | ∃ L ∈ β, M = (L.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ} with hBdef
  have hinj : ∀ {L₁ L₂ : Subgroup G}, L₁ ∈ fam K (conjSub g (piGen π)) →
      L₂ ∈ fam K (conjSub g (piGen π)) →
      (L₁.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ =
        (L₂.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ → L₁ = L₂ :=
    fun h₁ h₂ he => S.eq_of_map_le hn J h₁ h₂ (le_of_eq he)
  have hblock : TwinThinPf8.IsBlock B := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨L, hL, rfl⟩
      obtain ⟨β', hβ', c, hl⟩ := J.label L (S.beta_subset_fam hL)
      exact ⟨β', hβ', c, hl⟩
    · intro s hs
      have hs' : s ∈ J.φ.range := by rw [J.range_eq]; exact hs
      obtain ⟨x, rfl⟩ := hs'
      have hxX : (x : G) ∈ conjSub g (piGen π) := (SetLike.ext_iff.mp S.fam_gen (x : G)).mp x.2
      rcases block_betaOf S.hos.graph S.hK S.hπ (x : G) with hc | hc
      · left
        ext M
        constructor
        · rintro ⟨M0, ⟨L, hL, rfl⟩, rfl⟩
          have : conjSub (x : G) L ∈ β := by rw [hβ, ← hc]; exact ⟨L, hL, rfl⟩
          exact ⟨conjSub (x : G) L, this, (S.map_conj_member J x L).symm⟩
        · rintro ⟨L', hL', rfl⟩
          have : L' ∈ conjSub (x : G) '' β := by rw [hc]; exact hL'
          obtain ⟨L, hL, rfl⟩ := this
          exact ⟨_, ⟨L, hL, rfl⟩, (S.map_conj_member J x L).symm⟩
      · right
        refine Set.disjoint_left.mpr ?_
        rintro M ⟨M0, ⟨L, hL, rfl⟩, rfl⟩ ⟨L2, hL2, hM⟩
        have hLf : L ∈ fam K (conjSub g (piGen π)) := S.beta_subset_fam hL
        have h1 : conjSub (x : G) L ∈ fam K (conjSub g (piGen π)) := fam_inv L hLf (x : G) hxX
        have h2 := hinj h1 (S.beta_subset_fam hL2)
          ((S.map_conj_member J x L).trans hM)
        exact Set.disjoint_left.mp hc ⟨L, hL, rfl⟩ (h2 ▸ hL2)
  have hKB : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ ∈ B :=
    ⟨K, S.K_mem_beta, rfl⟩
  have hK'B : (K'.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ ∈ B :=
    ⟨K', S.K'_mem_beta, rfl⟩
  have htrue : AE.memBar α h true ∈ B := by
    cases b
    · have e : (K'.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ =
          AE.memBar α h true := hlab'
      rw [← e]; exact hK'B
    · rw [← hlab]; exact hKB
  have hfalse : AE.memBar α h false ∈ B := by
    cases b
    · rw [← hlab]; exact hKB
    · have e : (K'.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ =
          AE.memBar α h false := hlab'
      rw [← e]; exact hK'B
  rcases hB α h B hblock htrue hfalse with hB2 | hall
  ·
    apply Set.Subset.antisymm
    · intro L hL
      have hLB : (L.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ ∈ B := ⟨L, hL, rfl⟩
      rw [hB2] at hLB
      have hLf := S.beta_subset_fam hL
      rcases hLB with h1 | h1
      ·
        have hlab_true : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ =
            AE.memBar α h true ∨ (K'.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ =
            AE.memBar α h true := by
          cases b
          · right; rw [hlab']; rfl
          · left; exact hlab
        rcases hlab_true with ht | ht
        · left; exact hinj hLf S.mem_fam_self (h1.trans ht.symm)
        · right; exact hinj hLf S.twin_mem_fam (h1.trans ht.symm)
      · have hlab_false : (K.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ =
            AE.memBar α h false ∨ (K'.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ =
            AE.memBar α h false := by
          cases b
          · left; exact hlab
          · right; rw [hlab']; rfl
        rcases hlab_false with ht | ht
        · left; exact hinj hLf S.mem_fam_self ((Set.mem_singleton_iff.mp h1).trans ht.symm)
        · right; exact hinj hLf S.twin_mem_fam ((Set.mem_singleton_iff.mp h1).trans ht.symm)
    · rintro L (rfl | rfl)
      · exact S.K_mem_beta
      · exact S.K'_mem_beta
  · exfalso
    refine S.false_of_fam_le_beta fun L hL => ?_
    obtain ⟨β', hβ', c, hl⟩ := J.label L hL
    have : (L.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ ∈ B :=
      hall _ ⟨β', hβ', c, hl⟩
    obtain ⟨L2, hL2, hL2e⟩ := this
    have := hinj hL (S.beta_subset_fam hL2) hL2e
    rw [this]; exact hL2

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
