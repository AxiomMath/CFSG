module

public import CFSG.ClassicalInvolution.Asc77.WP3SCUConj
public import CFSG.ClassicalInvolution.Asc77.WP3SCUVertex
public import CFSG.ClassicalInvolution.Asc77.WP3SCUGenC

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Balance.StrongBalance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer

section End

variable (p f : ℕ) [Fact p.Prime]

@[expose] def ChainFrameEndPos : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K J K' : Subgroup G) (z t z' : G) (hs : ChainFrameSetting p f Ω K J K' z t z')
    (C : ChainCtx p f Ω z) (g a b : G) (M : Subgroup G), C.D.rank C.i₁ = 4 →
      ChainConjData hs C g a b M → ∀ j : Fin C.D.card,
        MovedByAll (conjSub g (Subgroup.closure ({z, t, z'} : Set G))) z (C.psi j).range →
          (C.D.tag j = .PSL ∨ C.D.tag j = .PSU) ∧
            ToralActionDiag 2 (C.D.tag j) (C.D.rank j) p (C.D.exp j) Fact.out (C.psi j)
              (modOdd z (conjSub g (Subgroup.closure ({z, t, z'} : Set G))))

end End

section Reduce

variable {p f : ℕ} [Fact p.Prime]

theorem chainFrameHyp51t_of_endPos (h : ChainFrameEndPos p f) : ChainFrameHyp51t p f := by
  intro G _ _ _ Ω K J K' z t z' hs
  rcases chainShape_cases hs.shape with h3 | h4
  · exact chainFrameHyp51t_rank3 hs h3
  obtain ⟨C, g, a, b, M, hrank, hd⟩ := chainFrame_conj hs h4 (by norm_num)
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  have hdd := hs.frame
  have hnc : ¬ ({z} : Set G) ⊆ Subgroup.center G :=
    Balance.not_subset_center_of_ne_one hs.nonabelian hdd.hz.ne_one
  have hzB : z ∈ conjSub g (Subgroup.closure ({z, t, z'} : Set G)) := by
    have htB : t ∈ Subgroup.closure ({z, t, z'} : Set G) := Subgroup.subset_closure (by simp)
    have := conj_mem_conjSub (n := g) htB
    rwa [hd.hgt] at this
  have haB : a ∈ conjSub g (Subgroup.closure ({z, t, z'} : Set G)) := by
    rw [hd.closure_eq]
    exact Subgroup.subset_closure (by simp)
  have hz : Hyp51At (conjSub g (Subgroup.closure ({z, t, z'} : Set G))) z :=
    FrameVertex.hyp51At_of_system_diag hp hq hΩ.conjInvariant hΩ.classical hs.below C.hc2 hnc
      hd.isElemAbelian hd.card_eight hzB C.hKz.ne_one haB hd.a_ne_one hd.a_ne_z hd.mem hd.cls
      ⟨C.D, fun j hmov => h G Ω K J K' z t z' hs C g a b M hrank hd j hmov⟩
  have := (hyp51At_conj g t (Subgroup.closure ({z, t, z'} : Set G))).mp
  rw [hd.hgt] at this
  exact this hz

theorem chainFrameGenT_of_endPos (h : ChainFrameEndPos p f) (hSU : SuPairGen) :
    ChainFrameGenT p f := by
  intro G _ _ _ Ω K J K' z t z' hs
  rcases chainShape_cases hs.shape with h3 | h4
  · exact chainFrameGenT_rank3 hs h3
  obtain ⟨C, g, a, b, M, hrank, hd⟩ := chainFrame_conj hs h4 (by norm_num)
  have hp := hs.odd
  have hq := hs.five
  have hΩ := hs.hyp
  have hzB : z ∈ conjSub g (Subgroup.closure ({z, t, z'} : Set G)) := by
    have htB : t ∈ Subgroup.closure ({z, t, z'} : Set G) := Subgroup.subset_closure (by simp)
    have := conj_mem_conjSub (n := g) htB
    rwa [hd.hgt] at this
  have h1 := centralizerGenerationStar_of_diagPos hSU hp hq hΩ.conjInvariant hΩ.classical C.hc2
    ⟨M, hd.mem⟩ hd.isElemAbelian hd.card_eight hzB C.hKz.ne_one
    ⟨C.D, fun j hmov => h G Ω K J K' z t z' hs C g a b M hrank hd j hmov⟩
  have h2 := centralizerGenerationStar_conj hΩ.conjInvariant g⁻¹ h1
  rw [conjSub_inv_conjSub] at h2
  have e : g⁻¹ * z * g⁻¹⁻¹ = t := by rw [← hd.hgt]; group
  rwa [e] at h2

end Reduce

end CFSG.ClassicalInvolution.Asc77
