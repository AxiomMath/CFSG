module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf19Iface
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Final
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Final9
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf13Abel

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

theorem conj_inv_ne : g * z * g⁻¹ ≠ z := by
  intro h
  refine S.hH1 (conjSub g K) S.hg (g * z * g⁻¹) (S.hz.conj g) fun x hx => ?_
  rw [h]
  exact S.hos.commute_unique_piGen S.hπ S.hz x hx

theorem nbrPiTwin_of_beta
    (hβ : betaOf (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) π = {K, K'}) :
    NbrPiTwin K₀ K K' π g := by
  have hfirst : ∀ J' ∈ omegaNbr (CoreAssembly.conjClass K₀) K, J' ∈ π ∨ J' = K' := by
    intro J' hJ'
    by_cases hJπ : J' ∈ π
    · exact Or.inl hJπ
    · right
      have hmem := S.hos.nbr_diff_subset_beta S.hπ ⟨S.hK, hJ'⟩ hJπ
      rw [hβ] at hmem
      rcases hmem with h | h
      · exact absurd h hJ'.2.1
      · exact h
  refine ⟨hfirst, ?_⟩
  have hKg : conjSub g K ∈ CoreAssembly.conjClass K₀ := S.hos.graph.conjMem K S.hK g
  have hK'Ω : K' ∈ CoreAssembly.conjClass K₀ := S.hK'.1
  have hK'g : conjSub g K' ∈ CoreAssembly.conjClass K₀ := S.hos.graph.conjMem K' hK'Ω g
  have htw : conjSub g K' ∈ twinSet (CoreAssembly.conjClass K₀) (conjSub g K) :=
    ⟨hK'g, g * z * g⁻¹, S.hz.conj g, S.hz'.conj g⟩
  have hadj : nbrAdj (CoreAssembly.conjClass K₀) K (conjSub g K) :=
    adj_of_mem_isMaxOrb S.hos.graph S.hπ S.hg
  have hKnbr : K ∈ omegaNbr (CoreAssembly.conjClass K₀) (conjSub g K) :=
    (S.hos.graph.graph.symm hadj).2
  have hperp := (Q3T7M.l6_3 G (CoreAssembly.conjClass K₀) S.hs.hyp (conjSub g K) hKg
    (conjSub g K') htw).1
  have hKperp : K ∈ KPerp (CoreAssembly.conjClass K₀) (conjSub g K') := by
    rw [← hperp]
    exact Set.mem_insert_of_mem _ hKnbr
  have hne : ∀ {L : Subgroup G}, IsUniqueInvolution L z → conjSub g K' ≠ L := by
    intro L hL heq
    have h1 := S.hz'.conj g
    rw [heq] at h1
    exact S.conj_inv_ne (h1.eq hL)
  have hKne : K ≠ conjSub g K' := fun h => hne S.hz h.symm
  have hKnbr' : K ∈ omegaNbr (CoreAssembly.conjClass K₀) (conjSub g K') := by
    rcases hKperp with h | h
    · exact absurd h hKne
    · exact h
  have hnbrK : conjSub g K' ∈ omegaNbr (CoreAssembly.conjClass K₀) K :=
    (S.hos.graph.graph.symm (⟨hK'g, hKnbr'⟩ : nbrAdj (CoreAssembly.conjClass K₀) (conjSub g K') K)).2
  rcases hfirst _ hnbrK with h | h
  · exact h
  · exact absurd h (hne S.hz')

theorem beta_eq_pair_of_ne_eight {m : ℕ} (hm : 5 ≤ m) (hm8 : m ≠ 8)
    (J : AEIdent (fam K (conjSub g (piGen π))) m) :
    betaOf (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) π = {K, K'} := by
  have hB : TwinThinPf10.AEBlocks' m := by
    by_cases h7 : m ≤ 7
    · exact TwinThinPf10.aeBlocks_small hm h7
    · exact TwinThinPf10.aeBlocks_ge_nine (by omega)
  obtain ⟨α, hα, c, hlab⟩ := J.label K S.mem_fam_self
  exact S.beta_eq_pair' hm hm8 hB J hlab

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
