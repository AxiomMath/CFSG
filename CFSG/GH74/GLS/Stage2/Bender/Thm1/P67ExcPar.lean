module

public import CFSG.LieType.Chevalley.ParabolicDiagonalFieldNormalizers
public import CFSG.GH74.GLS.Stage2.OddAut.RPData

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.OddAut

theorem conj_mem_diagonalFieldActors (τ : Tag) (K : Type) [Field K] :
    (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range ≤
      diagonalFieldActors τ K :=
  (Chevalley_diagonal_field_actor_data.1 τ K).2.2

theorem pCharData_adjoint (τ : Tag) (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] : PCharData (adjointGroup τ K) p (diagonalFieldActors τ K) := by
  classical
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element τ
  obtain ⟨⟨U, hU⟩, -⟩ := exceptional_ordinary_Sylow_opposition τ K p w₀ hw₀
  have hB := borel_self_normalizers τ K
  have hBC : borelGroup τ K ≤ adjointGroup τ K := by
    rw [← hB.1]
    exact inf_le_left
  have hBN : ∀ b ∈ borelGroup τ K,
      b ∈ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) := by
    intro b hb
    rw [← hB.1] at hb
    exact hb.2
  refine PCharData.of_standard (conj_mem_diagonalFieldActors τ K) U ?_
  intro P hNP hPtop
  have hBle : borelGroup τ K ≤ P.map (adjointGroup τ K).subtype := by
    intro b hb
    have hbC : b ∈ adjointGroup τ K := hBC hb
    have hbN : (⟨b, hbC⟩ : adjointGroup τ K) ∈
        Subgroup.normalizer ((U : Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K)) := by
      rw [hU, Subgroup.mem_normalizer_iff]
      intro u
      have := Subgroup.mem_normalizer_iff.1 (hBN b hb) (u : ModGL τ K)
      constructor
      · intro hu
        exact Subgroup.mem_subgroupOf.2 (this.1 (Subgroup.mem_subgroupOf.1 hu))
      · intro hu
        exact Subgroup.mem_subgroupOf.2 (this.2 (Subgroup.mem_subgroupOf.1 hu))
    exact ⟨_, hNP hbN, rfl⟩
  have hP'C : P.map (adjointGroup τ K).subtype ≤ adjointGroup τ K := Subgroup.map_subtype_le _
  have hcl := (borel_overgroup_classification τ K).1 _ hBle hP'C
  set P' : Subgroup (ModGL τ K) := P.map (adjointGroup τ K).subtype with hP'
  set J : Set (Fin τ.rank) := {i | weylElt τ K i 1 ∈ P'} with hJdef
  have hJ : J ≠ Set.univ := by
    intro h
    apply hPtop
    have hP'top : P' = adjointGroup τ K := by
      rw [hcl, h, (standard_parabolic_cells τ K).2.2.2.2.2.1]
    rw [eq_top_iff]
    intro x _
    have hx : (x : ModGL τ K) ∈ P' := by rw [hP'top]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hLevi := parabolic_root_radical_Levi_factors τ K J
  have hPJ : ∀ y : adjointGroup τ K, y ∈ P → (y : ModGL τ K) ∈ parabolicSubgroup τ K J := by
    intro y hy
    rw [← hcl]
    exact ⟨y, hy, rfl⟩
  have hQP : parabolicRadicalIn τ K J ≤ P := by
    intro x hx
    have h1 : (x : ModGL τ K) ∈ parabolicSubgroup τ K J := hLevi.1 (mem_parabolicRadicalIn.1 hx)
    rw [← hcl] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have hQn : ((parabolicRadicalIn τ K J).subgroupOf P).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hxQ : ((x : adjointGroup τ K) : ModGL τ K) ∈ parabolicRadical τ K J :=
      mem_parabolicRadicalIn.1 (Subgroup.mem_subgroupOf.1 hx)
    have hxP : ((x : adjointGroup τ K) : ModGL τ K) ∈ parabolicSubgroup τ K J := hLevi.1 hxQ
    have hgP := hPJ (g : adjointGroup τ K) g.2
    have key := hLevi.2.1.conj_mem
      (⟨((x : adjointGroup τ K) : ModGL τ K), hxP⟩ : ↥(parabolicSubgroup τ K J))
      (Subgroup.mem_subgroupOf.2 hxQ) ⟨((g : adjointGroup τ K) : ModGL τ K), hgP⟩
    have key' := Subgroup.mem_subgroupOf.1 key
    refine Subgroup.mem_subgroupOf.2 (mem_parabolicRadicalIn.2 ?_)
    simpa using key'
  have hQC : parabolicRadical τ K J ≤ adjointGroup τ K := parabolicRadical_le_adjointGroup J
  have hQp : IsPGroup p (parabolicRadicalIn τ K J) := by
    obtain ⟨-, hQp, -⟩ := hLevi.2.2.2.2.2.2.2.2.2.2.2.2 p
    exact hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQC).symm
  have hrigL :=
    (exact_parabolic_diagonal_field_normalizers_characteristic_p_ordinary (p := p) τ K hJ).2.2.2.1
  refine ⟨parabolicRadicalIn τ K J, hQP, hQn, hQp, fun α hαA hfix => ?_⟩
  obtain ⟨z, ⟨z', hz', hzz⟩, hzα⟩ := (hrigL α).1 ⟨hαA, hfix⟩
  have hzQ : z ∈ parabolicRadicalIn τ K J := by
    rw [← hzz]
    exact z'.2
  exact ⟨z, hzQ, hzα⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm1
