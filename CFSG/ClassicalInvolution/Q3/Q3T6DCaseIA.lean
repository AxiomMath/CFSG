module

public import CFSG.ClassicalInvolution.Q3.Q3T6DStmt
public import CFSG.ClassicalInvolution.Uniform.U7Comp
public import CFSG.ClassicalInvolution.Asc77.AscT3CoreComp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.T3Core CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Uniform CFSG.Assembly.LowTwoRank


section Comp

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem exists_g2Comp_of_quotViol (hΦ : HypOmegaModU (.sl2 3 1) Φ) (D : OmegaLieU 3 1 Φ)
    {K J : Subgroup X} {z j a : X} (hQ : QuotViol Φ K J z j a) :
    ∃ (C : G2Comp Φ) (R S : Subgroup G2Model), R ∈ G2Fund ∧ S ∈ G2Fund ∧ K = R.map C.ψ ∧
      J = S.map C.ψ := by
  obtain ⟨i, R, hR, hKR⟩ := D.fundamental K hQ.mem_left
  obtain ⟨j', S, hS, hJS⟩ := D.fundamental J hQ.mem_right
  obtain rfl : j' = i := by
    by_contra hij
    refine quotViol_false_of_commutes hQ ?_
    rw [hKR, hJS]
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
    exact D.commute i j' (Ne.symm hij) x y
  have hQ' : QuotViol Φ (R.map (D.hom j')) (S.map (D.hom j')) z j a := hKR ▸ hJS ▸ hQ
  have hc : D.kind j' = compModel 3 1 .G2 0 := D.kind_eq_g2_of_quotViol hΦ hR hS hQ'
  have hker := castHom_ker_le_center hc (D.hom j') (D.ker_le_center j')
  have hinj : Function.Injective (castHom hc (D.hom j')) :=
    RouteD.G2D4.injective_of_ker_le_center (p := 3) (e := 1) (by norm_num) (Or.inl rfl) 0 le_rfl
      _ hker
  obtain ⟨R', hR', hRR'⟩ := exists_map_castHom hc (D.hom j') hR
  obtain ⟨S', hS', hSS'⟩ := exists_map_castHom hc (D.hom j') hS
  refine ⟨⟨castHom hc (D.hom j'), hinj, ?_⟩, R', S', hR', hS', hKR.trans hRR'.symm,
    hJS.trans hSS'.symm⟩
  intro L hL
  obtain ⟨l, T, hT, hLT⟩ := D.fundamental L hL
  by_cases hlj : l = j'
  · subst hlj
    obtain ⟨T', hT', hTT'⟩ := exists_map_castHom hc (D.hom l) hT
    exact Or.inl ⟨T', hT', hLT.trans hTT'.symm⟩
  · right
    intro x hx y hy
    rw [hLT] at hx
    obtain ⟨x', -, rfl⟩ := hx
    rw [range_castHom hc] at hy
    obtain ⟨y', rfl⟩ := hy
    exact D.commute l j' hlj x' y'

theorem mem_members_of_quotViol_right (C : G2Comp Φ) {B D : Subgroup X} {z j a : X}
    (hB : B ∈ C.members) (hQ : QuotViol Φ B D z j a) : D ∈ C.members := by
  rcases C.cover D hQ.mem_right with ⟨S, hS, hDS⟩ | hc
  · exact ⟨hQ.mem_right, S, hS, hDS⟩
  · obtain ⟨-, R, -, rfl⟩ := hB
    exact (quotViol_false_of_commutes hQ fun x hx y hy =>
      (hc y hy x (Subgroup.map_le_range _ _ hx)).symm).elim

theorem mem_members_of_quotViol_left (C : G2Comp Φ) {B D : Subgroup X} {z j a : X}
    (hB : B ∈ C.members) (hQ : QuotViol Φ D B z j a) : D ∈ C.members := by
  rcases C.cover D hQ.mem_left with ⟨S, hS, hDS⟩ | hc
  · exact ⟨hQ.mem_left, S, hS, hDS⟩
  · obtain ⟨-, R, -, rfl⟩ := hB
    exact (quotViol_false_of_commutes hQ fun x hx y hy =>
      hc x hx y (Subgroup.map_le_range _ _ hy)).elim

end Comp

section Barimg

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem barImg_mem_members (hΩ : HypOmegaModU (.sl2 3 1) Ω) {H K : Subgroup G} (hK : K ∈ Ω)
    (hH : ∀ M ∈ aStar Ω K, M ≤ H) (C : G2Comp (oddQuotientFamily (restrictFamily Ω H)))
    (hKi : barImg H K ∈ C.members) : ∀ M ∈ aStar Ω K, barImg H M ∈ C.members := by
  have hΩg : HypOmegaGen Ω := hypGen_of_modU hΩ
  have hΛ : HypOmegaModU (.sl2 3 1) (restrictFamily Ω H) := hypOmegaModU_restrict hΩ H
  intro M hM
  induction hM with
  | refl => exact hKi
  | @tail B E hB hbc ih =>
    have hBΩ : B ∈ Ω := mem_of_mem_aStar hK hB
    have hBH : B ≤ H := hH B hB
    obtain ⟨hEΩ, h | h | ⟨ht, hne⟩⟩ := hbc
    · obtain ⟨zB, zE, hv⟩ := h
      have hEH : E ≤ H := hH E (Relation.ReflTransGen.tail hB ⟨hEΩ, Or.inl ⟨zB, zE, hv⟩⟩)
      obtain ⟨a, hQ⟩ := quotViol_of_aViol_three hΛ (subgroupOf_mem_restrictFamily hBΩ hBH)
        (aViol_subgroupOf hΩg hBH hEH hv)
      exact mem_members_of_quotViol_right C ih hQ
    · obtain ⟨zE, zB, hv⟩ := h
      have hEH : E ≤ H :=
        hH E (Relation.ReflTransGen.tail hB ⟨hEΩ, Or.inr (Or.inl ⟨zE, zB, hv⟩)⟩)
      obtain ⟨a, hQ⟩ := quotViol_of_aViol_three hΛ (subgroupOf_mem_restrictFamily hEΩ hEH)
        (aViol_subgroupOf hΩg hEH hBH hv)
      exact mem_members_of_quotViol_left C ih hQ
    · obtain ⟨-, z, hzB, hzE⟩ := ht
      have hEH : E ≤ H :=
        hH E (Relation.ReflTransGen.tail hB ⟨hEΩ, Or.inr (Or.inr ⟨⟨hEΩ, z, hzB, hzE⟩, hne⟩)⟩)
      exact C.twin_mem_members ih
        ⟨barImg_mem H hEΩ hEH, _, isUniqueInvolution_barImg H hzB hBH,
          isUniqueInvolution_barImg H hzE hEH⟩

theorem g2Comp_psi_surjective (hΩ : HypOmegaModU (.sl2 3 1) Ω) {H K : Subgroup G} (hK : K ∈ Ω)
    (hHdef : omegaGen (aStar Ω K) = H) (C : G2Comp (oddQuotientFamily (restrictFamily Ω H)))
    (hKi : barImg H K ∈ C.members) : Function.Surjective C.ψ := by
  have hMH : ∀ M ∈ aStar Ω K, M ≤ H := fun M hM => hHdef ▸ le_omegaGen hM
  have hcomp := barImg_mem_members hΩ hK hMH C hKi
  have hMQ : ∀ M ∈ aStar Ω K, M ≤ (C.ψ.range.comap (oddQuot ↥H)).map H.subtype := by
    intro M hM m hm
    obtain ⟨-, R, -, hMR⟩ := hcomp M hM
    refine ⟨⟨m, hMH M hM hm⟩, ?_, rfl⟩
    have hmem : oddQuot ↥H ⟨m, hMH M hM hm⟩ ∈ barImg H M :=
      ⟨⟨m, hMH M hM hm⟩, Subgroup.mem_subgroupOf.mpr hm, rfl⟩
    rw [hMR] at hmem
    exact Subgroup.map_le_range _ _ hmem
  have hHQ : H ≤ (C.ψ.range.comap (oddQuot ↥H)).map H.subtype :=
    hHdef.symm.le.trans (iSup₂_le fun M hM => hMQ M hM)
  intro y
  obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective _ y
  obtain ⟨q, hq', hqy⟩ := hHQ y'.2
  have hqy' : q = y' := Subtype.ext hqy
  subst hqy'
  exact hq'

end Barimg

end CFSG.ClassicalInvolution.Q3.Q3T6D
