module

public import CFSG.ClassicalInvolution.Q3.Q3T6OpenMuSym
public import CFSG.ClassicalInvolution.Uniform.U9G2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7E

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Comp

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}


theorem exists_g2Comp_of_quotViol (hΩ : HypOmegaModU (.sl2 3 1) Ω) (D : OmegaLieU 3 1 Ω)
    {K J : Subgroup G} {zK zJ a : G} (hQ : QuotViol Ω K J zK zJ a) :
    ∃ (C : G2Comp Ω) (R S : Subgroup G2Model), R ∈ G2Fund ∧ S ∈ G2Fund ∧ K = R.map C.ψ ∧
      J = S.map C.ψ := by
  obtain ⟨i, R, hR, hKR⟩ := D.fundamental K hQ.mem_left
  obtain ⟨j, S, hS, hJS⟩ := D.fundamental J hQ.mem_right
  obtain rfl : j = i := by
    by_contra hij
    refine quotViol_false_of_commutes hQ ?_
    rw [hKR, hJS]
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
    exact D.commute i j (Ne.symm hij) x y
  have hQ' : QuotViol Ω (R.map (D.hom j)) (S.map (D.hom j)) zK zJ a := hKR ▸ hJS ▸ hQ
  have hc : D.kind j = compModel 3 1 .G2 0 := D.kind_eq_g2_of_quotViol hΩ hR hS hQ'
  have hker := castHom_ker_le_center hc (D.hom j) (D.ker_le_center j)
  have hinj : Function.Injective (castHom hc (D.hom j)) :=
    RouteD.G2D4.injective_of_ker_le_center (p := 3) (e := 1) (by norm_num) (Or.inl rfl) 0 le_rfl
      _ hker
  obtain ⟨R', hR', hRR'⟩ := exists_map_castHom hc (D.hom j) hR
  obtain ⟨S', hS', hSS'⟩ := exists_map_castHom hc (D.hom j) hS
  refine ⟨⟨castHom hc (D.hom j), hinj, ?_⟩, R', S', hR', hS', hKR.trans hRR'.symm,
    hJS.trans hSS'.symm⟩
  intro L hL
  obtain ⟨l, T, hT, hLT⟩ := D.fundamental L hL
  by_cases hlj : l = j
  · subst hlj
    obtain ⟨T', hT', hTT'⟩ := exists_map_castHom hc (D.hom l) hT
    exact Or.inl ⟨T', hT', hLT.trans hTT'.symm⟩
  · right
    intro x hx y hy
    rw [hLT] at hx
    obtain ⟨x', -, rfl⟩ := hx
    rw [range_castHom hc] at hy
    obtain ⟨y', rfl⟩ := hy
    exact D.commute l j hlj x' y'

theorem mem_dstarComp_of_commutes_three (hΦ : HypOmegaGen Ω) {K M : Subgroup G} (hM : M ∈ Ω)
    (hc : Commutes M K) : M ∈ dstarComp Ω K := by
  by_cases hMK : M = K
  · subst hMK
    exact Relation.ReflTransGen.refl
  · have hcomm : ⁅M, K⁆ ≤ K := Subgroup.commutator_le.mpr fun x hx y hy => by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hc x hx y hy)]
      exact K.one_mem
    have hMN : M ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_commutator_le hcomm
    obtain ⟨R, hR, hRM, -⟩ := exists_mem_RSet_ge hM (isPGroup_two_bot' (G := G)) bot_le
    have hnb : M ∈ omegaNbr Ω K := ⟨hM, hMK, R, hR, hRM.1, hRM.1.trans hMN⟩
    exact Relation.ReflTransGen.single
      ⟨hM, Or.inl (Q3T6.Mu.omegaNbr_subset_omegaStarNbr hΦ K hnb)⟩

theorem QuotViol.mem_dstarComp_of_g2_three {z j a : G} (hgen : G2NonToralGenerate3)
    (hΩ : HypOmegaModU (.sl2 3 1) Ω) (C : G2Comp Ω) {R S : Subgroup G2Model} (hR : R ∈ G2Fund)
    (h : QuotViol Ω (R.map C.ψ) (S.map C.ψ) z j a) {R' : Subgroup G2Model} (hR' : R' ∈ G2Fund)
    (hR'Ω : R'.map C.ψ ∈ Ω) : R'.map C.ψ ∈ dstarComp Ω (R.map C.ψ) := by
  have hΩg : HypOmegaGen Ω := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ
  exact mem_of_invariant_g2_three hgen hΩ C hR h
    (fun _ hM _ hx => mem_conjStab_dstarComp hΩ.conjInvariant h.mem_left hM hx)
    (fun _ hM _ ht hne => by
      obtain ⟨hM'Φ, zz, hzM, hzM'⟩ := ht
      exact hM.tail ⟨hM'Φ, Or.inl (Q3T6.Mu.omegaNbr_subset_omegaStarNbr hΩg _
        (Q3CL.T3.twin_mem_omegaNbr hΩg (mem_dstarComp_symm h.mem_left hM).1 hM'Φ hne hzM hzM'))⟩)
    Relation.ReflTransGen.refl (Relation.ReflTransGen.single ⟨h.mem_right, Or.inl h.star⟩) hR'
    hR'Ω

theorem QuotViol.dstarConnected_of_split_three {z j a : G} (hgen : G2NonToralGenerate3)
    (hΦ : HypOmegaModU (.sl2 3 1) Ω) (D : OmegaLieU 3 1 Ω) {K J : Subgroup G}
    (h : QuotViol Ω K J z j a) : DStarConnected Ω := by
  have hΩg : HypOmegaGen Ω := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΦ
  obtain ⟨C, R, S, hR, hS, rfl, rfl⟩ := exists_g2Comp_of_quotViol hΦ D h
  refine dstarConnected_of_pivot h.mem_left fun M hMΩ => ?_
  rcases C.cover M hMΩ with ⟨R', hR', rfl⟩ | hc
  · exact QuotViol.mem_dstarComp_of_g2_three hgen hΦ C hR h hR' hMΩ
  · refine mem_dstarComp_of_commutes_three hΩg hMΩ fun x hx y hy => hc x hx y ?_
    obtain ⟨y', -, rfl⟩ := hy
    exact ⟨y', rfl⟩

end Comp

section Sect


theorem thm3SectBelow3_of_ih {n : ℕ} (hn : CITBelowT (.sl2 3 1) n) :
    ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n → ∀ Λ : Set (Subgroup Y),
      HypOmegaModU (.sl2 3 1) Λ → ¬ T3.DStarConnected (oddQuotientFamily Λ) → ∀ L ∈ Λ, AEmpty Λ L := by
  intro Y _ _ hY Λ hΛ hdis L hL
  by_contra hnA
  obtain ⟨J, zK, zJ, hv⟩ := not_aEmpty_iff.mp hnA
  obtain ⟨a, hQ⟩ := quotViol_of_aViol_three hΛ hL hv
  have hΛb : HypOmegaModU (.sl2 3 1) (oddQuotientFamily Λ) :=
    hypOmegaModU_oddQuotientFamily hΛ
  have hO : classicalInvolutionOddCore (Y ⧸ classicalInvolutionOddCore Y) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree Y
  have hlt : Nat.card (Y ⧸ classicalInvolutionOddCore Y) < n :=
    lt_of_le_of_lt (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)) hY
  obtain ⟨D⟩ := exists_omegaLieU hn hΛb ⟨_, mem_oddQuotientFamily hL⟩ hO hlt
  exact hdis (QuotViol.dstarConnected_of_split_three g2NonToralGenerate3_proved hΛb D hQ)

end Sect

end CFSG.ClassicalInvolution.Q3.Q3T7E
