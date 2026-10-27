module

public import CFSG.ClassicalInvolution.Asc77.AscR10E24
public import CFSG.ClassicalInvolution.Asc77.AscR10E20
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement


abbrev G2Model : Type := (modelUniv .G2 0 3 1 Nat.prime_three).K

abbrev G2Fund : Set (Subgroup G2Model) :=
  fundamentalSubgroups .G2 (modelUniv .G2 0 3 1 Nat.prime_three).D

section Comp

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

structure G2Comp (Ω : Set (Subgroup G)) where
  ψ : G2Model →* G
  inj : Function.Injective ψ
  cover : ∀ L ∈ Ω, (∃ R ∈ G2Fund, L = R.map ψ) ∨ ∀ x ∈ L, ∀ y ∈ ψ.range, x * y = y * x

@[expose] def G2Comp.members (C : G2Comp Ω) : Set (Subgroup G) :=
  {M | M ∈ Ω ∧ ∃ R ∈ G2Fund, M = R.map C.ψ}

namespace G2Comp

variable (C : G2Comp Ω)

theorem members_subset : C.members ⊆ Ω := fun _ h => h.1

theorem commutes_of_not_mem {M K : Subgroup G} (hM : M ∈ Ω) (hMi : M ∉ C.members)
    (hK : K ∈ C.members) : Commutes M K := by
  rcases C.cover M hM with ⟨R, hR, hMR⟩ | hc
  · exact absurd ⟨hM, R, hR, hMR⟩ hMi
  · obtain ⟨-, R, -, rfl⟩ := hK
    exact fun x hx y hy => hc x hx y (Subgroup.map_le_range _ _ hy)

theorem twin_mem_members {K J : Subgroup G} (hK : K ∈ C.members) (hJ : J ∈ twinSet Ω K) :
    J ∈ C.members := by
  obtain ⟨hJΩ, z, hzK, hzJ⟩ := hJ
  rcases C.cover J hJΩ with ⟨R, hR, hJR⟩ | hc
  · exact ⟨hJΩ, R, hR, hJR⟩
  · exfalso
    obtain ⟨-, R, -, rfl⟩ := hK
    obtain ⟨c, hcz⟩ := Subgroup.map_le_range _ _ hzK.mem
    have hcen : c ∈ Subgroup.center G2Model := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply C.inj
      rw [map_mul, map_mul, hcz]
      exact (hc z hzJ.mem _ ⟨y, rfl⟩).symm
    have hbot := RouteD.G2D4.center_modelUniv_g2d4_eq_bot (p := 3) (e := 1) (t := .G2)
      (by norm_num) (Or.inl rfl) 0 le_rfl
    rw [hbot, Subgroup.mem_bot] at hcen
    exact hzK.ne_one (by rw [← hcz, hcen, map_one])

end G2Comp

theorem quotViol_of_aViol_self_three (hΩ : HypOmegaModU (.sl2 3 1) Ω) {K J : Subgroup G}
    {zK zJ : G} (hK : K ∈ Ω) (hv : AViol Ω K J zK zJ) : ∃ a : G, QuotViol Ω K J zK zJ a := by
  have hΩg : HypOmegaGen Ω := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ
  obtain ⟨a, ha, haj, -, -, hne⟩ := exists_twin_three hΩ hK hv
  exact ⟨a, hK, hv.mem, hv.hzK, hv.hzJ, (AViol.ne_involution_gen hΩg hK hv).symm,
    AViol.comm_gen hΩg hv, hv.star, ha, haj, hne⟩

theorem OmegaLieU.kind_eq_g2_of_quotViol (hΩ : HypOmegaModU (.sl2 3 1) Ω) (D : OmegaLieU 3 1 Ω)
    {i : Fin D.card} {R S : Subgroup (D.kind i).G} (hR : R ∈ (D.kind i).fund)
    (hS : S ∈ (D.kind i).fund) {z j a : G}
    (h : QuotViol Ω (R.map (D.hom i)) (S.map (D.hom i)) z j a) :
    D.kind i = compModel 3 1 .G2 0 := by
  rcases D.valid i with ⟨t, n, e, ht, hadm, he, hc⟩ | ⟨h3, hc | hc⟩
  · have he1 : e = 1 := by rcases he with h' | ⟨-, h'⟩ <;> omega
    subst he1
    by_cases ht2 : t = .G2
    · subst ht2
      obtain ⟨hn, -⟩ := hadm.2.2
      subst hn
      exact hc
    · exfalso
      by_cases ht4 : t = .trialityD4
      · subst ht4
        exact quotViol_false_of_trialityD4_three hadm hΩ (D.card_eq (by norm_num)) hc
          (D.hom i) (D.ker_le_center i) hR hS h
      · exact quotViol_false_of_dich3 (stdDich3_all ModelFacts.stdDich3Orth
          ModelFacts.stdDich3Exc t n ht hadm ht2 ht4) ht hadm ht2 ht4 hΩ
          (D.card_eq (by norm_num)) hc (D.hom i) (D.ker_le_center i) hR hS h
  · exact (quotViol_false_of_sl23 hc (D.hom i) hR hS h).elim
  · exact (quotViol_false_of_m11 hc (D.hom i) (D.ker_le_center i) hR hS h).elim

theorem exists_g2Comp (hΩ : HypOmegaModU (.sl2 3 1) Ω) (D : OmegaLieU 3 1 Ω) {K : Subgroup G}
    (hK : K ∈ Ω) (hnA : ¬ AEmpty Ω K) :
    ∃ (C : G2Comp Ω) (R S : Subgroup G2Model) (J : Subgroup G) (zK zJ a : G),
      R ∈ G2Fund ∧ S ∈ G2Fund ∧ K = R.map C.ψ ∧ J = S.map C.ψ ∧ AViol Ω K J zK zJ ∧
        QuotViol Ω K J zK zJ a := by
  obtain ⟨J, zK, zJ, hv⟩ := not_aEmpty_iff.mp hnA
  obtain ⟨a, hQ⟩ := quotViol_of_aViol_self_three hΩ hK hv
  obtain ⟨i, R, hR, hKR⟩ := D.fundamental K hK
  obtain ⟨j, S, hS, hJS⟩ := D.fundamental J hv.mem
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
  refine ⟨⟨castHom hc (D.hom j), hinj, ?_⟩, R', S', J, zK, zJ, a, hR', hS', hKR.trans hRR'.symm,
    hJS.trans hSS'.symm, hv, hQ⟩
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

end Comp

end CFSG.ClassicalInvolution.Uniform
