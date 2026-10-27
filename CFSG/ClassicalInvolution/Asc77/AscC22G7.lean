module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabEdge
public import CFSG.ClassicalInvolution.Asc77.AscIHSectKB

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.CurtisTits

namespace C22G

set_option linter.unusedSectionVars false

section Linear

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}


theorem ih8_dstarConnected_psl4 (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hq4 : p ^ f % 4 = 1) {t : StatedLieTag} {k e : ℕ} (M : Ih8Model p f Ω t k e)
    (ht : t = .PSL) (hk : k = 4) : T3.DStarConnected Ω := by
  subst ht hk
  by_cases hne : Ω.Nonempty
  swap
  · intro K hK
    exact absurd ⟨K, hK⟩ hne
  have hD4 : (StatedLieTag.PSL) ≠ .trialityD4 := by decide
  have hG2 : (StatedLieTag.PSL) ≠ .G2 := by decide
  have hnpsl : ¬ (StatedLieTag.PSL = .PSL ∧ (4 : ℕ) = 2) := by simp
  have hef : e = f := M.exp_eq_f hD4
  let nd : Fin 3 → Subgroup (modelUniv .PSL 4 p e Fact.out).K := fun i =>
    (WeakCT.blockSL2 (GaloisField p e) 3 i).range
  have hfund : ∀ i, nd i ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 p e Fact.out).D := by
    intro i
    have hlong : ModelFacts.IsLongestRoot (modelUniv .PSL 4 p e Fact.out).D (Pi.single i 1) :=
      ModelFacts.isLongestRoot_single .PSL 4 p e Fact.out trivial M.admissible i trivial
    refine ⟨1, Pi.single i 1, Or.inl hlong, ?_⟩
    rw [conjSub_one]
    exact (WeakCT.rankOne_eq_range i).symm
  have hmem : ∀ i, nd i ∈ M.cls := fun i => M.fund_subset_cls hne hG2 hD4 (hfund i)
  have hgen : ⨆ i, nd i = ⊤ := WeakCT.iSup_range_blockSL2 3
  have hpair : ∀ i j : Fin 3, (j : ℕ) = i + 1 → dstarAdj Ω ((nd i).map M.ψ) ((nd j).map M.ψ) := by
    intro i j hij
    obtain ⟨W, hW⟩ : ∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W (nd i) (nd j) :=
      ⟨_, (WeakCT.weakCTSystem_standard (K := GaloisField p e) 3).pair i j hij⟩
    subst hef
    exact M.muTab_dstarAdj_linear hΩ hp2 hq hD4 hnpsl hq4 (hmem i) (hmem j) hW
  have h01 := hpair 0 1 rfl
  have h12 := hpair 1 2 rfl
  refine M.dstarConnected_of_gens hΩ hG2 hD4 nd 0 hmem hgen fun i => ?_
  fin_cases i
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single h01
  · exact (Relation.ReflTransGen.single h01).tail h12

theorem ih8_dstarConnected_psu4 (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hq3 : p ^ f % 4 = 3) {t : StatedLieTag} {k e : ℕ} (M : Ih8Model p f Ω t k e)
    (ht : t = .PSU) (hk : k = 4) : T3.DStarConnected Ω := by
  subst ht hk
  by_cases hne : Ω.Nonempty
  swap
  · intro K hK
    exact absurd ⟨K, hK⟩ hne
  have hD4 : (StatedLieTag.PSU) ≠ .trialityD4 := by decide
  have hG2 : (StatedLieTag.PSU) ≠ .G2 := by decide
  have hnpsl : ¬ (StatedLieTag.PSU = .PSL ∧ (4 : ℕ) = 2) := by simp
  have hef : e = f := M.exp_eq_f hD4
  have hf1 : 1 ≤ e := M.admissible.2.1
  have hK := CFSG.LieType.Universal.card_galoisField_two_mul p e hf1
  have hq2 : p ^ e ≠ 2 := by
    rw [hef]
    omega
  obtain ⟨φ, hφ⟩ := RouteD.psu_model_equiv hp2 M.admissible
  let nd : Fin 3 → Subgroup (modelUniv .PSU 4 p e Fact.out).K := fun i =>
    (Phan.standardU (GaloisField p (2 * e)) p e 3 i).map φ.symm.toMonoidHom
  have hfund : ∀ i, nd i ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p e Fact.out).D := by
    intro i
    show (Phan.standardU (GaloisField p (2 * e)) p e 3 i).map φ.symm.toMonoidHom ∈ _
    rw [hφ, muTab_map_equiv_symm_map]
    exact ⟨_, Models.isLongRootSU2_range_blockEmb hK hp2 (by omega : (i : ℕ) + 2 ≤ 3 + 1)⟩
  have hmem : ∀ i, nd i ∈ M.cls := fun i => M.fund_subset_cls hne hG2 hD4 (hfund i)
  have hgen : ⨆ i, nd i = ⊤ := by
    have h1 := (Phan.weakPhanA_standard hK hq2 3).gen
    show ⨆ i, (Phan.standardU (GaloisField p (2 * e)) p e 3 i).map φ.symm.toMonoidHom = ⊤
    rw [← Subgroup.map_iSup, h1]
    exact Subgroup.map_top_of_surjective _ φ.symm.surjective
  have hpair : ∀ i j : Fin 3, (j : ℕ) = i + 1 →
      dstarAdj Ω ((nd i).map M.ψ) ((nd j).map M.ψ) := by
    intro i j hij
    have hW := (Phan.weakPhanA_standard hK hq2 3).pair i j hij
    have hW' := Models.unitaryBlockStandardPair_map hW φ.symm.toMonoidHom φ.symm.injective
    subst hef
    exact M.muTab_dstarAdj_unitary hΩ hp2 hq hD4 hnpsl hq3 (hmem i) (hmem j) hW'
  have h01 := hpair 0 1 rfl
  have h12 := hpair 1 2 rfl
  refine M.dstarConnected_of_gens hΩ hG2 hD4 nd 0 hmem hgen fun i => ?_
  fin_cases i
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single h01
  · exact (Relation.ReflTransGen.single h01).tail h12

end Linear

end C22G

end CFSG.ClassicalInvolution.Asc77
