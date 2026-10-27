module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Classes
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E8Classes

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction
open Subgroup
open scoped commutatorElement

@[expose] def e7PairsX : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ)) :=
  [(![1, 0, 0, 0, 0, 0, 0], ![1, 2, 3, 4, 3, 2, 1])]

@[expose] def e7PairsY : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ)) :=
  [(![0, 0, 0, 0, 1, 1, 0], ![1, 1, 2, 3, 2, 1, 1]),
    (![0, 0, 0, 0, 0, 1, 0], ![1, 2, 2, 3, 2, 1, 1])]

@[expose] def e7PairsZ : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ)) :=
  [(![0, 1, 1, 1, 0, 0, 0], ![1, 1, 1, 2, 2, 1, 0]),
    (![0, 0, 1, 0, 0, 0, 0], ![1, 1, 1, 2, 2, 2, 1]),
    (![0, 0, 1, 1, 0, 0, 0], ![1, 1, 1, 2, 2, 1, 1])]

theorem e7Pairs_check : ∀ D ∈ [e7PairsX, e7PairsY, e7PairsZ], ∀ p ∈ D,
    (List.ofFn p.1 ∈ Tag.artifactRoots .E7 ∧ 0 < height p.1) ∧
      (List.ofFn p.2 ∈ Tag.artifactRoots .E7 ∧ 0 < height p.2) ∧ p.1 ≠ p.2 ∧ p.1 ≠ -p.2 ∧
        List.ofFn (p.1 + p.2) ∈ Tag.artifactRoots .E7 := by
  decide +kernel

theorem e7Pairs_map : e7PairsX.map (fun p => p.1 + p.2) = [highRoot .E7] ∧
    e7PairsY.map (fun p => p.1 + p.2) = oddDerivE7YFrame ∧
    e7PairsZ.map (fun p => p.1 + p.2) = oddDerivE7ZFrame := by
  decide +kernel

theorem e7Pairs_mem_S₂ :
    (∀ p ∈ e7PairsY, p.1 ∈ oddDerivE7YDeriv.map Prod.fst ∧ p.2 ∈ oddDerivE7YDeriv.map Prod.fst) ∧
    ∀ p ∈ e7PairsZ, p.1 ∈ oddDerivE7ZDeriv.map Prod.fst ∧ p.2 ∈ oddDerivE7ZDeriv.map Prod.fst := by
  decide +kernel

theorem e7Pairs_roots
    {D : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ))}
    (hD : D ∈ [e7PairsX, e7PairsY, e7PairsZ]) :
    ∀ p ∈ D, (IsRoot .E7 p.1 ∧ 0 < height p.1) ∧ (IsRoot .E7 p.2 ∧ 0 < height p.2) ∧
      p.1 ≠ p.2 ∧ p.1 ≠ -p.2 ∧ IsRoot .E7 (p.1 + p.2) := by
  intro p hp
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6, h7⟩ := e7Pairs_check D hD p hp
  exact ⟨⟨isRoot_iff_mem_artifactRoots.2 h1, h2⟩, ⟨isRoot_iff_mem_artifactRoots.2 h3, h4⟩, h5, h6,
    isRoot_iff_mem_artifactRoots.2 h7⟩

theorem e7FramePt_eq_prod {K : Type} [Field K]
    (F : List (Fin Tag.E7.rank → ℤ)) :
    e7FramePt K F = (F.map fun σ => (e7RootElt σ : adjointGroup .E7 K)).prod := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_list_prod, List.map_map]
  rfl

variable {K : Type} [Field K]

theorem oddCommWitness_of_pairs_e7 [Finite K] [CharP K 2] {t : adjointGroup .E7 K}
    (D : List ((Fin Tag.E7.rank → ℤ) × (Fin Tag.E7.rank → ℤ)))
    (hD : ∀ p ∈ D, (IsRoot .E7 p.1 ∧ 0 < height p.1) ∧ (IsRoot .E7 p.2 ∧ 0 < height p.2) ∧
      p.1 ≠ p.2 ∧ p.1 ≠ -p.2 ∧ IsRoot .E7 (p.1 + p.2))
    (ht : t = e7FramePt K (D.map fun p => p.1 + p.2))
    (hodd : ∀ p ∈ D, (e7RootElt p.1 : adjointGroup .E7 K) ∈
        closure {c | c * t = t * c ∧ Odd (orderOf c)} ∧
      (e7RootElt p.2 : adjointGroup .E7 K) ∈ closure {c | c * t = t * c ∧ Odd (orderOf c)}) :
    ∃ P : Subgroup (adjointGroup .E7 K), IsPGroup 2 P ∧
      P ≤ closure {c | c * t = t * c ∧ Odd (orderOf c)} ∧ t ∈ ⁅P, P⁆ := by
  have hτ : Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 :=
    Or.inr (Or.inr (Or.inl rfl))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Set (adjointGroup .E7 K) :=
    {g | ∃ p ∈ D, g = e7RootElt p.1 ∨ g = e7RootElt p.2} with hSdef
  refine ⟨closure S, ?_, ?_, ?_⟩
  · refine ((isPGroup_posUnipotent (K := K) 2 .E7).comap_subtype
      (K := adjointGroup .E7 K)).to_le ?_
    rw [closure_le]
    rintro _ ⟨p, hp, rfl | rfl⟩
    · exact pinnedX_mem_rootSpan (S := {α | IsRoot .E7 α ∧ 0 < height α}) (hD p hp).1 1
    · exact pinnedX_mem_rootSpan (S := {α | IsRoot .E7 α ∧ 0 < height α}) (hD p hp).2.1 1
  · rw [closure_le]
    rintro _ ⟨p, hp, rfl | rfl⟩
    exacts [(hodd p hp).1, (hodd p hp).2]
  · rw [ht, e7FramePt_eq_prod, List.map_map]
    refine list_prod_mem fun g hg => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
    obtain ⟨h1, h2, hne, hne', hab⟩ := hD p hp
    have hc : (e7RootElt (p.1 + p.2) : adjointGroup .E7 K) =
        ⁅(e7RootElt p.1 : adjointGroup .E7 K), e7RootElt p.2⁆ := by
      refine Subtype.ext ?_
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [EvenOddRadical.pinnedX_conj_of_isRoot hτ CharTwo.two_eq_zero h1.1 h2.1 hne hne' hab 1 1,
        mul_one, mul_inv_cancel_right]
    show (e7RootElt (p.1 + p.2) : adjointGroup .E7 K) ∈ _
    rw [hc]
    exact commutator_mem_commutator (subset_closure ⟨p, hp, Or.inl rfl⟩)
      (subset_closure ⟨p, hp, Or.inr rfl⟩)

theorem residual_witness_e7_x [Finite K] [CharP K 2] :
    ∃ P : Subgroup (adjointGroup .E7 K), IsPGroup 2 P ∧
      P ≤ closure {c | c * e7FramePt K [highRoot .E7] = e7FramePt K [highRoot .E7] * c ∧
        Odd (orderOf c)} ∧ e7FramePt K [highRoot .E7] ∈ ⁅P, P⁆ := by
  have hτ : Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 := Or.inr (Or.inl rfl)
  obtain ⟨m, hm, hK⟩ := exists_card_eq_two_pow_eClasses K
  have ht : ((e7FramePt K [highRoot .E7] : adjointGroup .E7 K) : ModGL .E7 K) =
      pinnedX .E7 K (highRoot .E7) 1 := by
    simp [e7FramePt]
  have hD := e7Pairs_roots (D := e7PairsX) (by simp)
  have hodd : ∀ γ, IsRoot .E7 γ → 0 < height γ → (e7RootElt γ : adjointGroup .E7 K) ∈
      closure {c | c * e7FramePt K [highRoot .E7] = e7FramePt K [highRoot .E7] * c ∧
        Odd (orderOf c)} := by
    intro γ hγ hγp
    rcases (show m = 1 ∨ 2 ≤ m by omega) with h1 | hf
    · exact posUnipotent_le_closure_odd_E_two hτ (by rw [hK, h1, pow_one]) ht
        (pinnedX_mem_rootSpan (S := {α | IsRoot .E7 α ∧ 0 < height α}) ⟨hγ, hγp⟩ 1)
    · exact pinnedX_mem_closure_odd_E hτ hf hK ht hγ hγp 1
  exact oddCommWitness_of_pairs_e7 e7PairsX hD (by rw [e7Pairs_map.1]) fun p hp =>
    ⟨hodd _ (hD p hp).1.1 (hD p hp).1.2, hodd _ (hD p hp).2.1.1 (hD p hp).2.1.2⟩

theorem residual_witness_e7_y [Finite K] [CharP K 2] :
    ∃ P : Subgroup (adjointGroup .E7 K), IsPGroup 2 P ∧
      P ≤ closure {c | c * e7FramePt K oddDerivE7YFrame = e7FramePt K oddDerivE7YFrame * c ∧
        Odd (orderOf c)} ∧ e7FramePt K oddDerivE7YFrame ∈ ⁅P, P⁆ := by
  have hD := e7Pairs_roots (D := e7PairsY) (by simp)
  refine oddCommWitness_of_pairs_e7 e7PairsY hD (by rw [e7Pairs_map.2.1]) fun p hp => ⟨?_, ?_⟩
  · exact rootSpan_le_closure_odd_E7_y (t := e7FramePt K oddDerivE7YFrame) rfl _
      (pinnedX_mem_rootSpan (e7Pairs_mem_S₂.1 p hp).1 1)
  · exact rootSpan_le_closure_odd_E7_y (t := e7FramePt K oddDerivE7YFrame) rfl _
      (pinnedX_mem_rootSpan (e7Pairs_mem_S₂.1 p hp).2 1)

theorem residual_witness_e7_z [Finite K] [CharP K 2] :
    ∃ P : Subgroup (adjointGroup .E7 K), IsPGroup 2 P ∧
      P ≤ closure {c | c * e7FramePt K oddDerivE7ZFrame = e7FramePt K oddDerivE7ZFrame * c ∧
        Odd (orderOf c)} ∧ e7FramePt K oddDerivE7ZFrame ∈ ⁅P, P⁆ := by
  have hD := e7Pairs_roots (D := e7PairsZ) (by simp)
  refine oddCommWitness_of_pairs_e7 e7PairsZ hD (by rw [e7Pairs_map.2.2]) fun p hp => ⟨?_, ?_⟩
  · exact rootSpan_le_closure_odd_E7_z (t := e7FramePt K oddDerivE7ZFrame) rfl _
      (pinnedX_mem_rootSpan (e7Pairs_mem_S₂.2 p hp).1 1)
  · exact rootSpan_le_closure_odd_E7_z (t := e7FramePt K oddDerivE7ZFrame) rfl _
      (pinnedX_mem_rootSpan (e7Pairs_mem_S₂.2 p hp).2 1)

theorem residualMem_e7FramePt_x [Finite K] [CharP K 2] :
    Exc.ResidualMem (e7FramePt K e7FrameX) := by
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_e7FramePt_inner (K := K)).1
  obtain ⟨P, hP, hPx, hxP⟩ := residual_witness_e7_x (K := K)
  rw [← hg]
  exact E8.residualMem_conj_of_witness hP hPx hxP g

theorem residualMem_e7FramePt_y [Finite K] [CharP K 2] :
    Exc.ResidualMem (e7FramePt K e7FrameY) := by
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_e7FramePt_inner (K := K)).2.1
  obtain ⟨P, hP, hPx, hxP⟩ := residual_witness_e7_y (K := K)
  rw [← hg]
  exact E8.residualMem_conj_of_witness hP hPx hxP g

theorem residualMem_e7FramePt_z [Finite K] [CharP K 2] :
    Exc.ResidualMem (e7FramePt K e7FrameZ) := by
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_e7FramePt_inner (K := K)).2.2.1
  obtain ⟨P, hP, hPx, hxP⟩ := residual_witness_e7_z (K := K)
  rw [← hg]
  exact E8.residualMem_conj_of_witness hP hPx hxP g

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
