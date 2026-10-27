module

public import CFSG.CharacterTheory.Semidihedral.CentralizerStructure
public import CFSG.CharacterTheory.Semidihedral.AlternatingSevenExclusion
public import CFSG.Milestones.LR_dihedral_simple_recognition

public section

namespace CFSG.Semidihedral.FieldInterface

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.CentralizerResidual
open CFSG.Semidihedral.ReducedQuotients CFSG.Semidihedral.CentralizerAlternatives

variable {G : Type} [Group G] [Finite G]

theorem psl_two_field_size_ge_five {L : Type} [Group L] {p f : ℕ}
    (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel L .PSL 2 p f) :
    5 ≤ p ^ f := by
  have hthree : p ^ f ≠ 3 := by
    have hadmissible := hmodel.1
    change p.Prime ∧ 1 ≤ f ∧ 2 ≤ 2 ∧
      (2, p ^ f) ≠ (2, 2) ∧ (2, p ^ f) ≠ (2, 3) at hadmissible
    intro heq
    exact hadmissible.2.2.2.2 (by rw [heq])
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hpodd).pow
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq3 : 3 ≤ p ^ f := hp3.trans (Nat.le_pow (by omega : 0 < f))
  obtain ⟨k, hk⟩ := hodd
  omega

@[expose] def FieldAlternatives (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : Prop :=
  let Γ := involutionCentralizer n S f ⧸ centralizerFullKernel n S f
  let J := reducedResidual n S f
  (∀ U : Sylow 2 Γ, Nonempty (U ≃* DihedralGroup (2 ^ (n - 2)))) ∧
  ((n = 4 ∧ ∃ φ : Γ ≃* Equiv.Perm (Fin 4),
      J.map φ.toMonoidHom = alternatingGroup (Fin 4)) ∨
    (IsSimpleGroup (CFSG.generalizedFitting Γ) ∧
      (∃ x y : CFSG.generalizedFitting Γ, x * y ≠ y * x) ∧
      CFSG.generalizedFitting Γ ≤ J ∧
      Subgroup.centralizer (CFSG.generalizedFitting Γ : Set Γ) = ⊥ ∧
      (∀ U : Sylow 2 (CFSG.generalizedFitting Γ),
        ∃ m : ℕ, 2 ≤ m ∧ m ≤ n - 2 ∧ Nonempty (U ≃* DihedralGroup (2 ^ (m - 1)))) ∧
      (∃ p a : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ a ∧ 5 ≤ p ^ a ∧
        CFSG.Assembly.LowTwoRank.StatedClassicalModel (CFSG.generalizedFitting Γ) .PSL 2 p a)))

theorem centered_field_alternatives
    (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) : FieldAlternatives n S f := by
  refine ⟨every_reducedCentralizerSylow_dihedral n hn S f, ?_⟩
  rcases CentralizerStructure.centered_structural_alternatives n hn S f hG with hfour | hlayer
  · exact Or.inl hfour
  · obtain ⟨hsimple, hnonab, hLJ, hcentral, hSylow, _, _⟩ := hlayer
    let Γ := involutionCentralizer n S f ⧸ centralizerFullKernel n S f
    let : IsSimpleGroup (CFSG.generalizedFitting Γ) := hsimple
    let U : Sylow 2 (CFSG.generalizedFitting Γ) := Classical.choice Sylow.nonempty
    obtain ⟨m, hm, _, hU⟩ := hSylow U
    have hnotseven :=
      AlternatingSevenExclusion.dihedral_index_two_excludes_alternating_seven_layer
        hnonab (reducedCentralizerSylow n hn S f) (n - 1) (by omega)
        (by
          rw [show n - 1 - 1 = n - 2 by omega]
          exact (reducedCentralizerDihedralEquiv n hn S f).symm)
        (reducedResidual n S f) (reducedResidual_index n hn S f hG) hLJ
    rcases CFSG.Milestones.lr_dihedral_simple_recognition (CFSG.generalizedFitting Γ)
        hnonab U m hm hU with hfield | hseven
    · obtain ⟨p, a, hp, hpodd, ha, hmodel⟩ := hfield
      exact Or.inr ⟨hsimple, hnonab, hLJ, hcentral, hSylow,
        p, a, hp, hpodd, ha, psl_two_field_size_ge_five hp hpodd ha hmodel, hmodel⟩
    · exact (hnotseven hseven).elim

theorem involution_centralizer_field_or_four_point
    (n : ℕ) (hn : 4 ≤ n)
    (S₀ : Sylow 2 G) (f₀ : SemidihedralGroup n ≃* S₀)
    (hG : ∀ L : Subgroup G, L.index ≠ 2) :
    ∀ t : G, orderOf t = 2 →
      (∃ (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S), centeredInvolution n S f = t) ∧
      (∀ (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S), centeredInvolution n S f = t →
        involutionCentralizer n S f = Subgroup.centralizer {t} ∧
        (centralInvolution n S f : G) = t ∧ FieldAlternatives n S f) := by
  intro t ht
  obtain ⟨S, f, hz, _⟩ :=
    (InvolutionFusion.involution_centered_sylow_existence n hn S₀ f₀ hG t ht).2
  refine ⟨⟨S, f, hz⟩, ?_⟩
  intro S f hz
  refine ⟨?_, hz, centered_field_alternatives n hn S f hG⟩
  change Subgroup.centralizer {centeredInvolution n S f} = Subgroup.centralizer {t}
  rw [hz]

end CFSG.Semidihedral.FieldInterface
