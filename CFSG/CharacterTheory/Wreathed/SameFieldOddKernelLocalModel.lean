module

public import CFSG.CharacterTheory.Wreathed.SameFieldOddKernelQuotient
public import CFSG.CharacterTheory.Wreathed.DegreeThreeModelFullCenter
public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldLayer

public noncomputable section

namespace CFSG.Wreathed.SameFieldOddKernel

open CFSG.Assembly.LowTwoRank
open DegreeThreeModelFullCenter SmallerRecognitionOriginalField

variable {X : Type*} [Group X]

theorem not_symFour_of_nonabelian_simple_subgroup (A : Subgroup X) [IsSimpleGroup A]
    (hA : ∃ a b : A, a * b ≠ b * a) : ¬ Nonempty (X ≃* Equiv.Perm (Fin 4)) := by
  rintro ⟨e⟩
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
  let : Group.IsSolvable X := Group.isSolvable_of_isSolvable_injective
    (f := e.toMonoidHom) e.injective
  let : Group.IsSolvable A := inferInstance
  have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr (inferInstance : Group.IsSolvable A)
  obtain ⟨a, b, hab⟩ := hA
  exact hab (hcomm a b)

variable {G : Type} [Group G] [Finite G]

theorem layer_local_quotient_conclusions
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) (L : Subgroup (K ⧸ O)) [L.Normal] (hindex : Odd L.index)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (tau : StatedLieTag) (htau : tau = .PSL ∨ tau = .PSU)
    (hmodel : StatedClassicalModel L tau 3 p f) :
    localQuotientConclusions p f
      (centralizerFullQuotient n hn (layerSylow S K hSK O L hindex)
        (layerCoordinates S e K hSK O hO L hindex)) := by
  let P := layerSylow S K hSK O L hindex
  let eP := layerCoordinates S e K hSK O hO L hindex
  let xL : L := wreathModelHom P eP (Original.x (2 ^ n))
  have hxL : orderOf xL = 2 := layerInvolution_order n hn S e K hSK O hO L hindex
  have hc := degree_three_model_full_center_local_quotient_parameter
    L p f hp hpodd hf tau htau hmodel xL hxL
  let E := originalFullCenterQuotientEquiv n hn P eP
  exact localQuotientConclusions_of_equiv E p f hp hpodd hf hc

theorem same_field_layer_local_data
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (K : Subgroup G) (hSK : (S : Subgroup G) ≤ K) (O : Subgroup K) [O.Normal]
    (hO : Odd (Nat.card O)) (L : Subgroup (K ⧸ O)) [L.Normal] (hindex : Odd L.index)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : (p ^ f % 4 = 1 ∧ StatedClassicalModel L .PSL 3 p f) ∨
      (p ^ f % 4 = 3 ∧ StatedClassicalModel L .PSU 3 p f)) :
    let P := layerSylow S K hSK O L hindex
    let eP := layerCoordinates S e K hSK O hO L hindex
    let Gamma := centralizerFullQuotient n hn P eP
    let A := centralizerSimpleLayer n hn P eP
    (¬ Nonempty (Gamma ≃* Equiv.Perm (Fin 4))) ∧
      IsSimpleGroup A ∧ (∃ a b : A, a * b ≠ b * a) ∧
      Subgroup.centralizer (A : Set Gamma) = ⊥ ∧ A.index = 2 ∧
      StatedClassicalModel A .PSL 2 p f ∧ Nat.card A = p ^ f * ((p ^ f) ^ 2 - 1) / 2 ∧
      ∀ (r a : ℕ), r.Prime → Odd r → 1 ≤ a → StatedClassicalModel A .PSL 2 r a →
        r ^ a = p ^ f ∧ r = p ∧ a = f := by
  let P := layerSylow S K hSK O L hindex
  let eP := layerCoordinates S e K hSK O hO L hindex
  let Gamma := centralizerFullQuotient n hn P eP
  let A := centralizerSimpleLayer n hn P eP
  have hlocal : localQuotientConclusions p f Gamma := by
    rcases hmodel with ⟨_, hmodel⟩ | ⟨_, hmodel⟩
    · exact layer_local_quotient_conclusions n hn S e K hSK O hO L hindex
        p f hp hpodd hf .PSL (Or.inl rfl) hmodel
    · exact layer_local_quotient_conclusions n hn S e K hSK O hO L hindex
        p f hp hpodd hf .PSU (Or.inr rfl) hmodel
  have hlarge := hlocal.2 hq
  let : IsSimpleGroup A := hlarge.1
  exact ⟨not_symFour_of_nonabelian_simple_subgroup A hlarge.2.1, hlarge⟩

end CFSG.Wreathed.SameFieldOddKernel
