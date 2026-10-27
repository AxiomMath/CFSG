module

public import CFSG.CharacterTheory.Semidihedral.DihedralNormalIndex
public import CFSG.CharacterTheory.Semidihedral.AlternatingSevenExclusion
public import CFSG.CharacterTheory.Wreathed.CyclicWeakClosure

public noncomputable section

namespace CFSG.Wreathed

universe u

@[expose] def DihedralFourPointAlternative (E : Type u) [Group E]
    (n : ℕ) (J : Subgroup E) : Prop :=
  n = 2 ∧ ∃ φ : E ≃* Equiv.Perm (Fin 4),
    J.map φ.toMonoidHom = alternatingGroup (Fin 4)

@[expose] def DihedralSimpleLayerAlternative (E : Type u) [Group E]
    (n : ℕ) (J : Subgroup E) : Prop :=
  IsSimpleGroup (CFSG.generalizedFitting E) ∧
    (∃ x y : CFSG.generalizedFitting E, x * y ≠ y * x) ∧
    Subgroup.centralizer (CFSG.generalizedFitting E : Set E) = ⊥ ∧
    CFSG.generalizedFitting E ≤ J ∧
    Odd ((CFSG.generalizedFitting E).relIndex J) ∧
    (∀ U : Sylow 2 (CFSG.generalizedFitting E),
      Nonempty (U ≃* DihedralGroup (2 ^ (n - 1)))) ∧
    ¬ Nonempty (CFSG.generalizedFitting E ≃* alternatingGroup (Fin 7)) ∧
    (CFSG.generalizedFitting E).index.factorization 2 = 1 ∧
    2 ^ (CFSG.generalizedFitting E).index.factorization 2 = 2

theorem dihedral_sylow_not_isCyclic {D : Type u} [Group D]
    (m : ℕ) (hm : 2 ≤ m) (e : D ≃* DihedralGroup (2 ^ (m - 1))) :
    ¬ IsCyclic D := by
  intro hcyclic
  have hone : 2 ^ (m - 1) = 1 :=
    DihedralGroup.isCyclic_iff.mp (e.isCyclic.mp hcyclic)
  have htwo : 2 ≤ 2 ^ (m - 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ m - 1)
  omega

theorem normal_sylow_equiv_actual_intersection
    {E : Type u} [Group E] [Finite E]
    (P : Sylow 2 E) (L : Subgroup E) [L.Normal] (U : Sylow 2 L) :
    Nonempty (U ≃* ↥((P : Subgroup E) ⊓ L)) := by
  obtain ⟨Q, hQ⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.normal_subgroup_sylow_intersection 2 L P
  let eQ : Q ≃* ↥((P : Subgroup E) ⊓ L) := by
    rw [hQ, ← Subgroup.inf_subgroupOf_right (P : Subgroup E) L]
    exact Subgroup.subgroupOfEquivOfLe inf_le_right
  exact ⟨(Sylow.equiv U Q).trans eQ⟩

theorem symmetricFour_no_nonabelian_simple_subgroup
    {E : Type u} [Group E] (L : Subgroup E) [IsSimpleGroup L]
    (hnonabelian : ∃ x y : L, x * y ≠ y * x)
    (e : E ≃* Equiv.Perm (Fin 4)) : False := by
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) :=
    Equiv.Perm.isSolvable (by simp)
  let : Group.IsSolvable E :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hcomm : ∀ x y : L, x * y = y * x :=
    IsSimpleGroup.comm_iff_isSolvable.mpr (inferInstance : Group.IsSolvable L)
  obtain ⟨x, y, hxy⟩ := hnonabelian
  exact hxy (hcomm x y)

theorem dihedral_layer_alternatives_exclusive
    {E : Type u} [Group E] (n : ℕ) (J : Subgroup E) :
    ¬ (DihedralFourPointAlternative E n J ∧
      DihedralSimpleLayerAlternative E n J) := by
  rintro ⟨⟨_, φ, _⟩, hL⟩
  let : IsSimpleGroup (CFSG.generalizedFitting E) := hL.1
  exact symmetricFour_no_nonabelian_simple_subgroup _ hL.2.1 φ

theorem dihedral_layer_alternatives
    {E : Type u} [Group E] [Finite E]
    (n : ℕ) (hn : 2 ≤ n) (hcore : CFSG.oddCore E = ⊥)
    (P : Sylow 2 E) (eP : P ≃* DihedralGroup (2 ^ n))
    (J : Subgroup E) [J.Normal] (hJ : J.index = 2)
    (T : Sylow 2 J) (eT : T ≃* DihedralGroup (2 ^ (n - 1)))
    (htrivial : ∀ (D : Type u) [Group D] [Finite D],
      IsPGroup 2 D → ∀ f : J →* D, f = 1) :
    DihedralFourPointAlternative E n J ∨
      DihedralSimpleLayerAlternative E n J := by
  have hprimecore : CFSG.pPrimeCore 2 E = ⊥ := by
    rw [← weakClosure_oddCore_eq_pPrimeCore]
    exact hcore
  have eP' : P ≃* DihedralGroup (2 ^ (n + 2 - 2)) := by
    rw [show n + 2 - 2 = n by omega]
    exact eP
  have eT' : T ≃* DihedralGroup (2 ^ (n + 2 - 3)) := by
    rw [show n + 2 - 3 = n - 1 by omega]
    exact eT
  rcases CFSG.Semidihedral.CentralizerAlternatives.generic_structural_alternatives
      (n + 2) (by omega) hprimecore P eP' J hJ T eT' htrivial with hfour | hsimple
  · obtain ⟨hnfour, φ, hφ⟩ := hfour
    exact Or.inl ⟨by omega, φ, hφ⟩
  · obtain ⟨hsimple, hnonabelian, hLJ, hC, hSylow, _, _⟩ := hsimple
    let : IsSimpleGroup (CFSG.generalizedFitting E) := hsimple
    let U₀ : Sylow 2 (CFSG.generalizedFitting E) := Classical.choice Sylow.nonempty
    obtain ⟨m, hm, _, ⟨eU₀⟩⟩ := hSylow U₀
    have hU₀nc : ¬ IsCyclic U₀ := dihedral_sylow_not_isCyclic m hm eU₀
    have ePk : P ≃* DihedralGroup (2 ^ (n + 1 - 1)) := by
      rw [show n + 1 - 1 = n by omega]
      exact eP
    obtain ⟨_, _, _, hOdd, ⟨eInt⟩, hfactorization, htwoPart⟩ :=
      CFSG.Semidihedral.DihedralNormalIndex.noncyclic_normal_dihedral_fills_index_two
        (n + 1) (by omega) P ePk (CFSG.generalizedFitting E) inferInstance
        J hJ hLJ U₀ hU₀nc
    rw [show n + 1 - 2 = n - 1 by omega] at eInt
    have hExact : ∀ U : Sylow 2 (CFSG.generalizedFitting E),
        Nonempty (U ≃* DihedralGroup (2 ^ (n - 1))) := by
      intro U
      obtain ⟨eU⟩ := normal_sylow_equiv_actual_intersection P
        (CFSG.generalizedFitting E) U
      exact ⟨eU.trans eInt⟩
    have hNotSeven : ¬ Nonempty (CFSG.generalizedFitting E ≃*
        alternatingGroup (Fin 7)) :=
      CFSG.Semidihedral.AlternatingSevenExclusion.dihedral_index_two_excludes_alternating_seven_layer
        hnonabelian P (n + 1) (by omega) ePk J hJ hLJ
    exact Or.inr ⟨hsimple, hnonabelian, hC, hLJ, hOdd,
      hExact, hNotSeven, hfactorization, htwoPart⟩

theorem dihedral_layer_exactly_one
    {E : Type u} [Group E] [Finite E]
    (n : ℕ) (hn : 2 ≤ n) (hcore : CFSG.oddCore E = ⊥)
    (P : Sylow 2 E) (eP : P ≃* DihedralGroup (2 ^ n))
    (J : Subgroup E) [J.Normal] (hJ : J.index = 2)
    (T : Sylow 2 J) (eT : T ≃* DihedralGroup (2 ^ (n - 1)))
    (htrivial : ∀ (D : Type u) [Group D] [Finite D],
      IsPGroup 2 D → ∀ f : J →* D, f = 1) :
    (DihedralFourPointAlternative E n J ∨
      DihedralSimpleLayerAlternative E n J) ∧
    ¬ (DihedralFourPointAlternative E n J ∧
      DihedralSimpleLayerAlternative E n J) :=
  ⟨dihedral_layer_alternatives n hn hcore P eP J hJ T eT htrivial,
    dihedral_layer_alternatives_exclusive n J⟩

end CFSG.Wreathed
