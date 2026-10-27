module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterCartan

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving TauCeti

private theorem d4center_aux1 (t : DynkinType) (ht : t.Valid) (i : Fin t.rank)
    (j : Fin t.numRoots) :
    (t.simplyConnectedRootDatum ht).toLinearMap
        ((t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i))
        ((t.simplyConnectedRootDatum ht).coroot j)
      = ∑ k, t.cartanMatrix i k * (t.simplyConnectedRootDatum ht).coroot j k := by
  have hx : (t.simplyConnectedRootDatum ht).coroot j =
      ∑ k, (t.simplyConnectedRootDatum ht).coroot j k •
        (t.simplyConnectedRootDatum ht).coroot (t.simpleIndex ht k) := by
    funext l
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, DynkinType.coroot_simpleIndex, Pi.single_apply]
    rw [Finset.sum_eq_single l]
    · simp
    · intro b _ hb; simp [show l ≠ b from fun h => hb h.symm]
    · intro h; simp at h
  conv_lhs => rw [hx]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, RootPairing.root_coroot_eq_pairing,
    DynkinType.pairing_simpleIndex]
  ring

private theorem d4center_aux2 (t : DynkinType) (ht : t.Valid) (i : Fin t.rank)
    (j : Fin t.numRoots) :
    coordReflect t.cartanMatrix i ((t.simplyConnectedRootDatum ht).coroot j) =
      (t.simplyConnectedRootDatum ht).coroot
        ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) j) := by
  rw [coordReflect, ← DynkinType.coroot_simpleIndex t ht i,
    ← d4center_aux1 t ht i j,
    ← RootPairing.reflectionPerm_coroot]

private theorem d4center_aux3 (t : DynkinType) (ht : t.Valid) {x : Fin t.rank → ℤ}
    (hx : IsOrbitRoot t.cartanMatrix x) :
    ∃ j : Fin t.numRoots, (t.simplyConnectedRootDatum ht).coroot j = x := by
  induction hx with
  | single i => exact ⟨t.simpleIndex ht i, DynkinType.coroot_simpleIndex t ht i⟩
  | reflect i _ ih =>
      obtain ⟨j, rfl⟩ := ih
      exact ⟨(t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) j,
        (d4center_aux2 t ht i j).symm⟩

private theorem d4center_aux4 (t : DynkinType) (ht : t.Valid)
    (l : List (t.simplyConnectedBase ht).support) (i : Fin t.numRoots)
    (hi : IsOrbitRoot t.cartanMatrix ((t.simplyConnectedRootDatum ht).coroot i)) :
    IsOrbitRoot t.cartanMatrix
      ((t.simplyConnectedRootDatum ht).coroot
        ((t.simplyConnectedRootDatum ht).weylGroupToPerm
          (wordProd (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht) l) i)) := by
  induction l generalizing i with
  | nil => simpa using hi
  | cons a l ih =>
      rw [wordProd_cons, RootPairing.weylGroupToPerm_ofIdx_mul_apply]
      let i0 := (t.simpleSupportEquivSimplyConnectedBase ht).symm a
      have hcoe : ((a : (t.simplyConnectedBase ht).support) : Fin t.numRoots) =
          t.simpleIndex ht i0 := by
        rw [← DynkinType.coe_simpleSupportEquivSimplyConnectedBase t ht i0]
        exact (congrArg Subtype.val
          (Equiv.apply_symm_apply (t.simpleSupportEquivSimplyConnectedBase ht) a)).symm
      rw [hcoe, ← d4center_aux2 t ht i0]
      exact IsOrbitRoot.reflect i0 (ih i hi)

private theorem d4center_aux5 (t : DynkinType) (ht : t.Valid) (j : Fin t.numRoots) :
    IsOrbitRoot t.cartanMatrix ((t.simplyConnectedRootDatum ht).coroot j) := by
  have := DynkinType.isReduced_simplyConnectedRootDatum t ht
  obtain ⟨i, hi, w, hw⟩ :=
    exists_mem_support_weylGroupToPerm_eq (P := t.simplyConnectedRootDatum ht)
      (t.simplyConnectedBase ht) j
  obtain ⟨l, hl⟩ := exists_wordProd_eq (P := t.simplyConnectedRootDatum ht)
    (t.simplyConnectedBase ht) w
  let i0 := (t.simpleSupportEquivSimplyConnectedBase ht).symm ⟨i, hi⟩
  have hi0 : t.simpleIndex ht i0 = i := by
    rw [← DynkinType.coe_simpleSupportEquivSimplyConnectedBase t ht i0]
    exact congrArg Subtype.val
      (Equiv.apply_symm_apply (t.simpleSupportEquivSimplyConnectedBase ht) ⟨i, hi⟩)
  have hstart : IsOrbitRoot t.cartanMatrix
      ((t.simplyConnectedRootDatum ht).coroot (i : Fin t.numRoots)) := by
    rw [← hi0, DynkinType.coroot_simpleIndex]
    exact IsOrbitRoot.single i0
  have h := d4center_aux4 t ht l (i : Fin t.numRoots) hstart
  rwa [hl, hw] at h

theorem ncard_setOf_isOrbitRoot_cartanMatrix (t : DynkinType) (ht : t.Valid) :
    {x : Fin t.rank → ℤ | IsOrbitRoot t.cartanMatrix x}.ncard = t.numRoots := by
  have hsubset : {x : Fin t.rank → ℤ | IsOrbitRoot t.cartanMatrix x} ⊆
      Set.range (t.simplyConnectedRootDatum ht).coroot := by
    intro x hx
    exact d4center_aux3 t ht hx
  have hsubset' : Set.range (t.simplyConnectedRootDatum ht).coroot ⊆
      {x : Fin t.rank → ℤ | IsOrbitRoot t.cartanMatrix x} := by
    rintro _ ⟨j, rfl⟩
    exact d4center_aux5 t ht j
  have heq : {x : Fin t.rank → ℤ | IsOrbitRoot t.cartanMatrix x} =
      Set.range (t.simplyConnectedRootDatum ht).coroot :=
    Set.Subset.antisymm hsubset hsubset'
  rw [heq, Set.ncard_range_of_injective (t.simplyConnectedRootDatum ht).coroot.injective,
    Nat.card_fin]

theorem det_cartan_eq_four_of_typeD
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hr : 4 ≤ compRank Ψ) (hc : Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1)) :
    (Matrix.of fun β γ : simpleRoots Ψ =>
      corootPair (β : Fin τ.rank → ℤ) γ).det = 4 := by
  classical
  have hΨne : Ψ.Nonempty := by
    rcases Ψ.eq_empty_or_nonempty with rfl | hne
    · exfalso
      have h0 : compRank (∅ : Set (Fin τ.rank → ℤ)) = 0 := by simp [compRank]
      omega
    · exact hne
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ :=
    (isFiniteType_simpleRoots_corootPair hΨ).existsUnique_dynkinType
      (diagramGraph_simpleRoots_connected hΨ hΨne)
  have he' : ∀ β γ : simpleRoots Ψ,
      corootPair (β : Fin τ.rank → ℤ) γ = t.cartanMatrix (e β) (e γ) :=
    fun β γ => by simpa only [Matrix.of_apply] using he β γ
  have hcardΔ : (simpleRoots Ψ).card = t.rank := by
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
  have hrank : t.rank = compRank Ψ := by
    rw [← hcardΔ, ← compRank_eq_card hΨ]
  have hN : Ψ.ncard = t.numRoots := by
    rw [ncard_eq_ncard_orbit hΨ e he', ncard_setOf_isOrbitRoot_cartanMatrix t ht]
  have hnum : t.numRoots = 2 * t.rank * (t.rank - 1) := by
    rw [← hN, hc, hrank]
  have hD : t = .D (compRank Ψ) := by
    cases t with
    | A n =>
        simp only [TauCeti.DynkinType.rank_A, TauCeti.DynkinType.numRoots_A] at hrank hnum
        rw [hrank] at hnum
        have h1 : compRank Ψ * (compRank Ψ + 1) =
            compRank Ψ * (2 * (compRank Ψ - 1)) := by
          rw [hnum, mul_comm 2 (compRank Ψ), mul_assoc]
        have h2 := Nat.eq_of_mul_eq_mul_left
          (show 0 < compRank Ψ by omega) h1
        omega
    | B n =>
        simp only [TauCeti.DynkinType.rank_B, TauCeti.DynkinType.numRoots_B] at hrank hnum
        rw [hrank] at hnum
        have h1 : 2 * compRank Ψ * compRank Ψ =
            2 * compRank Ψ * (compRank Ψ - 1) := by
          rw [← hnum, pow_two, mul_assoc]
        have h2 := Nat.eq_of_mul_eq_mul_left
          (show 0 < 2 * compRank Ψ by omega) h1
        omega
    | C n =>
        simp only [TauCeti.DynkinType.rank_C, TauCeti.DynkinType.numRoots_C] at hrank hnum
        rw [hrank] at hnum
        have h1 : 2 * compRank Ψ * compRank Ψ =
            2 * compRank Ψ * (compRank Ψ - 1) := by
          rw [← hnum, pow_two, mul_assoc]
        have h2 := Nat.eq_of_mul_eq_mul_left
          (show 0 < 2 * compRank Ψ by omega) h1
        omega
    | D n =>
        simp only [TauCeti.DynkinType.rank_D] at hrank
        rw [hrank]
    | E6 =>
        simp only [TauCeti.DynkinType.rank_E6, TauCeti.DynkinType.numRoots_E6] at hnum
        norm_num at hnum
    | E7 =>
        simp only [TauCeti.DynkinType.rank_E7, TauCeti.DynkinType.numRoots_E7] at hnum
        norm_num at hnum
    | E8 =>
        simp only [TauCeti.DynkinType.rank_E8, TauCeti.DynkinType.numRoots_E8] at hnum
        norm_num at hnum
    | F4 =>
        simp only [TauCeti.DynkinType.rank_F4, TauCeti.DynkinType.numRoots_F4] at hnum
        norm_num at hnum
    | G2 =>
        simp only [TauCeti.DynkinType.rank_G2] at hrank
        omega
  have hmat : (Matrix.of fun β γ : simpleRoots Ψ =>
      corootPair (β : Fin τ.rank → ℤ) γ) =
      (DynkinType.cartanMatrix t).submatrix e e := by
    ext β γ
    simp only [Matrix.of_apply, Matrix.submatrix_apply]
    exact he' β γ
  rw [hmat, Matrix.det_submatrix_equiv_self, hD, TauCeti.DynkinType.cartanMatrix_D]
  exact CartanMatrix.D_det (by omega)

theorem det_cartan_eq_four_of_compRank_four_ncard_24
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hr : compRank Ψ = 4) (hc : Ψ.ncard = 24) :
    (Matrix.of fun β γ : simpleRoots Ψ =>
      corootPair (β : Fin τ.rank → ℤ) γ).det = 4 :=
  det_cartan_eq_four_of_typeD hΨ (by omega) (by simp only [hc, hr])

theorem center_eq_bot_of_compRank_four_ncard_24
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ)
    (hr : compRank (componentRoots χ i) = 4)
    (hc : (componentRoots χ i).ncard = 24) :
    Subgroup.center (rootSpan τ L (componentRoots χ i)) = ⊥ := by
  have hdet := det_cartan_eq_four_of_compRank_four_ncard_24
    (isRootComponent_componentRoots i) hr hc
  have h := center_eq_bot_of_cartan_det_eq_four (L := L) i hdet
  change Subgroup.center (rootSpan τ L (componentRoots χ i)) = ⊥
  exact h

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
