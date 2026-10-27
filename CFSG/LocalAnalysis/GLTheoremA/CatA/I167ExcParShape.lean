module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcParDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups



open CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.Steinberg.Adjoint TauCeti

private theorem exc_component_shape_aux1 (t : DynkinType) (ht : t.Valid) (i : Fin t.rank)
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

private theorem exc_component_shape_aux2 (t : DynkinType) (ht : t.Valid) (i : Fin t.rank)
    (j : Fin t.numRoots) :
    coordReflect t.cartanMatrix i ((t.simplyConnectedRootDatum ht).coroot j) =
      (t.simplyConnectedRootDatum ht).coroot
        ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) j) := by
  rw [coordReflect, ← DynkinType.coroot_simpleIndex t ht i,
    ← exc_component_shape_aux1 t ht i j,
    ← RootPairing.reflectionPerm_coroot]

private theorem exc_component_shape_aux3 (t : DynkinType) (ht : t.Valid) {x : Fin t.rank → ℤ}
    (hx : IsOrbitRoot t.cartanMatrix x) :
    ∃ j : Fin t.numRoots, (t.simplyConnectedRootDatum ht).coroot j = x := by
  induction hx with
  | single i => exact ⟨t.simpleIndex ht i, DynkinType.coroot_simpleIndex t ht i⟩
  | reflect i _ ih =>
      obtain ⟨j, rfl⟩ := ih
      exact ⟨(t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) j,
        (exc_component_shape_aux2 t ht i j).symm⟩

private theorem exc_component_shape_aux4 (t : DynkinType) (ht : t.Valid)
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
      rw [hcoe, ← exc_component_shape_aux2 t ht i0]
      exact IsOrbitRoot.reflect i0 (ih i hi)

private theorem exc_component_shape_aux5 (t : DynkinType) (ht : t.Valid) (j : Fin t.numRoots) :
    IsOrbitRoot t.cartanMatrix ((t.simplyConnectedRootDatum ht).coroot j) := by
  haveI := DynkinType.isReduced_simplyConnectedRootDatum t ht
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
  have h := exc_component_shape_aux4 t ht l (i : Fin t.numRoots) hstart
  rwa [hl, hw] at h

private theorem exc_component_shape_aux6 (t : DynkinType) (ht : t.Valid) :
    {x : Fin t.rank → ℤ | IsOrbitRoot t.cartanMatrix x}.ncard = t.numRoots := by
  have hsubset : {x : Fin t.rank → ℤ | IsOrbitRoot t.cartanMatrix x} ⊆
      Set.range (t.simplyConnectedRootDatum ht).coroot := by
    intro x hx
    exact exc_component_shape_aux3 t ht hx
  have hsubset' : Set.range (t.simplyConnectedRootDatum ht).coroot ⊆
      {x : Fin t.rank → ℤ | IsOrbitRoot t.cartanMatrix x} := by
    rintro _ ⟨j, rfl⟩
    exact exc_component_shape_aux5 t ht j
  have heq : {x : Fin t.rank → ℤ | IsOrbitRoot t.cartanMatrix x} =
      Set.range (t.simplyConnectedRootDatum ht).coroot :=
    Set.Subset.antisymm hsubset hsubset'
  rw [heq, Set.ncard_range_of_injective (t.simplyConnectedRootDatum ht).coroot.injective,
    Nat.card_fin]

private theorem exc_component_shape_aux7 {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : NoG2 τ := by
  rcases hτ with rfl | rfl | rfl | rfl <;> intro j <;> fin_cases j <;> decide

private theorem exc_component_shape_aux8 {τ : Tag} (hnoG2 : NoG2 τ)
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {t : DynkinType} (ht : t.Valid) (e : simpleRoots Ψ ≃ Fin t.rank)
    (he : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) (γ : Fin τ.rank → ℤ) =
      t.cartanMatrix (e β) (e γ)) : t ≠ .G2 := by
  intro hG2
  subst hG2
  let i : Fin 2 := ⟨1, by decide⟩
  let j : Fin 2 := ⟨0, by decide⟩
  have hij : i ≠ j := by decide
  let β : simpleRoots Ψ := e.symm i
  let γ : simpleRoots Ψ := e.symm j
  have hβγ : (β : Fin τ.rank → ℤ) ≠ (γ : Fin τ.rank → ℤ) := by
    intro h
    have h2 : e (e.symm i) = e (e.symm j) := by
      simpa [β, γ] using congrArg e (Subtype.ext h)
    apply hij
    rw [← Equiv.apply_symm_apply e i, ← Equiv.apply_symm_apply e j]
    exact h2
  have hβγ' : (β : Fin τ.rank → ℤ) ≠ -(γ : Fin τ.rank → ℤ) := by
    intro h
    have hb := (mem_simpleRoots.mp β.2).2.1.2
    have hg := (mem_simpleRoots.mp γ.2).2.1.2
    have hsum : height (γ : Fin τ.rank → ℤ) = - height (β : Fin τ.rank → ℤ) := by
      rw [h, height_neg]
      omega
    omega
  have hM : (DynkinType.G2).cartanMatrix i j = -3 := by
    simp [i, j, DynkinType.cartanMatrix_G2, CartanMatrix.G₂]
  have hM' : (DynkinType.G2).cartanMatrix (e β) (e γ) = -3 := by
    have hb : e β = i := by simpa [β] using Equiv.apply_symm_apply e i
    have hg : e γ = j := by simpa [γ] using Equiv.apply_symm_apply e j
    rw [hb, hg, hM]
  have hpair : corootPair (β : Fin τ.rank → ℤ) (γ : Fin τ.rank → ℤ) = -3 := by
    rw [he β γ, hM']
  have hroot : IsRoot τ (3 • (β : Fin τ.rank → ℤ) + 1 • (γ : Fin τ.rank → ℤ)) := by
    have hb := hΨ.isRoot β.1 (simpleRoots_subset β.2)
    have hg := hΨ.isRoot γ.1 (simpleRoots_subset γ.2)
    have h := IsRoot.smul hg (rootReflection (β : Fin τ.rank → ℤ))
    rw [rootReflection_smul hb (γ : Fin τ.rank → ℤ), hpair] at h
    simpa [add_comm] using h
  exact (CFSG.LieType.Steinberg.Adjoint.not_isRoot_nsmul_add_nsmul hnoG2
    (hΨ.isRoot β.1 (simpleRoots_subset β.2))
    (hΨ.isRoot γ.1 (simpleRoots_subset γ.2)) hβγ hβγ' (i := 3) (j := 1)
    (by norm_num) (by norm_num) (by norm_num)) hroot

private theorem exc_component_shape_aux9 (t : DynkinType) (ht : t.Valid)
    (hr8 : t.rank ≤ 8) (hG2 : t ≠ .G2) : ExcShape t.rank t.numRoots := by
  cases t with
  | A n =>
      have hn : 1 ≤ n := by simpa using ht
      have hn8 : n ≤ 8 := by simpa using hr8
      left
      refine ⟨hn, hn8, ?_⟩
      simp [DynkinType.rank_A, DynkinType.numRoots_A]
  | B n =>
      have hn : 2 ≤ n := by simpa using ht
      have hn8 : n ≤ 8 := by simpa using hr8
      right; left
      refine ⟨hn, hn8, ?_⟩
      simp [DynkinType.rank_B, DynkinType.numRoots_B, pow_two]
  | C n =>
      have hn : 2 ≤ n := by
        have h3 : 3 ≤ n := by simpa using ht
        omega
      have hn8 : n ≤ 8 := by simpa using hr8
      right; left
      refine ⟨hn, hn8, ?_⟩
      simp [DynkinType.rank_C, DynkinType.numRoots_C, pow_two]
  | D n =>
      have hn : 4 ≤ n := by simpa using ht
      have hn8 : n ≤ 8 := by simpa using hr8
      right; right; left
      refine ⟨hn, hn8, ?_⟩
      simp only [DynkinType.rank_D, DynkinType.numRoots_D]
      ring
  | E6 => simp [ExcShape]
  | E7 => simp [ExcShape]
  | E8 => simp [ExcShape]
  | F4 => simp [ExcShape]
  | G2 => exact absurd rfl hG2

theorem exc_component_shape {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] (a : Fin τ.rank → Kˣ) (i : KernelComponent (rootCharHom a)) :
    ExcShape (compRank (componentRoots (rootCharHom a) i)) (componentRoots (rootCharHom a) i).ncard := by
  classical
  set Ψ := componentRoots (rootCharHom a) i with hΨdef
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  have hΨne : Ψ.Nonempty := by
    obtain ⟨α, hα⟩ := Quot.exists_rep i
    exact ⟨α.1, α.2, hα⟩
  obtain ⟨t, ⟨ht, e, he⟩, -⟩ :=
    (CFSG.HardMathSupport.Timmesfeld.Proving.isFiniteType_simpleRoots_corootPair hΨ).existsUnique_dynkinType
      (CFSG.HardMathSupport.Timmesfeld.Proving.diagramGraph_simpleRoots_connected hΨ hΨne)
  have he' : ∀ β γ : simpleRoots Ψ,
      corootPair (β : Fin τ.rank → ℤ) (γ : Fin τ.rank → ℤ) = t.cartanMatrix (e β) (e γ) :=
    fun β γ => by simpa only [Matrix.of_apply] using he β γ
  have hcardΔ : (simpleRoots Ψ).card = t.rank := by
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fin]
  have hrank : compRank Ψ = t.rank := by
    rw [compRank_eq_card hΨ, hcardΔ]
  have hr8 : t.rank ≤ 8 := hrank ▸ (compRank_le Ψ).trans (rank_le_eight τ)
  have hN : Ψ.ncard = t.numRoots := by
    rw [ncard_eq_ncard_orbit hΨ e he', exc_component_shape_aux6 t ht]
  have hnoG2 : NoG2 τ := exc_component_shape_aux7 hτ
  have htG2 : t ≠ .G2 := exc_component_shape_aux8 hnoG2 hΨ ht e he'
  rw [hrank, hN]
  exact exc_component_shape_aux9 t ht hr8 htG2

end CFSG.LocalAnalysis.GLTheoremA.I167

end
