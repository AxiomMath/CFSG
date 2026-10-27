module

public import CFSG.RankThree.PartOne.KC.OrthogonalSplitPrimeBridge
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Orth3Local
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalInnerPlane
public import CFSG.RankThree.PartOne.KC.OrthogonalSplitPrimeGeneration

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonal
open scoped commutatorElement

section Roots

variable {K : Type*} [Field K] {p r : ℕ}

theorem split_root_le_derivedCentralizer3 (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K}
    (hζ : orderOf ζ = p) (A : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)))
    (hAG : A ≤ orthElementaryGroup (quadPlus r K)) (hAcard : Nat.card A = p ^ 2)
    (χ : Fin r → (A →* Multiplicative (ZMod p)))
    (hχ : ∀ (g : A) (i : Fin r),
      (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (Pi.single (Sum.inl i) 1) =
          ζ ^ (χ i g).toAdd.val • Pi.single (Sum.inl i) 1 ∧
        (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (Pi.single (Sum.inr i) 1) =
          (ζ ^ (χ i g).toAdd.val)⁻¹ • Pi.single (Sum.inr i) 1)
    {α : Fin r → ℤ} (hα : α ∈ roots r) :
    ∃ a ∈ A, a ≠ 1 ∧
      rootSubgroup r K α ≤ derivedCentralizer (orthElementaryGroup (quadPlus r K)) a := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hζ0 : ζ ≠ 0 := fun h => by
    rw [h, zero_pow hp.ne_zero] at hζp
    exact zero_ne_one hζp
  have hζ2 : ζ * ζ ≠ 1 := fun h => by
    have h1 : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    have h2 := Nat.le_of_dvd (by norm_num) (hζ ▸ h1)
    have := hp.two_le
    omega
  obtain ⟨a, b, hab, hwt, h1, -⟩ := exists_rootElt_eq_rpElt (K := K) hα
  obtain ⟨g, hg1, hgψ⟩ := exists_ne_one_mem_ker hp hAcard (coordChar χ a * (coordChar χ b)⁻¹)
  have hgab : coordChar χ a g = coordChar χ b g := by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at hgψ
    exact hgψ
  refine ⟨(g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)), g.2, fun h => hg1 (Subtype.ext h),
    ?_⟩
  have hgc := apply_single_of_chars hζp χ hχ g
  have hκ : zetaPow ζ (coordChar χ a g).toAdd * zetaPow ζ (coordChar χ b.swap g).toAdd = 1 := by
    rw [← zetaPow_add hζp, coordChar_swap, MonoidHom.inv_apply, toAdd_inv, hgab, add_neg_cancel,
      zetaPow_zero]
  set ζ' : Kˣ := Units.mk0 ζ hζ0 with hζ'
  set δ := torusElt r K fun i => ζ' ^ α i with hδ
  have hδG : δ ∈ orthElementaryGroup (quadPlus r K) := by
    have h := rootH_mem (r := r) (K := K) α ζ
    rwa [show rootH r K α ζ = δ from rootH_eq_torusElt hα ζ'] at h
  have hδc : ∀ c : Fin r ⊕ Fin r,
      δ (Pi.single c 1) = ((ζ' ^ (coordWt c ⬝ᵥ α) : Kˣ) : K) • Pi.single c 1 := fun c => by
    rw [hδ, torusElt_apply_single, sumElim_zpow_eq]
  have hα' : α = coordWt a - coordWt b := hwt.symm
  have hμ : coordWt a ⬝ᵥ α = 1 := by
    rw [hα', dotProduct_sub, coordWt_dotProduct, coordWt_dotProduct, ite_eq_left rfl,
      ite_eq_right (ne_of_coordIdx_ne hab), ite_eq_right (ne_swap_of_coordIdx_ne hab)]
    norm_num
  have hν : coordWt b.swap ⬝ᵥ α = 1 := by
    rw [hα', dotProduct_sub, coordWt_dotProduct, coordWt_dotProduct,
      ite_eq_right (fun h => ne_swap_of_coordIdx_ne hab h.symm),
      ite_eq_right (swap_ne_swap_of_coordIdx_ne hab).symm, ite_eq_right (swap_ne_self b),
      ite_eq_left rfl]
    norm_num
  have hδa : δ * (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) =
      (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) * δ :=
    mul_comm_of_eigen span_range_single_eq_top (by
      rintro _ ⟨c, rfl⟩
      exact ⟨_, _, hδc c, hgc c⟩)
  have hG₀ : orthElementaryGroup (quadPlus r K) ≤ TauCeti.QuadraticMap.orthogonalGroup
      (quadPlus r K) := orthElementaryGroup_le _
  have hpolar : ∀ t : K, polar (quadPlus r K) (Pi.single a 1) (t • -(Pi.single b.swap 1)) = 0 :=
    fun t => by
      rw [smul_neg, polar_neg_right,
        polar_single_smul_single (swap_ne_swap_of_coordIdx_ne hab).symm t, neg_zero]
  rintro _ ⟨t, rfl⟩
  have hrp : rootElt r K α t = eichler (quadPlus r K) (Pi.single a 1)
      (t • -(Pi.single b.swap 1)) := by
    rw [h1]
    show eichler (quadPlus r K) (Pi.single a 1) ((-t) • Pi.single b.swap 1) = _
    rw [smul_neg, neg_smul]
  rw [hrp]
  refine eichler_mem_derivedCentralizer (Q := quadPlus r K) hG₀ (hpolar t)
    (fun s => eichler_mem_elementaryGroup _ _ _) (hAG g.2) hδG hδa
    (κ := zetaPow ζ (coordChar χ a g).toAdd) (κ' := zetaPow ζ (coordChar χ b.swap g).toAdd)
    (μ := ζ) (ν := ζ) (hgc a) ?_ hκ ?_ ?_ hζ2
  · rw [smul_neg, map_neg, map_smul, hgc b.swap, smul_neg, smul_comm]
  · rw [hδc a, hμ]
    simp [hζ']
  · rw [smul_neg, map_neg, map_smul, hδc b.swap, hν, smul_neg, smul_comm]
    simp [hζ']

end Roots

section TailRootsMain

variable {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] {r p : ℕ}
  {qA : QuadraticForm K U}

theorem tail_long_root_le_derivedCentralizer3 (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K}
    (hζ : orderOf ζ = p) (hr : 3 ≤ r)
    (A : Subgroup (((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)))
    (hAG : A ≤ orthElementaryGroup (quadTail r qA)) (hAcard : Nat.card A = p ^ 2)
    (χ : Fin r → (A →* Multiplicative (ZMod p)))
    (hχ : ∀ (g : A) (i : Fin r),
      (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)) (hypVec K U (Sum.inl i)) =
          ζ ^ (χ i g).toAdd.val • hypVec K U (Sum.inl i) ∧
        (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U))
            (hypVec K U (Sum.inr i)) = (ζ ^ (χ i g).toAdd.val)⁻¹ • hypVec K U (Sum.inr i))
    (hfix : ∀ (g : A) (u : U),
      (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)) ((0 : Fin r ⊕ Fin r → K), u) =
        (0, u))
    {α : Fin r → ℤ} (hα : α ∈ roots r) :
    ∃ a ∈ A, a ≠ 1 ∧
      tailRootGroup r qA α ≤ derivedCentralizer (orthElementaryGroup (quadTail r qA)) a := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hζ0 : ζ ≠ 0 := fun h => by
    rw [h, zero_pow hp.ne_zero] at hζp
    exact zero_ne_one hζp
  have hζ2 : ζ * ζ ≠ 1 := fun h => by
    have h1 : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    have h2 := Nat.le_of_dvd (by norm_num) (hζ ▸ h1)
    have := hp.two_le
    omega
  obtain ⟨a, b, hab, hwt, h1, -⟩ := exists_rootElt_eq_rpElt (K := K) hα
  obtain ⟨g, hg1, hgψ⟩ := exists_ne_one_mem_ker hp hAcard (coordChar χ a * (coordChar χ b)⁻¹)
  have hgab : coordChar χ a g = coordChar χ b g := by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at hgψ
    exact hgψ
  refine ⟨(g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)), g.2,
    fun h => hg1 (Subtype.ext h), ?_⟩
  have hgc := apply_hypVec_of_chars hζp χ hχ g
  have hκ : zetaPow ζ (coordChar χ a g).toAdd * zetaPow ζ (coordChar χ b.swap g).toAdd = 1 := by
    rw [← zetaPow_add hζp, coordChar_swap, MonoidHom.inv_apply, toAdd_inv, hgab, add_neg_cancel,
      zetaPow_zero]
  set ζ' : Kˣ := Units.mk0 ζ hζ0 with hζ'
  set δ := prodHom U (torusElt r K fun i => ζ' ^ α i) with hδ
  have hδG : δ ∈ orthElementaryGroup (quadTail r qA) := prodHom_mem_tail hr hα hζ0
  have hδc : ∀ c : Fin r ⊕ Fin r,
      δ (hypVec K U c) = ((ζ' ^ (coordWt c ⬝ᵥ α) : Kˣ) : K) • hypVec K U c := fun c =>
    prodHom_apply_hypVec _ c _ (by rw [torusElt_apply_single, sumElim_zpow_eq])
  have hα' : α = coordWt a - coordWt b := hwt.symm
  have hμ : coordWt a ⬝ᵥ α = 1 := by
    rw [hα', dotProduct_sub, coordWt_dotProduct, coordWt_dotProduct, ite_eq_left rfl,
      ite_eq_right (ne_of_coordIdx_ne hab), ite_eq_right (ne_swap_of_coordIdx_ne hab)]
    norm_num
  have hν : coordWt b.swap ⬝ᵥ α = 1 := by
    rw [hα', dotProduct_sub, coordWt_dotProduct, coordWt_dotProduct,
      ite_eq_right (fun h => ne_swap_of_coordIdx_ne hab h.symm),
      ite_eq_right (swap_ne_swap_of_coordIdx_ne hab).symm, ite_eq_right (swap_ne_self b),
      ite_eq_left rfl]
    norm_num
  have hδa : δ * (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)) =
      (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)) * δ :=
    mul_comm_of_eigen span_hypVec_tail_eq_top (by
      rintro v (⟨c, rfl⟩ | ⟨u, rfl⟩)
      · exact ⟨_, _, hδc c, hgc c⟩
      · exact ⟨1, 1, by rw [one_smul]; exact prodHom_apply_tail _ u,
          by rw [one_smul]; exact hfix g u⟩)
  have hG₀ : orthElementaryGroup (quadTail r qA) ≤ TauCeti.QuadraticMap.orthogonalGroup
      (quadTail r qA) := orthElementaryGroup_le _
  have hpolar : ∀ t : K, polar (quadTail r qA) (hypVec K U a) (t • -(hypVec K U b.swap)) = 0 :=
    fun t => by
      rw [smul_neg, polar_neg_right, polar_smul_right_eq, polar_hypVec_hypVec,
        ite_eq_right (swap_ne_swap_of_coordIdx_ne hab).symm, mul_zero, neg_zero]
  intro y hy
  obtain ⟨t, rfl⟩ := (mem_tailRootGroup_long hα).1 hy
  rw [tailLongElt_eq_eichler_pair h1 t]
  refine eichler_mem_derivedCentralizer (Q := quadTail r qA) hG₀ (hpolar t)
    (fun s => eichler_mem_elementaryGroup _ _ _) (hAG g.2) hδG hδa
    (κ := zetaPow ζ (coordChar χ a g).toAdd) (κ' := zetaPow ζ (coordChar χ b.swap g).toAdd)
    (μ := ζ) (ν := ζ) (hgc a) ?_ hκ ?_ ?_ hζ2
  · rw [smul_neg, map_neg, map_smul, hgc b.swap, smul_neg, smul_comm]
  · rw [hδc a, hμ]
    simp [hζ']
  · rw [smul_neg, map_neg, map_smul, hδc b.swap, hν, smul_neg, smul_comm]
    simp [hζ']

end TailRootsMain

section Plane

theorem split_diagonal_orthogonal_plane_derived_centralizer_generation3
    {K : Type*} [Field K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K} (hζ : orderOf ζ = p)
    {r : ℕ} (hr : 3 ≤ r) :
    (∀ A : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)),
      A ≤ orthElementaryGroup (quadPlus r K) → Assembly.IsElemAbelian p A →
      Nat.card A = p ^ 2 → ∀ χ : Fin r → (A →* Multiplicative (ZMod p)),
      (∀ (g : A) (i : Fin r),
        (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (Pi.single (Sum.inl i) 1) =
            ζ ^ (χ i g).toAdd.val • Pi.single (Sum.inl i) 1 ∧
          (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (Pi.single (Sum.inr i) 1) =
            (ζ ^ (χ i g).toAdd.val)⁻¹ • Pi.single (Sum.inr i) 1) →
      (∀ α ∈ roots r, ∃ a ∈ A, a ≠ 1 ∧
        rootSubgroup r K α ≤ derivedCentralizer (orthElementaryGroup (quadPlus r K)) a) ∧
      (⨆ (a : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (_ : a ∈ A ∧ a ≠ 1),
        derivedCentralizer (orthElementaryGroup (quadPlus r K)) a) =
        orthElementaryGroup (quadPlus r K) ∧
      ∀ φ : ↥(orthElementaryGroup (quadPlus r K)) ≃* ↥(orthElementaryGroup (quadPlus r K)),
        (∀ a ∈ A, a ≠ 1 → ∀ g : ↥(orthElementaryGroup (quadPlus r K)),
          (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) ∈
            derivedCentralizer (orthElementaryGroup (quadPlus r K)) a → φ g = g) →
        φ = MulEquiv.refl _) ∧
    (∀ {U : Type*} [AddCommGroup U] [Module K U] (qA : QuadraticForm K U), qA.Anisotropic →
      (∃ u : U, u ≠ 0) →
      ∀ A : Subgroup (((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)),
      A ≤ orthElementaryGroup (quadTail r qA) → Assembly.IsElemAbelian p A →
      Nat.card A = p ^ 2 → ∀ χ : Fin r → (A →* Multiplicative (ZMod p)),
      (∀ (g : A) (i : Fin r),
        (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U))
            (hypVec K U (Sum.inl i)) = ζ ^ (χ i g).toAdd.val • hypVec K U (Sum.inl i) ∧
          (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U))
            (hypVec K U (Sum.inr i)) = (ζ ^ (χ i g).toAdd.val)⁻¹ • hypVec K U (Sum.inr i)) →
      (∀ (g : A) (u : U),
        (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U))
          ((0 : Fin r ⊕ Fin r → K), u) = (0, u)) →
      (∀ α ∈ rootsB r, ∃ a ∈ A, a ≠ 1 ∧
        tailRootGroup r qA α ≤ derivedCentralizer (orthElementaryGroup (quadTail r qA)) a) ∧
      (⨆ (a : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U))
          (_ : a ∈ A ∧ a ≠ 1), derivedCentralizer (orthElementaryGroup (quadTail r qA)) a) =
        orthElementaryGroup (quadTail r qA) ∧
      ∀ φ : ↥(orthElementaryGroup (quadTail r qA)) ≃* ↥(orthElementaryGroup (quadTail r qA)),
        (∀ a ∈ A, a ≠ 1 → ∀ g : ↥(orthElementaryGroup (quadTail r qA)),
          (g : ((Fin r ⊕ Fin r → K) × U) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × U)) ∈
            derivedCentralizer (orthElementaryGroup (quadTail r qA)) a → φ g = g) →
        φ = MulEquiv.refl _) := by
  refine ⟨fun A hAG hA hAcard χ hχ => ?_, fun {U} _ _ qA hani hU A hAG hA hAcard χ hχ hfix => ?_⟩
  · have _hA := hA
    have hroot : ∀ α ∈ roots r, ∃ a ∈ A, a ≠ 1 ∧
        rootSubgroup r K α ≤ derivedCentralizer (orthElementaryGroup (quadPlus r K)) a :=
      fun α hα => split_root_le_derivedCentralizer3 hp hp2 hζ A hAG hAcard χ hχ hα
    have hgen := iSup_derivedCentralizer_eq (S := roots r) (A := A)
      (X := fun α => rootSubgroup r K α) (orthogonal_geometry_split_root_generation hr).1.symm hroot
    exact ⟨hroot, hgen, fun φ hφ => eq_refl_of_fixes_derivedCentralizers hgen φ hφ⟩
  · have _hA := hA
    have hroot : ∀ α ∈ rootsB r, ∃ a ∈ A, a ≠ 1 ∧
        tailRootGroup r qA α ≤ derivedCentralizer (orthElementaryGroup (quadTail r qA)) a := by
      intro α hα
      rcases hα with hs | hl
      · exact tail_short_root_le_derivedCentralizer hp hζ hr A hAG hAcard χ hχ hfix hs
      · exact tail_long_root_le_derivedCentralizer3 hp hp2 hζ hr A hAG hAcard χ hχ hfix hl
    have hgen := iSup_derivedCentralizer_eq (S := rootsB r) (A := A)
      (X := fun α => tailRootGroup r qA α)
      (orthogonal_geometry_tail_root_generation hani hU).1.symm hroot
    exact ⟨hroot, hgen, fun φ hφ => eq_refl_of_fixes_derivedCentralizers hgen φ hφ⟩

end Plane

section Main

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem orthogonal_plane_derived_centralizers_generate3
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    (G : Subgroup (V ≃ₗ[K] V)) (hGΩ : G ≤ orthDerived Q) (hG : Assembly.IsElemAbelian p G)
    (hGcard : Nat.card G = p ^ 2) :
    (⨆ (x : V ≃ₗ[K] V) (_ : x ∈ G ∧ x ≠ 1), derivedCentralizer (orthDerived Q) x) =
      orthDerived Q := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζord⟩ := exists_root_of_dvd_card_sub_one hp hpq
  have hζ : IsPrimitiveRoot ζ p := by
    rw [← hζord]
    exact IsPrimitiveRoot.orderOf ζ
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_dvd_card_sub_one hp hpq
  have hΩ : orthDerived Q = elementaryGroup Q :=
    (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ hT).1
  have hΩO : orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  have hGQ : G ≤ TauCeti.QuadraticMap.orthogonalGroup Q := fun g hg => hΩO (hGΩ hg)
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have : IsMulCommutative G := hG.1
  have hGcardK : (Nat.card G : K) ≠ 0 := by
    rw [hGcard, Nat.cast_pow]
    exact pow_ne_zero 2 hpK
  obtain ⟨r, U, φ, χ, hφQ, hani, -, hdiag, hfix⟩ :=
    exists_split_coordinates hQ hp hp2 hζ G hGQ hG.2 hGcardK
  have hani' : (Q.comp U.subtype).Anisotropic := fun u hu => Subtype.ext (hani u u.2 hu)
  have hr3 : 3 ≤ r := by
    obtain ⟨L, hL3, hLs⟩ := hT
    have hsing : ∀ x ∈ L.map (φ : V →ₗ[K] _), quadTail r (Q.comp U.subtype) x = 0 := by
      rintro _ ⟨v, hv, rfl⟩
      rw [LinearEquiv.coe_coe, hφQ]
      exact hLs v hv
    have := finrank_le_of_totSing_tail hani' hsing
    rwa [LinearEquiv.finrank_map_eq, hL3] at this
  by_cases hU0 : U = ⊥
  ·
    have : Subsingleton ↥U := Submodule.subsingleton_iff_eq_bot.mpr hU0
    have : Unique ↥U := Unique.mk' _
    set Φ : V ≃ₗ[K] (Fin r ⊕ Fin r → K) := φ.trans LinearEquiv.prodUnique with hΦ
    have hΦapp : ∀ v, Φ v = (φ v).1 := fun v => rfl
    have hΦsymm : ∀ z, Φ.symm z = φ.symm (z, 0) := fun z => by
      rw [LinearEquiv.symm_apply_eq, hΦapp, LinearEquiv.apply_symm_apply]
    have hΦQ : ∀ v, quadPlus r K (Φ v) = Q v := by
      intro v
      have h := hφQ v
      rw [quadTail_apply] at h
      have h0 : (φ v).2 = 0 := Subsingleton.elim _ _
      rw [h0] at h
      rw [hΦapp]
      simpa using h
    have hconj : ∀ (g : V ≃ₗ[K] V) (z : Fin r ⊕ Fin r → K),
        LinearEquiv.autCongr Φ g z = (LinearEquiv.autCongr φ g (z, 0)).1 := by
      intro g z
      rw [LinearEquiv.autCongr_apply_apply, LinearEquiv.autCongr_apply_apply, hΦsymm, hΦapp]
    let hiso : Q.IsometryEquiv (quadPlus r K) := { Φ with map_app' := hΦQ }
    have hmap : (orthDerived Q).map (LinearEquiv.autCongr Φ).toMonoidHom =
        orthElementaryGroup (quadPlus r K) := by
      rw [hΩ]
      exact CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.elementaryGroup_map
        hiso
    have hAle : G.map (LinearEquiv.autCongr Φ).toMonoidHom ≤
        orthElementaryGroup (quadPlus r K) := by
      rw [← hmap]
      exact Subgroup.map_mono hGΩ
    obtain ⟨hAel, hAcard⟩ := isElemAbelian_map (LinearEquiv.autCongr Φ) hG hGcard
    obtain ⟨χ', hχ'⟩ := exists_transport_chars (LinearEquiv.autCongr Φ) G χ
    have hgen := (split_diagonal_orthogonal_plane_derived_centralizer_generation3.{0, 0} hp hp2
      hζord hr3).1 (G.map (LinearEquiv.autCongr Φ).toMonoidHom) hAle hAel hAcard χ' (fun g' i => by
        obtain ⟨g, hg, hχ⟩ := hχ' g'
        rw [hg, hχ i, hconj, hconj]
        exact ⟨congrArg Prod.fst (hdiag g i).1, congrArg Prod.fst (hdiag g i).2⟩)
    exact iSup_derivedCentralizer_of_map (LinearEquiv.autCongr Φ) (orthDerived Q) G
      (by rw [hmap]; exact hgen.2.1)
  ·
    obtain ⟨u, hu⟩ : ∃ u : ↥U, u ≠ 0 := by
      by_contra h
      push Not at h
      exact hU0 ((Submodule.eq_bot_iff U).mpr fun x hx => congrArg Subtype.val (h ⟨x, hx⟩))
    let hiso : Q.IsometryEquiv (quadTail r (Q.comp U.subtype)) := { φ with map_app' := hφQ }
    have hmap : (orthDerived Q).map (LinearEquiv.autCongr φ).toMonoidHom =
        orthElementaryGroup (quadTail r (Q.comp U.subtype)) := by
      rw [hΩ]
      exact CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.elementaryGroup_map
        hiso
    have hAle : G.map (LinearEquiv.autCongr φ).toMonoidHom ≤
        orthElementaryGroup (quadTail r (Q.comp U.subtype)) := by
      rw [← hmap]
      exact Subgroup.map_mono hGΩ
    obtain ⟨hAel, hAcard⟩ := isElemAbelian_map (LinearEquiv.autCongr φ) hG hGcard
    obtain ⟨χ', hχ'⟩ := exists_transport_chars (LinearEquiv.autCongr φ) G χ
    have hgen := (split_diagonal_orthogonal_plane_derived_centralizer_generation3 hp hp2 hζord
      hr3).2 (Q.comp U.subtype) hani' ⟨u, hu⟩ (G.map (LinearEquiv.autCongr φ).toMonoidHom) hAle
      hAel hAcard χ' (fun g' i => by
        obtain ⟨g, hg, hχ⟩ := hχ' g'
        rw [hg, hχ i]
        exact hdiag g i) (fun g' u' => by
        obtain ⟨g, hg, -⟩ := hχ' g'
        rw [hg]
        exact hfix g u')
    exact iSup_derivedCentralizer_of_map (LinearEquiv.autCongr φ) (orthDerived Q) G
      (by rw [hmap]; exact hgen.2.1)

end Main

section Rigid

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem orth3_split_derived_rigid
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    (A : Subgroup (ProjOrthDerived Q)) (hA : Assembly.IsElemAbelian p A)
    (hAcard : Nat.card A = p ^ 2) (g : MulAut (ProjOrthDerived Q))
    (hg : ∀ a ∈ A, a ≠ 1 → ∀ n ∈ ⁅Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)),
        Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))⁆, g n = n) : g = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_dvd_card_sub_one hp hpq
  have hpl : p ≠ ringChar K := fun h => hpK (by rw [h]; exact ringChar.Nat.cast_ringChar)
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have : CharP K (ringChar K) := ringChar.charP K
  have hℓ : (ringChar K).Prime :=
    (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right
      (CharP.char_ne_zero_of_finite K (ringChar K))
  have : Nontrivial V := by
    obtain ⟨U, hU3, -⟩ := hT
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have := Module.finrank_zero_of_subsingleton (R := K) (M := ↥U)
    omega
  set Ω := orthDerived Q with hΩ
  set ρ : ↥Ω →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf Ω) with hρ
  have hρsurj : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  obtain ⟨Ã, hÃM, -, e, he, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_inner_plane_kernel_line_quadratic_decomposition
      (ℓ := ringChar K) hℓ hp hp2 hpl Q hQ A hA hAcard
  have : IsMulCommutative Ã := ⟨⟨fun a b => e.injective (by
    have := hA.1
    rw [map_mul, map_mul, mul_comm' (e a) (e b)])⟩⟩
  have hexpÃ : ∀ x : Ã, x ^ p = 1 := fun x => e.injective (by
    rw [map_pow, map_one]
    exact Subtype.ext (hA.2 _ (e x).2))
  have hGel : Assembly.IsElemAbelian p (Ã.map Ω.subtype) := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
      apply Subtype.ext
      show (a : V ≃ₗ[K] V) * b = b * a
      have h : (⟨a, ha⟩ : Ã) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := mul_comm' _ _
      exact congrArg (fun y : Ã => ((y : Ω) : V ≃ₗ[K] V)) h
    · rintro _ ⟨a, ha, rfl⟩
      show ((a : Ω) : V ≃ₗ[K] V) ^ p = 1
      have h := congrArg (fun y : Ã => ((y : Ω) : V ≃ₗ[K] V)) (hexpÃ ⟨a, ha⟩)
      simpa using h
  have hGcard : Nat.card (Ã.map Ω.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective Ω.subtype_injective, ← hAcard]
    exact Nat.card_congr e.toEquiv
  have hgenV := orthogonal_plane_derived_centralizers_generate3 hQ hT hp hp2 hpq (Ã.map Ω.subtype)
    (Subgroup.map_subtype_le Ã) hGel hGcard
  have hgenΩ := iSup_commutator_isometryCentralizer_eq_top Ã hgenV
  have hx : ∀ x : ↥Ω, x ∈ Ã → x ≠ 1 → ρ x ∈ A ∧ ρ x ≠ 1 ∧ orderOf x = p := by
    intro x hxÃ hx1
    refine ⟨hÃM hxÃ, ?_, orderOf_eq_prime (by
      have := congrArg (fun y : Ã => (y : Ω)) (hexpÃ ⟨x, hxÃ⟩)
      simpa using this) hx1⟩
    intro h1
    apply hx1
    have h2 : e ⟨x, hxÃ⟩ = 1 := Subtype.ext (by rw [he]; exact h1)
    have := e.injective (h2.trans (map_one e).symm)
    exact congrArg Subtype.val this
  have hfixρ : ∀ x : ↥Ω, x ∈ Ã → x ≠ 1 →
      ∀ m ∈ ⁅(isometryCentralizer Q (x : V ≃ₗ[K] V)).subgroupOf Ω,
      (isometryCentralizer Q (x : V ≃ₗ[K] V)).subgroupOf Ω⁆, g (ρ m) = ρ m := by
    intro x hxÃ hx1 m hm
    obtain ⟨haA, ha1, hxp⟩ := hx x hxÃ hx1
    have ha : orderOf (ρ x) = p := by
      refine orderOf_eq_prime ?_ ha1
      rw [← map_pow]
      have : x ^ p = 1 := by
        have := congrArg (fun y : Ã => (y : Ω)) (hexpÃ ⟨x, hxÃ⟩)
        simpa using this
      rw [this, map_one]
    obtain ⟨-, hNeq⟩ := orth3_conj_injective_and_centralizer hQ hT hp hp2 (ρ x) ha x rfl hxp
    have h1 : ⁅Subgroup.centralizer ({ρ x} : Set (ProjOrthDerived Q)),
        Subgroup.centralizer ({ρ x} : Set (ProjOrthDerived Q))⁆ =
        (⁅(isometryCentralizer Q (x : V ≃ₗ[K] V)).subgroupOf Ω,
          (isometryCentralizer Q (x : V ≃ₗ[K] V)).subgroupOf Ω⁆).map ρ := by
      rw [hNeq, Subgroup.map_commutator]
      rfl
    exact hg (ρ x) haA ha1 (ρ m) (by rw [h1]; exact Subgroup.mem_map_of_mem ρ hm)
  have hall : ∀ n : ProjOrthDerived Q, g n = n := by
    intro n
    obtain ⟨m, rfl⟩ := hρsurj n
    have hm : m ∈ (⨆ (x : ↥Ω) (_ : x ∈ Ã ∧ x ≠ 1),
        ⁅(isometryCentralizer Q (x : V ≃ₗ[K] V)).subgroupOf Ω,
          (isometryCentralizer Q (x : V ≃ₗ[K] V)).subgroupOf Ω⁆) := by
      rw [hgenΩ]
      exact Subgroup.mem_top m
    have hle : (⨆ (x : ↥Ω) (_ : x ∈ Ã ∧ x ≠ 1),
        ⁅(isometryCentralizer Q (x : V ≃ₗ[K] V)).subgroupOf Ω,
          (isometryCentralizer Q (x : V ≃ₗ[K] V)).subgroupOf Ω⁆) ≤
        MonoidHom.eqLocus (g.toMonoidHom.comp ρ) ρ :=
      iSup_le fun x => iSup_le fun hxx m' hm' => hfixρ x hxx.1 hxx.2 m' hm'
    exact hle hm
  exact MulEquiv.ext fun n => hall n

end Rigid


end CFSG.HardMathSupport.Timmesfeld.CrossChar
