module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerLines
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicBlocks

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne.KCSpFull
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

variable {r : ℕ} {K : Type} [Field K]

structure SpPlaneSetupQ (ℓ f p r : ℕ) (K : Type) [Field K] (Ahat : Subgroup (StatedSp r K)) :
    Prop where
  prime_ell : ℓ.Prime
  one_le_f : 1 ≤ f
  card_K : Nat.card K = ℓ ^ f
  prime_p : p.Prime
  p_ne_two : p ≠ 2
  ne_char : p ≠ ℓ
  two_le_r : 2 ≤ r
  four_le_q : 4 ≤ ℓ ^ f
  elem : CFSG.IsElementaryAbelian p Ahat
  card_plane : Nat.card Ahat = p ^ 2

variable {ℓ f p : ℕ} {Ahat : Subgroup (StatedSp r K)}

theorem SpPlaneSetupQ.not_exceptional (S : SpPlaneSetupQ ℓ f p r K Ahat) :
    ¬ (r = 2 ∧ ℓ ^ f = 2) := fun h => by
  have := S.four_le_q
  omega

theorem SpPlaneSetupQ.finite (S : SpPlaneSetupQ ℓ f p r K Ahat) : Finite K :=
  Nat.finite_of_card_ne_zero (by rw [S.card_K]; exact pow_ne_zero f S.prime_ell.ne_zero)

theorem SpPlaneSetupQ.four_le_card (S : SpPlaneSetupQ ℓ f p r K Ahat) : 4 ≤ Nat.card K := by
  rw [S.card_K]
  exact S.four_le_q

theorem SpPlaneSetupQ.charP (S : SpPlaneSetupQ ℓ f p r K Ahat) : CharP K ℓ := by
  have := S.finite
  have := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨S.prime_ell⟩
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, S.card_K])

theorem SpPlaneSetupQ.neZero (S : SpPlaneSetupQ ℓ f p r K Ahat) : NeZero r :=
  ⟨by have := S.two_le_r; omega⟩

theorem SpPlaneSetupQ.p_cast_ne_zero (S : SpPlaneSetupQ ℓ f p r K Ahat) : (p : K) ≠ 0 := by
  have := S.charP
  intro h
  rw [CharP.cast_eq_zero_iff K ℓ] at h
  exact S.ne_char ((Nat.prime_dvd_prime_iff_eq S.prime_ell S.prime_p).mp h).symm

theorem SpPlaneSetupQ.conj_injective (S : SpPlaneSetupQ ℓ f p r K Ahat) :
    Function.Injective (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K))) :=
  spConj_injective S.prime_ell S.one_le_f S.card_K S.two_le_r S.not_exceptional

theorem SpPlaneSetupQ.pow_eq_one (S : SpPlaneSetupQ ℓ f p r K Ahat) {x : StatedSp r K}
    (hx : x ∈ Ahat) : x ^ p = 1 := by
  have := S.elem
  exact elemPow_eq_one_of_isElementaryAbelian x hx

theorem SpPlaneSetupQ.orderOf_eq (S : SpPlaneSetupQ ℓ f p r K Ahat) {x : StatedSp r K}
    (hx : x ∈ Ahat) (hx1 : x ≠ 1) : orderOf x = p :=
  have : Fact p.Prime := ⟨S.prime_p⟩
  orderOf_eq_prime (S.pow_eq_one hx) hx1

open _root_.Classical in
theorem SpPlaneSetupQ.decomp (S : SpPlaneSetupQ ℓ f p r K Ahat) : SpPlaneDecomp p Ahat := by
  have := S.finite
  have := S.charP
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := symplectic_plane_kernel_line_decomposition
    S.prime_ell S.prime_p S.p_ne_two S.ne_char S.elem S.card_plane
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem SpPlaneSetupQ.spFixedListed (S : SpPlaneSetupQ ℓ f p r K Ahat)
    (D : SpPlaneDecomp p Ahat) {M : Subgroup ↥Ahat} (hM : Nat.card M = p)
    (hVM : spLineSpace M ≠ ⊥) {x : StatedSp r K} (hxA : x ∈ Ahat)
    (hxM : (⟨x, hxA⟩ : ↥Ahat) ∈ M) (hx1 : x ≠ 1) : SpFixedListed x ∧ 2 ≤ spFixedDim x := by
  obtain ⟨h2, hle⟩ := D.lcm_le_finrank_ker hM hVM hxA hxM hx1
  rw [← spFixedDim_eq_finrank_ker] at hle
  have hq4 := S.four_le_card
  exact ⟨⟨by omega, fun h => by omega⟩, by omega⟩

theorem SpPlaneSetupQ.orderOf_proj (S : SpPlaneSetupQ ℓ f p r K Ahat) {x : StatedSp r K}
    (hxA : x ∈ Ahat) (hx1 : x ≠ 1) : orderOf (proj r K x) = p := by
  have := S.finite
  have : Fact p.Prime := ⟨S.prime_p⟩
  have hxp := S.pow_eq_one hxA
  have hr : 1 ≤ r := by have := S.two_le_r; omega
  have h1 : proj r K x ≠ 1 := by
    intro h
    exact hx1 (eq_of_map_eq_of_pow_eq_one_of_coprime (proj r K) ker_proj_le_center
      (coprime_card_ker_proj hr S.prime_p S.p_ne_two) (a := 1) (b := 1)
      (by rwa [pow_one]) (by simp) (by rw [h, map_one]))
  refine orderOf_eq_prime ?_ h1
  rw [← map_pow, hxp, map_one]

theorem SpPlaneSetupQ.blocks (S : SpPlaneSetupQ ℓ f p r K Ahat) {x : StatedSp r K}
    (hxA : x ∈ Ahat) (hx1 : x ≠ 1) : SpPrimaryBlocks ℓ f p x (proj r K x) := by
  have hr : 1 ≤ r := by have := S.two_le_r; omega
  exact (symplectic_cross_prime_primary_centralizer_blocks S.prime_ell S.one_le_f S.card_K
    S.prime_p S.p_ne_two S.ne_char hr (proj r K x) (S.orderOf_proj hxA hx1)).2 x rfl
    (S.orderOf_eq hxA hx1)

theorem SpPlaneSetupQ.line_scalar [NeZero r] (S : SpPlaneSetupQ ℓ f p r K Ahat)
    (D : SpPlaneDecomp p Ahat)
    {M : Subgroup ↥Ahat} (hM : Nat.card M = p) (hVM : spLineSpace M ≠ ⊥) {x : StatedSp r K}
    (hxA : x ∈ Ahat) (hxM : (⟨x, hxA⟩ : ↥Ahat) ∈ M) (hx1 : x ≠ 1) (A : gsp r K) (σ : K ≃+* K)
    {α : MulAut (StatedProj (StatedSp r K))} (hα : α = conjAut r K A * fieldAut r K σ)
    (hcent : CentralizesListed α x) :
    σ = RingEquiv.refl K ∧ ∃ l : K,
      (∀ u ∈ LinearMap.ker (spEnd x - 1), semilinMap A σ u = l • u) ∧
        l * l = (multiplier r K A : K) := by
  have := S.finite
  have hnd := D.nondegenerate_ker hM hxA hxM hx1
  obtain ⟨hlisted, h2dim⟩ := S.spFixedListed D hM hVM hxA hxM hx1
  have hdim : spFixedDim x = Module.finrank K (LinearMap.ker (spEnd x - 1)) :=
    spFixedDim_eq_finrank_ker x
  have hne : LinearMap.ker (spEnd x - 1) ≠ ⊥ := by
    intro h
    have h0 : Module.finrank K (LinearMap.ker (spEnd x - 1)) = 0 := by
      rw [h]
      exact finrank_bot K _
    omega
  have hinj := S.conj_injective
  have hq4 := S.four_le_card
  have h42 : ¬ (spFixedDim x = 4 ∧ Nat.card K = 2) := fun h => by omega
  have himg : spFixedLayerImage x = (spFixedFactor x).map (proj r K) := by
    simp [spFixedLayerImage, hlisted, h42]
  have hcomm : ∀ g ∈ spFixedFactor x,
      α * MulAut.conj (proj r K g) = MulAut.conj (proj r K g) * α := fun g hg =>
    hcent.1 hlisted _ (himg ▸ Subgroup.mem_map_of_mem _ hg)
  have hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd x) := by
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hev1 : (spEnd x).HasEigenvalue 1 :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr (by
        rw [one_smul]; exact mem_ker_sub_one_iff.mp hu), hu0⟩
    have := KCUnitaryScalar.X_sub_C_mem_primaryFactors hev1
    rwa [map_one] at this
  have hfd : Module.finrank K (primaryComponent (spEnd x) (X - 1)) = spFixedDim x := rfl
  have hG : Group.IsPerfect (spFixedFactor x) ∨ (proj r K).ker = ⊥ :=
    Or.inl (isPerfect_spFixedFactor (S.blocks hxA hx1) hmem (by rw [hfd]; exact h2dim)
      (Or.inl hq4))
  have hfix := semiConj_eq_of_commute hinj A σ hG (hα ▸ hcomm)
  exact line_scalar_of_fixedFactor A σ hfix hnd hne

theorem spBlockFacts_of_spPaired_q (hq : 4 ≤ ℓ ^ f) {x : StatedSp r K}
    {h : primaryFactors (spEnd x)} (hP : SpPairedBlock ℓ f p x h) :
    KCSpIsotypic.SpBlockFacts (spForm r K) (spLin r K x) h := by
  obtain ⟨φ, hφ, -⟩ := hP.factor
  refine KCSpIsotypic.spBlockFacts_of_paired ((KCSpIsotypic.spOrbitEquiv x rfl).trans φ)
    (fun g v hv => ?_) ?_
  · rw [MulEquiv.trans_apply, hφ, KCSpIsotypic.spEnd_orbitEquiv]
  · have hdeg : 1 ≤ (h : K[X]).natDegree :=
      Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
    have hN : ℓ ^ f ≤ (ℓ ^ f) ^ (h : K[X]).natDegree := Nat.le_self_pow (by omega) _
    have hcard : 4 ≤ Nat.card (AdjoinRoot (h : K[X])) := by
      rw [hP.card_field]
      omega
    have : Finite (AdjoinRoot (h : K[X])) := Nat.finite_of_card_ne_zero (by omega)
    exact KCSpIsotypic.exists_finset_card_four_of_card hcard

theorem spBlockFacts_of_spSelfDual_q (hq : 4 ≤ ℓ ^ f) {x : StatedSp r K}
    {h : primaryFactors (spEnd x)} (hself : KCOrthogonal.reciprocalPolynomial (h : K[X]) = h)
    (hS : SpSelfDualBlock ℓ f p x h) :
    KCSpIsotypic.SpBlockFacts (spForm r K) (spLin r K x) h := by
  obtain ⟨d, hd, -, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, hφ⟩ := hS.exists_half
  have hO : ({(h : K[X]), KCOrthogonal.reciprocalPolynomial (h : K[X])} : Set K[X]) =
      {(h : K[X])} := by
    rw [hself, Set.pair_eq_singleton]
  refine KCSpIsotypic.spBlockFacts_of_selfDual hE hHf hHfl
    ((KCSpIsotypic.spOrbitEquiv x hO).trans φ) (fun g v hv => ?_) ?_
  · rw [MulEquiv.trans_apply]
    have := hφ (KCSpIsotypic.spOrbitEquiv x hO g) v hv
    rw [this, KCSpIsotypic.spEnd_orbitEquiv]
  · have hdeg : 1 ≤ (h : K[X]).natDegree :=
      Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
    have hd1 : 1 ≤ d := by omega
    have hN : 4 ≤ (ℓ ^ f) ^ d := hq.trans (Nat.le_self_pow (by omega) _)
    rw [← pow_mul] at hN
    exact hN

theorem spBlockFacts_of_ne_X_sub_one_q {x : StatedSp r K} (hq : 4 ≤ ℓ ^ f)
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x)) (h : primaryFactors (spEnd x))
    (h1 : (h : K[X]) ≠ X - 1) : KCSpIsotypic.SpBlockFacts (spForm r K) (spLin r K x) h := by
  by_cases h2 : KCOrthogonal.reciprocalPolynomial (h : K[X]) = h
  · exact spBlockFacts_of_spSelfDual_q hq h2 (blocks.selfDual h h1 h2)
  · exact spBlockFacts_of_spPaired_q hq (blocks.paired h (Ne.symm h2))

end CFSG.HardMathSupport.Timmesfeld.CrossChar
