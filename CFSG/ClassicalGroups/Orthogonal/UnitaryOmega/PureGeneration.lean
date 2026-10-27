module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Chamber
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureBlocks
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockGeneration

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal

section EichlerTwoLt

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [FiniteDimensional K V] in
theorem eichler_mem_supportedDerived_of_two_lt (hK : 2 < Nat.card K) {X : Submodule K V}
    (hX : (polarBilin (Q.comp X.subtype)).Nondegenerate) {e w : V} (he : e ∈ X) (hw : w ∈ X) :
    eichler Q e w ∈ supportedDerived Q X := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  by_cases h : Q e = 0 ∧ polar Q e w = 0
  · obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne_one_of_two_lt hK
    exact eichler_mem_supportedDerived he hw h.1 h.2
      (CFSG.SeitzReduction.OmegaPilot.eichler_mem_orthDerived_of_ne_zero_ne_one hX hc0 hc1 _ _)
  · rw [eichler_of_not h]
    exact one_mem _

end EichlerTwoLt

end CFSG.RankThree.PartOne.KCOrthogonal

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
open CFSG.ClassicalGroups.Orthogonal
open Module QuadraticMap
open scoped commutatorElement

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

private abbrev NormV (F K : Type) [Field F] [Field K] [Algebra F K] (n : ℕ) : Type :=
  (F × F) × (Fin n → K)

private theorem normHypForm_zero_single_add {n : ℕ} {a b : Fin n} (hab : a ≠ b) (x y : K) :
    normHypForm E n (((0, 0), Pi.single a x + Pi.single b y) : NormV F K n) =
      normQuad E x + normQuad E y := by
  rw [normHypForm_apply_coord]
  have h1 : hypPlane F (0 : F × F) = 0 := by simp [hypPlane_apply]
  rw [show ((0, 0), (Pi.single a x + Pi.single b y : Fin n → K)).1 = (0 : F × F) from rfl,
    h1, zero_add]
  have h0 : ∀ k ∈ (Finset.univ : Finset (Fin n)), k ∉ ({a, b} : Finset (Fin n)) →
      normQuad E ((Pi.single a x + Pi.single b y : Fin n → K) k) = 0 := by
    intro k _ hk
    have hka : k ≠ a := fun h => hk (by simp [h])
    have hkb : k ≠ b := fun h => hk (by simp [h])
    simp [Pi.add_apply, Pi.single_eq_of_ne hka, Pi.single_eq_of_ne hkb]
  rw [← Finset.sum_subset (Finset.subset_univ _) h0, Finset.sum_pair hab]
  simp [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab,
    Pi.single_eq_of_ne (Ne.symm hab)]

private theorem polar_normHypForm_zero_pair {n : ℕ} {i j : Fin n} (x : NormV F K n) (a b : K) :
    polar (normHypForm E n) x (((0, 0), Pi.single i a + Pi.single j b) : NormV F K n) =
      polar (normQuad E) (x.2 i) a + polar (normQuad E) (x.2 j) b := by
  rw [normHypForm, polar_hypSum]
  show x.1.1 * (0 : F) + (0 : F) * x.1.2 +
      polar (Qn E n) x.2 (Pi.single i a + Pi.single j b) =
    polar (normQuad E) (x.2 i) a + polar (normQuad E) (x.2 j) b
  rw [mul_zero, zero_mul, zero_add, polar_add_right, polar_Qn_single, polar_Qn_single, zero_add]

private theorem algebraMap_polar_normHypForm_zero_pair {n : ℕ} {i j : Fin n}
    (x : NormV F K n) (a b : K) :
    algebraMap F K
        (polar (normHypForm E n) x (((0, 0), Pi.single i a + Pi.single j b) : NormV F K n)) =
      (x.2 i * unitaryInvolution K 2 f a + a * unitaryInvolution K 2 f (x.2 i)) +
        (x.2 j * unitaryInvolution K 2 f b + b * unitaryInvolution K 2 f (x.2 j)) := by
  rw [polar_normHypForm_zero_pair, map_add, algebraMap_polar_normQuad, algebraMap_polar_normQuad]

private theorem algebraMap_polar_normHypForm_u {n : ℕ} {i j : Fin n} (x : NormV F K n) :
    algebraMap F K
        (polar (normHypForm E n) x (((0, 0), Pi.single i 1 + Pi.single j 1) : NormV F K n)) =
      (x.2 i + x.2 j) + unitaryInvolution K 2 f (x.2 i + x.2 j) := by
  rw [algebraMap_polar_normHypForm_zero_pair]
  simp only [map_one, mul_one]
  rw [map_add]
  ring

private theorem algebraMap_polar_normHypForm_v {n : ℕ} {i j : Fin n} {ω : K} (x : NormV F K n) :
    algebraMap F K
        (polar (normHypForm E n) x (((0, 0), Pi.single i ω + Pi.single j ω) : NormV F K n)) =
      (x.2 i + x.2 j) * unitaryInvolution K 2 f ω +
        ω * unitaryInvolution K 2 f (x.2 i + x.2 j) := by
  rw [algebraMap_polar_normHypForm_zero_pair]
  rw [map_add]
  ring

omit [Finite K] in
private theorem neg_eq_self_of_charP_two (z : K) : -z = z := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hzz : z + z = 0 := by rw [← two_mul, h2, zero_mul]
  exact neg_eq_of_add_eq_zero_left hzz

omit [Finite K] in
private theorem add_self_eq_zero_of_charP_two (z : K) : z + z = 0 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [← two_mul, h2, zero_mul]

private theorem swap_increment {ω : K} (hω : polar (normQuad E) 1 ω = 1) (t : K) :
    (t + unitaryInvolution K 2 f t) * ω -
        (t * unitaryInvolution K 2 f ω + ω * unitaryInvolution K 2 f t) = t := by
  have hω' : unitaryInvolution K 2 f ω + ω = 1 := by
    have h := algebraMap_polar_normQuad E (1 : K) ω
    rw [hω, map_one] at h
    simpa only [map_one, mul_one, one_mul] using h.symm
  calc
    (t + unitaryInvolution K 2 f t) * ω -
        (t * unitaryInvolution K 2 f ω + ω * unitaryInvolution K 2 f t)
        = (t + unitaryInvolution K 2 f t) * ω -
            (t * unitaryInvolution K 2 f ω + unitaryInvolution K 2 f t * ω) := by
          rw [mul_comm ω (unitaryInvolution K 2 f t)]
    _ = t * ω + unitaryInvolution K 2 f t * ω -
            (t * unitaryInvolution K 2 f ω + unitaryInvolution K 2 f t * ω) := by ring
    _ = t * (ω - unitaryInvolution K 2 f ω) := by ring
    _ = t * (ω + unitaryInvolution K 2 f ω) := by
          rw [sub_eq_add_neg, neg_eq_self_of_charP_two]
    _ = t * (unitaryInvolution K 2 f ω + ω) := by rw [add_comm]
    _ = t := by rw [hω', mul_one]

private theorem normHypForm_swapU_eq_zero {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    normHypForm E n (((0, 0), Pi.single i 1 + Pi.single j 1) : NormV F K n) = 0 := by
  have h2F : (2 : F) = 0 := (algebraMap F K).injective (by
    rw [map_ofNat, map_zero]
    simpa using (CharP.cast_eq_zero K 2))
  rw [normHypForm_zero_single_add E hij 1 1, normQuad_one]
  rw [← two_mul, h2F, zero_mul]

private theorem normHypForm_swapV_eq_zero {n : ℕ} {i j : Fin n} (hij : i ≠ j) (ω : K) :
    normHypForm E n (((0, 0), Pi.single i ω + Pi.single j ω) : NormV F K n) = 0 := by
  have h2F : (2 : F) = 0 := (algebraMap F K).injective (by
    rw [map_ofNat, map_zero]
    simpa using (CharP.cast_eq_zero K 2))
  rw [normHypForm_zero_single_add E hij ω ω]
  rw [← two_mul, h2F, zero_mul]

private theorem polar_normHypForm_swapU_swapV_eq_zero {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {ω : K} (hω : polar (normQuad E) 1 ω = 1) :
    polar (normHypForm E n) (((0, 0), Pi.single i 1 + Pi.single j 1) : NormV F K n)
        (((0, 0), Pi.single i ω + Pi.single j ω) : NormV F K n) = 0 := by
  have h2F : (2 : F) = 0 := (algebraMap F K).injective (by
    rw [map_ofNat, map_zero]
    simpa using (CharP.cast_eq_zero K 2))
  have hselfF : ∀ z : F, z + z = 0 := fun z => by rw [← two_mul, h2F, zero_mul]
  rw [polar_normHypForm_zero_pair E]
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
    Pi.single_eq_of_ne (Ne.symm hij), zero_add, add_zero]
  rw [hω]
  exact hselfF 1

private theorem eichler_swap_coord {n : ℕ} {i j : Fin n} (hij : i ≠ j) {ω : K}
    (hω : polar (normQuad E) 1 ω = 1) (x : NormV F K n) (k : Fin n) :
    (eichler (normHypForm E n) (((0, 0), Pi.single i 1 + Pi.single j 1) : NormV F K n)
        (((0, 0), Pi.single i ω + Pi.single j ω) : NormV F K n) x).2 k =
      x.2 k +
          (polar (normHypForm E n) x
            (((0, 0), Pi.single i 1 + Pi.single j 1) : NormV F K n)) •
            ((Pi.single i ω + Pi.single j ω : Fin n → K) k) -
        (polar (normHypForm E n) x
          (((0, 0), Pi.single i ω + Pi.single j ω) : NormV F K n)) •
          ((Pi.single i 1 + Pi.single j 1 : Fin n → K) k) := by
  have hu := normHypForm_swapU_eq_zero E hij
  have hv := normHypForm_swapV_eq_zero E hij ω
  have huv := polar_normHypForm_swapU_swapV_eq_zero E hij hω
  rw [eichler_apply hu huv x]
  simp only [Prod.snd_add, Prod.snd_sub, Prod.smul_snd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    hv, zero_mul, add_zero]

private theorem eichler_swap_fst {n : ℕ} {i j : Fin n} (hij : i ≠ j) {ω : K}
    (hω : polar (normQuad E) 1 ω = 1) (x : NormV F K n) :
    (eichler (normHypForm E n) (((0, 0), Pi.single i 1 + Pi.single j 1) : NormV F K n)
        (((0, 0), Pi.single i ω + Pi.single j ω) : NormV F K n) x).1 = x.1 := by
  have hu := normHypForm_swapU_eq_zero E hij
  have huv := polar_normHypForm_swapU_swapV_eq_zero E hij hω
  rw [eichler_apply hu huv x]
  simp [Prod.fst_add, Prod.fst_sub]

private theorem eichler_swap_coord_i {n : ℕ} {i j : Fin n} (hij : i ≠ j) {ω : K}
    (hω : polar (normQuad E) 1 ω = 1) (x : NormV F K n) :
    (eichler (normHypForm E n) (((0, 0), Pi.single i 1 + Pi.single j 1) : NormV F K n)
        (((0, 0), Pi.single i ω + Pi.single j ω) : NormV F K n) x).2 i = x.2 j := by
  have hxi : x.2 i + (x.2 i + x.2 j) = x.2 j := by
    rw [← add_assoc, add_self_eq_zero_of_charP_two, zero_add]
  have hinc := swap_increment E hω (x.2 i + x.2 j)
  rw [eichler_swap_coord E hij hω x i]
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, add_zero]
  rw [Algebra.smul_def, Algebra.smul_def, mul_one,
    algebraMap_polar_normHypForm_u, algebraMap_polar_normHypForm_v]
  calc
    x.2 i + (x.2 i + x.2 j + unitaryInvolution K 2 f (x.2 i + x.2 j)) * ω -
        ((x.2 i + x.2 j) * unitaryInvolution K 2 f ω +
          ω * unitaryInvolution K 2 f (x.2 i + x.2 j))
        = x.2 i + ((x.2 i + x.2 j + unitaryInvolution K 2 f (x.2 i + x.2 j)) * ω -
            ((x.2 i + x.2 j) * unitaryInvolution K 2 f ω +
              ω * unitaryInvolution K 2 f (x.2 i + x.2 j))) := by ring
    _ = x.2 i + (x.2 i + x.2 j) := by rw [hinc]
    _ = x.2 j := hxi

private theorem eichler_swap_coord_j {n : ℕ} {i j : Fin n} (hij : i ≠ j) {ω : K}
    (hω : polar (normQuad E) 1 ω = 1) (x : NormV F K n) :
    (eichler (normHypForm E n) (((0, 0), Pi.single i 1 + Pi.single j 1) : NormV F K n)
        (((0, 0), Pi.single i ω + Pi.single j ω) : NormV F K n) x).2 j = x.2 i := by
  have hxj : x.2 j + (x.2 i + x.2 j) = x.2 i := by
    rw [add_comm (x.2 i) (x.2 j), ← add_assoc,
      add_self_eq_zero_of_charP_two, zero_add]
  have hinc := swap_increment E hω (x.2 i + x.2 j)
  rw [eichler_swap_coord E hij hω x j]
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij), zero_add]
  rw [Algebra.smul_def, Algebra.smul_def, mul_one,
    algebraMap_polar_normHypForm_u, algebraMap_polar_normHypForm_v]
  calc
    x.2 j + (x.2 i + x.2 j + unitaryInvolution K 2 f (x.2 i + x.2 j)) * ω -
        ((x.2 i + x.2 j) * unitaryInvolution K 2 f ω +
          ω * unitaryInvolution K 2 f (x.2 i + x.2 j))
        = x.2 j + ((x.2 i + x.2 j + unitaryInvolution K 2 f (x.2 i + x.2 j)) * ω -
            ((x.2 i + x.2 j) * unitaryInvolution K 2 f ω +
              ω * unitaryInvolution K 2 f (x.2 i + x.2 j))) := by ring
    _ = x.2 j + (x.2 i + x.2 j) := by
        rw [show (x.2 i + x.2 j + unitaryInvolution K 2 f (x.2 i + x.2 j)) * ω -
            ((x.2 i + x.2 j) * unitaryInvolution K 2 f ω +
              ω * unitaryInvolution K 2 f (x.2 i + x.2 j)) = x.2 i + x.2 j from hinc]
    _ = x.2 i := hxj

private theorem eichler_swap_coord_other {n : ℕ} {i j : Fin n} (hij : i ≠ j) {ω : K}
    (hω : polar (normQuad E) 1 ω = 1) (x : NormV F K n) {k : Fin n} (hki : k ≠ i)
    (hkj : k ≠ j) :
    (eichler (normHypForm E n) (((0, 0), Pi.single i 1 + Pi.single j 1) : NormV F K n)
        (((0, 0), Pi.single i ω + Pi.single j ω) : NormV F K n) x).2 k = x.2 k := by
  rw [eichler_swap_coord E hij hω x k]
  simp [Pi.add_apply, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]

theorem normPerm_swap_eq_eichler {n : ℕ} (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) {ω : K}
    (hω : polar (normQuad E) 1 ω = 1) :
    ((normPerm E hn (Equiv.swap i j) : normOmega E n) :
        ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) =
      eichler (normHypForm E n)
        (((0, 0), Pi.single i 1 + Pi.single j 1) : (F × F) × (Fin n → K))
        (((0, 0), Pi.single i ω + Pi.single j ω) : (F × F) × (Fin n → K)) := by
  classical
  let u : NormV F K n := ((0, 0), Pi.single i 1 + Pi.single j 1)
  let v : NormV F K n := ((0, 0), Pi.single i ω + Pi.single j ω)
  let Q : QuadraticForm F (NormV F K n) := normHypForm E n
  apply LinearEquiv.ext
  intro x
  rw [normPerm_apply]
  simp only [Equiv.swap_inv]
  refine Prod.ext ?_ (funext fun k => ?_)
  · exact (eichler_swap_fst E hij hω x).symm
  · by_cases hki : k = i
    · change x.2 (Equiv.swap i j k) = (eichler Q u v x).2 k
      rw [hki, Equiv.swap_apply_left]
      exact (eichler_swap_coord_i E hij hω x).symm
    · by_cases hkj : k = j
      · change x.2 (Equiv.swap i j k) = (eichler Q u v x).2 k
        rw [hkj, Equiv.swap_apply_right]
        exact (eichler_swap_coord_j E hij hω x).symm
      · change x.2 (Equiv.swap i j k) = (eichler Q u v x).2 k
        rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
        exact (eichler_swap_coord_other E hij hω x hki hkj).symm

private theorem nondegenerate_normPlane_sup_pair {n : ℕ} {i j : Fin n} :
    (polarBilin ((normHypForm E n).comp
      ((coordPlane (LinearEquiv.refl F (NormV F K n)) i ⊔
        coordPlane (LinearEquiv.refl F (NormV F K n)) j)).subtype)).Nondegenerate := by
  have : FiniteDimensional F K := finiteDimensional_of_quadExt E
  let ψ := LinearEquiv.refl F (NormV F K n)
  have hψ := normHypForm_apply_coord E n
  have hQE := normQuad_polarBilin_nondegenerate E
  have hU : ∀ k, PolarNondegOn (normHypForm E n) (coordPlane ψ k) :=
    fun k => coordPlane_polarNondegOn ψ hψ hQE k
  have horth : ∀ k l, k ≠ l → ∀ x ∈ coordPlane ψ k, ∀ y ∈ coordPlane ψ l,
      polar (normHypForm E n) x y = 0 :=
    fun k l hkl x hx y hy => polar_coordPlane_plane ψ hψ hkl hx hy
  have hsup : ({i, j} : Finset (Fin n)).sup (coordPlane ψ) = coordPlane ψ i ⊔ coordPlane ψ j := by
    rw [Finset.sup_insert, Finset.sup_singleton]
  rw [← hsup]
  exact nondegenerate_finset_sup (coordPlane ψ) hU horth {i, j}

omit [Finite K] [CharP K 2] in
private theorem mem_normPlane_pair_swapU {n : ℕ} {i j : Fin n} :
    (((0, 0), Pi.single i 1 + Pi.single j 1) : NormV F K n) ∈
      coordPlane (LinearEquiv.refl F (NormV F K n)) i ⊔
        coordPlane (LinearEquiv.refl F (NormV F K n)) j := by
  have hsum : (((0, 0), Pi.single i 1 + Pi.single j 1) : NormV F K n) =
      (((0, 0), Pi.single i 1) : NormV F K n) +
        (((0, 0), Pi.single j 1) : NormV F K n) := by
    ext <;> simp
  rw [hsum]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (mem_coordPlane.mpr ⟨1, rfl⟩))
    (Submodule.mem_sup_right (mem_coordPlane.mpr ⟨1, rfl⟩))

omit [Finite K] [CharP K 2] in
private theorem mem_normPlane_pair_swapV {n : ℕ} {i j : Fin n} (ω : K) :
    (((0, 0), Pi.single i ω + Pi.single j ω) : NormV F K n) ∈
      coordPlane (LinearEquiv.refl F (NormV F K n)) i ⊔
        coordPlane (LinearEquiv.refl F (NormV F K n)) j := by
  have hsum : (((0, 0), Pi.single i ω + Pi.single j ω) : NormV F K n) =
      (((0, 0), Pi.single i ω) : NormV F K n) +
        (((0, 0), Pi.single j ω) : NormV F K n) := by
    ext <;> simp
  rw [hsum]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (mem_coordPlane.mpr ⟨ω, rfl⟩))
    (Submodule.mem_sup_right (mem_coordPlane.mpr ⟨ω, rfl⟩))

theorem normPerm_swap_mem_normPureBlock (hq : 2 < Nat.card F) {n : ℕ} (hn : 3 ≤ n)
    (i j : Fin n) : normPerm E hn (Equiv.swap i j) ∈ normPureBlock E n {i, j} := by
  classical
  by_cases hij : i = j
  · subst j
    rw [normPureBlock]
    simp only [Equiv.swap_self]
    exact Subgroup.one_mem _
  · let ψ := LinearEquiv.refl F (NormV F K n)
    let X : Submodule F (NormV F K n) := coordPlane ψ i ⊔ coordPlane ψ j
    have hsup : ({i, j} : Finset (Fin n)).sup (coordPlane ψ) = X := by
      dsimp only [X]
      rw [Finset.sup_insert, Finset.sup_singleton]
    have hX : (polarBilin ((normHypForm E n).comp X.subtype)).Nondegenerate := by
      dsimp only [X, ψ]
      exact nondegenerate_normPlane_sup_pair E
    obtain ⟨ω, hω⟩ := exists_polar_normQuad_one_eq_one E
    have heq := normPerm_swap_eq_eichler E hn hij hω
    have hu : (((0, 0), Pi.single i 1 + Pi.single j 1) : NormV F K n) ∈ X := by
      dsimp only [X, ψ]
      exact mem_normPlane_pair_swapU
    have hw : (((0, 0), Pi.single i ω + Pi.single j ω) : NormV F K n) ∈ X := by
      dsimp only [X, ψ]
      exact mem_normPlane_pair_swapV ω
    have hmem : eichler (normHypForm E n)
        (((0, 0), Pi.single i 1 + Pi.single j 1) : NormV F K n)
        (((0, 0), Pi.single i ω + Pi.single j ω) : NormV F K n) ∈
          supportedDerived (normHypForm E n) X :=
      eichler_mem_supportedDerived_of_two_lt hq hX hu hw
    rw [normPureBlock]
    refine Subgroup.mem_subgroupOf.mpr ?_
    rw [hsup, heq]
    exact hmem

theorem normBlock_singleton_sup_normPureBlock_pair (hq : 2 < Nat.card F) {n : ℕ} (hn : 3 ≤ n)
    (i j : Fin n) :
    normBlock E n {i} ⊔ normPureBlock E n {i, j} = normBlock E n {i, j} := by
  classical
  let H : Subgroup (normOmega E n) := normBlock E n {i} ⊔ normPureBlock E n {i, j}
  by_cases hij : i = j
  · subst j
    have hle : normPureBlock E n {i} ≤ normBlock E n {i} := normPureBlock_le_normBlock E n {i}
    simpa [H] using
      (sup_eq_left.mpr hle : normBlock E n {i} ⊔ normPureBlock E n {i} = normBlock E n {i})
  · have hHle : H ≤ normBlock E n {i, j} := by
      dsimp only [H]
      refine sup_le ?_ ?_
      · exact normBlock_mono E n (by
          intro x hx
          simp only [Finset.mem_singleton] at hx
          subst x
          simp)
      · exact normPureBlock_le_normBlock E n {i, j}
    have hleH : normBlock E n {i, j} ≤ H := by
      have h_i : normBlock E n {i} ≤ H := by
        dsimp only [H]
        exact le_sup_left
      have hs : normPerm E hn (Equiv.swap i j) ∈ H := by
        dsimp only [H]
        exact Subgroup.mem_sup_right (normPerm_swap_mem_normPureBlock E hq hn i j)
      have himage : ({i} : Finset (Fin n)).image (Equiv.swap i j) = {j} := by
        rw [Finset.image_singleton, Equiv.swap_apply_left]
      have hmap : (normBlock E n {i}).map
            (MulAut.conj (normPerm E hn (Equiv.swap i j))).toMonoidHom = normBlock E n {j} := by
        rw [map_normBlock_normPerm E hn (Equiv.swap i j) ({i} : Finset (Fin n)), himage]
      have hconj : (normBlock E n {i}).map
            (MulAut.conj (normPerm E hn (Equiv.swap i j))).toMonoidHom ≤ H := by
        rintro y hy
        obtain ⟨x, hx, rfl⟩ := hy
        exact H.mul_mem (H.mul_mem hs (h_i hx)) (H.inv_mem hs)
      have h_j : normBlock E n {j} ≤ H := by
        rw [← hmap]
        exact hconj
      rw [← normBlock_singleton_sup_singleton E i j]
      exact sup_le h_i h_j
    exact le_antisymm hHle hleH

private theorem normBlock_triple_le_of_singletons {n : ℕ} {i j k : Fin n}
    {L : Subgroup (normOmega E n)} (hij : i ≠ j)
    (h_i : normBlock E n {i} ≤ L) (h_j : normBlock E n {j} ≤ L)
    (h_k : normBlock E n {k} ≤ L) :
    normBlock E n {i, j, k} ≤ L := by
  classical
  have hsub_ij : ({i, j} : Finset (Fin n)) ⊆ {i, j, k} := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl <;> simp
  have hcard : 2 ≤ ({i, j, k} : Finset (Fin n)).card := by
    have h12 : ({i, j} : Finset (Fin n)).card = 2 := by simp [hij]
    rw [← h12]
    exact Finset.card_le_card hsub_ij
  rw [normBlock_eq_iSup_pairs E n {i, j, k} hcard]
  refine iSup_le fun P => ?_
  obtain ⟨a, b, hab, hPab⟩ := Finset.card_eq_two.mp P.2.2
  have haS : a ∈ ({i, j, k} : Finset (Fin n)) := P.2.1 (by rw [hPab]; simp)
  have hbS : b ∈ ({i, j, k} : Finset (Fin n)) := P.2.1 (by rw [hPab]; simp)
  have hsingle : ∀ x ∈ ({i, j, k} : Finset (Fin n)), normBlock E n {x} ≤ L := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact h_i
    · exact h_j
    · exact h_k
  rw [hPab, ← normBlock_singleton_sup_singleton E a b]
  exact sup_le (hsingle a haS) (hsingle b hbS)

private theorem normBlock_triple_le_pair_sup_pure {n : ℕ} {i j k : Fin n} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hq : 2 < Nat.card F) (hn : 3 ≤ n) :
    normBlock E n {i, j, k} ≤ normBlock E n {i, j} ⊔ normPureBlock E n {i, j, k} := by
  classical
  let L : Subgroup (normOmega E n) := normBlock E n {i, j} ⊔ normPureBlock E n {i, j, k}
  have hsub_ik : ({i, k} : Finset (Fin n)) ⊆ {i, j, k} := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl <;> simp
  have h_i : normBlock E n {i} ≤ L := by
    dsimp only [L]
    refine (normBlock_mono E n ?_).trans le_sup_left
    intro x hx
    simp only [Finset.mem_singleton] at hx
    subst x
    simp
  have h_j : normBlock E n {j} ≤ L := by
    dsimp only [L]
    refine (normBlock_mono E n ?_).trans le_sup_left
    intro x hx
    simp only [Finset.mem_singleton] at hx
    subst x
    simp
  have h_k : normBlock E n {k} ≤ L := by
    have hk_ik : normBlock E n {k} ≤ normBlock E n {i, k} :=
      normBlock_mono E n (by
        intro x hx
        simp only [Finset.mem_singleton] at hx
        subst x
        simp)
    refine hk_ik.trans ?_
    have hik_eq : normBlock E n {i, k} = normBlock E n {i} ⊔ normPureBlock E n {i, k} :=
      (normBlock_singleton_sup_normPureBlock_pair E hq hn i k).symm
    rw [hik_eq]
    exact sup_le h_i ((normPureBlock_mono E n hsub_ik).trans le_sup_right)
  exact normBlock_triple_le_of_singletons E hij h_i h_j h_k

theorem normBlock_pair_sup_normPureBlock_triple (hq : 2 < Nat.card F) {n : ℕ} (hn : 3 ≤ n)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    normBlock E n {i, j} ⊔ normPureBlock E n {i, j, k} = normBlock E n {i, j, k} := by
  classical
  have hsub_ij : ({i, j} : Finset (Fin n)) ⊆ {i, j, k} := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl <;> simp
  refine le_antisymm ?_ (normBlock_triple_le_pair_sup_pure E hij hik hjk hq hn)
  exact sup_le (normBlock_mono E n hsub_ij) (normPureBlock_le_normBlock E n {i, j, k})

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
