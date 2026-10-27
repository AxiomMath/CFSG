module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFiveFamily
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Kind

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open scoped commutatorElement

section DoubleFlip

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {a b a' b' : Fin d}

theorem swapLin_single (a b j : Fin d) :
    swapLin (K := K) a b (Pi.single j 1) = Pi.single (Equiv.swap a b j) 1 := by
  funext i
  rw [swapLin_apply]
  simp only [Pi.single_apply, Equiv.swap_apply_eq_iff]

theorem swapLin_inv (a b : Fin d) : (swapLin (K := K) a b)⁻¹ = swapLin a b :=
  inv_eq_of_mul_eq_one_right (swapLin_mul_swapLin a b)

theorem swap_comm_of_pairDisjoint (hd : PairDisjoint a b a' b') (i : Fin d) : Equiv.swap a' b' (Equiv.swap a b i) = Equiv.swap a b (Equiv.swap a' b' i) := by
  have h1 := hd.left_ne_left
  have h2 := hd.left_ne_right
  have h3 := hd.right_ne_left
  have h4 := hd.right_ne_right
  simp only [Equiv.swap_apply_def]
  split_ifs <;> simp_all

theorem pairSwap_apply_single_of_ne (h : IsHypCoord Q a b) (h' : IsHypCoord Q a' b') {c : Fin d}
    (hca : c ≠ a) (hcb : c ≠ b) (hca' : c ≠ a') (hcb' : c ≠ b') :
    pairSwap Q a b a' b' (Pi.single c 1) = Pi.single c 1 := by
  apply eichler_apply_of_polar_eq_zero
  · rw [polar_add_right, polar_comm, h.polar_left, polar_comm, h'.polar_left,
      Pi.single_eq_of_ne (Ne.symm hcb), Pi.single_eq_of_ne (Ne.symm hcb'), add_zero]
  · rw [polar_add_right, polar_comm, h.polar_right, polar_comm, h'.polar_right,
      Pi.single_eq_of_ne (Ne.symm hca), Pi.single_eq_of_ne (Ne.symm hca'), add_zero]

theorem pairSwap_apply_right' [CharP K 2] (h : IsHypCoord Q a b) (h' : IsHypCoord Q a' b')
    (hd : PairDisjoint a b a' b') :
    pairSwap Q a b a' b' (Pi.single a' 1) = Pi.single a 1 ∧
      pairSwap Q a b a' b' (Pi.single b' 1) = Pi.single b 1 := by
  rw [pairSwap_comm]
  exact pairSwap_apply_left h' h hd.symm

theorem pairSwap_mul_swapLin [CharP K 2] (h : IsHypCoord Q a b) (h' : IsHypCoord Q a' b')
    (hd : PairDisjoint a b a' b') :
    pairSwap Q a b a' b' * swapLin a b = swapLin a' b' * pairSwap Q a b a' b' := by
  obtain ⟨hga, hgb⟩ := pairSwap_apply_left h h' hd
  obtain ⟨hga', hgb'⟩ := pairSwap_apply_right' h h' hd
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun K (Fin d)).ext
  intro j
  simp only [Pi.basisFun_apply, LinearEquiv.coe_coe, LinearEquiv.mul_apply]
  by_cases hja : j = a
  · subst hja
    rw [swapLin_single, Equiv.swap_apply_left, hgb, hga, swapLin_single, Equiv.swap_apply_left]
  by_cases hjb : j = b
  · subst hjb
    rw [swapLin_single, Equiv.swap_apply_right, hga, hgb, swapLin_single, Equiv.swap_apply_right]
  by_cases hja' : j = a'
  · subst hja'
    rw [swapLin_single, Equiv.swap_apply_of_ne_of_ne hd.left_ne_left hd.left_ne_right, hga',
      swapLin_single, Equiv.swap_apply_of_ne_of_ne (Ne.symm hd.left_ne_left)
        (Ne.symm hd.right_ne_left)]
  by_cases hjb' : j = b'
  · subst hjb'
    rw [swapLin_single, Equiv.swap_apply_of_ne_of_ne hd.right_ne_left hd.right_ne_right, hgb',
      swapLin_single, Equiv.swap_apply_of_ne_of_ne (Ne.symm hd.left_ne_right)
        (Ne.symm hd.right_ne_right)]
  rw [swapLin_single, Equiv.swap_apply_of_ne_of_ne hja hjb,
    pairSwap_apply_single_of_ne h h' hja hjb hja' hjb', swapLin_single,
    Equiv.swap_apply_of_ne_of_ne hja' hjb']

@[expose] noncomputable def doubleFlip (a b a' b' : Fin d) : (Fin d → K) ≃ₗ[K] (Fin d → K) :=
  swapLin a b * swapLin a' b'

theorem doubleFlip_apply (v : Fin d → K) (i : Fin d) :
    doubleFlip (K := K) a b a' b' v i = v (Equiv.swap a' b' (Equiv.swap a b i)) := rfl

theorem doubleFlip_eq_commutator [CharP K 2] (h : IsHypCoord Q a b) (h' : IsHypCoord Q a' b')
    (hd : PairDisjoint a b a' b') :
    doubleFlip (K := K) a b a' b' = ⁅(swapLin a b : (Fin d → K) ≃ₗ[K] (Fin d → K)),
      pairSwap Q a b a' b'⁆ := by
  have hgs := pairSwap_mul_swapLin h h' hd
  rw [commutatorElement_def, swapLin_inv,
    mul_assoc (swapLin a b) (pairSwap Q a b a' b') (swapLin a b), hgs, ← mul_assoc,
    mul_inv_cancel_right]
  rfl

theorem doubleFlip_mem_orthDerived [CharP K 2] (h : IsHypCoord Q a b) (h' : IsHypCoord Q a' b')
    (hd : PairDisjoint a b a' b') : doubleFlip (K := K) a b a' b' ∈ orthDerived Q := by
  rw [doubleFlip_eq_commutator h h' hd]
  exact Subgroup.commutator_mem_commutator h.swapLin_mem_orthogonalGroup
    (eichler_mem_orthogonalGroup Q _ _)

theorem doubleFlip_mul_self (hd : PairDisjoint a b a' b') :
    doubleFlip (K := K) a b a' b' * doubleFlip a b a' b' = 1 := by
  ext v i
  simp only [LinearEquiv.mul_apply, doubleFlip_apply]
  rw [← swap_comm_of_pairDisjoint hd (Equiv.swap a b i), Equiv.swap_apply_self,
    Equiv.swap_apply_self]
  rfl

theorem doubleFlip_inv (hd : PairDisjoint a b a' b') :
    (doubleFlip (K := K) a b a' b')⁻¹ = doubleFlip a b a' b' :=
  inv_eq_of_mul_eq_one_right (doubleFlip_mul_self hd)

theorem doubleFlip_single (hd : PairDisjoint a b a' b') :
    doubleFlip (K := K) a b a' b' (Pi.single a 1) = Pi.single b 1 ∧
      doubleFlip (K := K) a b a' b' (Pi.single b 1) = Pi.single a 1 := by
  refine ⟨?_, ?_⟩
  · change swapLin a b (swapLin a' b' (Pi.single a 1)) = _
    rw [swapLin_single, Equiv.swap_apply_of_ne_of_ne (Ne.symm hd.left_ne_left)
      (Ne.symm hd.right_ne_left), swapLin_single, Equiv.swap_apply_left]
  · change swapLin a b (swapLin a' b' (Pi.single b 1)) = _
    rw [swapLin_single, Equiv.swap_apply_of_ne_of_ne (Ne.symm hd.left_ne_right)
      (Ne.symm hd.right_ne_right), swapLin_single, Equiv.swap_apply_right]

theorem torusEntry_swap_swap (hab : a ≠ b) (hd : PairDisjoint a b a' b') (c : Kˣ) (i : Fin d) :
    torusEntry a b c (Equiv.swap a' b' (Equiv.swap a b i)) = torusEntry a b c⁻¹ i := by
  have h1 := hd.left_ne_left
  have h2 := hd.left_ne_right
  have h3 := hd.right_ne_left
  have h4 := hd.right_ne_right
  simp only [torusEntry, Equiv.swap_apply_def]
  split_ifs <;> simp_all

theorem doubleFlip_conj_torusLin (hab : a ≠ b) (hd : PairDisjoint a b a' b') (c : Kˣ) :
    doubleFlip (K := K) a b a' b' * torusLin a b c * (doubleFlip a b a' b')⁻¹ =
      torusLin a b c⁻¹ := by
  rw [doubleFlip_inv hd]
  ext v i
  simp only [LinearEquiv.mul_apply, doubleFlip_apply, torusLin_apply]
  rw [torusEntry_swap_swap hab hd, ← swap_comm_of_pairDisjoint hd (Equiv.swap a b i),
    Equiv.swap_apply_self, Equiv.swap_apply_self]

theorem doubleFlip_conj_mem_stabSub (hd : PairDisjoint a b a' b')
    {x : (Fin d → K) ≃ₗ[K] (Fin d → K)} (hx : x ∈ stabSub a b) :
    doubleFlip a b a' b' * x * (doubleFlip a b a' b')⁻¹ ∈ stabSub a b := by
  obtain ⟨hwa, hwb⟩ := doubleFlip_single (K := K) hd
  obtain ⟨hxa, hxb⟩ := mem_stabSub.1 hx
  rw [doubleFlip_inv hd]
  refine mem_stabSub.2 ⟨?_, ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hwa, hxb, hwb]
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hwb, hxa, hwa]

end DoubleFlip

section Proj

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a b a' b' : Fin d}

theorem mem_normalizer_of_map_conj_le_of_mul_self {M : Type*} [Group M] {H : Subgroup M} {g : M}
    (hg : g * g = 1) (hle : H.map (MulAut.conj g).toMonoidHom ≤ H) : g ∈ normalizer (H : Set M) := by
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  refine mem_normalizer_iff.2 fun h => ⟨fun hh => hle ⟨h, hh, rfl⟩, fun hh => ?_⟩
  have h1 := hle ⟨g * h * g⁻¹, hh, rfl⟩
  have h2 : (MulAut.conj g).toMonoidHom (g * h * g⁻¹) = h := by
    change g * (g * h * g⁻¹) * g⁻¹ = h
    rw [hinv, show g * (g * h * g) * g = (g * g) * h * (g * g) by group, hg, one_mul, mul_one]
  rwa [h2] at h1

theorem projHom_doubleFlip_mul_self (hd : PairDisjoint a b a' b')
    (hw : doubleFlip (K := K) a b a' b' ∈ orthDerived Q) :
    projHom Q ⟨_, hw⟩ * projHom Q ⟨_, hw⟩ = 1 := by
  rw [← map_mul, ← map_one (projHom Q)]
  congr 1
  exact Subtype.ext (doubleFlip_mul_self hd)

theorem projHom_doubleFlip_mem_normalizer_pairTorusOf (h : IsHypCoord Q a b)
    (hd : PairDisjoint a b a' b') (hw : doubleFlip (K := K) a b a' b' ∈ orthDerived Q) :
    projHom Q ⟨_, hw⟩ ∈ normalizer (pairTorusOf Q a b : Set (matrixProjectiveDerived Q)) := by
  refine mem_normalizer_of_map_conj_le_of_mul_self (projHom_doubleFlip_mul_self hd hw) ?_
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  obtain ⟨c, hc⟩ := mem_subgroupOf.1 hx
  refine ⟨⟨_, hw⟩ * x * ⟨_, hw⟩⁻¹, mem_subgroupOf.2 ⟨c⁻¹, ?_⟩, ?_⟩
  · change torusLin a b c⁻¹ = doubleFlip a b a' b' * (x : (Fin d → K) ≃ₗ[K] (Fin d → K)) *
      (doubleFlip a b a' b')⁻¹
    rw [← hc, doubleFlip_conj_torusLin h.ne hd]
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

theorem projHom_doubleFlip_mem_normalizer_pairPerpOf (hd : PairDisjoint a b a' b')
    (hw : doubleFlip (K := K) a b a' b' ∈ orthDerived Q) :
    projHom Q ⟨_, hw⟩ ∈ normalizer (pairPerpOf Q a b : Set (matrixProjectiveDerived Q)) := by
  refine mem_normalizer_of_map_conj_le_of_mul_self (projHom_doubleFlip_mul_self hd hw) ?_
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  refine ⟨⟨_, hw⟩ * x * ⟨_, hw⟩⁻¹, mem_subgroupOf.2 ?_, ?_⟩
  · exact doubleFlip_conj_mem_stabSub hd (mem_subgroupOf.1 hx)
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

end Proj

section Perp

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus plusIndexEquiv
  regular_coordinateQuadPlus)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem pairPerpEquiv_apply_apply (hn : 4 ≤ n) (k : Fin n)
    (y : orthDerived (coordinateQuadPlus n K))
    (hy : (y : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) ∈
      stabSub (K := K) (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k)))
    (w : Fin (2 * (n - 1)) → K) (x : Fin (2 * (n - 1))) :
    ((pairPerpEquiv hn k ⟨projHom _ y, ⟨y, mem_subgroupOf.2 hy, rfl⟩⟩ :
      orthDerived (coordinateQuadPlus (n - 1) K)) :
        (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) w x =
      (y : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K))
        (Function.extend (plusPerpCoord (by omega) k) w 0) (plusPerpCoord (by omega) k x) := by
  set h := isHypCoord_coordinateQuadPlus (K := K) k
  set y' : stabDerived (coordinateQuadPlus n K) (plusIndexEquiv n (.inl k))
      (plusIndexEquiv n (.inr k)) := ⟨y, mem_subgroupOf.2 hy⟩ with hy'
  have hsymm : ((stabDerived (coordinateQuadPlus n K) (plusIndexEquiv n (.inl k))
      (plusIndexEquiv n (.inr k))).equivMapOfInjective (projHom (coordinateQuadPlus n K))
      (projHom_injective h.exists_ne_zero)).symm
        ⟨projHom _ y, ⟨y, mem_subgroupOf.2 hy, rfl⟩⟩ = y' := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  have key : pairPerpEquiv hn k ⟨projHom _ y, ⟨y, mem_subgroupOf.2 hy, rfl⟩⟩ =
      orthDerivedCongr (plusPerpIsometry (by omega) k)
        (h.stabDerivedEquiv (regular_coordinateQuadPlus n K (by omega)).1
          (regular_plusPerp hn k).1 (regular_plusPerp hn k).2 y') := by
    rw [← hsymm]
    rfl
  rw [key]
  have hcoe : ((orthDerivedCongr (plusPerpIsometry (K := K) (by omega) k)
      (h.stabDerivedEquiv (regular_coordinateQuadPlus n K (by omega)).1
        (regular_plusPerp hn k).1 (regular_plusPerp hn k).2 y') :
      orthDerived (coordinateQuadPlus (n - 1) K)) :
        (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) =
      LinearEquiv.autCongr (plusPerpIsometry (K := K) (by omega) k).toLinearEquiv
        ((h.stabDerivedEquiv (regular_coordinateQuadPlus n K (by omega)).1
          (regular_plusPerp hn k).1 (regular_plusPerp hn k).2 y' :
            orthDerived ((coordinateQuadPlus n K).comp
              (perpSub K (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k))).subtype)) :
          perpSub K (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k)) ≃ₗ[K]
            perpSub K (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k))) := rfl
  rw [hcoe, LinearEquiv.autCongr_apply_apply]
  rfl

theorem swap_swap_plusPerpCoord (hn : 1 ≤ n) (k : Fin n) (ℓ : Fin (n - 1))
    (x : Fin (2 * (n - 1))) :
    Equiv.swap (plusIndexEquiv n (.inl (avoid (M := n - 1) (by omega) k ℓ)))
        (plusIndexEquiv n (.inr (avoid (M := n - 1) (by omega) k ℓ)))
        (Equiv.swap (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k))
          (plusPerpCoord hn k x)) =
      plusPerpCoord hn k (Equiv.swap (plusIndexEquiv (n - 1) (.inl ℓ))
        (plusIndexEquiv (n - 1) (.inr ℓ)) x) := by
  rw [Equiv.swap_apply_of_ne_of_ne (plusPerpCoord_ne_left hn k x)
    (plusPerpCoord_ne_right hn k x)]
  obtain ⟨s, rfl⟩ := (plusIndexEquiv (n - 1)).surjective x
  have hinj : Function.Injective (Sum.map (avoid (M := n - 1) (by omega) k)
      (avoid (M := n - 1) (by omega) k)) :=
    Sum.map_injective.mpr ⟨avoid_injective _ k, avoid_injective _ k⟩
  have hpc : ∀ s' : Fin (n - 1) ⊕ Fin (n - 1), plusPerpCoord hn k (plusIndexEquiv (n - 1) s') =
      plusIndexEquiv n (Sum.map (avoid (by omega) k) (avoid (by omega) k) s') := by
    intro s'
    simp [plusPerpCoord]
  rw [(plusIndexEquiv (n - 1)).injective.swap_apply, hpc, hpc]
  have h1 : (Sum.inl (avoid (M := n - 1) (by omega) k ℓ) : Fin n ⊕ Fin n) =
      Sum.map (avoid (M := n - 1) (by omega) k) (avoid (M := n - 1) (by omega) k) (Sum.inl ℓ) :=
    rfl
  have h2 : (Sum.inr (avoid (M := n - 1) (by omega) k ℓ) : Fin n ⊕ Fin n) =
      Sum.map (avoid (M := n - 1) (by omega) k) (avoid (M := n - 1) (by omega) k) (Sum.inr ℓ) :=
    rfl
  rw [h1, h2, (plusIndexEquiv n).injective.swap_apply, hinj.swap_apply]

theorem doubleFlip_extend (hn : 1 ≤ n) (k : Fin n) (ℓ : Fin (n - 1))
    (v : Fin (2 * (n - 1)) → K) :
    doubleFlip (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k))
        (plusIndexEquiv n (.inl (avoid (M := n - 1) (by omega) k ℓ)))
        (plusIndexEquiv n (.inr (avoid (M := n - 1) (by omega) k ℓ)))
        (Function.extend (plusPerpCoord hn k) v 0) =
      Function.extend (plusPerpCoord hn k)
        (swapLin (plusIndexEquiv (n - 1) (.inl ℓ)) (plusIndexEquiv (n - 1) (.inr ℓ)) v) 0 := by
  have hd := pairDisjoint_plus (n := n) (Ne.symm (avoid_ne (M := n - 1) (by omega) k ℓ))
  funext p
  rw [doubleFlip_apply]
  by_cases hp : ∃ x, plusPerpCoord hn k x = p
  · obtain ⟨x, rfl⟩ := hp
    rw [swap_comm_of_pairDisjoint hd, ← swap_comm_of_pairDisjoint hd, swap_swap_plusPerpCoord,
      (plusPerpCoord_injective hn k).extend_apply, (plusPerpCoord_injective hn k).extend_apply,
      swapLin_apply]
  · rw [Function.extend_apply' _ _ _ hp, Function.extend_apply' _ _ _ ?_]
    · rfl
    rintro ⟨x, hx⟩
    apply hp
    refine ⟨Equiv.swap (plusIndexEquiv (n - 1) (.inl ℓ)) (plusIndexEquiv (n - 1) (.inr ℓ)) x, ?_⟩
    rw [← swap_swap_plusPerpCoord, hx, ← swap_comm_of_pairDisjoint hd (Equiv.swap _ _ p),
      Equiv.swap_apply_self, Equiv.swap_apply_self]

theorem pairPerpEquiv_conj_doubleFlip (hn : 4 ≤ n) (k : Fin n) (ℓ : Fin (n - 1))
    (w y : orthDerived (coordinateQuadPlus n K))
    (hw : (w : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) =
      doubleFlip (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k))
        (plusIndexEquiv n (.inl (avoid (M := n - 1) (by omega) k ℓ)))
        (plusIndexEquiv n (.inr (avoid (M := n - 1) (by omega) k ℓ))))
    (hy : (y : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) ∈
      stabSub (K := K) (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k)))
    (hy' : ((w * y * w⁻¹ : orthDerived (coordinateQuadPlus n K)) :
      (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) ∈
      stabSub (K := K) (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k))) :
    ((pairPerpEquiv hn k ⟨projHom _ (w * y * w⁻¹), ⟨w * y * w⁻¹, mem_subgroupOf.2 hy', rfl⟩⟩ :
        orthDerived (coordinateQuadPlus (n - 1) K)) :
        (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) =
      swapLin (plusIndexEquiv (n - 1) (.inl ℓ)) (plusIndexEquiv (n - 1) (.inr ℓ)) *
        ((pairPerpEquiv hn k ⟨projHom _ y, ⟨y, mem_subgroupOf.2 hy, rfl⟩⟩ :
          orthDerived (coordinateQuadPlus (n - 1) K)) :
            (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) *
        swapLin (plusIndexEquiv (n - 1) (.inl ℓ)) (plusIndexEquiv (n - 1) (.inr ℓ)) := by
  have hd := pairDisjoint_plus (n := n) (Ne.symm (avoid_ne (M := n - 1) (by omega) k ℓ))
  have hcoe : ((w * y * w⁻¹ : orthDerived (coordinateQuadPlus n K)) :
      (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) =
      doubleFlip (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k))
        (plusIndexEquiv n (.inl (avoid (M := n - 1) (by omega) k ℓ)))
        (plusIndexEquiv n (.inr (avoid (M := n - 1) (by omega) k ℓ))) *
        (y : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) *
      doubleFlip (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k))
        (plusIndexEquiv n (.inl (avoid (M := n - 1) (by omega) k ℓ)))
        (plusIndexEquiv n (.inr (avoid (M := n - 1) (by omega) k ℓ))) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hw, doubleFlip_inv hd]
  ext v x
  rw [pairPerpEquiv_apply_apply hn k _ hy' v x, hcoe]
  simp only [LinearEquiv.mul_apply]
  rw [swapLin_apply, pairPerpEquiv_apply_apply hn k y hy, doubleFlip_extend, doubleFlip_apply,
    swap_swap_plusPerpCoord]

end Perp

section Model

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus plusIndexEquiv)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusSwap
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)

variable {F : Type} [Field F] {m : ℕ}

theorem statedOmegaPlusEquiv_symm_projHom_entry [CharP F 2] (hm : 1 ≤ m)
    (u : orthDerived (coordinateQuadPlus m F)) (i j : Fin m ⊕ Fin m) :
    (((statedOmegaPlusEquiv F m hm).symm (projHom _ u) : StatedOmega (StatedQuadPlus m F)) :
      GL (Fin m ⊕ Fin m) F).val i j =
      (u : (Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F)) (Pi.single (plusIndexEquiv m j) 1)
        (plusIndexEquiv m i) := by
  have hsymm : (statedOmegaPlusEquiv F m hm).symm (projHom _ u) =
      (statedDerivedPlusEquiv F m).symm ((derivedEquiv _).symm u) := by
    rw [MulEquiv.symm_apply_eq]
    simp only [statedOmegaPlusEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  rw [hsymm, statedDerivedPlusEquiv_symm_entry, derivedEquiv_symm_entry]

theorem permMatrix_conj_apply_eq {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (σ : Equiv.Perm ι) (M : Matrix ι ι R) (i j : ι) :
    (σ.permMatrix R * M * σ.permMatrix R) i j = M (σ i) (σ.symm j) := by
  rw [Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_apply, ← Equiv.toPEquiv_symm,
    Equiv.toPEquiv_apply]
  change ((σ.toPEquiv.toMatrix : Matrix ι ι R) * M) i (σ.symm j) = _
  rw [PEquiv.toMatrix_mul_apply, Equiv.toPEquiv_apply]

theorem plusFlipAut_projHom [CharP F 2] (hm : 1 ≤ m) (z : orthDerived (coordinateQuadPlus m F))
    (hz : swapLin (K := F) (plusIndexEquiv m (.inl ⟨m - 1, by omega⟩))
        (plusIndexEquiv m (.inr ⟨m - 1, by omega⟩)) *
        (z : (Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F)) *
        swapLin (plusIndexEquiv m (.inl ⟨m - 1, by omega⟩))
          (plusIndexEquiv m (.inr ⟨m - 1, by omega⟩)) ∈ orthDerived (coordinateQuadPlus m F)) :
    plusFlipAut m F (by omega) (projHom _ z) = projHom _ ⟨_, hz⟩ := by
  set A := (statedOmegaPlusEquiv F m hm).symm (projHom _ z) with hA
  have hzA : projHom _ z = statedOmegaPlusEquiv F m hm A := by
    rw [hA, MulEquiv.apply_symm_apply]
  have hAe : ∀ i j, (A : GL (Fin m ⊕ Fin m) F).val i j =
      (z : (Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F)) (Pi.single (plusIndexEquiv m j) 1)
        (plusIndexEquiv m i) := fun i j => statedOmegaPlusEquiv_symm_projHom_entry hm z i j
  rw [hzA, plusFlipAut_statedOmegaPlusEquiv, ← MulEquiv.eq_symm_apply]
  apply Subtype.ext
  apply Units.ext
  ext i j
  have hR := statedOmegaPlusEquiv_symm_projHom_entry hm ⟨_, hz⟩ i j
  refine Eq.trans ?_ hR.symm
  rw [plusSwapDerived_val, plusSwapMatrix_inv, Units.val_mul, Units.val_mul, coe_plusSwapMatrix,
    permMatrix_conj_apply_eq, hAe]
  change _ = ((swapLin (K := F) (plusIndexEquiv m (.inl ⟨m - 1, by omega⟩))
        (plusIndexEquiv m (.inr ⟨m - 1, by omega⟩)) *
        (z : (Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F)) *
        swapLin (plusIndexEquiv m (.inl ⟨m - 1, by omega⟩))
          (plusIndexEquiv m (.inr ⟨m - 1, by omega⟩)) : (Fin (2 * m) → F) ≃ₗ[F] (Fin (2 * m) → F))
    (Pi.single (plusIndexEquiv m j) 1) (plusIndexEquiv m i))
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, swapLin_single, swapLin_apply,
    (plusIndexEquiv m).injective.swap_apply, (plusIndexEquiv m).injective.swap_apply]
  simp only [plusSwapPerm, Equiv.symm_swap]

end Model

end CFSG.SeitzReduction.OmegaPilot
