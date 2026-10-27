module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lExcDatum
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lExcIform
public import CFSG.RankThree.PartOne.S11c.G2Torus

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification
open CFSG.RankThree.Chevalley
  (rootSL2Equiv coe_rootSL2Equiv rootSL2_injective_of_field rootChar_neg')
open CFSG.RankThree.PartOne (rootSL2_HSL_eq_rootDiagUnit)
open CFSG.OddStandard.SmallF3.HypA2 (TypU)

section Perp

variable {τ : Tag}

theorem a2l_ne_of_perp {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (h : iform α β = 0) : α ≠ β ∧ α ≠ -β := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact (iform_self_pos hα.ne_zero).ne' h
  · rintro rfl
    rw [a2l_iform_neg_left] at h
    have := iform_self_pos hβ.ne_zero
    omega

theorem a2l_not_isRoot_nsmul_add {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hmax : ∀ γ, IsRoot τ γ → iform γ γ ≤ iform α α) (h : iform α β = 0) (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) : ¬IsRoot τ (a • α + b • β) := by
  intro hγ
  have h1 := hmax _ hγ
  have h' : iform β α = 0 := by rw [iform_comm]; exact h
  rw [← Nat.cast_smul_eq_nsmul ℤ a, ← Nat.cast_smul_eq_nsmul ℤ b] at h1
  simp only [iform_add_left, iform_add_right, iform_smul_left, iform_smul_right, h, h',
    mul_zero, add_zero, zero_add] at h1
  have hαα := iform_self_pos hα.ne_zero
  have hββ := iform_self_pos hβ.ne_zero
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have haa : (1 : ℤ) ≤ (a : ℤ) * a := by nlinarith
  have hbb : (1 : ℤ) ≤ (b : ℤ) * b := by nlinarith
  have h2 := mul_le_mul_of_nonneg_right haa hαα.le
  have h3 := mul_pos (lt_of_lt_of_le one_pos hbb) hββ
  nlinarith

theorem a2l_hmax_neg {θ : Fin τ.rank → ℤ} (hmax : ∀ γ, IsRoot τ γ → iform γ γ ≤ iform θ θ) :
    ∀ γ, IsRoot τ γ → iform γ γ ≤ iform (-θ) (-θ) := by
  intro γ hγ
  rw [a2l_iform_neg_left, a2l_iform_neg_right, neg_neg]
  exact hmax γ hγ

end Perp

section Sign

variable {τ : Tag} {K : Type}
  [Field K]

theorem a2l_prod_zpow {G ι : Type*} [CommGroup G] (ξ : G) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, ξ ^ f i = ξ ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

theorem a2l_rootChar_sign {θ δ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) (hδ : IsRoot τ δ) (c : Kˣ) :
    rootChar (fun i : Fin τ.rank => c ^ (2 * iform θ (Pi.single i 1) / iform θ θ)) δ =
      c ^ (2 * iform θ δ / iform θ θ) := by
  rw [a2l_hm hθ δ hδ, rootChar, ← a2l_prod_zpow]
  exact Finset.prod_congr rfl fun i _ => by rw [← zpow_mul, mul_comm]

theorem a2l_rootChar_self {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) :
    rootChar (fun i : Fin τ.rank => (-1 : Kˣ) ^ (2 * iform θ (Pi.single i 1) / iform θ θ)) θ =
      1 := by
  rw [a2l_rootChar_sign hθ hθ, Int.mul_ediv_cancel _ (iform_self_pos hθ.ne_zero).ne']
  exact (even_two : Even (2 : ℤ)).neg_one_zpow

theorem a2l_even_of_rootChar (hK2 : ringChar K ≠ 2) {θ δ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ)
    (hδ : IsRoot τ δ)
    (h : rootChar (fun i : Fin τ.rank => (-1 : Kˣ) ^ (2 * iform θ (Pi.single i 1) / iform θ θ))
      δ = 1) : Even (2 * iform θ δ / iform θ θ) := by
  rw [a2l_rootChar_sign hθ hδ] at h
  rcases Int.even_or_odd (2 * iform θ δ / iform θ θ) with he | ho
  · exact he
  · exfalso
    rw [ho.neg_one_zpow] at h
    have h1 : ((-1 : Kˣ) : K) = ((1 : Kˣ) : K) := congrArg Units.val h
    simp only [Units.val_neg, Units.val_one] at h1
    exact Ring.neg_one_ne_one_of_char_ne_two hK2 h1

end Sign

section SL2

variable {K : Type} [Field K]

theorem a2l_coe_HSL_neg_one : ((HSL (-1 : Kˣ) : SL2 K) : Matrix (Fin 2) (Fin 2) K) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_HSL]

theorem a2l_HSL_neg_one_comm (A : SL2 K) : A * HSL (-1) = HSL (-1) * A := by
  ext i j
  simp [Matrix.SpecialLinearGroup.coe_mul, a2l_coe_HSL_neg_one]

theorem a2l_HSL_neg_one_mul_self : HSL (-1 : Kˣ) * HSL (-1) = (1 : SL2 K) := by
  ext i j
  simp [Matrix.SpecialLinearGroup.coe_mul, a2l_coe_HSL_neg_one]

theorem a2l_HSL_neg_one_ne_one (hK2 : ringChar K ≠ 2) : HSL (-1 : Kˣ) ≠ (1 : SL2 K) := by
  intro h
  have h00 : ((HSL (-1 : Kˣ) : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0 = -1 := by
    simp [a2l_coe_HSL_neg_one]
  rw [h] at h00
  exact Ring.neg_one_ne_one_of_char_ne_two hK2 (by simpa using h00.symm)

end SL2

section Main

variable
  {τ : Tag}

theorem a2l_rootSubgroup_le_centralizer {K : Type} [Field K] {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (hmax : ∀ γ, IsRoot τ γ → iform γ γ ≤ iform α α)
    (h : iform α β = 0) :
    rootSubgroup τ K α ≤ centralizer (rootSubgroup τ K β : Set (ModGL τ K)) := by
  obtain ⟨hne, hne'⟩ := a2l_ne_of_perp hα hβ h
  intro x hx y hy
  exact (commute_of_forall_not_isRoot hα hβ hne hne' (a2l_not_isRoot_nsmul_add hα hβ hmax h) K
    x hx y hy).symm.eq

theorem a2l_rootSpan_le_normalizer {K : Type} [Field K] (hK2 : ringChar K ≠ 2)
    {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) (hmax : ∀ γ, IsRoot τ γ → iform γ γ ≤ iform θ θ) :
    rootSpan τ K (rootCharKernel
      (fun i : Fin τ.rank => (-1 : Kˣ) ^ (2 * iform θ (Pi.single i 1) / iform θ θ))) ≤
      normalizer ((rootSubgroup τ K θ ⊔ rootSubgroup τ K (-θ) : Subgroup (ModGL τ K)) :
        Set (ModGL τ K)) := by
  refine iSup₂_le fun δ hδ => ?_
  obtain ⟨hδr, hδχ⟩ := hδ
  have hev := a2l_even_of_rootChar hK2 hθ hδr hδχ
  rcases a2l_hperp hθ hδr (hmax δ hδr) hev with h | h | h
  · rw [h]
    exact le_sup_left.trans le_normalizer
  · rw [h]
    exact le_sup_right.trans le_normalizer
  · refine le_trans ?_ (centralizer_le_normalizer _)
    rw [le_centralizer_iff]
    refine sup_le ?_ ?_
    · exact a2l_rootSubgroup_le_centralizer hθ hδr hmax h
    · exact a2l_rootSubgroup_le_centralizer (CFSG.LieType.Chevalley.IsRoot.neg hθ) hδr
        (a2l_hmax_neg hmax) (by rw [a2l_iform_neg_left, h, neg_zero])

theorem a2l_datum_adjoint_of_root {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2)
    (h9 : 9 ≤ Nat.card K) {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ)
    (hmax : ∀ γ, IsRoot τ γ → iform γ γ ≤ iform θ θ) : a2lDatum ↥(adjointGroup τ K) := by
  haveI : Finite (ModGL τ K) := finite_modGL
  haveI : Fintype K := Fintype.ofFinite K
  let m : Fin τ.rank → ℤ := fun i => 2 * iform θ (Pi.single i 1) / iform θ θ
  let a : Fin τ.rank → Kˣ := fun i => (-1 : Kˣ) ^ m i
  have ha : ∀ i, a i = 1 ∨ a i = -1 := fun i => by
    rcases Int.even_or_odd (m i) with h | h
    · exact Or.inl h.neg_one_zpow
    · exact Or.inr h.neg_one_zpow
  have hHSL : rootSL2 τ K θ (HSL (-1)) = rootDiagUnit τ a :=
    rootSL2_HSL_eq_rootDiagUnit hθ m (a2l_hm hθ) (-1)
  let Q : Subgroup (ModGL τ K) := rootSubgroup τ K θ ⊔ rootSubgroup τ K (-θ)
  let e : SL2 K ≃* Q := rootSL2Equiv hθ
  have he : ∀ A, (e A : ModGL τ K) = rootSL2 τ K θ A := fun A => coe_rootSL2Equiv hθ A
  have hQH : Q ≤ adjointGroup τ K := (odd_arbitrary_root_pair_SL2_p_components τ K hK2 hθ).1
  have hz2 : rootDiagUnit τ a * rootDiagUnit τ a = 1 := by
    rw [← hHSL, ← map_mul, a2l_HSL_neg_one_mul_self, map_one]
  have hz1 : rootDiagUnit τ a ≠ 1 := by
    rw [← hHSL]
    intro h
    exact a2l_HSL_neg_one_ne_one hK2 (rootSL2_injective_of_field θ (h.trans (map_one _).symm))
  have hzQ : rootDiagUnit τ a ∈ Q := by
    rw [← hHSL, ← he]
    exact (e _).2
  have hQc : Q ≤ centralizer ({rootDiagUnit τ a} : Set (ModGL τ K)) := by
    intro x hx
    obtain ⟨A, hA⟩ := e.surjective ⟨x, hx⟩
    have hx' : x = rootSL2 τ K θ A := by rw [← he, hA]
    rw [mem_centralizer_singleton_iff, hx', ← hHSL, ← map_mul, ← map_mul,
      a2l_HSL_neg_one_comm]
  obtain ⟨hSX, hSN, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction τ K hK2 a ha
  have hθK : θ ∈ rootCharKernel a := ⟨hθ, a2l_rootChar_self hθ⟩
  have hnθK : -θ ∈ rootCharKernel a :=
    ⟨CFSG.LieType.Chevalley.IsRoot.neg hθ, by rw [rootChar_neg', a2l_rootChar_self hθ, inv_one]⟩
  have hQS : Q ≤ rootSpan τ K (rootCharKernel a) :=
    sup_le (le_iSup₂_of_le θ hθK le_rfl) (le_iSup₂_of_le (-θ) hnθK le_rfl)
  have hQsub : CFSG.Assembly.IsSubnormal Q (toralCentralizer τ K a) :=
    .step hQS ((normal_subgroupOf_iff_le_normalizer hQS).2
      (a2l_rootSpan_le_normalizer hK2 hθ hmax)) (.step hSX hSN (.refl _))
  have hq : CFSG.IsQuasisimple ↥Q := by
    obtain ⟨-, -, -, hfinK⟩ := odd_arbitrary_root_pair_SL2_p_components τ K hK2 hθ
    obtain ⟨-, h5⟩ := @hfinK inferInstance
    exact (h5 (by omega)).1
  have hodd : Odd (Nat.card K) := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.odd_iff.2 (FiniteField.odd_card_of_char_ne_two hK2)
  have hN : HarrisLit.IsSLTwoOver (Nat.card K) ↥Q :=
    ⟨K, inferInstance, inferInstance, Nat.card_eq_fintype_card.symm, ⟨e.symm⟩⟩
  exact a2lDatum_of_subgroup_component (adjointGroup τ K) (hQH hzQ) hz2 hz1 hodd (by omega)
    ⟨le_inf hQH hQc, hQsub, (AssemblyBPredicates.isQuasisimple_iff_native _).2 hq⟩ hzQ hN
    (a2l_typU_of_isSLTwoOver hodd h9 hN)

theorem a2l_datum_adjoint {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2)
    (h9 : 9 ≤ Nat.card K) : a2lDatum ↥(adjointGroup τ K) := by
  have : Nonempty (Fin τ.rank) := ⟨⟨0, by cases τ <;> decide⟩⟩
  obtain ⟨j₀, hj₀⟩ := Finite.exists_max fun j : Fin τ.rank => τ.symmetrizer j j
  exact a2l_datum_adjoint_of_root hK2 h9 (IsRoot.basis j₀) (a2l_hmax_single hj₀)

end Main

end CFSG.OddStandard.SmallF3.HypA2Leaves
