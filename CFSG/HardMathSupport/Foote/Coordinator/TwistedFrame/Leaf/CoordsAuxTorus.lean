module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ScalarTorus

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped commutatorElement

set_option linter.unusedSectionVars false


namespace CoordsAux

section Field

variable {τ : Tag} {F : Type} [Field F]

private theorem torus_comm_torus (c : Fˣ) {y : ModGL τ F} (hy : y ∈ torusGroup τ F) :
    rootTorusSL2 τ F (highRoot τ) c * y = y * rootTorusSL2 τ F (highRoot τ) c := by
  obtain ⟨-, hdH, -, -, -, hH, -, -⟩ :=
    exceptional_Lang_root_rank_one_torus_transport τ F (isRoot_highRoot τ)
  obtain ⟨a, ha, -⟩ := hH _ (hdH c)
  obtain ⟨b, hb, -⟩ := hH y hy
  rw [ha, hb, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

private theorem torus_comm_pinnedX {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (h0 : α (iθ τ) = 0)
    (c : Fˣ) (z : F) :
    rootTorusSL2 τ F (highRoot τ) c * pinnedX τ F α z =
      pinnedX τ F α z * rootTorusSL2 τ F (highRoot τ) c := by
  have h := ScalarTorusAux.torus_conj_pinnedX (isRoot_highRoot τ) hα c z
  rw [iform_highRoot_apply τ α, h0, mul_zero, mul_zero, Int.zero_ediv, zpow_zero, Units.val_one,
    one_mul] at h
  exact mul_inv_eq_iff_eq_mul.1 h

variable (τ F) in
private def goodSub (g : ModGL τ F) (c : F) : Subgroup (ModGL τ F) where
  carrier := {q | q ∈ Qθ τ F ∧ g * q * g⁻¹ ∈ Qθ τ F ∧
    heisCoord τ F (g * q * g⁻¹) = c • heisCoord τ F q}
  mul_mem' := by
    rintro q q' ⟨hq, hcq, hqe⟩ ⟨hq', hcq', hq'e⟩
    have e : g * (q * q') * g⁻¹ = (g * q * g⁻¹) * (g * q' * g⁻¹) := by group
    refine ⟨mul_mem hq hq', ?_, ?_⟩
    · rw [e]
      exact mul_mem hcq hcq'
    · rw [e, (heisCoord_spec τ F).mul _ hcq _ hcq', hqe, hq'e,
        (heisCoord_spec τ F).mul _ hq _ hq', smul_add]
  one_mem' := by
    refine ⟨one_mem _, ?_, ?_⟩
    · rw [mul_one, mul_inv_cancel]
      exact one_mem _
    · rw [mul_one, mul_inv_cancel, heisCoord_one, smul_zero]
  inv_mem' := by
    rintro q ⟨hq, hcq, hqe⟩
    have e : g * q⁻¹ * g⁻¹ = (g * q * g⁻¹)⁻¹ := by group
    refine ⟨inv_mem hq, ?_, ?_⟩
    · rw [e]
      exact inv_mem hcq
    · rw [e, heisCoord_inv hcq, hqe, heisCoord_inv hq, smul_neg]

private theorem Qθ_le_goodSub (c : Fˣ) :
    Qθ τ F ≤ goodSub τ F (rootTorusSL2 τ F (highRoot τ) c) (c : F) := by
  have hθ : IsRoot τ (highRoot τ) := isRoot_highRoot τ
  show rootSpan τ F (parabolicRadicalRoots τ (Jθ τ)) ≤ _
  refine iSup₂_le fun α hα => ?_
  intro g hg
  obtain ⟨z, rfl⟩ := mem_rootSubgroup.1 hg
  have hQ : ∀ w : F, pinnedX τ F α w ∈ Qθ τ F := fun w => pinnedX_mem_rootSpan hα w
  rcases (CoordAux.mem_radRoots_iff α).1 hα with h | h
  · have hconj := ScalarTorusAux.torus_conj_pinnedX hθ (CoordAux.mem_Deg1.1 h).1 c z
    rw [ScalarTorusAux.exponent_of_Deg1 h, zpow_one] at hconj
    refine ⟨hQ z, ?_, ?_⟩
    · rw [hconj]
      exact hQ _
    · rw [hconj, (heisCoord_spec τ F).pinnedX_deg1 α h, (heisCoord_spec τ F).pinnedX_deg1 α h]
      ext β
      by_cases hβ : β = α
      · subst hβ
        simp
      · simp [Pi.single_apply, hβ]
  · subst h
    have hconj := ScalarTorusAux.torus_conj_pinnedX hθ hθ c z
    refine ⟨hQ z, ?_, ?_⟩
    · rw [hconj]
      exact hQ _
    · rw [hconj, (heisCoord_spec τ F).pinnedX_highRoot, (heisCoord_spec τ F).pinnedX_highRoot,
        smul_zero]

theorem exists_scalarTorus_central {a : F} (ha : a ≠ 0) :
    ∃ h : ModGL τ F, (∀ y ∈ Lθ τ F, h * y = y * h) ∧ ∀ q ∈ Qθ τ F, h * q * h⁻¹ ∈ Qθ τ F ∧
      heisCoord τ F (h * q * h⁻¹) = a • heisCoord τ F q := by
  have hle : Lθ τ F ≤ Subgroup.centralizer
      ({rootTorusSL2 τ F (highRoot τ) (Units.mk0 a ha)} : Set (ModGL τ F)) := by
    unfold Lθ parabolicLevi
    refine sup_le (fun y hy => ?_) ((Subgroup.closure_le _).2 ?_)
    · rw [Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact torus_comm_torus _ hy
    · rintro _ ⟨j, hj, c, rfl | rfl⟩
      · have hj' : j ≠ iθ τ := hj
        have h0 : (Pi.single j 1 : Fin τ.rank → ℤ) (iθ τ) = 0 :=
          Pi.single_eq_of_ne (Ne.symm hj') 1
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        rintro _ rfl
        rw [← pinnedX_single τ F j c]
        exact torus_comm_pinnedX (isRoot_single τ j) h0 _ c
      · have hj' : j ≠ iθ τ := hj
        have h0 : (-Pi.single j 1 : Fin τ.rank → ℤ) (iθ τ) = 0 := by
          rw [Pi.neg_apply, Pi.single_eq_of_ne (Ne.symm hj') 1, neg_zero]
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        rintro _ rfl
        rw [← pinnedX_neg_single τ F j c]
        exact torus_comm_pinnedX (isRoot_neg_single τ j) h0 _ c
  refine ⟨rootTorusSL2 τ F (highRoot τ) (Units.mk0 a ha), fun y hy => ?_, fun q hq => ?_⟩
  · exact Subgroup.mem_centralizer_iff.1 (hle hy) _ rfl
  · exact (Qθ_le_goodSub (Units.mk0 a ha) hq).2

end Field

theorem mem_range_algebraMap_of_pow_card {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    {x : L} (hx : x ^ Nat.card K = x) : x ∈ Set.range (algebraMap K L) := by
  classical
  haveI := Fintype.ofFinite K
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hP0 : (Polynomial.X ^ Nat.card K - Polynomial.X : Polynomial L) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero L hq
  have hdeg : (Polynomial.X ^ Nat.card K - Polynomial.X : Polynomial L).natDegree =
      Nat.card K := FiniteField.X_pow_card_sub_X_natDegree_eq L hq
  have hroot : ∀ y : L, y ^ Nat.card K = y →
      y ∈ (Polynomial.X ^ Nat.card K - Polynomial.X : Polynomial L).roots.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hy, sub_self]
  have hSc : (Finset.univ.image (algebraMap K L)).card = Nat.card K := by
    rw [Finset.card_image_of_injective _ (algebraMap K L).injective, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
  have hSsub : Finset.univ.image (algebraMap K L) ⊆
      (Polynomial.X ^ Nat.card K - Polynomial.X : Polynomial L).roots.toFinset := by
    intro y hy
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hy
    refine hroot _ ?_
    rw [← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hle : (Polynomial.X ^ Nat.card K - Polynomial.X : Polynomial L).roots.toFinset.card ≤
      (Finset.univ.image (algebraMap K L)).card :=
    calc _ ≤ Multiset.card (Polynomial.X ^ Nat.card K - Polynomial.X : Polynomial L).roots :=
          Multiset.toFinset_card_le _
      _ ≤ (Polynomial.X ^ Nat.card K - Polynomial.X : Polynomial L).natDegree :=
          Polynomial.card_roots' _
      _ = _ := by rw [hdeg, hSc]
  have hxmem := hroot x hx
  rw [← Finset.eq_of_subset_of_card_le hSsub hle] at hxmem
  obtain ⟨t, -, ht⟩ := Finset.mem_image.1 hxmem
  exact ⟨t, ht⟩

end CoordsAux

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
