module

public import CFSG.LieType.Universal.Spin.Twisted.Map
public import CFSG.ClassicalInvolution.Q3.Q3TWInputs
public import CFSG.ClassicalInvolution.Q3.Q3TWLMap

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank

section Shift

variable {m n : ℕ} (hmn : m + 2 = n)

@[expose] def shiftIdxM (i : Fin (m - 1)) : Fin (n - 1) :=
  ⟨i.val + 2, by have := i.isLt; omega⟩

theorem shiftIdxM_injective : Function.Injective (shiftIdxM hmn) := fun i j h =>
  Fin.ext (by have := congrArg Fin.val h; simpa [shiftIdxM] using this)

@[expose] def minusCoord :
    (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) → (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) :=
  Sum.map (shiftIdxM hmn) (Sum.map (shiftIdxM hmn) id)

theorem minusCoord_injective : Function.Injective (minusCoord hmn) :=
  Sum.map_injective.2 ⟨shiftIdxM_injective hmn, Sum.map_injective.2
    ⟨shiftIdxM_injective hmn, Function.injective_id⟩⟩

variable (K : Type*) [Field K]

@[expose] noncomputable def minusShift :
    (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) →ₗ[K] (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :=
  Function.ExtendByZero.linearMap K (minusCoord hmn)

theorem minusShift_coord (v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)
    (a : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) : minusShift hmn K v (minusCoord hmn a) = v a := by
  simp only [minusShift, Function.ExtendByZero.linearMap, LinearMap.coe_mk]
  exact (minusCoord_injective hmn).extend_apply v 0 a

theorem minusShift_off (v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)
    (b : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (hb : b ∉ Set.range (minusCoord hmn)) :
    minusShift hmn K v b = 0 := by
  simp only [minusShift, Function.ExtendByZero.linearMap, LinearMap.coe_mk]
  exact Function.extend_apply' _ _ _ (fun ⟨a, ha⟩ => hb ⟨a, ha⟩)

theorem minusShift_single (a : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) :
    minusShift hmn K (Pi.single a 1) = Pi.single (minusCoord hmn a) 1 := by
  funext b
  by_cases hb : b ∈ Set.range (minusCoord hmn)
  · obtain ⟨a', rfl⟩ := hb
    rw [minusShift_coord, Pi.single_apply, Pi.single_apply]
    simp only [(minusCoord_injective hmn).eq_iff]
  · rw [minusShift_off hmn K _ _ hb, Pi.single_apply]
    symm
    rw [ite_eq_right_iff]
    rintro rfl
    exact absurd ⟨a, rfl⟩ hb

theorem quadMinus_minusShift (b c : K) (v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) :
    quadMinus n K b c (minusShift hmn K v) = quadMinus m K b c v := by
  rw [quadMinus_apply, quadMinus_apply]
  have h0 : minusShift hmn K v (.inr (.inr 0)) = v (.inr (.inr 0)) :=
    minusShift_coord hmn K v (.inr (.inr 0))
  have h1 : minusShift hmn K v (.inr (.inr 1)) = v (.inr (.inr 1)) :=
    minusShift_coord hmn K v (.inr (.inr 1))
  rw [h0, h1]
  congr 3
  refine (Fintype.sum_of_injective (shiftIdxM hmn) (shiftIdxM_injective hmn) _ _ ?_ ?_).symm
  · intro j hj
    have : minusShift hmn K v (.inl j) = 0 := minusShift_off hmn K v _ (fun ⟨a, ha⟩ => by
      rcases a with a | a | a
      · exact hj ⟨a, by simpa [minusCoord] using ha⟩
      · simp [minusCoord] at ha
      · simp [minusCoord] at ha)
    rw [this, zero_mul]
  · intro i
    rw [show (Sum.inl (shiftIdxM hmn i) : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) =
        minusCoord hmn (.inl i) from rfl, show (Sum.inr (Sum.inl (shiftIdxM hmn i)) :
        Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) = minusCoord hmn (.inr (.inl i)) from rfl,
      minusShift_coord, minusShift_coord]

end Shift

section Iso

variable {m n : ℕ} (hmn : m + 2 = n) {K : Type*} [Field K]

theorem minusShift_eq_zero (v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)
    (b : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (h : ∀ a, minusCoord hmn a = b → v a = 0) :
    minusShift hmn K v b = 0 := by
  by_cases hb : b ∈ Set.range (minusCoord hmn)
  · obtain ⟨a, rfl⟩ := hb
    rw [minusShift_coord]
    exact h a rfl
  · exact minusShift_off hmn K v b hb

variable (b c : K)

@[expose] noncomputable def minusIso : (quadMinus m K b c).Isometry (quadMinus n K b c) where
  toLinearMap := minusShift hmn K
  map_app' v := quadMinus_minusShift hmn K b c v

theorem minusIso_vec (i : Fin (m - 1)) (s : Bool) :
    minusIso hmn b c (minusVec m i s) = minusVec n (shiftIdxM hmn i) s := by
  cases s
  · exact minusShift_single hmn K (.inr (.inl i))
  · exact minusShift_single hmn K (.inl i)

theorem minusIso_planeVec (w : Fin 2 → K) : minusIso hmn b c (planeVec m w) = planeVec n w := by
  funext x
  rcases x with i | i | t
  · refine minusShift_eq_zero hmn _ _ fun a ha => ?_
    rcases a with a | a | t
    · simp [planeVec]
    · simp [planeVec]
    · simp [minusCoord] at ha
  · refine minusShift_eq_zero hmn _ _ fun a ha => ?_
    rcases a with a | a | t
    · simp [planeVec]
    · simp [planeVec]
    · simp [minusCoord] at ha
  · exact minusShift_coord hmn K (planeVec m w) (.inr (.inr t))

theorem minusIso_injective : Function.Injective (minusIso hmn b c) := by
  intro v w h
  funext a
  have := congrFun h (minusCoord hmn a)
  exact (minusShift_coord hmn K v a).symm.trans (this.trans (minusShift_coord hmn K w a))

end Iso

section Nodes

variable {m n : ℕ} (hmn : m + 2 = n) {K : Type} [Field K] {b c : K}
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

theorem minusIso_comp_shortPosHom (k : Fin (m - 1)) :
    (minusIso hmn b c).spinGroupMap.comp (shortPosHom m hirr k) =
      shortPosHom n hirr (shiftIdxM hmn k) := by
  simpa only [twShortRoot_true] using
    (spinGroupMap_comp_twShortRoot (minusIso hmn b c) hirr true
      (minusIso_vec hmn b c k true) (minusIso_planeVec hmn b c))

theorem minusIso_comp_shortNegHom (k : Fin (m - 1)) :
    (minusIso hmn b c).spinGroupMap.comp (shortNegHom m hirr k) =
      shortNegHom n hirr (shiftIdxM hmn k) := by
  simpa only [twShortRoot_false] using
    (spinGroupMap_comp_twShortRoot (minusIso hmn b c) hirr false
      (minusIso_vec hmn b c k false) (minusIso_planeVec hmn b c))

theorem shiftIdxM_succ {k : Fin (m - 1)} (h : k.val + 1 < m - 1)
    (h' : (shiftIdxM hmn k).val + 1 < n - 1) :
    shiftIdxM hmn ⟨k.val + 1, h⟩ = ⟨(shiftIdxM hmn k).val + 1, h'⟩ :=
  Fin.ext (by show k.val + 1 + 2 = k.val + 2 + 1; omega)

theorem minusIso_map_rankOne (k : Fin (m - 1)) :
    (rankOne (minusDatum m hirr).rootGroup k).map (minusIso hmn b c).spinGroupMap =
      rankOne (minusDatum n hirr).rootGroup (shiftIdxM hmn k) := by
  change ((minusRootGroup m hirr (Pi.single k 1)) ⊔
      (minusRootGroup m hirr (-Pi.single k 1))).map _ =
    minusRootGroup n hirr (Pi.single (shiftIdxM hmn k) 1) ⊔
      minusRootGroup n hirr (-Pi.single (shiftIdxM hmn k) 1)
  rw [Subgroup.map_sup]
  by_cases h : k.val + 1 < m - 1
  · have h' : (shiftIdxM hmn k).val + 1 < n - 1 := by simp only [shiftIdxM]; omega
    have e1 := spinGroupMap_comp_longRoot (minusIso hmn b c) (minusFrame m b c).toHypFrame
      (minusFrame n b c).toHypFrame (succ_ne_of_lt m h) (succ_ne_of_lt n h') true false
      (minusIso_vec hmn b c k true)
      (by rw [← shiftIdxM_succ hmn h h']; exact minusIso_vec hmn b c ⟨k.val + 1, h⟩ false)
    have e2 := spinGroupMap_comp_longRoot (minusIso hmn b c) (minusFrame m b c).toHypFrame
      (minusFrame n b c).toHypFrame (succ_ne_of_lt m h).symm (succ_ne_of_lt n h').symm true false
      (by rw [← shiftIdxM_succ hmn h h']; exact minusIso_vec hmn b c ⟨k.val + 1, h⟩ true)
      (minusIso_vec hmn b c k false)
    rw [minusRootGroup_single_of_lt m hirr h, minusRootGroup_neg_single_of_lt m hirr h,
      minusRootGroup_single_of_lt n hirr h', minusRootGroup_neg_single_of_lt n hirr h',
      map_range_eq_of_comp_eq _ _ _ e1, map_range_eq_of_comp_eq _ _ _ e2]
  · have h' : ¬ (shiftIdxM hmn k).val + 1 < n - 1 := by simp only [shiftIdxM]; omega
    rw [minusRootGroup_single_of_not_lt m hirr h, minusRootGroup_neg_single_of_not_lt m hirr h,
      minusRootGroup_single_of_not_lt n hirr h', minusRootGroup_neg_single_of_not_lt n hirr h',
      map_range_eq_of_comp_eq _ _ _ (minusIso_comp_shortPosHom hmn hirr k),
      map_range_eq_of_comp_eq _ _ _ (minusIso_comp_shortNegHom hmn hirr k)]

end Nodes

section Main

variable {m n : ℕ} (hmn : m + 2 = n)

theorem leviEmbedMinus {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p f : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus m p f) (hF : Nat.card K = p ^ f) :
    ∃ Θ : spinGroup (quadMinus m K b c) →* spinGroup (quadMinus n K b c),
      Θ.ker ≤ Subgroup.center _ ∧
      (∀ k : Fin (m - 1), (rankOne (minusDatum m hirr).rootGroup k).map Θ =
        rankOne (minusDatum n hirr).rootGroup (shiftIdxM hmn k)) ∧
      Θ.range = ⨆ k : Fin (m - 1), rankOne (minusDatum n hirr).rootGroup (shiftIdxM hmn k) := by
  refine ⟨(minusIso hmn b c).spinGroupMap,
    ker_spinGroupMap_le_center _ (minusIso_injective hmn b c), minusIso_map_rankOne hmn hirr, ?_⟩
  refine range_eq_iSup_of_map_eq _ (fun k => rankOne (minusDatum m hirr).rootGroup k) _ ?_
    (minusIso_map_rankOne hmn hirr)
  have hgen := (curtisTitsConclusion_spinMinus.{0} hirr hadm hF).1.1
  rw [eq_top_iff, ← hgen]
  refine iSup_le fun J => ?_
  exact iSup₂_le fun j _ => le_iSup (fun k => rankOne (minusDatum m hirr).rootGroup k) j

theorem leviEmbed3Minus_proved : LeviEmbed3Minus := by
  intro n hn
  have hadm : StatedLieAdmissible .POmegaMinus (n - 2) 3 1 :=
    ⟨Nat.prime_three, le_rfl, by show 4 ≤ n - 2; omega⟩
  exact leviEmbedMinus (m := n - 2) (n := n) (by omega) (minusCoeffs_irr 3 1) hadm
    (GaloisField.card 3 1 one_ne_zero)

end Main

end CFSG.ClassicalInvolution.Q3.Q3TW
