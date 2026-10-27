module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.Cocode

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.FrameJ

open CFSG.EvenSporadicStandard.Wong77.Module

variable {G : Type*} [Group G]

theorem two_zsmul_ofMul (g : G) (hg : g * g = 1) : ((2 : ℕ) : ℤ) • Additive.ofMul g = 0 := by
  rw [natCast_zsmul, two_nsmul]
  exact congrArg Additive.ofMul hg

@[expose] noncomputable def involHom (g : G) (hg : g * g = 1) : ZMod 2 →+ Additive G :=
  ZMod.lift 2 ⟨zmultiplesHom (Additive G) (Additive.ofMul g), by
    rw [zmultiplesHom_apply]
    exact two_zsmul_ofMul g hg⟩

theorem involHom_one (g : G) (hg : g * g = 1) : involHom g hg 1 = Additive.ofMul g := by
  have h := ZMod.lift_coe 2 ⟨zmultiplesHom (Additive G) (Additive.ofMul g), by
    rw [zmultiplesHom_apply]
    exact two_zsmul_ofMul g hg⟩ 1
  rw [Int.cast_one] at h
  refine h.trans ?_
  show zmultiplesHom (Additive G) (Additive.ofMul g) 1 = _
  rw [zmultiplesHom_apply, one_zsmul]

theorem involHom_eq (g : G) (hg : g * g = 1) (x : ZMod 2) :
    involHom g hg x = 0 ∨ involHom g hg x = Additive.ofMul g := by
  have : x = 0 ∨ x = 1 := by
    revert x
    decide
  rcases this with rfl | rfl
  · exact Or.inl (map_zero _)
  · exact Or.inr (involHom_one g hg)

variable (p : Fin 23 → G) (hsq : ∀ i, p i * p i = 1) (hcomm : ∀ i j, p i * p j = p j * p i)

@[expose] noncomputable def frameAdd : Word →+ Additive G :=
  AddMonoidHom.noncommPiCoprod (fun i => involHom (p i) (hsq i)) (by
    intro i j _ x y
    rcases involHom_eq (p i) (hsq i) x with hx | hx
    · rw [hx]
      exact AddCommute.zero_left _
    rcases involHom_eq (p j) (hsq j) y with hy | hy
    · rw [hy]
      exact AddCommute.zero_right _
    rw [hx, hy]
    exact congrArg Additive.ofMul (hcomm i j))

@[expose] noncomputable def frameHom : Multiplicative Word →* G where
  toFun w := Additive.toMul (frameAdd p hsq hcomm (Multiplicative.toAdd w))
  map_one' := by simp
  map_mul' a b := by simp

theorem frameHom_ofAdd (w : Word) :
    frameHom p hsq hcomm (Multiplicative.ofAdd w) = Additive.toMul (frameAdd p hsq hcomm w) := rfl

theorem frameHom_eVec (i : Fin 23) : frameHom p hsq hcomm (eVec i) = p i := by
  rw [eVec, frameHom_ofAdd, frameAdd, AddMonoidHom.noncommPiCoprod_single, involHom_one]
  rfl

theorem frameHom_list_sum (L : List (Fin 23)) :
    frameHom p hsq hcomm
        (Multiplicative.ofAdd (L.map fun i => (Pi.single i (1 : ZMod 2) : Word)).sum) =
      (L.map p).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ofAdd_add, map_mul, ih, List.map_cons, List.prod_cons]
    exact congrArg (· * _) (frameHom_eVec p hsq hcomm a)

@[expose] def rowList (m : ℕ) : List (Fin 23) := (List.finRange 23).filter fun i => m.testBit i.val

theorem wordOfNat_eq_list_sum (m : ℕ) :
    wordOfNat m = ((rowList m).map fun i => (Pi.single i (1 : ZMod 2) : Word)).sum := by
  have hnd : (rowList m).Nodup := (List.nodup_finRange 23).filter _
  rw [← List.sum_toFinset (fun i => (Pi.single i (1 : ZMod 2) : Word)) hnd, ← ind_eq_sum]
  funext i
  simp [wordOfNat, ind, rowList]

theorem frameHom_golayCode
    (hrel : ∀ r : Fin 12, ((rowList (golayMask r)).map p).prod = 1) {w : Word}
    (hw : w ∈ golayCode) : frameHom p hsq hcomm (Multiplicative.ofAdd w) = 1 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨r, rfl⟩
    rw [golayRow, wordOfNat_eq_list_sum, frameHom_list_sum]
    exact hrel r
  · simp
  · intro x y _ _ hx hy
    rw [ofAdd_add, map_mul, hx, hy, mul_one]
  · intro a x _ hx
    have : a = 0 ∨ a = 1 := by
      revert a
      decide
    rcases this with rfl | rfl
    · simp
    · simpa using hx

theorem frameHom_ofAdd_eq_one_iff
    (hrel : ∀ r : Fin 12, ((rowList (golayMask r)).map p).prod = 1)
    (h1 : ∀ i, p i ≠ 1) (h2 : ∀ i j, i ≠ j → p i * p j ≠ 1)
    (h3 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → p i * p j * p k ≠ 1) (w : Word) :
    frameHom p hsq hcomm (Multiplicative.ofAdd w) = 1 ↔ w ∈ golayCode := by
  refine ⟨fun hw => ?_, frameHom_golayCode p hsq hcomm hrel⟩
  obtain ⟨s, hs, hsw⟩ := exists_card_le_three (coMk w)
  have hmem : ind s - w ∈ golayCode := coMk_eq_coMk.1 hsw
  have hker := frameHom_golayCode p hsq hcomm hrel hmem
  have hs1 : frameHom p hsq hcomm (Multiplicative.ofAdd (ind s)) = 1 := by
    have : ind s = (ind s - w) + w := by abel
    rw [this, ofAdd_add, map_mul, hker, hw, mul_one]
  have hs0 : s = ∅ := by
    have hc : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 ∨ s.card = 3 := by omega
    rcases hc with h | h | h | h
    · exact Finset.card_eq_zero.1 h
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h
      rw [ind_singleton] at hs1
      exact absurd ((frameHom_eVec p hsq hcomm a).symm.trans hs1) (h1 a)
    · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 h
      rw [ind_eq_sum, Finset.sum_pair hxy, ofAdd_add, map_mul] at hs1
      exact absurd (by
        rw [← frameHom_eVec p hsq hcomm x, ← frameHom_eVec p hsq hcomm y]
        exact hs1) (h2 x y hxy)
    · obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 h
      rw [ind_eq_sum, Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_pair hyz, ofAdd_add,
        ofAdd_add, map_mul, map_mul, ← mul_assoc] at hs1
      exact absurd (by
        rw [← frameHom_eVec p hsq hcomm x, ← frameHom_eVec p hsq hcomm y,
          ← frameHom_eVec p hsq hcomm z]
        exact hs1) (h3 x y z hxy hxz hyz)
  rw [hs0, ind_empty, word_sub_eq_add, zero_add] at hmem
  exact hmem

end CFSG.EvenSporadicStandard.TwoFi22.FrameJ
