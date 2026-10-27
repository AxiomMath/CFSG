module

public import CFSG.LargeExtraspecial.S12InspP5Hyp
public import CFSG.LargeExtraspecial.S12InspXR3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Matrix CFSG.Open CFSG.Fischer.Classification
  CFSG.Fischer.Classification.Recognition.R3

namespace S12InspP5

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem nine_dvd_normCount {n : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3)}
    (hf : IsF3Form f) (hn : n = 5 ∨ n = 6) : 9 ∣ normCount f 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have key : ∀ k < 6, (k = 4 ∨ k = 5) → 9 ∣ (T^[k] (1, 2, 0)).2.1 ∧
      9 ∣ (T^[k] (1, 0, 2)).2.1 := by
    decide
  obtain ⟨h₁, h₂⟩ := key k (by omega) (by omega)
  rcases normCount_one_mem hf with h | h <;> rw [h]
  · exact h₁
  · exact h₂

theorem exists_restrict_dvd {n : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin (n + 1) → ZMod 3)}
    (hf : IsF3Form f) (hn : 3 ≤ n) :
    ∃ f' : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3), IsF3Form f' ∧
      normCount f 1 * Nat.card (F3.reflGroup f') ∣ Nat.card (F3.reflGroup f) := by
  obtain ⟨v, hv⟩ := F3.exists_norm_eq hf (by omega) (one_ne_zero (α := ZMod 3))
  let e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin n → ZMod 3) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [F3.finrank_perpOne hv, Module.finrank_fin_fun]; omega)
  exact ⟨restrictForm f e, isF3Form_restrictForm hf hv e,
    normCount_mul_card_dvd hf (by omega) hv e⟩

theorem three_pow_six_dvd_card_reflGroup_seven
    {f : LinearMap.BilinForm (ZMod 3) (Fin 7 → ZMod 3)} (hf : IsF3Form f) :
    3 ^ 6 ∣ Nat.card (F3.reflGroup f) := by
  obtain ⟨f₆, hf₆, h₇⟩ := exists_restrict_dvd (n := 6) hf (by norm_num)
  obtain ⟨f₅, hf₅, h₆⟩ := exists_restrict_dvd (n := 5) hf₆ (by norm_num)
  obtain ⟨f₄, -, h₅⟩ := exists_restrict_dvd (n := 4) hf₅ (by norm_num)
  have hN₇ : 3 ^ 3 ∣ normCount f 1 := (pow_dvd_normCount hf).1 (Or.inl rfl)
  have hN₆ : 9 ∣ normCount f₆ 1 := nine_dvd_normCount hf₆ (Or.inr rfl)
  have hN₅ : 9 ∣ normCount f₅ 1 := nine_dvd_normCount hf₅ (Or.inl rfl)
  have hR₅ : 9 ∣ Nat.card (F3.reflGroup f₅) := (hN₅.trans (dvd_mul_right _ _)).trans h₅
  have hR₆ : 9 * 9 ∣ Nat.card (F3.reflGroup f₆) := (mul_dvd_mul hN₆ hR₅).trans h₆
  have hR₇ : 3 ^ 3 * (9 * 9) ∣ Nat.card (F3.reflGroup f) := (mul_dvd_mul hN₇ hR₆).trans h₇
  exact (by norm_num : 3 ^ 6 ∣ 3 ^ 3 * (9 * 9)).trans hR₇

theorem det_reflMat {v : Fin m → ZMod 3} (hv : f v v = 1) : (F3.reflMat f v).det = -1 := by
  have hM : F3.reflMat f v = 1 + replicateCol (Fin 1) v *
      replicateRow (Fin 1) (fun j => f (Pi.single j 1) v) := by
    ext i j
    rw [F3.reflMat, LinearMap.toMatrix'_apply, F3.reflLin_apply]
    simp [Matrix.mul_apply, Matrix.one_apply, Pi.single_apply, mul_comm]
  have h1 := det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) v
    (fun j => f (Pi.single j 1) v)
  rw [hM]
  erw [h1]
  have e : (∑ j, v j • (Pi.single j 1 : Fin m → ZMod 3)) = v := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hsum : (fun j => f (Pi.single j 1) v) ⬝ᵥ v = f v v := by
    calc (fun j => f (Pi.single j 1) v) ⬝ᵥ v = ∑ j, v j * f (Pi.single j 1) v := by
          rw [dotProduct]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      _ = f (∑ j, v j • (Pi.single j 1 : Fin m → ZMod 3)) v := by
          rw [LinearMap.BilinForm.sum_left]
          simp
      _ = f v v := by rw [e]
  rw [hsum, hv]
  decide

theorem reflBar_not_mem_commutator_of_even (hf : IsF3Form f) (hm : 4 ≤ m) (heven : Even m)
    {v : Fin m → ZMod 3} (hv : f v v = 1) : reflBar f v ∉ commutator (R3 f) := by
  let d : F3.reflGroup f →* (ZMod 3)ˣ :=
    Matrix.GeneralLinearGroup.det.comp (F3.reflGroup f).subtype
  have hZ : center (F3.reflGroup f) ≤ d.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rcases F3.coe_eq_of_mem_center hf hm hz with h | h
    · simp [d, h]
    · simp [d, h, Matrix.det_neg, heven.neg_one_pow]
  let d' : R3 f →* (ZMod 3)ˣ := QuotientGroup.lift _ d hZ
  intro hc
  have hk := Abelianization.commutator_subset_ker d' hc
  rw [MonoidHom.mem_ker] at hk
  have h1 : d' (reflBar f v) = d (reflElt f v) := QuotientGroup.lift_mk _ _ _
  have h2 : ((d (reflElt f v) : (ZMod 3)ˣ) : ZMod 3) = -1 := by
    show ((F3.refl f v : GL (Fin m) (ZMod 3)) : Matrix (Fin m) (Fin m) (ZMod 3)).det = -1
    rw [F3.refl, dite_eq_left_of_eq_true (eq_true hv)]
    exact det_reflMat hv
  rw [← h1, hk, Units.val_one] at h2
  exact absurd h2 (by decide)

end S12InspP5

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem false_of_reflGroup_seven (hw : S.width = 4) {g : G}
    {f : LinearMap.BilinForm (ZMod 3) (Fin 7 → ZMod 3)} (hsymm : ∀ x y, f x y = f y x)
    (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (hmod : fischerCentralQuotientModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) : False := by
  have hf : IsF3Form f := ⟨hsymm, hnd⟩
  obtain ⟨ψ, -⟩ := (fischerCentralQuotientModel_iff _).1 hmod
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (F3.reflGroup f))
  have hZ := S12Insp4.card_center_reflGroup_le_two hf (by norm_num)
  have hZ0 : 0 < Nat.card (Subgroup.center (F3.reflGroup f)) := Nat.card_pos
  have h36 : 3 ^ 6 ∣ Nat.card (S.Xbar12 g) * Nat.card (Subgroup.center (F3.reflGroup f)) := by
    rw [Nat.card_congr ψ.toEquiv, ← h1]
    exact S12InspP5.three_pow_six_dvd_card_reflGroup_seven hf
  have hcop : Nat.Coprime (3 ^ 6) (Nat.card (Subgroup.center (F3.reflGroup f))) := by
    refine Nat.Coprime.pow_left _ ?_
    interval_cases Nat.card (Subgroup.center (F3.reflGroup f)) <;> decide
  exact S12Insp4.not_three_pow_six_dvd_card_O S hw
    ((hcop.dvd_of_dvd_mul_right h36).trans (Subgroup.card_subgroup_dvd_card _))


theorem false_of_reflGroup_of_not_mem_commutator {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (hS : S.S12Standing g t)
    (hdeg : ¬ S.IsNondeg12 g) {m : ℕ} (hm : 5 ≤ m)
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hsymm : ∀ x y, f x y = f y x)
    (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (hmod : fischerCentralQuotientModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
    (htG : (⟨t, subset_Xbar12 (mem_Ebar12_of_mem_Lbar ht htA)⟩ : S.Xbar12 g) ∉
      commutator (S.Xbar12 g)) : False := by
  obtain ⟨hH, hna⟩ := hyp_Xbar12 haQ hne hn ht htA hS hdeg
  have htE := mem_Ebar12_of_mem_Lbar ht htA
  exact false_of_triGood_Xbar12 haQ hne hn ht htA _
    (S12Tri.triGood_case5 hH hna htE htG ⟨m, hm, f, hsymm, hnd, hmod⟩)

theorem false_of_reflGroup_six {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (hS : S.S12Standing g t)
    (hdeg : ¬ S.IsNondeg12 g) {f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)}
    (hsymm : ∀ x y, f x y = f y x) (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (hmod : fischerCentralQuotientModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) : False := by
  refine false_of_reflGroup_of_not_mem_commutator haQ hne hn ht htA hS hdeg (by norm_num)
    hsymm hnd hmod fun hc => ?_
  have htE := mem_Ebar12_of_mem_Lbar ht htA
  obtain ⟨ψ, hψ⟩ := (fischerCentralQuotientModel_iff _).1 hmod
  obtain ⟨v, hv, hvd⟩ := mem_D3_iff.1 ((hψ ⟨t, subset_Xbar12 htE⟩).1 htE)
  have h := (S12Tri.apply_mem_commutator_iff ψ).mpr hc
  rw [← hvd] at h
  exact S12InspP5.reflBar_not_mem_commutator_of_even ⟨hsymm, hnd⟩ (by norm_num) (by decide) hv h

end Setting

end CFSG.LargeExtraspecial
