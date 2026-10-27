module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FoursInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Props
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import Certificates.Data.A5

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.EvenSporadicStandard.HSStd

theorem e16_a5_card_invol :
    Nat.card {x : alternatingGroup (Fin 5) // x ≠ 1 ∧ x * x = 1} = 15 := by
  rw [Nat.card_eq_fintype_card]
  set_option maxRecDepth 100000 in decide +kernel

theorem e16_a5_invol_conj (x y : alternatingGroup (Fin 5)) (hx1 : x ≠ 1) (hx2 : x * x = 1)
    (hy1 : y ≠ 1) (hy2 : y * y = 1) : ∃ c : alternatingGroup (Fin 5), c * x * c⁻¹ = y := by
  have key : ∀ z : alternatingGroup (Fin 5), z ≠ 1 → z * z = 1 →
      ∃ c : alternatingGroup (Fin 5), c * (⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
        rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ : alternatingGroup (Fin 5)) * c⁻¹ = z := by
    set_option maxRecDepth 100000 in decide +kernel
  obtain ⟨a, ha⟩ := key x hx1 hx2
  obtain ⟨b, hb⟩ := key y hy1 hy2
  refine ⟨b * a⁻¹, ?_⟩
  rw [← hb, ← ha]
  group

theorem e16_ncard_conjugatesOf_modEq {K : Type} [Group K] [Finite K] {τ : MulAut K}
    (hτ : τ * τ = 1) {κ : K} (hκ : τ κ = κ) :
    (conjugatesOf κ).ncard ≡ Nat.card {x : K // IsConj κ x ∧ τ x = x} [MOD 2] := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hττ : ∀ x : K, τ (τ x) = x := fun x => by
    have := congrArg (fun ψ : MulAut K => ψ x) hτ
    simpa using this
  have hmem : ∀ x : K, IsConj κ x → IsConj κ (τ x) := by
    intro x hx
    obtain ⟨c, hc⟩ := isConj_iff.1 hx
    refine isConj_iff.2 ⟨τ c, ?_⟩
    rw [← hc]
    simp [hκ]
  let g : Function.End (conjugatesOf κ) := fun x => ⟨τ x, hmem x x.2⟩
  have hg : g ^ 2 ^ 1 = 1 := by
    funext x
    simp only [pow_one, pow_two]
    exact Subtype.ext (hττ x)
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := g) (p := 2) (n := 1) hg
  have hfix : Nat.card (Function.fixedPoints g) = Nat.card {x : K // IsConj κ x ∧ τ x = x} := by
    refine Nat.card_congr ⟨fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩,
      fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩, fun x => rfl, fun x => rfl⟩
  rw [← Nat.card_coe_set_eq, ← hfix]
  simpa only [Nat.card_eq_fintype_card] using hmod

theorem e16_odd_index {K : Type} [Group K] [Finite K] {τ : MulAut K} (hτ : τ * τ = 1)
    (e : ↥(autCentralizer τ) ≃* alternatingGroup (Fin 5)) {κ : K}
    (hκ : κ ∈ autCentralizer τ) (hκ2 : orderOf κ = 2) :
    Odd (Subgroup.centralizer ({κ} : Set K)).index := by
  have hκτ : τ κ = κ := hκ
  have hκ1 : κ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hκ2
    exact absurd hκ2 (by norm_num)
  have hκsq : κ * κ = 1 := by
    rw [← sq, ← hκ2, pow_orderOf_eq_one]
  rw [Subgroup.index_centralizer_eq_ncard]
  have hmod := e16_ncard_conjugatesOf_modEq hτ hκτ
  have hne : ∀ x : K, IsConj κ x → x ≠ 1 := by
    intro x hx hx1
    obtain ⟨c, hc⟩ := isConj_iff.1 hx
    apply hκ1
    rw [hx1] at hc
    calc κ = c⁻¹ * (c * κ * c⁻¹) * c := by group
      _ = 1 := by rw [hc]; group
  have hsq : ∀ x : K, IsConj κ x → x * x = 1 := by
    intro x hx
    obtain ⟨c, hc⟩ := isConj_iff.1 hx
    rw [← hc]
    calc c * κ * c⁻¹ * (c * κ * c⁻¹) = c * (κ * κ) * c⁻¹ := by group
      _ = 1 := by rw [hκsq]; group
  have hconj : ∀ y : ↥(autCentralizer τ), y ≠ 1 → y * y = 1 → IsConj κ (y : K) := by
    intro y hy1 hy2
    set κ' : ↥(autCentralizer τ) := ⟨κ, hκ⟩ with hκ'
    obtain ⟨c, hc⟩ := e16_a5_invol_conj (e κ') (e y)
      (by
        intro h
        apply hκ1
        have := e.injective (h.trans (map_one e).symm)
        exact congrArg Subtype.val this)
      (by rw [← map_mul, show κ' * κ' = 1 from Subtype.ext hκsq, map_one])
      (by
        intro h
        exact hy1 (e.injective (h.trans (map_one e).symm)))
      (by rw [← map_mul, hy2, map_one])
    refine isConj_iff.2 ⟨(e.symm c : K), ?_⟩
    have h2 : e.symm c * κ' * (e.symm c)⁻¹ = y := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc]
    exact congrArg Subtype.val h2
  let e1 : {x : K // IsConj κ x ∧ τ x = x} ≃
      {y : ↥(autCentralizer τ) // y ≠ 1 ∧ y * y = 1} :=
    { toFun := fun x => ⟨⟨x.1, x.2.2⟩, fun h => hne x.1 x.2.1 (congrArg Subtype.val h),
        Subtype.ext (hsq x.1 x.2.1)⟩
      invFun := fun y => ⟨y.1.1, hconj y.1 y.2.1 y.2.2, y.1.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  have hcard : Nat.card {x : K // IsConj κ x ∧ τ x = x} = 15 := by
    rw [Nat.card_congr e1, ← e16_a5_card_invol]
    refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun y => ?_))
    simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ne_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (e.injective (h.trans (map_one e).symm)), by rw [← map_mul, h2, map_one]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (by rw [h, map_one]), e.injective (by rw [map_mul, h2, map_one])⟩
  rw [hcard] at hmod
  rw [Nat.odd_iff]
  have h15 : (conjugatesOf κ).ncard % 2 = 15 % 2 := hmod
  omega

structure CatE16Data (K : Type) [Group K] [Finite K] where
  τ : MulAut K
  hτ2 : τ * τ = 1
  hout : τ ∉ (MulAut.conj : K →* MulAut K).range
  e : ↥(autCentralizer τ) ≃* alternatingGroup (Fin 5)
  κ : K
  hκ : κ ∈ autCentralizer τ
  hκ2 : orderOf κ = 2
  hQ : Nat.card (Subgroup.centralizer ({κ} : Set K)) ≤ 16

namespace CatE16Data

variable {K : Type} [Group K] [Finite K] (D : CatE16Data K)

include D

theorem τ_ne_one : D.τ ≠ 1 := by
  intro h
  apply D.hout
  rw [h]
  exact ⟨1, by simp⟩

theorem orderOf_τ : orderOf D.τ = 2 :=
  orderOf_eq_prime (by rw [sq]; exact D.hτ2) D.τ_ne_one

theorem card_fixed : Nat.card (autCentralizer D.τ) = 60 := by
  rw [Nat.card_congr D.e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem fixed_ne_top : autCentralizer D.τ ≠ ⊤ := by
  intro h
  apply D.τ_ne_one
  ext x
  have hx : x ∈ autCentralizer D.τ := h ▸ Subgroup.mem_top x
  have hx' : D.τ x = x := hx
  simpa using hx'

theorem card_ne_sixty : Nat.card K ≠ 60 := by
  intro h
  apply D.fixed_ne_top
  rw [← Subgroup.card_eq_iff_eq_top, D.card_fixed, h]

theorem sixty_dvd : 60 ∣ Nat.card K := by
  have := Subgroup.card_subgroup_dvd_card (autCentralizer D.τ)
  rwa [D.card_fixed] at this

theorem odd_index : Odd (Subgroup.centralizer ({D.κ} : Set K)).index :=
  e16_odd_index D.hτ2 D.e D.hκ D.hκ2

theorem two_pow_dvd_card_iff (k : ℕ) :
    2 ^ k ∣ Nat.card K ↔ 2 ^ k ∣ Nat.card (Subgroup.centralizer ({D.κ} : Set K)) := by
  have hmul := Subgroup.index_mul_card (Subgroup.centralizer ({D.κ} : Set K))
  rw [← hmul]
  have hcop : Nat.Coprime (2 ^ k) (Subgroup.centralizer ({D.κ} : Set K)).index :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 D.odd_index)
  exact hcop.dvd_mul_left

theorem not_two_pow_five_dvd : ¬ 2 ^ 5 ∣ Nat.card K := by
  rw [D.two_pow_dvd_card_iff]
  intro h
  have hpos : 0 < Nat.card (Subgroup.centralizer ({D.κ} : Set K)) := Nat.card_pos
  have := Nat.le_of_dvd hpos h
  have := D.hQ
  omega

end CatE16Data

end CFSG.ComponentClassification.CatFC
