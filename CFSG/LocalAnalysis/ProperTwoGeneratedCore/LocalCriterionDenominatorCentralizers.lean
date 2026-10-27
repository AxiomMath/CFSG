module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorFixedSets

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

@[expose] def internalCentralizerEquiv (L : Subgroup G) (x : G) (hxL : x ∈ L) :
    (L ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) ≃*
      Subgroup.centralizer ({(⟨x, hxL⟩ : L)} : Set L) where
  toFun y := ⟨⟨y, y.property.1⟩, Subgroup.mem_centralizer_singleton_iff.mpr
    (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.property.2))⟩
  invFun y := ⟨(y : L), ⟨y.val.property, Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp y.property))⟩⟩
  left_inv y := by ext; rfl
  right_inv y := by ext; rfl
  map_mul' y z := by ext; rfl

@[expose] def elementCentralizerEquiv {F : Type*} [Group F] (e : G ≃* F) (x : G) :
    Subgroup.centralizer ({x} : Set G) ≃* Subgroup.centralizer ({e x} : Set F) where
  toFun y := ⟨e y.val, Subgroup.mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg e
      (Subgroup.mem_centralizer_singleton_iff.mp y.property))⟩
  invFun y := ⟨e.symm y.val, Subgroup.mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul, e.symm_apply_apply] using congrArg e.symm
      (Subgroup.mem_centralizer_singleton_iff.mp y.property))⟩
  left_inv y := by ext; simp
  right_inv y := by ext; simp
  map_mul' y z := by ext; simp

theorem inverter_normalizes_element_centralizer (x t : G) (ht : orderOf t = 2)
    (hinv : rightConjugateElem x t = x⁻¹) :
    t ∈ Subgroup.normalizer ((Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) := by
  have htinv : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two ht
  have htt : t * t = 1 := by simpa only [ht, pow_two] using pow_orderOf_eq_one t
  have hxinv : t * x * t⁻¹ = x⁻¹ := by
    simpa only [rightConjugateElem, htinv] using hinv
  have forward : ∀ c ∈ Subgroup.centralizer ({x} : Set G),
      t * c * t⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
    intro c hc
    have hcx : Commute c x := Subgroup.mem_centralizer_singleton_iff.mp hc
    have h : Commute (t * c * t⁻¹) (t * x * t⁻¹) := by
      exact (hcx.map (MulAut.conj t).toMonoidHom)
    rw [hxinv] at h
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by simpa only [inv_inv] using h.inv_right.eq)
  apply Subgroup.mem_normalizer_iff.mpr
  intro c
  constructor
  · exact forward c
  · intro hc
    have h := forward (t * c * t⁻¹) hc
    have hback : t * (t * c * t⁻¹) * t⁻¹ = c := by
      rw [htinv]
      calc
        t * (t * c * t) * t = (t * t) * c * (t * t) := by group
        _ = c := by rw [htt, one_mul, mul_one]
    rwa [hback] at h

variable [Finite G]

theorem odd_element_full_centralizer_odd (x : G) (hx : x ≠ 1)
    (hodd : Odd (orderOf x))
    (hCtwo : ∀ t : G, orderOf t = 2 → IsPGroup 2 (Subgroup.centralizer ({t} : Set G))) :
    Odd (Nat.card (Subgroup.centralizer ({x} : Set G))) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.centralizer ({x} : Set G)) 2 (even_iff_two_dvd.mp heven)
  have htG : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  let y : Subgroup.centralizer ({(t : G)} : Set G) :=
    ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp t.property).symm⟩
  have hyodd : Odd (orderOf y) := (Subgroup.orderOf_coe y).symm ▸ hodd
  have hcop := (hCtwo t htG).orderOf_coprime hyodd.coprime_two_left y
  have hyorder : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl
  exact hx (congrArg Subtype.val (orderOf_eq_one_iff.mp hyorder))

theorem pair_full_centralizer_eq (H : Subgroup G)
    (a b : pointRightCosetSpace H) (hab : a ≠ b) (L : Subgroup G)
    (hcomm : IsMulCommutative (L ⊓
      (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) : Subgroup G))
    (x : G) (hxW : x ∈ L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b))
    (hfix : elementFixedSet H x = {a, b})
    (hCodd : Odd (Nat.card (L ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G))) :
    L ⊓ Subgroup.centralizer ({x} : Set G) =
      L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) := by
  let W := L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)
  let C := L ⊓ Subgroup.centralizer ({x} : Set G)
  have hCN : C ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    intro c hc
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    have hcx : Commute c x := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    have heq : (MulAut.conj c) x = x := by
      simp only [MulAut.conj_apply, hcx.eq, mul_inv_cancel_right]
    change Subgroup.zpowers ((MulAut.conj c) x) = Subgroup.zpowers x
    rw [heq]
  have hCD : C ≤ rightCosetStabilizer H a ⊓ rightCosetStabilizer H b :=
    odd_normalizer_fixes_pair H (Subgroup.zpowers x) C hCodd hCN a b hab
      ((pointFixedSet_zpowers_eq H x).trans hfix)
  apply le_antisymm
  · exact fun c hc => ⟨hc.1, hCD hc⟩
  · intro c hc
    refine ⟨hc.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val ((@IsMulCommutative.is_comm W _ hcomm).comm
      (⟨c, hc⟩ : W) (⟨x, hxW⟩ : W))

theorem odd_inverted_pair_full_centralizer_eq (H : Subgroup G)
    (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (hthree : ThreePointCentralization H
      (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b))
    (L : Subgroup G) (t : G) (ht : orderOf t = 2)
    (hWodd : Odd (Nat.card (L ⊓
      (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) : Subgroup G)))
    (hcomm : IsMulCommutative (L ⊓
      (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) : Subgroup G))
    (hinv : ∀ x ∈ L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b),
      rightConjugateElem x t = x⁻¹)
    (hCtwo : ∀ s : L, orderOf s = 2 → IsPGroup 2 (Subgroup.centralizer ({s} : Set L)))
    (x : G) (hxW : x ∈ L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b))
    (hx : x ≠ 1) :
    elementFixedSet H x = {a, b} ∧
      L ⊓ Subgroup.centralizer ({x} : Set G) =
        L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) := by
  let W := L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)
  have hxodd : Odd (orderOf x) := by
    have h := hWodd.of_dvd_nat (orderOf_dvd_natCard (⟨x, hxW⟩ : W))
    exact (Subgroup.orderOf_coe (⟨x, hxW⟩ : W)) ▸ h
  have hfix := pair_inverted_element_full_fixed_set H a b hab hthree t ht x hx hxW.2 hxodd
    (hinv x hxW)
  let y : L := ⟨x, hxW.1⟩
  have hyne : y ≠ 1 := by intro hy; exact hx (congrArg Subtype.val hy)
  have hyodd : Odd (orderOf y) := (Subgroup.orderOf_coe y).symm ▸ hxodd
  have hCodd : Odd (Nat.card (L ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G)) :=
    (Nat.card_congr (internalCentralizerEquiv L x hxW.1).toEquiv).symm ▸
      odd_element_full_centralizer_odd y hyne hyodd hCtwo
  exact ⟨hfix, pair_full_centralizer_eq H a b hab L hcomm x hxW hfix hCodd⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
