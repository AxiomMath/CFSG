module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveTenSeven
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveTenFinalCorrected

import CFSG.GroupTheory.HeisenbergF4FixedDim
import CFSG.LargeExtraspecial.S3Fourteen
public import CFSG.ClassicalInvolution.Q3.Q3MFOU4F9
public import CFSG.LargeExtraspecial.Transport
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435
open CFSG.GroupTheory.HeisenbergF4

variable {G : Type} [Group G] [Finite G]

private instance : Fintype W3 :=
  Fintype.ofEquiv ((M3 → M3) × M3) (RegularWreathProduct.equivProd M3 M3).symm

private instance : DecidableEq W3 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right)
    ⟨fun h => RegularWreathProduct.ext h.1 h.2, fun h => ⟨congrArg _ h, congrArg _ h⟩⟩

private def prodHom : W3 →* M3 where
  toFun w := ∏ x, w.left x
  map_one' := by simp
  map_mul' a b := by
    simp only [RegularWreathProduct.mul_left, Pi.mul_apply, Finset.prod_mul_distrib]
    congr 1
    exact Function.Bijective.prod_comp
      ⟨fun x y h => mul_left_cancel h, fun y => ⟨a.right * y, by simp⟩⟩ b.left

private theorem prodHom_surjective : Function.Surjective prodHom := by
  intro a
  refine ⟨⟨fun x => if x = 1 then a else 1, 1⟩, ?_⟩
  rw [show prodHom ⟨fun x => if x = 1 then a else 1, 1⟩ =
    ∏ x : M3, (if x = 1 then a else 1) from rfl]
  rw [Fintype.prod_eq_single 1 (fun x hx => by simp [hx])]
  simp

private theorem card_ker : Nat.card ↥prodHom.ker = 27 := by
  have h := Subgroup.card_ker_mul_card_of_surjective (f := prodHom) prodHom_surjective
  rw [card_W3, card_M3] at h
  omega

private def phiFun (x : ↥prodHom.ker) : H27 :=
  let p := (x.1.left 1).toAdd
  let q := (x.1.left (Multiplicative.ofAdd (1 : ZMod 3))).toAdd
  let k := x.1.right.toAdd
  ⟨q - p, k, -(p + q) + (q - p) * k⟩

private theorem phiFun_mul : ∀ x y : ↥prodHom.ker,
    (phiFun (x * y)).a = (phiFun x).a + (phiFun y).a ∧
      (phiFun (x * y)).b = (phiFun x).b + (phiFun y).b ∧
      (phiFun (x * y)).c = (phiFun x).c + (phiFun y).c + (phiFun x).a * (phiFun y).b := by
  decide

private theorem phiFun_one : (phiFun 1).a = 0 ∧ (phiFun 1).b = 0 ∧ (phiFun 1).c = 0 := by
  decide

private theorem phiFun_inj_coords : ∀ x y : ↥prodHom.ker,
    (phiFun x).a = (phiFun y).a → (phiFun x).b = (phiFun y).b →
      (phiFun x).c = (phiFun y).c → x = y := by
  decide

private def phiHom : ↥prodHom.ker →* H27 where
  toFun := phiFun
  map_one' := by
    obtain ⟨h1, h2, h3⟩ := phiFun_one
    exact H27.ext h1 h2 h3
  map_mul' x y := by
    obtain ⟨h1, h2, h3⟩ := phiFun_mul x y
    exact H27.ext h1 h2 h3

private theorem phiHom_injective : Function.Injective phiHom := by
  intro x y h
  exact phiFun_inj_coords x y (congrArg H27.a h) (congrArg H27.b h) (congrArg H27.c h)

private theorem phiHom_surjective : Function.Surjective phiHom := by
  have hcard : Nat.card ↥(MonoidHom.range phiHom) = Nat.card H27 := by
    rw [H27.nat_card, ← card_ker]
    exact (Nat.card_congr (Equiv.ofInjective phiHom phiHom_injective)).symm
  have htop : MonoidHom.range phiHom = ⊤ :=
    Subgroup.eq_of_le_of_card_ge le_top (by rw [Subgroup.card_top, hcard])
  exact MonoidHom.range_eq_top.mp htop

private theorem isExtraspecialPGroup_H27 : IsExtraspecialPGroup 3 H27 := by
  have h3prime : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine CFSG.LargeExtraspecial.isExtraspecialPGroup_of_card_center ?_ ?_ ?_ ?_ ?_
  · exact IsPGroup.of_card (n := 3) (by rw [H27.nat_card]; norm_num)
  · rw [H27.center_eq, H27.card_center]
  · intro x y
    rw [H27.center_eq]
    exact H27.commutator_mem_center x y
  · intro x
    rw [H27.center_eq, H27.mem_centerSubgroup_iff, H27.exponent_three]
    exact ⟨H27.one_a, H27.one_b⟩
  · obtain ⟨x, y, hxy⟩ := H27.noncommutative
    exact ⟨x, y, hxy⟩

private theorem isThreeOnePlusTwo_H27 : IsThreeOnePlusTwo H27 :=
  ⟨isExtraspecialPGroup_H27, H27.nat_card, H27.exponent_three⟩

theorem IsThreeOnePlusTwo.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsThreeOnePlusTwo X) : IsThreeOnePlusTwo Y :=
  ⟨CFSG.LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv e h.1,
    by rw [← Nat.card_congr e.toEquiv, h.2.1],
    fun y => by
      obtain ⟨x, rfl⟩ := e.surjective y
      rw [← map_pow, h.2.2, map_one]⟩

private theorem isThreeOnePlusTwo_ker : IsThreeOnePlusTwo ↥prodHom.ker :=
  IsThreeOnePlusTwo.of_mulEquiv
    (MulEquiv.ofBijective phiHom ⟨phiHom_injective, phiHom_surjective⟩).symm
    isThreeOnePlusTwo_H27

theorem p_eq_three_and_card_of_twelveSevenA {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}
    (h : TwelveCtx G M p Q H) (hA : TwelveSevenA M H Q) :
    p = 3 ∧ Nat.card Q = p ^ 4 := by
  obtain ⟨e, -, -⟩ := hA
  have h81 : Nat.card Q = 81 := card_of_equiv e
  have hpprime : Fact p.Prime := ⟨h.p_prime⟩
  obtain ⟨n, hn⟩ := h.Q_isPGroup.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    omega
  have hpow : p ^ n = 3 ^ 4 := by
    rw [← hn, h81]
    norm_num
  have hp3 : p = 3 :=
    (Nat.prime_dvd_prime_iff_eq h.p_prime Nat.prime_three).mp
      (h.p_prime.dvd_of_dvd_pow (by rw [← hpow]; exact dvd_pow_self p hn0))
  subst hp3
  exact ⟨rfl, by rw [h81]; norm_num⟩

theorem twelveTenFinalA'_of_twelveSevenA {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}
    (h : TwelveCtx G M p Q H) (hA : TwelveSevenA M H Q) :
    TwelveTenFinalA' M H Q p := by
  obtain ⟨e, -, -⟩ := hA
  obtain ⟨E, hEQ, hE, hEcard, hΓ⟩ := h.exists_E_sq
  have hD3 : IsThreeOnePlusTwo
      ↥((prodHom.ker.map e.symm.toMonoidHom).map Q.subtype) := by
    have h1 : ↥prodHom.ker ≃* ↥(prodHom.ker.map e.symm.toMonoidHom) :=
      Subgroup.equivMapOfInjective prodHom.ker e.symm.toMonoidHom e.symm.injective
    have h2 : ↥(prodHom.ker.map e.symm.toMonoidHom) ≃*
        ↥((prodHom.ker.map e.symm.toMonoidHom).map Q.subtype) :=
      Subgroup.equivMapOfInjective _ Q.subtype Q.subtype_injective
    exact IsThreeOnePlusTwo.of_mulEquiv (h1.trans h2) isThreeOnePlusTwo_ker
  exact ⟨E, _, hEQ, hE, hEcard, hΓ, hD3, Subgroup.map_subtype_le _⟩

theorem twelveTenFinalStep_of_twelveSevenA {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}
    (h : TwelveCtx G M p Q H) (hA : TwelveSevenA M H Q) (hB : TwelveTenFinalB' M H Q p) :
    TwelveTenFinalStep M H Q p :=
  twelveTenFinalStep_of_p_eq_three (p_eq_three_and_card_of_twelveSevenA h hA).1
    (p_eq_three_and_card_of_twelveSevenA h hA).2 (twelveTenFinalA'_of_twelveSevenA h hA) hB

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
