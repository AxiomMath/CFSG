module

public import CFSG.LinearAlgebra.LinearGroups.LinearTwoOddFourGroups
public import CFSG.GH74.Generic.S45.LQData
public import CFSG.GH74.Generic.S45.LSporCommon
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.AutL2Facts CFSG.GH74.Uniqueness.Bender CFSG.LinearGroups
open scoped MatrixGroups

theorem QData.four_dvd_card {S : Type} [Group S] {ya : MulAut S} {Lb : Subgroup S} {q : ℕ}
    (hQ : QData S ya Lb q) : 4 ∣ Nat.card ↥Lb := by
  obtain ⟨k, hk⟩ := hQ.odd
  have h1 : q ^ 2 - 1 = 4 * (k * (k + 1)) := by
    have : q ^ 2 = 4 * (k * (k + 1)) + 1 := by rw [hk]; ring
    omega
  obtain ⟨m, hm⟩ := Nat.even_mul_succ_self k
  have h2 : Nat.card ↥Lb * 2 = (4 * ((2 * k + 1) * m)) * 2 := by
    rw [hQ.card, h1, hk, hm]
    ring
  exact ⟨(2 * k + 1) * m, Nat.eq_of_mul_eq_mul_right two_pos h2⟩

theorem QData.exists_kleinFour {S : Type} [Group S] [Finite S] {ya : MulAut S} {Lb : Subgroup S}
    {q : ℕ} (hQ : QData S ya Lb q) :
    ∃ W : Subgroup ↥Lb, Nat.card W = 4 ∧ ∀ x : W, x ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, hW⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥Lb) 2
    (n := 2) (by simpa using hQ.four_dvd_card)
  refine ⟨W, by simpa using hW, fun x => ?_⟩
  have hdvd : orderOf x ∣ 2 ^ 2 := by
    rw [← hW]
    exact orderOf_dvd_natCard x
  have hno : ¬ 4 ∣ orderOf x := by
    have := hQ.no4 (((x : ↥Lb) : S)) (x : ↥Lb).2
    rwa [Subgroup.orderOf_coe, Subgroup.orderOf_coe] at this
  obtain ⟨i, hi, hix⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [orderOf_dvd_iff_pow_eq_one.symm]
  interval_cases i
  · rw [hix]
    norm_num
  · rw [hix]
    norm_num
  · exact absurd (by rw [hix]; norm_num) hno

theorem psl2_linear_false
    {F : Type} [Field F] [Finite F] (hK : IsOddPrimePower (Nat.card F))
    {S : Type} [Group S] [Finite S] (e : S ≃* PSL2 F) {yb : MulAut S} {Lb : Subgroup S} {q : ℕ}
    (hQ : QData S yb Lb q) {C : PGL2 F} (hC : autEquiv e yb = SemidirectProduct.inl C) : False := by
  classical
  let Φ : S →* PGL2 F :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).comp e.toMonoidHom
  have hΦ : Function.Injective Φ :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp e.injective
  have hcomm : ∀ s ∈ Lb, Φ s * C = C * Φ s := by
    intro s hs
    have h1 := semilinearAction_autEquiv_apply e yb s
    rw [hC, semilinearAction_inl] at h1
    have h2 : yb s = s := (mem_autFixed_iff).1 (hQ.le hs)
    rw [h2] at h1
    have h3 := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL h1
    rw [toPGL_pglAction] at h3
    change Matrix.ProjectiveSpecialLinearGroup.toPGL (e s) * C =
      C * Matrix.ProjectiveSpecialLinearGroup.toPGL (e s)
    calc Matrix.ProjectiveSpecialLinearGroup.toPGL (e s) * C
        = (C * Matrix.ProjectiveSpecialLinearGroup.toPGL (e s) * C⁻¹) * C := by rw [h3]
      _ = C * Matrix.ProjectiveSpecialLinearGroup.toPGL (e s) := by group
  obtain ⟨W, hW4, hWsq⟩ := hQ.exists_kleinFour
  let ψ : ↥Lb →* PGL2 F := Φ.comp Lb.subtype
  have hψ : Function.Injective ψ := hΦ.comp Subtype.val_injective
  let V : Subgroup (PGL2 F) := W.map ψ
  have hVcard : Nat.card V = 4 := by
    rw [Subgroup.card_map_of_injective hψ]
    exact hW4
  have hVsq : ∀ x : V, x ^ 2 = 1 := by
    rintro ⟨_, w, hw, rfl⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow]
    have := congrArg Subtype.val (hWsq ⟨w, hw⟩)
    rw [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [this, map_one]
  have hVK : IsKleinFour V := isKleinFour_of_card_eq_four hVcard hVsq
  have hcent := pgl2_kleinFour_centralizer_eq_self F hK V hVK
  have hCV : C ∈ V := by
    rw [← hcent, Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, -, rfl⟩
    exact hcomm w.1 w.2
  obtain ⟨w, -, hwC⟩ := hCV
  have hwz : w ∈ Subgroup.center ↥Lb := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply hψ
    rw [map_mul, map_mul, hwC]
    exact hcomm z.1 z.2
  have hZ : Subgroup.center ↥Lb = ⊥ := center_eq_bot_of_simple_nonab hQ.simple hQ.nonab
  rw [hZ, Subgroup.mem_bot] at hwz
  have hC1 : C = 1 := by rw [← hwC, hwz, map_one]
  have hy : yb = 1 := by
    apply (autEquiv e).injective
    rw [hC, hC1, map_one, map_one]
  exact hQ.ne hy

theorem Hyp1310.false_of_fixed_order_four_of_center_bot {K : Type} [Group K] [Finite K] {y : MulAut K}
    {L : Subgroup K} (hyp : Hyp1310 K y L) (hZ : Subgroup.center K = ⊥)
    {yb : MulAut (K ⧸ Subgroup.center K)}
    (hyb : ∀ k : K, yb (QuotientGroup.mk k) = QuotientGroup.mk (y k))
    {x : K ⧸ Subgroup.center K} (hx : yb x = x) (h4 : 4 ∣ orderOf x) : False := by
  obtain ⟨-, -, -, -, hno4, -⟩ := hyp.data
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
  have hmk : ∀ a b : K, (QuotientGroup.mk a : K ⧸ Subgroup.center K) = QuotientGroup.mk b → a = b := by
    intro a b hab
    have h1 : a⁻¹ * b ∈ Subgroup.center K := QuotientGroup.eq.1 hab
    rw [hZ, Subgroup.mem_bot] at h1
    exact (inv_mul_eq_one.1 h1)
  have hym : y m = m := by
    apply hmk
    rw [← hyb m]
    exact hx
  have hdvd : orderOf (QuotientGroup.mk m : K ⧸ Subgroup.center K) ∣ orderOf m :=
    orderOf_map_dvd (QuotientGroup.mk' _) m
  exact hno4 m hym (h4.trans hdvd)

end CFSG.GH74.Generic.S45
