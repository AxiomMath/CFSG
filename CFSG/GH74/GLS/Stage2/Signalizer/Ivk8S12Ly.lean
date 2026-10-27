module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8S12Count
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Ly
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Gen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.Stage2.Bender.Thm1

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}

theorem AFrame.isSporadic_ly_of_comp (hA : LyAllInner)
    (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J)
    (h : NativeSporadic.IsSporadic (↥J ⧸ center ↥J) .Ly) : NativeSporadic.IsSporadic A .Ly := by
  obtain ⟨e⟩ := h
  have hN : Nat.card (↥J ⧸ center ↥J) = 51765179004000000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Ly.card_Ly
  have hY : ¬ KindFactorAll Kind.ly (↥J ⧸ center ↥J) := fun hK =>
    (by decide : ¬ 51765179004000000 ∣ Nat.factorial 11) (hN ▸ hK.card_dvd (Or.inr rfl))
  obtain ⟨hZ, hu, -⟩ := hfr.reduce hJ hY
  have hJn : J.Normal := Gen.normal_of_unique_comp hJ hu
  let eJ : ↥J ≃* (↥J ⧸ center ↥J) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  let eL : ↥J ≃* NativeSporadic.Ly := eJ.trans e
  have hAJC : ∀ a : A, ∃ g ∈ J, g⁻¹ * a ∈ centralizer (J : Set A) := by
    intro a
    have han : a ∈ normalizer (J : Set A) := by
      rw [Subgroup.normalizer_eq_top]
      exact mem_top a
    obtain ⟨g, hg⟩ := hA ↥J ⟨eL⟩ (J.normalizerMonoidHom ⟨a, han⟩)
    refine ⟨(g : A), g.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' := congrArg (fun φ : MulAut ↥J => ((φ ⟨x, hx⟩ : ↥J) : A)) hg
    simp only [MulAut.conj_apply] at hx'
    have hx'' : a * x * a⁻¹ = (g : A) * x * (g : A)⁻¹ := hx'
    calc x * ((g : A)⁻¹ * a) = (g : A)⁻¹ * ((g : A) * x * (g : A)⁻¹) * a := by group
      _ = (g : A)⁻¹ * (a * x * a⁻¹) * a := by rw [hx'']
      _ = (g : A)⁻¹ * a * x := by group
  have hCn : (centralizer (J : Set A)).Normal := by
    refine ⟨fun c hc g => ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    have hx' : g⁻¹ * x * g ∈ J := by
      have := hJn.conj_mem x hx g⁻¹
      simpa using this
    have := hc _ hx'
    calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
      _ = g * c * g⁻¹ * x := by group
  have hJC : ∀ x ∈ J, x ∈ centralizer (J : Set A) → x = 1 := by
    intro x hxJ hxC
    have hz : (⟨x, hxJ⟩ : ↥J) ∈ center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxC y y.2)
    rw [hZ, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  have hfin2 : (Nat.card A).factorization 2 = 8 := by
    have h1 := hfr.sylow.card_eq
    rw [hfr.card, Subgroup.card_top] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hJ2 : (Nat.card ↥J).factorization 2 = 8 := by
    have hc : Nat.card ↥J = 51765179004000000 := by
      rw [Nat.card_congr eL.toEquiv]
      exact CFSG.Sporadic.Ly.card_Ly
    rw [hc]
    exact factorization_two_eq (by norm_num) (by norm_num)
  have hquot : ¬ 2 ∣ Nat.card (A ⧸ J) := by
    intro h2
    have hm := J.card_eq_card_quotient_mul_card_subgroup
    have hq0 : Nat.card (A ⧸ J) ≠ 0 := Nat.card_pos.ne'
    have hJ0 : Nat.card ↥J ≠ 0 := Nat.card_pos.ne'
    have h3 := congrArg (fun n => n.factorization 2) hm
    simp only [Nat.factorization_mul hq0 hJ0, Finsupp.add_apply, hfin2, hJ2] at h3
    have h4 : 0 < (Nat.card (A ⧸ J)).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two hq0 h2
    omega
  have hCle : centralizer (J : Set A) ≤ pPrimeCore 2 A := by
    have hinj : Function.Injective
        ((QuotientGroup.mk' J).comp (centralizer (J : Set A)).subtype) := by
      rw [injective_iff_map_eq_one]
      intro c hc
      have hcJ : (c : A) ∈ J := (QuotientGroup.eq_one_iff (c : A)).1 hc
      exact Subtype.ext (hJC c hcJ c.2)
    have hdvd := Subgroup.card_dvd_of_injective _ hinj
    have hcop : Nat.Coprime 2 (Nat.card (centralizer (J : Set A))) := by
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 fun h2 => hquot (h2.trans hdvd)
    exact le_sSup ⟨hCn, hcop⟩
  have hCbot : ∀ c ∈ centralizer (J : Set A), c = 1 := by
    intro c hc
    have := hCle hc
    rw [hfr.core, Subgroup.mem_bot] at this
    exact this
  have hJtop : ∀ a : A, a ∈ J := by
    intro a
    obtain ⟨g, hg, hga⟩ := hAJC a
    have : g⁻¹ * a = 1 := hCbot _ hga
    have h1 : a = g := by
      calc a = g * (g⁻¹ * a) := by group
        _ = g := by rw [this, mul_one]
    rw [h1]
    exact hg
  let eA : ↥J ≃* A :=
    MulEquiv.ofBijective J.subtype ⟨J.subtype_injective, fun a => ⟨⟨a, hJtop a⟩, rfl⟩⟩
  exact ⟨eA.symm.trans eL⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
