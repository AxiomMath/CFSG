module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911G2
import CFSG.GH74.Generic.BProg.B2.PumpupOutOrders
public import CFSG.GH74.Generic.BProg.B2.Defs

public section

namespace CFSG.GH74.Generic.BProg.B2.PuG2OddAux

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup
open CFSG.Open (ordG2)

open CFSG.GH74.Generic.BProg.B2.PumpupOutOrders (not_qShape1_of_simple sixteen_dvd_ordG2
  not_sixteen_dvd_ordRee not_sixteen_dvd_J1 g2_not_shape3)


section Orders


theorem not_qShapeNS_of_G2_big {X : Type} [Group X] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq5 : 5 ≤ p ^ e) (hX : LieModel X .G2 0 p e) (hs : IsSimpleGroup X) :
    ¬ QShapeNS X := by
  have hcard : Nat.card X = ordG2 (p ^ e) := CFSG.GH74.card_of_lieModel_G2 hp2 hX
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have h16 : 16 ∣ Nat.card X := hcard ▸ sixteen_dvd_ordG2 hodd
  rintro (h1 | ⟨s, g, hsp, hs2, hr, hL | hL⟩ | ⟨f, hf⟩ | h5)
  · exact not_qShape1_of_simple h1 h16
  · have hc := CFSG.GH74.card_of_lieModel_PSL (n := 3) (by norm_num) hL
    exact g2_not_shape3 hp hp2 hq5 (r := s ^ g) (by omega) (Or.inl (hcard.symm.trans hc))
  · have hc := CFSG.GH74.card_of_lieModel_PSU (n := 3) (by norm_num) hs2 hL
    exact g2_not_shape3 hp hp2 hq5 (r := s ^ g) (by omega) (Or.inr (hcard.symm.trans hc))
  · obtain ⟨k, -, hk⟩ := CFSG.GH74.card_of_lieModel_twistedG2 hf
    rw [hk] at h16
    exact not_sixteen_dvd_ordRee k h16
  · rw [ShapeOrders.qShape5_facts h5] at h16
    exact not_sixteen_dvd_J1 h16

theorem not_qShapeNS_of_G2_three_one {X : Type} [Group X] (hX : LieModel X .G2 0 3 1) :
    ¬ QShapeNS X := by
  intro hQ
  have hc := CFSG.GH74.card_of_lieModel_G2 (n := 0) (p := 3) (by norm_num) hX
  have hc' : Nat.card X = 4245696 := hc.trans (by decide)
  exact PumpupTableThree.not_dvd_of_qShapeNS_three hQ (m := 4245696)
    (PumpupTableThree.smallOrder3_of_dvd (m := 4245696) (by decide) (by decide) (by decide)
      (by decide)) (by decide)
    (PumpupTableThree.notJ1Order_of_not_dvd (m := 4245696) (by decide)) (by rw [hc'])

theorem not_qShapeNS_of_G2_three {X : Type} [Group X] {e : ℕ} (he : 1 ≤ e)
    (hX : LieModel X .G2 0 3 e) (hs : IsSimpleGroup X) : ¬ QShapeNS X := by
  by_cases h1 : e = 1
  · subst h1
    exact not_qShapeNS_of_G2_three_one hX
  · have h9 : 3 ^ 2 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact not_qShapeNS_of_G2_big Nat.prime_three (by norm_num) (by omega) hX hs

end Orders

open CFSG.LieType.Chevalley in
theorem card_fixSubfield_quad {F : Type} [Field F] [Finite F] {p e : ℕ} (hp : p.Prime)
    (he : 1 ≤ e) (hK : Nat.card F = (p ^ e) ^ 2) (δ : F ≃+* F)
    (hδ : ∀ c, δ c = c ^ (p ^ e)) : Nat.card (fixSubfield δ) = p ^ e := by
  have hK' : Nat.card F = p ^ (2 * e) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨φ, hφ, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp
      (by omega) hK'
  have hδφ : δ = φ ^ e :=
    RingEquiv.ext fun c => by rw [hδ, ringAut_pow_apply_of_frobenius hφ]
  have hsq : δ ^ 2 = 1 := by
    rw [hδφ, ← pow_mul, show e * 2 = 2 * e by ring, ← hord, pow_orderOf_eq_one]
  have hne : δ ≠ 1 := by
    intro h1
    rw [hδφ] at h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at this
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  obtain ⟨-, -, hcard⟩ := ringEquiv_sq_eq_one_facts hp (by omega) hK' hsq hne
  rw [show 2 * e / 2 = e by omega] at hcard
  exact hcard

section Outer

open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley (fixSubfield odd_pinned_Chevalley_p_components)

open CFSG.LieType.Ree (ReeTag)

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (fixSub mem_fixSub)

open CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement


theorem g2_three_outer_fixed_even {F : Type} [Field F] [Finite F] {f : ℕ} (hf : 1 ≤ f)
    (hfe : Even f) (hK : Nat.card F = 3 ^ f) {α : MulAut (adjointGroup ReeTag.G2.tag F)}
    (hα : α ^ 2 = 1) (hnot : α ∉ (MulAut.conj : adjointGroup ReeTag.G2.tag F →*
      MulAut (adjointGroup ReeTag.G2.tag F)).range) :
    ∃ e : ℕ, 1 ≤ e ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 3 ^ e ∧
      Nonempty (↥(fixSub α) ≃* adjointGroup ReeTag.G2.tag k) := by
  have : CharP F ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      hf hK
  rcases CFSG.LieType.AlgebraicGroups.G2_three_involution_inner_quadratic_or_exceptional hf hK
      hα with ⟨g, a, hαg⟩ | ⟨e, he, hKe, δ, hδ, g, a, hαg⟩ | ⟨b, g, hfb, -⟩
  · exact absurd (ivk93res_inner_of_diag hαg) hnot
  · exact ⟨e, he, fixSubfield δ, inferInstance, inferInstance,
      card_fixSubfield_quad Nat.prime_three he hKe δ hδ,
      CFSG.GH74.GLS.Stage2.Bender.Thm2.P911.g2_quadratic_fixed_equiv Nat.prime_three he hKe δ hδ
        hαg hα⟩
  · exfalso
    obtain ⟨m, hm⟩ := hfe
    omega

theorem mem_of_shape_g2_three_even {N : Type} [Group N] [Finite N] {H : Subgroup N} {t : N}
    {L : Subgroup N} (hs : ShapeInCent H t L) {f : ℕ} (hf : 1 ≤ f) (hfe : Even f)
    (hH : LieModel ↥H .G2 0 3 f) : t ∈ H := by
  by_contra htH
  have := hs.normal
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := Ivk47ab.exists_equiv_of_lieModel hH
  obtain ⟨α, hα2, hαout, hαfix⟩ :=
    PumpupOutOrders.exists_outer_aut hs.inv hs.faithful htH e
  obtain ⟨e', he', k, _, _, hk, ⟨Φ⟩⟩ :=
    g2_three_outer_fixed_even hf hfe hcard ((sq α).trans hα2) hαout
  set X : Subgroup ↥H := fixSub (MulAut.conjNormal t : MulAut ↥H) with hX
  have hXα : X.map e.toMonoidHom = fixSub α := by
    ext y
    rw [Subgroup.mem_map, mem_fixSub, hαfix y]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using (PumpupOutOrders.mem_fixSub_conjNormal (H := H) (t := t) (y := x)).1 hx
    · intro h
      exact ⟨e.symm y, (PumpupOutOrders.mem_fixSub_conjNormal (H := H) (t := t)).2 h,
        e.apply_symm_apply y⟩
  let Ψ : ↥X ≃* ↥(fixSub α) :=
    (X.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hXα)
  have hkodd : ringChar k ≠ 2 :=
    CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow Nat.prime_three (by norm_num) hk
  obtain ⟨hsk, -⟩ := odd_pinned_Chevalley_p_components ReeTag.G2.tag k hkodd
  have hsimple : IsSimpleGroup ↥X := (MulEquiv.isSimpleGroup_congr (Ψ.trans Φ)).2 hsk
  have hQ := PumpupOutOrders.qShapeNS_of_descent hs X le_rfl (fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) hsimple
  have hQk : QShapeNS (adjointGroup ReeTag.G2.tag k) := QShapeNS.of_mulEquiv (Ψ.trans Φ) hQ
  have h3k : 3 ≤ 3 ^ e' := Nat.le_self_pow (by omega) 3
  have hmodel : LieModel (adjointGroup ReeTag.G2.tag k) .G2 0 3 e' :=
    Ivk47ab.lieModel_G2g Nat.prime_three he' h3k hk
  exact not_qShapeNS_of_G2_three he' hmodel hsk hQk

end Outer

end CFSG.GH74.Generic.BProg.B2.PuG2OddAux
