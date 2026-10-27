module

public import CFSG.LieType.SeitzGeneration.OuterModel
public import CFSG.RankThree.PartOne.CTP.SeitzL2Odd
public import CFSG.RankThree.PartOne.CTP.SeitzL2Even
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import all CFSG.RankThree.PartOne.CTP.SeitzL2

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG CFSG.GorensteinWalter CFSG.Open CFSG.AGLEmbeddingD2 CFSG.RankThree.PartOne.CTP
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.AutL2Facts
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent (fixedSubfield)

section Data

variable {F : Type} [Field F] [Finite F]

theorem fieldAutData_psl2_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmax : ∀ τ : F ≃+* F, orderOf τ = p →
      IsCoatom (signalizerFixedSubgroup (psl2FieldAut F τ)) ∨
        ¬ p ∣ Nat.card (signalizerFixedSubgroup (psl2FieldAut F τ))) :
    FieldAutData (PSL2 F) p :=
  CFSG.RankThree.PartOne.CTP.fieldAutData_psl2_of_ne_two hp hp2 hmax

end Data

section Even

variable {F : Type} [Field F] [Finite F]

theorem isCoatom_or_fixed_psl2FieldAut_even_odd {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hexc : ¬ (p = 3 ∧ Nat.card F = 8)) (hchar : ringChar F = 2)
    {τ : F ≃+* F} (hτ : orderOf τ = p) :
    IsCoatom (signalizerFixedSubgroup (psl2FieldAut F τ)) ∨
      ¬ p ∣ Nat.card (signalizerFixedSubgroup (psl2FieldAut F τ)) := by
  have : Fact (ringChar F).Prime := ⟨finiteField_characteristic_prime F⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := one_le_finiteFieldExponent F
  have hFc : Nat.card F = 2 ^ finiteFieldExponent F := by
    rw [← hchar]
    exact finiteField_card_eq F
  obtain ⟨hdvd, hcard⟩ := CFSG.RankThree.LinearTwo.card_fixedSubfield
    (finiteField_characteristic_prime F) hf (finiteField_card_eq F) τ
  rw [hτ] at hdvd hcard
  obtain ⟨m, hm⟩ := hdvd
  have hm1 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hm
      omega
    · exact h0
  have hmeq : finiteFieldExponent F / p = m := by
    rw [hm]
    exact Nat.mul_div_cancel_left m hp.pos
  rw [hmeq, hchar] at hcard
  obtain ⟨e⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.nonempty_mulEquiv_fixed_psl2FieldAut
    (hp.odd_of_ne_two hp2) hτ
  let eF := CFSG.ClassicalModels.finiteFieldEquivGaloisField (fixedSubfield F τ) 2 m hm1 hcard
  let e' := e.trans (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF (Fin 2))
  by_cases hm2 : 2 ≤ m
  · exact Or.inl (isCoatom_of_mulEquiv_psl2_even hFc hp hp2 (by rw [hm, mul_comm]) hm2 e')
  · right
    have hm1' : m = 1 := by omega
    have h6 : Nat.card (signalizerFixedSubgroup (psl2FieldAut F τ)) = 6 := by
      rw [Nat.card_congr e'.toEquiv, CFSG.Walter.psl2_even_card hm1.ne', hm1']
      norm_num
    have hFp : Nat.card F = 2 ^ p := by rw [hFc, hm, hm1', mul_one]
    rw [h6]
    intro h
    have h2 := hp.two_le
    have hle := Nat.le_of_dvd (by norm_num) h
    interval_cases p
    · exact absurd rfl hp2
    · exact hexc ⟨rfl, by rw [hFp]; norm_num⟩
    · exact absurd hp (by norm_num)
    · exact absurd h (by norm_num)
    · exact absurd hp (by norm_num)

theorem fieldAutData_psl2_even_odd_prime {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hexc : ¬ (p = 3 ∧ Nat.card F = 8)) (hchar : ringChar F = 2) :
    FieldAutData (PSL2 F) p :=
  fieldAutData_psl2_of_ne_two hp hp2 fun _ hτ =>
    isCoatom_or_fixed_psl2FieldAut_even_odd hp hp2 hexc hchar hτ

theorem fieldAutData_psl2_odd_prime {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hodd : ringChar F ≠ 2) : FieldAutData (PSL2 F) p :=
  fieldAutData_psl2_of_ne_two hp hp2 fun _ hτ => Or.inl (isCoatom_fixed_psl2FieldAut hp hp2 hodd hτ)

end Even

section Main

theorem exists_noncomm_of_perfect {G : Type*} [Group G] [Nontrivial G] (h : commutator G = ⊤) :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hbot : commutator G = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro x _
    exact hcon x g
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  have hx' : x ∈ (⊥ : Subgroup G) := hbot ▸ h ▸ Subgroup.mem_top x
  exact hx (Subgroup.mem_bot.mp hx')


theorem planeGen_outer_A1 {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.A 1 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hex : ¬ IsD2SeitzException p (.A 1 q))
    {E : Subgroup (MulAut (Cat ⟨.A 1 q, hv⟩))} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hout : ¬ InnerPlane ⟨.A 1 q, hv⟩ p E) : PlaneGen E := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Fact p.Prime := ⟨hp⟩
  let e : Cat ⟨.A 1 q, hv⟩ ≃* PSL2 (GaloisField q.p q.exponent) :=
    CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have h4 : 4 ≤ q.card := hrange.2 rfl
  have hfour : 3 ≤ 2 ∨ ∃ s : Finset (GaloisField q.p q.exponent), s.card = 4 := by
    right
    have : Fintype (GaloisField q.p q.exponent) := Fintype.ofFinite _
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ :
      Finset (GaloisField q.p q.exponent))) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcardF]; exact h4)
    exact ⟨s, hs⟩
  obtain ⟨hnt, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (n := 2)
    (K := GaloisField q.p q.exponent) le_rfl hfour
  have hperf := (CFSG.LinearGroups.linear_projective_perfect (n := 2)
    (K := GaloisField q.p q.exponent) le_rfl hfour).commutator_eq_top
  have hnab : ∃ a b : PSL2 (GaloisField q.p q.exponent), a * b ≠ b * a :=
    exists_noncomm_of_perfect hperf
  have hd : FieldAutData (PSL2 (GaloisField q.p q.exponent)) p := by
    by_cases hchar : ringChar (GaloisField q.p q.exponent) = 2
    · refine fieldAutData_psl2_even_odd_prime hp hp2 ?_ hchar
      rintro ⟨hp3, h8⟩
      apply hex
      have hq2 : q.p = 2 := by
        rw [← hchar]
        exact (ringChar.eq (GaloisField q.p q.exponent) q.p).symm
      refine Or.inl ⟨hp3, Or.inl ⟨q, hq2, ?_, rfl⟩⟩
      rw [hcardF, TauCeti.PrimePower.card_def, hq2] at h8
      exact Nat.pow_right_injective (le_refl 2) (by simpa using h8)
    · exact fieldAutData_psl2_odd_prime hp hp2 hchar
  have hEi : CFSG.IsElementaryAbelian p (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
    rw [card_map_congr, hc]
  have hout' : ¬ ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h
    exact not_le_range_conj_map_congr e hout fun φ hφ => (h φ hφ).imp fun g hg => hg.symm
  have hclos := closure_fixUnion_eq_top_of_fieldAutData hnab hp hd
    (E.map (MulAut.congr e).toMonoidHom) hc' hout'
  exact planeGen_of_outer_model e ((planeGen_iff_closure_fixUnion _).mpr hclos)

theorem seitzOuter_A1 :
    SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ ∃ q, d.1 = .A 1 q := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, q, hd⟩
  subst hd
  exact planeGen_outer_A1 hv hp hp2 hex hE hc hout

end Main

end CFSG.LieType.SeitzGeneration
