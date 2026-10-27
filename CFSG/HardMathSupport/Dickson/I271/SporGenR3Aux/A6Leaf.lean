module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SporRec
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Primitive
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationTwelveOut

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

section Alt6

theorem alt6_isSimpleGroup : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem alt6_nonabelian : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  haveI := alt6_isSimpleGroup
  letI : CommGroup (alternatingGroup (Fin 6)) :=
    { (inferInstance : Group (alternatingGroup (Fin 6))) with mul_comm := hc }
  have hp := IsSimpleGroup.prime_card (α := alternatingGroup (Fin 6))
  rw [Nat.card_eq_fintype_card, card_alternatingGroup] at hp
  norm_num [Nat.factorial] at hp

theorem alt6_center_eq_bot : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ := by
  haveI := alt6_isSimpleGroup
  obtain ⟨a, b, hab⟩ := alt6_nonabelian
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (alternatingGroup (Fin 6)))
    with h | h
  · exact h
  · exfalso
    exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)

theorem alt6_isQuasisimple : CFSG.Open.IsQuasisimple (alternatingGroup (Fin 6)) := by
  haveI := alt6_isSimpleGroup
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (alternatingGroup (Fin 6)))
      with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := alt6_nonabelian
      have h1 : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.1 h1)
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq alt6_center_eq_bot).trans
      QuotientGroup.quotientBot).isSimpleGroup

theorem three_dvd_card_alt6 : 3 ∣ Nat.card (alternatingGroup (Fin 6)) := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  norm_num [Nat.factorial]

theorem rkAut_three_alt6 : RkAut 3 (alternatingGroup (Fin 6)) := by
  refine rkAut_of_simple Nat.prime_three alt6_center_eq_bot ?_ ⟨CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.F06, ?_, ?_⟩
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      (CFSG.Quasithin.A10.three_not_dvd_card_outer (MulEquiv.refl _))
  · exact CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.isElemAbelian_F06
  · exact CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.card_F06

end Alt6

section Equiv

variable {J : Type} [Group J]

theorem isQuasisimple_of_equiv_alt6 (e : J ≃* alternatingGroup (Fin 6)) :
    CFSG.Open.IsQuasisimple J :=
  isQuasisimple_of_mulEquiv' e.symm alt6_isQuasisimple

theorem center_eq_bot_of_equiv_alt6 (e : J ≃* alternatingGroup (Fin 6)) :
    Subgroup.center J = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  apply e.injective
  rw [map_one]
  have : e z ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff]
    intro b
    have h := Subgroup.mem_center_iff.1 hz (e.symm b)
    have h2 := congrArg e h
    simpa using h2
  rw [alt6_center_eq_bot] at this
  exact this

theorem glaPPrimeCore_three_eq_bot_of_equiv_alt6 (e : J ≃* alternatingGroup (Fin 6)) [Finite J] :
    GLAPPrimeCore 3 J = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsSimpleGroup J := e.isSimpleGroup_congr.2 alt6_isSimpleGroup
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 J)) :=
    CFSG.pPrimeCore_coprime_card (p := 3) (G := J)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 J) with h | h
  · exact h
  · exfalso
    have h3 : 3 ∣ Nat.card J := by
      rw [Nat.card_congr e.toEquiv]
      exact three_dvd_card_alt6
    rw [h, Subgroup.card_top] at hcop
    exact absurd (hcop.eq_one_of_dvd h3) (by norm_num)

end Equiv

section Shape

variable {Q : Type} [Group Q] [Finite Q]

noncomputable def pQuotEquivAlt6 (L : Subgroup Q) (eL : ↥L ≃* alternatingGroup (Fin 6)) :
    PQuot 3 L ≃* alternatingGroup (Fin 6) :=
  ((QuotientGroup.quotientMulEquivOfEq
    (glaPPrimeCore_three_eq_bot_of_equiv_alt6 eL)).trans QuotientGroup.quotientBot).trans eL

noncomputable def pSimpleEquivAlt6 (L : Subgroup Q) (eL : ↥L ≃* alternatingGroup (Fin 6)) :
    PSimple 3 L ≃* alternatingGroup (Fin 6) :=
  (QuotientGroup.congr _ _ (pQuotEquivAlt6 L eL)
    (Subgroup.map_center_eq (pQuotEquivAlt6 L eL))).trans
    ((QuotientGroup.quotientMulEquivOfEq alt6_center_eq_bot).trans QuotientGroup.quotientBot)

theorem shapeRkAt_alt6_of_normal {t : Q} (E : Subgroup ↥(Subgroup.centralizer ({t} : Set Q)))
    [E.Normal] (eE : ↥E ≃* alternatingGroup (Fin 6))
    (hq : Nat.card (↥(Subgroup.centralizer ({t} : Set Q)) ⧸ E) = 9) :
    ShapeRkAt 3 (IsA6At 3) (RkAut 3) t := by
  let L : Subgroup Q := E.map (Subgroup.centralizer ({t} : Set Q)).subtype
  have eEL : ↥E ≃* ↥L := E.equivMapOfInjective _ (Subgroup.centralizer ({t} : Set Q)).subtype_injective
  have eL : ↥L ≃* alternatingGroup (Fin 6) := eEL.symm.trans eE
  have hLC : L ≤ Subgroup.centralizer ({t} : Set Q) := Subgroup.map_subtype_le E
  have hLn : ∀ g ∈ Subgroup.centralizer ({t} : Set Q), ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    rintro g hg _ ⟨e, he, rfl⟩
    exact ⟨⟨g, hg⟩ * e * ⟨g, hg⟩⁻¹, ‹E.Normal›.conj_mem e he ⟨g, hg⟩, rfl⟩
  have hpL : 3 ∣ Nat.card ↥L := by
    rw [Nat.card_congr eL.toEquiv]
    exact three_dvd_card_alt6
  have hcent : IsPGroup 3 ↥(Subgroup.centralizer ({t} : Set Q) ⊓ Subgroup.centralizer (L : Set Q)) := by
    let ι : ↥(Subgroup.centralizer ({t} : Set Q) ⊓ Subgroup.centralizer (L : Set Q)) →*
        ↥(Subgroup.centralizer ({t} : Set Q)) := Subgroup.inclusion inf_le_left
    let f : ↥(Subgroup.centralizer ({t} : Set Q) ⊓ Subgroup.centralizer (L : Set Q)) →*
        ↥(Subgroup.centralizer ({t} : Set Q)) ⧸ E := (QuotientGroup.mk' E).comp ι
    have hf : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro z hz
      have hzE : ι z ∈ E := (QuotientGroup.eq_one_iff _).1 hz
      have hzL : (z : Q) ∈ L := ⟨ι z, hzE, rfl⟩
      let ζ : ↥L := ⟨(z : Q), hzL⟩
      have hζ : eL ζ = 1 := by
        have hcen : eL ζ ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
          rw [Subgroup.mem_center_iff]
          intro b
          have hb : (eL.symm b : Q) ∈ L := (eL.symm b).2
          have h1 : (eL.symm b : Q) * (z : Q) = (z : Q) * (eL.symm b : Q) :=
            Subgroup.mem_centralizer_iff.1 z.2.2 _ hb
          have h2 : eL.symm b * ζ = ζ * eL.symm b := Subtype.ext h1
          have h3 := congrArg eL h2
          simpa using h3
        rw [alt6_center_eq_bot] at hcen
        exact hcen
      have hζ1 : ζ = 1 := eL.injective (by rw [hζ, map_one])
      have h4 : (z : Q) = 1 := congrArg (fun x : ↥L => (x : Q)) hζ1
      exact Subtype.ext h4
    have hp9 : IsPGroup 3 (↥(Subgroup.centralizer ({t} : Set Q)) ⧸ E) := IsPGroup.of_card (n := 2) (by rw [hq]; norm_num)
    exact hp9.of_injective f hf
  refine shapeRkAt_of_normal_quasisimple Nat.prime_three hLC hLn
    (isQuasisimple_of_equiv_alt6 eL) hpL hcent ⟨rfl, ⟨pSimpleEquivAlt6 L eL⟩⟩ ?_
  exact rkAut_of_equiv (pQuotEquivAlt6 L eL).symm rkAut_three_alt6

end Shape

end CFSG.HardMathSupport.Dickson.I271
