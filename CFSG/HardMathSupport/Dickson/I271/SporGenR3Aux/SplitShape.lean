module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.CoverA6

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.Yardstones.Md0ec50421ce4

section Normal

variable {Q : Type} [Group Q] [Finite Q]

theorem splitShape_alt6_of_normal {t : Q}
    (E : Subgroup ↥(Subgroup.centralizer ({t} : Set Q))) [E.Normal]
    (eE : ↥E ≃* alternatingGroup (Fin 6)) (hq : IsPGroup 3 (↥(Subgroup.centralizer ({t} : Set Q)) ⧸ E))
    (hsplit : A6Split3 (E.map (Subgroup.centralizer ({t} : Set Q)).subtype)) :
    ∃ J : Subgroup Q, GLAPComponent 3 (Subgroup.centralizer ({t} : Set Q)) J ∧
      (∀ I : Subgroup Q, GLAPComponent 3 (Subgroup.centralizer ({t} : Set Q)) I → I = J) ∧
      SplitGoodAt 3 J := by
  let L : Subgroup Q := E.map (Subgroup.centralizer ({t} : Set Q)).subtype
  have eEL : ↥E ≃* ↥L :=
    E.equivMapOfInjective _ (Subgroup.centralizer ({t} : Set Q)).subtype_injective
  have eL : ↥L ≃* alternatingGroup (Fin 6) := eEL.symm.trans eE
  have hLC : L ≤ Subgroup.centralizer ({t} : Set Q) := Subgroup.map_subtype_le E
  have hLn : ∀ g ∈ Subgroup.centralizer ({t} : Set Q), ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    rintro g hg _ ⟨e, he, rfl⟩
    exact ⟨⟨g, hg⟩ * e * ⟨g, hg⟩⁻¹, ‹E.Normal›.conj_mem e he ⟨g, hg⟩, rfl⟩
  have hpL : 3 ∣ Nat.card ↥L := by
    rw [Nat.card_congr eL.toEquiv]
    exact three_dvd_card_alt6
  have hcent : IsPGroup 3
      ↥(Subgroup.centralizer ({t} : Set Q) ⊓ Subgroup.centralizer (L : Set Q)) := by
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
    exact hq.of_injective f hf
  have hLq : CFSG.Open.IsQuasisimple ↥L := isQuasisimple_of_equiv_alt6 eL
  have hcore := glaPPrimeCore_eq_bot_of_normal_quasisimple Nat.prime_three hLC hLn hLq hpL hcent
  refine ⟨L, glaPComponent_of_normal_quasisimple hLC hLn hLq hcore,
    fun I hI => eq_of_glaPComponent_of_normal_quasisimple Nat.prime_three hLC hLn hLq hcore hcent hI,
    Or.inr ⟨⟨rfl, ⟨pSimpleEquivAlt6 L eL⟩⟩, hsplit⟩⟩

end Normal

end CFSG.HardMathSupport.Dickson.I271
