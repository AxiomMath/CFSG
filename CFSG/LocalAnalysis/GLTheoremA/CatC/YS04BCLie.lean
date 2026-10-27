module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04BCRes
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Easy
public import CFSG.Models.Transport
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier


theorem exc_blueprint {S : Type} [Group S] {d : ValidLieTypeIndex} {t : StatedLieTag} {p f : ℕ}
    (e : S ≃* (CFSGIndex.lie d).Group) (h : StatedLieAdmissible t 0 p f)
    (hd : CFSG.Models.NamesTag d.1 t p f) : CFSG.Blueprint.LieModel S t 0 p f :=
  blueprintLieModel_of_models (CFSG.Models.LieModel.of_mulEquiv e.symm (lieModel_lie h d hd))

theorem qEps_card_true (qq : PrimePower) : qEps true qq.card = qq.p ^ qq.exponent - 1 := by
  simp [qEps, PrimePower.card_def]

theorem qEps_card_false (qq : PrimePower) : qEps false qq.card = qq.p ^ qq.exponent + 1 := by
  simp [qEps, PrimePower.card_def]

theorem bc_lie_case (hL : KD26bcLinUni) (hD4 : KD26bcD4) (hE6 : KD26bcE6)
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (d : ValidLieTypeIndex)
    (e : S ≃* (CFSGIndex.lie d).Group) (D : Subgroup (MulAut S)) (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 2) (hinn : D ⊓ inner S = ⊥) :
    ∃ y ∈ D, y ≠ 1 ∧ ∃ L : Subgroup S, L ≤ fixSub y ∧ IsSimpleGroup ↥L ∧
      (∃ a b : ↥L, a * b ≠ b * a) ∧ p ∣ Nat.card L ∧
      ∀ g ∈ fixSub y, ∀ x ∈ L, g * x * g⁻¹ ∈ L := by
  obtain ⟨d, hv⟩ := d
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  cases d with
  | A r qq =>
    have hm : CFSG.Blueprint.LieModel S .PSL (r + 1) qq.p qq.exponent :=
      blueprintLieModel_of_models (CFSG.Models.LieModel.of_mulEquiv e.symm (lieModel_typeA r qq hv))
    have hLn : IsLnEps S (r + 1) qq.card true := ⟨CFSGIndex.lie ⟨.A r qq, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩
    by_cases hdiv : p ∣ Nat.gcd (r + 1) (qEps true qq.card)
    · by_cases hsq : p ^ 2 ∣ Nat.gcd (r + 1) (qEps true qq.card)
      · exact hL S hs hna (r + 1) qq.card true hLn p hp hp2 hdiv hsq D hD hcard hinn
      · exact (false_of_le_mul hp hcard hinn (YS04F.kd26f_psl hLn hp hp2 hdiv hsq D hD)).elim
    · exact (false_of_outPChain hp (outPChain_of_lieModel hp hp2 hm (fun _ => by rw [← qEps_card_true]; exact hdiv)) D hD hcard
        hinn).elim
  | twistedA r qq =>
    have hm : CFSG.Blueprint.LieModel S .PSU (r + 1) qq.p qq.exponent :=
      blueprintLieModel_of_models (lieModel_of_classical
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r qq hv e))
    have hLn : IsLnEps S (r + 1) qq.card false := ⟨CFSGIndex.lie ⟨.twistedA r qq, hv⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩
    by_cases hdiv : p ∣ Nat.gcd (r + 1) (qEps false qq.card)
    · by_cases hsq : p ^ 2 ∣ Nat.gcd (r + 1) (qEps false qq.card)
      · exact hL S hs hna (r + 1) qq.card false hLn p hp hp2 hdiv hsq D hD hcard hinn
      · exact (false_of_le_mul hp hcard hinn (YS04F.kd26f_psu hLn hp hp2 hdiv hsq D hD)).elim
    · exact (false_of_outPChain hp (outPChain_of_lieModel hp hp2 hm
        (show ¬ p ∣ Nat.gcd (r + 1) (qq.p ^ qq.exponent + 1) by
          rw [← qEps_card_false]; exact hdiv)) D hD hcard hinn).elim
  | B r qq =>
    have hr : 2 ≤ r := hrange.1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact (false_of_outPChain hp (outPChain_of_lieModel hp hp2
        (blueprintLieModel_of_models (lieModel_of_classical
          (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 qq hv e))) trivial) D hD hcard
        hinn).elim
    · by_cases hpq : qq.p = 2
      · exact (false_of_outPChain hp (outPChain_of_lieModel hp hp2
          (blueprintLieModel_of_models (lieModel_of_classical
            (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r qq hv hpq hr3 e)))
          trivial) D hD hcard hinn).elim
      · exact (false_of_outPChain hp (outPChain_of_lieModel hp hp2
          (blueprintLieModel_of_models (lieModel_of_classical
            (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r qq hv hpq hr3 e)))
          trivial) D hD hcard hinn).elim
  | C r qq =>
    exact (false_of_outPChain hp (outPChain_of_lieModel hp hp2
      (blueprintLieModel_of_models (lieModel_of_classical
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r qq hv e))) trivial) D hD hcard
      hinn).elim
  | D r qq =>
    by_cases h4 : r = 4
    · subst h4
      have hm : CFSG.Blueprint.LieModel S .POmegaPlus 4 qq.p qq.exponent :=
        blueprintLieModel_of_models (lieModel_of_classical
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD 4 qq hv e))
      by_cases hp3 : p = 3
      · subst hp3
        exact hD4 S hs hna qq.card ⟨CFSGIndex.lie ⟨.D 4 qq, hv⟩, rfl, ⟨e⟩⟩ D hD hcard hinn
      · exact (false_of_outPChain hp (outPChain_of_lieModel hp hp2 hm
          (fun _ => three_lt_of_ne hp hp2 hp3)) D hD hcard hinn).elim
    · have hm : CFSG.Blueprint.LieModel S .POmegaPlus r qq.p qq.exponent :=
        blueprintLieModel_of_models (lieModel_of_classical
          (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r qq hv e))
      exact (false_of_outPChain hp (outPChain_of_lieModel hp hp2 hm (fun h => absurd h h4)) D hD
        hcard hinn).elim
  | twistedD r qq =>
    exact (false_of_outPChain hp (outPChain_of_lieModel hp hp2
      (blueprintLieModel_of_models (lieModel_of_classical
        (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r qq hv e))) trivial) D hD
      hcard hinn).elim
  | E6 qq =>
    have hm : CFSG.Blueprint.LieModel S .E6 0 qq.p qq.exponent :=
      exc_blueprint e (t := .E6) ⟨qq.prime_p, qq.exponent_pos, rfl⟩ ⟨rfl, rfl⟩
    by_cases hp3 : p = 3
    · subst hp3
      by_cases hdiv : 3 ∣ qEps true qq.card
      · exact hE6 S hs hna qq.card true ⟨CFSGIndex.lie ⟨.E6 qq, hv⟩, rfl, ⟨e⟩⟩ hdiv D hD hcard hinn
      · exact (false_of_outPChain hp (outPChain_of_lieModel hp hp2 hm (Or.inr (Or.inl (by rw [← qEps_card_true]; exact hdiv)))) D hD
          hcard hinn).elim
    · exact (false_of_outPChain hp (outPChain_of_lieModel hp hp2 hm (Or.inl hp3)) D hD hcard
        hinn).elim
  | twistedE6 qq =>
    have hm : CFSG.Blueprint.LieModel S .twistedE6 0 qq.p qq.exponent :=
      exc_blueprint e (t := .twistedE6) ⟨qq.prime_p, qq.exponent_pos, rfl⟩ ⟨rfl, rfl⟩
    by_cases hp3 : p = 3
    · subst hp3
      by_cases hdiv : 3 ∣ qEps false qq.card
      · exact hE6 S hs hna qq.card false ⟨CFSGIndex.lie ⟨.twistedE6 qq, hv⟩, rfl, ⟨e⟩⟩ hdiv D hD
          hcard hinn
      · exact (false_of_outPChain hp (outPChain_of_lieModel hp hp2 hm (Or.inr (Or.inl (by rw [← qEps_card_false]; exact hdiv)))) D hD
          hcard hinn).elim
    · exact (false_of_outPChain hp (outPChain_of_lieModel hp hp2 hm (Or.inl hp3)) D hD hcard
        hinn).elim
  | E7 qq =>
    exact (false_of_outPChain hp (outPChain_of_lieModel hp hp2
      (exc_blueprint e (t := .E7) ⟨qq.prime_p, qq.exponent_pos, rfl⟩ ⟨rfl, rfl⟩) trivial) D hD hcard
      hinn).elim
  | E8 qq =>
    exact (false_of_outPChain hp (outPChain_of_lieModel hp hp2
      (exc_blueprint e (t := .E8) ⟨qq.prime_p, qq.exponent_pos, rfl⟩ ⟨rfl, rfl⟩) trivial) D hD hcard
      hinn).elim
  | F4 qq =>
    exact (false_of_outPChain hp (outPChain_of_lieModel hp hp2
      (exc_blueprint e (t := .F4) ⟨qq.prime_p, qq.exponent_pos, rfl⟩ ⟨rfl, rfl⟩) trivial) D hD hcard
      hinn).elim
  | G2 qq =>
    have h3q : 3 ≤ qq.p ^ qq.exponent := by simpa only [PrimePower.card_def] using hrange
    exact (false_of_outPChain hp (outPChain_of_lieModel hp hp2
      (exc_blueprint e (t := .G2) ⟨qq.prime_p, qq.exponent_pos, rfl, h3q⟩ ⟨rfl, rfl⟩) trivial) D hD
      hcard hinn).elim
  | trialityD4 qq =>
    exact (false_of_outPChain hp (outPChain_of_lieModel hp hp2
      (exc_blueprint e (t := .trialityD4) ⟨qq.prime_p, qq.exponent_pos, rfl⟩ ⟨rfl, rfl⟩) trivial) D hD
      hcard hinn).elim
  | suzuki m =>
    have hm1 : 1 ≤ m := hrange
    exact (false_of_outPChain hp (outPChain_of_lieModel hp hp2
      (exc_blueprint e (t := .twistedB2) (p := 2) (f := 2 * m + 1)
        ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨rfl, rfl⟩) trivial) D hD hcard
      hinn).elim
  | reeG2 m =>
    have hm1 : 1 ≤ m := hrange
    exact (false_of_outPChain hp (outPChain_of_lieModel hp hp2
      (exc_blueprint e (t := .twistedG2) (p := 3) (f := 2 * m + 1)
        ⟨Nat.prime_three, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨rfl, rfl⟩) trivial) D hD hcard
      hinn).elim
  | reeF4 m =>
    have hm1 : 1 ≤ m := hrange
    exact (false_of_outPChain hp (outPChain_of_lieModel hp hp2
      (exc_blueprint e (t := .twistedF4) (p := 2) (f := 2 * m + 1)
        ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨rfl, rfl⟩) trivial) D hD hcard
      hinn).elim
  | tits =>
    exact (false_of_outPChain hp (outPChain_of_lieModel hp hp2
      (exc_blueprint e (t := .Tits) (p := 2) (f := 1) ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩) trivial) D hD hcard hinn).elim

end CFSG.LocalAnalysis.GLTheoremA
