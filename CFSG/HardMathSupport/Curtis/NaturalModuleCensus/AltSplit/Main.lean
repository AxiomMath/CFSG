module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltSplit.Defs
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltSplit.Classical
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltSplit.Unitary
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltSplit.SpinMinus
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltSplit.G2
import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
import CFSG.RankThree.PartOne.N143.Inspect613Even

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank

variable {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y} {p : ℕ}

theorem dvd_two_pow_sub_one_of_split {q : TauCeti.PrimePower} (hd : q.p = 2 ∧ p ∣ q.card - 1) :
    p ∣ 2 ^ q.exponent - 1 := by
  have := hd.2
  rwa [TauCeti.PrimePower.card_def, hd.1] at this

theorem false_of_altSq_split_A (h : CompParabE L J) (hp : p = 5 ∨ p = 7)
    (hAlt : PerfectSectionsAltSq p J) {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A r q).Valid) (hd : q.p = 2 ∧ p ∣ q.card - 1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group) : False := by
  have hm := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
  rw [hd.1] at hm
  exact false_of_altSq_split_psl h hp hAlt hm (dvd_two_pow_sub_one_of_split hd)

theorem false_of_altSq_split_twistedA (h : CompParabE L J) (hp : p = 5 ∨ p = 7)
    (hAlt : PerfectSectionsAltSq p J) {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hd : q.p = 2 ∧ p ∣ q.card - 1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group) :
    False := by
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  rw [hd.1] at hm
  exact false_of_altSq_split_psu h hp hAlt hm (dvd_two_pow_sub_one_of_split hd)

theorem false_of_altSq_split_B (h : CompParabE L J) (hp : p = 5 ∨ p = 7)
    (hAlt : PerfectSectionsAltSq p J) {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hd : q.p = 2 ∧ p ∣ q.card - 1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group) : False := by
  have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
  have hm : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp r 2 q.exponent := by
    by_cases h2 : r = 2
    · subst h2
      have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      rwa [hd.1] at hm
    · have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd.1
        (by omega) e
      rwa [hd.1] at hm
  exact false_of_altSq_split_psp h hp hAlt hm (dvd_two_pow_sub_one_of_split hd)

theorem false_of_altSq_split_D (h : CompParabE L J) (hp : p = 5 ∨ p = 7)
    (hAlt : PerfectSectionsAltSq p J) {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.D r q).Valid) (hd : q.p = 2 ∧ p ∣ q.card - 1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩).Group) : False := by
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd.1 e
  rw [hd.1] at hm
  exact false_of_altSq_split_pomegaPlus h hp hAlt hm (dvd_two_pow_sub_one_of_split hd)

theorem false_of_altSq_split_twistedD (h : CompParabE L J) (hp : p = 5 ∨ p = 7)
    (hAlt : PerfectSectionsAltSq p J) {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) (hd : q.p = 2 ∧ p ∣ q.card - 1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group) :
    False := by
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd.1 e
  rw [hd.1] at hm
  exact false_of_altSq_split_pomegaMinus h hp hAlt hm (dvd_two_pow_sub_one_of_split hd)

section Certificates


open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem false_of_altSq_split_G2 (h : CompParabE L J) (hp : p = 5 ∨ p = 7)
    (hAlt : PerfectSectionsAltSq p J) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (hd : q.p = 2 ∧ p ∣ q.card - 1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) : False := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd.1
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [TauCeti.PrimePower.card_def, GaloisField.card q.p q.exponent q.exponent_pos.ne']
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hd.1
    (GaloisField q.p q.exponent) hK
  have hc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hd.1]
  exact false_of_altSq_split_g2_field h hp hAlt (K := GaloisField q.p q.exponent)
    (f := q.exponent) q.exponent_pos (by rw [hK, hc]) (e.trans b.symm)
    (by rw [hK]; exact hd.2)

theorem false_of_altSq_split (h : CompParabE L J) (hp : p = 5 ∨ p = 7)
    (hAlt : PerfectSectionsAltSq p J)
    (hX : IsLieOf (IdxSplit p) (↥L ⧸ Subgroup.center ↥L)) : False := by
  obtain ⟨d, hd, ⟨e⟩⟩ := hX
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q => exact false_of_altSq_split_A h hp hAlt hv hd e
  | twistedA r q => exact false_of_altSq_split_twistedA h hp hAlt hv hd e
  | B r q => exact false_of_altSq_split_B h hp hAlt hv hd e
  | D r q => exact false_of_altSq_split_D h hp hAlt hv hd e
  | twistedD r q => exact false_of_altSq_split_twistedD h hp hAlt hv hd e
  | G2 q => exact false_of_altSq_split_G2 h hp hAlt hv hd e
  | _ => exact hd.elim

end Certificates

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
