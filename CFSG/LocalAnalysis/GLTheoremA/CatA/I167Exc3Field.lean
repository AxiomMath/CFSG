module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167FieldDict
import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcFieldGen
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerBase
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Timmesfeld

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem exc3_arith {e f : ℕ} (hef : e ∣ f) (h3 : 3 ∣ 2 ^ f + 1) : 3 ∣ 2 ^ e + 1 := by
  obtain ⟨m, rfl⟩ := hef
  have hne : ¬ 3 ∣ 2 ^ e := fun h => by
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    omega
  have hmod : (2 ^ e) % 3 = 1 ∨ (2 ^ e) % 3 = 2 := by omega
  rcases hmod with h1 | h2
  · exfalso
    have : (2 ^ (e * m)) % 3 = 1 := by
      rw [pow_mul, Nat.pow_mod, h1, one_pow]
      norm_num
    omega
  · omega

section Certs


theorem exc3_fieldRel {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp 3 B X D J x) {f : ℕ}
    (hJ : catalogIs (PSimple 3 J) (T167Idx f)) {k : DefChar.LieFamily} {qc : TauCeti.PrimePower}
    {hv : (LocalTwo.excIndex k qc).Valid}
    (hk : k = .F4 ∨ k = .E6 ∨ k = .twistedE6 ∨ k = .E7 ∨ k = .E8) (hqc : qc.p = 2)
    (eE : PSimple 3 X ≃* LocalTwo.CatT ⟨LocalTwo.excIndex k qc, hv⟩) : qc.exponent ∣ f := by
  have hd : (LocalTwo.excIndex k qc).characteristic = 2 := by
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact (TauCeti.LieTypeIndex.characteristic_F4 qc).trans hqc
    · exact (TauCeti.LieTypeIndex.characteristic_E6 qc).trans hqc
    · exact (TauCeti.LieTypeIndex.characteristic_twistedE6 qc).trans hqc
    · exact (TauCeti.LieTypeIndex.characteristic_E7 qc).trans hqc
    · exact (TauCeti.LieTypeIndex.characteristic_E8 qc).trans hqc
  have hgen : ∃ e : ℕ, 2 ^ e = KD264Lie.fieldSize (LocalTwo.excIndex k qc) ∧ e ∣ f := by
    obtain ⟨iJ, hiJ, ⟨eJ'⟩⟩ := hJ
    rcases hiJ with ⟨hf1, n, -, hn5, hi⟩ | ⟨hf1, n, -, hn6, hi⟩ | ⟨n, -, hn3, hnk, hk1, -, hi⟩
    · exact exc_fieldRel_of_lieModel (d := ⟨LocalTwo.excIndex k qc, hv⟩) H hd eE
        (hf1.symm ▸ fld_lieModel_of_isLnA hn5 ⟨iJ, hi, ⟨eJ'⟩⟩)
    · exact exc_fieldRel_of_lieModel (d := ⟨LocalTwo.excIndex k qc, hv⟩) H hd eE
        (hf1.symm ▸ fld_lieModel_of_isOmMA (by omega) ⟨iJ, hi, ⟨eJ'⟩⟩)
    · rcases fld_lieModel_of_isOmPA hk1 hn3 hnk ⟨iJ, hi, ⟨eJ'⟩⟩ with ⟨-, hm⟩ | ⟨-, -, hm⟩
      · exact exc_fieldRel_of_lieModel (d := ⟨LocalTwo.excIndex k qc, hv⟩) H hd eE hm
      · exact exc_fieldRel_of_lieModel (d := ⟨LocalTwo.excIndex k qc, hv⟩) H hd eE hm
  obtain ⟨e, he, hef⟩ := hgen
  have hfs : KD264Lie.fieldSize (LocalTwo.excIndex k qc) = 2 ^ qc.exponent := by
    have hc : qc.card = 2 ^ qc.exponent := by rw [TauCeti.PrimePower.card_def, hqc]
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> exact hc
  have hee : e = qc.exponent := Nat.pow_right_injective le_rfl (he.trans hfs)
  exact hee ▸ hef

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I167

end
