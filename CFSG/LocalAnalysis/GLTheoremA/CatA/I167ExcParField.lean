module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcFieldGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167FieldDict

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Timmesfeld

variable {Ω : Type} [Group Ω] [Finite Ω]


theorem exc_fieldRel {p : ℕ} {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x) {n k : ℕ}
    (hn : 3 ≤ n) (hk : 1 ≤ k) (hnk : k = 1 → 5 ≤ n) (hJ : catalogIs (PSimple p J) (isOmPA n (2 ^ k)))
    {kf : DefChar.LieFamily} (hkf : kf = .F4 ∨ kf = .E6 ∨ kf = .twistedE6 ∨ kf = .E7 ∨ kf = .E8)
    {qc : TauCeti.PrimePower} (hqc : qc.p = 2) {hv : (LocalTwo.excIndex kf qc).Valid}
    (hcat : Nonempty (PSimple p X ≃* LocalTwo.CatT ⟨LocalTwo.excIndex kf qc, hv⟩)) :
    qc.exponent ∣ k := by
  have hd : (LocalTwo.excIndex kf qc).characteristic = 2 := by
    rcases hkf with rfl | rfl | rfl | rfl | rfl
    · exact (TauCeti.LieTypeIndex.characteristic_F4 qc).trans hqc
    · exact (TauCeti.LieTypeIndex.characteristic_E6 qc).trans hqc
    · exact (TauCeti.LieTypeIndex.characteristic_twistedE6 qc).trans hqc
    · exact (TauCeti.LieTypeIndex.characteristic_E7 qc).trans hqc
    · exact (TauCeti.LieTypeIndex.characteristic_E8 qc).trans hqc
  obtain ⟨eE⟩ := hcat
  have hkey : ∃ e : ℕ, 2 ^ e = KD264Lie.fieldSize (LocalTwo.excIndex kf qc) ∧ e ∣ k := by
    rcases fld_lieModel_of_isOmPA hk hn hnk hJ with ⟨-, hm⟩ | ⟨-, -, hm⟩
    · exact exc_fieldRel_of_lieModel (d := ⟨LocalTwo.excIndex kf qc, hv⟩) H hd eE hm
    · exact exc_fieldRel_of_lieModel (d := ⟨LocalTwo.excIndex kf qc, hv⟩) H hd eE hm
  obtain ⟨e, he, hek⟩ := hkey
  have hfs : KD264Lie.fieldSize (LocalTwo.excIndex kf qc) = 2 ^ qc.exponent := by
    have hc : qc.card = 2 ^ qc.exponent := by rw [TauCeti.PrimePower.card_def, hqc]
    rcases hkf with rfl | rfl | rfl | rfl | rfl <;> exact hc
  have hee : e = qc.exponent := Nat.pow_right_injective le_rfl (he.trans hfs)
  exact hee ▸ hek

end CFSG.LocalAnalysis.GLTheoremA.I167

end

