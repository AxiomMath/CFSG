module

public import CFSG.GH74.Generic.BProg.B2.T4PGVTBasic
import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4L3U3

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.PGV

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint Subgroup

theorem q3In_l3 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hf : Odd f) :
    Q3EmptyIn (fun X _ => LieModel X .PSL 3 p f) := by
  intro N _ _ H t K hs htH hH
  have hst := PumpupTableBasic.stated_of_lieModel (Or.inl rfl) hH
  obtain ⟨S, hInv⟩ := CFSG.GH74.GLS.IVK.exists_invData_lin hp hp2 h5 hf hst (⟨t, htH⟩ : ↥H)
    (Subtype.ext hs.mul_self) (fun h => hs.ne_one (congrArg Subtype.val h))
  exact PumpupTableL3.false_of_invData hs.comp htH hs.two hInv

theorem q3In_u3 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) :
    Q3EmptyIn (fun X _ => LieModel X .PSU 3 p f) := by
  intro N _ _ H t K hs htH hH
  have hst := PumpupTableBasic.stated_of_lieModel (Or.inr rfl) hH
  obtain ⟨S, hInv⟩ := ((CFSG.GH74.Generic.S3.libData_uni hp hp2 h5) ↥H hst).1 (⟨t, htH⟩ : ↥H)
    (Subtype.ext hs.mul_self) (fun h => hs.ne_one (congrArg Subtype.val h))
  exact PumpupTableL3.false_of_invData hs.comp htH hs.two hInv

end CFSG.GH74.Generic.BProg.B2.T4.PGV
