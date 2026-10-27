module

public import CFSG.GH74.QTGen4.DSGen4.Main
public import CFSG.GH74.QTGen4.DSGen4.OpenLeavesAmal

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

theorem dsAAmal_F4_of_leaves
    (hNF : LeafDSANoField) (hZS : LeafZiStructure) (hS3 : LeafDSACaseIIStep3)
    (hS4 : LeafDSACaseIIStep4) (hSt4 : LeafDSACaseIStep4) (hModel : LeafL34Model)
    (hLocal : LeafL34Local) (hGlue : LeafL34Glue) : DSAAmal_F4 := by
  intro G _ _ L1 L2 S hyp _hq hS hns1 hns2
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hyp
  have h : DSAHyp L1 L2 S := ⟨hR, hns1, hns2, hS⟩
  obtain ⟨c1, c2⟩ := dsA_caseI_of_leaves hNF hZS hS3 hS4 h
  obtain ⟨Mdl, hMdl⟩ := hModel
  obtain ⟨ψ₁, ψ₂, hS1, hS2, hB1, hB2, hQ1, hQ2⟩ := hLocal Mdl hMdl h c1 c2
  obtain ⟨hQQ, hS64, ⟨hQ1e, hQ1c⟩, ⟨hQ2e, hQ2c⟩⟩ := hSt4 h c1 c2
  have hQ1S : dsQ L1 L2 S ≤ S := le_sup_left.trans hQQ.le
  have hQ2S : dsQ L2 L1 S ≤ S := le_sup_right.trans hQQ.le
  have hne : dsQ L1 L2 S ≠ dsQ L2 L1 S := by
    intro heq
    rw [heq, sup_idem] at hQQ
    have hcard : Nat.card ↥(dsQ L2 L1 S) = Nat.card ↥S := by rw [hQQ]
    rw [hQ2c, hS64] at hcard
    norm_num at hcard
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  have hSP1 : S ≤ L1 ⊔ bigB L1 L2 S := hSB.trans le_sup_right
  have hSP2 : S ≤ L2 ⊔ bigB L1 L2 S := hSB.trans le_sup_right
  have iso := hGlue Mdl hMdl ψ₁ ψ₂ hSP1 hSP2 hQ1S (hQ2S.trans hSP2) hQ1e hQ1c hne hS1 hS2 hB1 hB2
    hQ1 hQ2
  exact ⟨Mdl.Y, Mdl.grp, Mdl.lie, Mdl.T0, Mdl.M1, Mdl.M2, Mdl.pair, iso⟩

end CFSG.GH74.QTGen4.DSGen4
