module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3
public import CFSG.ClassicalInvolution.Q3.TL3CentStep
public import CFSG.ClassicalInvolution.Q3.TL4MF163L3
public import CFSG.ClassicalInvolution.Q3.TL4MF163U3
public import CFSG.ClassicalInvolution.Q3.TL4MF163M12O
public import CFSG.ClassicalInvolution.Q3.TL4MF163M12A
public import CFSG.ClassicalInvolution.Q3.TL4E3Norm

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint

section Cit3


@[expose] def TightE3S3Sec163Z (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (J : Subgroup Y)
    (u : Y), E3Frame n R S t J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (Sb : Sylow 2 ↥(secR R u)), TightEx (SecQ R u) (secR R u) Sb (E3.secT htu ht) →
      TightEdgeless (secR R u) → (∀ W ∈ WSet (E3.secΩ R u), MuIsoS3 (E3.secΩ R u) W) →
        ¬ TightInO2 (E3.secT htu ht) → Subgroup.center (SecQ R u) ≠ ⊥ →
          Concl163 (secR R u) (E3.secT htu ht)

end Cit3

section Cit3c


theorem tightE3S3Sec163_of {n : ℕ} (hZ : TightE3S3Sec163Z n) (hM : Model163)
    (hM12 : ModelM12Acts3) : TightE3S3Sec163 n := by
  intro Y _ _ R S t J u hF htu ht Sb hex hedge hμ hnE2
  by_cases hZ0 : Subgroup.center (SecQ R u) = ⊥
  swap
  · exact hZ Y R S t J u hF htu ht Sb hex hedge hμ hnE2 hZ0
  obtain ⟨Sq, hdq, hcq⟩ := hF.exists_secCls htu ht
  have hm : EdgelessMember3 (secR R u) Sq (E3.secT htu ht) :=
    ⟨hdq, tightClsR_three_iff.mpr hcq, hedge⟩
  have hμ' : MuS3Member (secR R u) := hμ
  rcases TightEx.reduce hdq hcq hex hnE2 with ⟨-, h3⟩ | ⟨-, ⟨e⟩⟩ | ⟨hZ1, -⟩
  · have hFq : TightFStarQuasisimple (SecQ R u) := by
      rcases hF.sec_dich htu ht with h | h | ⟨L, -, -, -, -, -, hFc, hFL⟩
      · exact absurd h hnE2
      · exact h
      · rw [hZ0] at hFc
        exact absurd (hFc.trans bot_le) hFL
    have hZF : Subgroup.center ↥(genFittingFStar (SecQ R u)) = ⊥ := by
      have h1 := TightDatum.center_genFittingFStar_le hdq hcq hnE2
      rw [hZ0, le_bot_iff] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ (genFittingFStar _).subtype_injective).mp h1
    have hs : IsSimpleGroup ↥(genFittingFStar (SecQ R u)) :=
      (isSimpleGroup_of_quasisimple_of_center_eq_bot hFq hZF).1
    rcases hF.plus.thm6 (SecQ R u) hF.card_secQ_lt (secR R u) Sq (E3.secT htu ht) hdq
        (tightClsR_three_iff.mpr hcq) hnE2 hFq hedge with hg | hX
    · exact absurd (acts3_of_good hg) h3
    · exact concl163_of_e3a hM hM12 hm hs hμ' h3 hX
  · have e' : SecQ R u ≃* NativeSporadic.Carrier .M12 :=
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ0).symm).trans e
    exact hM.2.2.2 _ _ _ _ hm ⟨e'⟩
  · exact absurd hZ0 hZ1

theorem tightE3S3Sec163_of_center
    {n : ℕ}
    (hZ : TightE3S3Sec163Z n) : TightE3S3Sec163 n :=
  tightE3S3Sec163_of hZ ⟨model163L2_proved, model163L3_proved, model163U3_proved,
    model163M12_proved⟩ modelM12Acts3_proved

end Cit3c

end CFSG.ClassicalInvolution.Q3.TL4
