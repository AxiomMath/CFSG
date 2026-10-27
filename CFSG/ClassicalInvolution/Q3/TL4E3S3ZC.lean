module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3ZB
public import CFSG.ClassicalInvolution.Q3.TL4E3S3Sec
public import CFSG.ClassicalInvolution.Q3.TL4E3C269Sec
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4All

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint

namespace E3S3Z

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem concl163_of_e3a {n : ℕ} (h6 : Thm6RBelow 3 n) (hA : ModelM12Acts3)
    (hY : Nat.card Y < n) (hd : TightDatum R S t) (hc : TightCls Y R S t) (hE2 : ¬ TightInO2 t)
    (hE : TightEdgeless R) (h3 : ¬ TightActs3 R t) : Concl163 R t := by
  have hN2 := isPGroup_center hc
  have htN := not_mem_center hc hE2
  have hnt := noTwin hd hE
  have hm := edgelessMember3_quot hd hc hE2 hE
  have hcb := TwistQ.cls hd le_rfl hN2 htN hc
  have hE2b : ¬ TightInO2 (QuotientGroup.mk' (Subgroup.center Y) t) :=
    fun h => hE2 (TwistQ.inO2_of hN2 h)
  have hZb := center_quot_eq_bot hd hc hE2
  have h3b : ¬ TightActs3 (R.map (QuotientGroup.mk' (Subgroup.center Y)))
      (QuotientGroup.mk' (Subgroup.center Y) t) :=
    fun h => h3 (acts3_of_map hd le_rfl hN2 htN hnt h)
  have hq : TightFStarQuasisimple (Y ⧸ Subgroup.center Y) := by
    rcases tightDichotomy_of hm.datum hcb with h | h | ⟨L, -, -, -, -, -, hFc, hFL⟩
    · exact absurd h hE2b
    · exact h
    · rw [hZb] at hFc
      exact absurd (hFc.trans bot_le) hFL
  have hZF : Subgroup.center ↥(genFittingFStar (Y ⧸ Subgroup.center Y)) = ⊥ := by
    have h1 := TightDatum.center_genFittingFStar_le hm.datum hcb hE2b
    rw [hZb, le_bot_iff] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (genFittingFStar _).subtype_injective).mp h1
  obtain ⟨hs, hnab⟩ := isSimpleGroup_of_quasisimple_of_center_eq_bot hq hZF
  have hlt : Nat.card (Y ⧸ Subgroup.center Y) < n :=
    lt_of_le_of_lt (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)) hY
  refine concl163_of_quot hd hc hE2 ?_
  rcases h6 _ hlt _ _ _ hm.datum hm.cls hE2b hq hm.edgeless with hg | hX
  · exact absurd (acts3_of_good (TwistQ.good_of hd le_rfl hN2 htN hnt hg)) h3
  · have := hs
    obtain ⟨p, f, hp, hp2, ⟨hf, hl, hi⟩ | ⟨hl | hl, -⟩⟩ | ⟨hm12, hi⟩ := hX
    · exact model163L2_proved _ _ _ _ hm hs hi p f hp hp2 hf hl
    · by_cases hq3 : p ^ f = 3
      · exact absurd (E3C269.tightActs3_of_psl3_three hm hl hq3) h3b
      · exact E3C269.concl163_psl3_of_ne_three hm hp hp2 hl hq3
    · by_cases hq3 : p ^ f = 3
      · have hC := centralizer_genFittingFStar_eq_bot hnab
        have : (genFittingFStar (Y ⧸ Subgroup.center Y)).Normal := genFittingFStar_normal _
        obtain ⟨eF⟩ := MFMuZ2.nonempty_fstar_equiv (MFMuZ2.center_fstar_eq_bot hnab)
        obtain ⟨rfl, rfl⟩ := TA3.eq_three_of_pow_eq_three hq3
        exact MF163.U3.concl163_u3_three hm.datum hm.cls.1 hm.cls.2.1 h3b hC
          (MFMuZ2.lieModel_of_mulEquiv_classical eF (Or.inr rfl) hl)
      · exact E3C269.concl163_psu3_of_ne_three hm hp hp2 hl hq3
    · exact absurd (hA _ _ _ _ hm hs hi hm12) h3b

theorem concl163_of_edgeless_exit {n : ℕ} (h6 : Thm6RBelow 3 n) (hE4 : SecIdE4Edge)
    (hM12 : Model163M12) (hA : ModelM12Acts3) (hY : Nat.card Y < n) (hd : TightDatum R S t)
    (hc : TightCls Y R S t) {S' : Sylow 2 R} (hex : TightEx Y R S' t) (hE : TightEdgeless R)
    (hE2 : ¬ TightInO2 t) : Concl163 R t := by
  rcases TightEx.reduce hd hc hex hE2 with ⟨-, h3⟩ | ⟨-, ⟨e⟩⟩ | ⟨hZ, h4⟩
  · exact concl163_of_e3a h6 hA hY hd hc hE2 hE h3
  · exact concl163_of_quot hd hc hE2 (hM12 _ _ _ _ (edgelessMember3_quot hd hc hE2 hE) ⟨e⟩)
  · exact absurd hE (hE4 _ _ _ _ hd hc hE2 hZ h4)

end E3S3Z

theorem tightE3S3Sec163Z_of {n : ℕ} (hE4 : SecIdE4Edge) (hM12 : Model163M12)
    (hA : ModelM12Acts3) : TightE3S3Sec163Z n := by
  intro Y _ _ R S t J u hF htu ht Sb hex hedge _ hnE2 _
  obtain ⟨Sq, hd, hc⟩ := hF.exists_secCls htu ht
  exact E3S3Z.concl163_of_edgeless_exit hF.plus.thm6 hE4 hM12 hA hF.card_secQ_lt hd hc hex hedge
    hnE2

theorem tightE3S3Sec163Z_proved (n : ℕ) : TightE3S3Sec163Z n :=
  tightE3S3Sec163Z_of secIdE4Edge_proved model163M12_proved modelM12Acts3_proved

end CFSG.ClassicalInvolution.Q3.TL4
