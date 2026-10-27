module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CentDCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CentDPull
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888F3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCentTrans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCentInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverPocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5PocketOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82FactOm6CentD_of (hS : Asc82SchurU43) : Asc82FactOm6CentD := by
  intro G _ _ L z K₁ K₂ hL hodd hz2 hK₁ hK₂ _ _ hprod Y hY
  obtain ⟨V, _, _, _, Q, hQ, φ, hφ⟩ := t5_exists_cover hS hL
  have hdim := hφ.finrank_eq
  have hsgn := hφ.quadSign_eq
  have hker : CFSG.oddCore ↥L = ⊥ := by
    have h : (CFSG.oddCore ↥L).map L.subtype = ⊥ := hodd
    exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.oddCore ↥L) L.subtype_injective).mp h
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, hφ.ker_eq, hker]
  have hsurj : Function.Surjective φ := hφ.surjective
  have hzL : z ∈ L := (Subgroup.mem_inf.mp (hK₁.2.1 hK₁.1)).1
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2]; exact pow_orderOf_eq_one z
  let zL : ↥L := ⟨z, hzL⟩
  have hφzz : φ zL * φ zL = 1 := by
    rw [← map_mul, show zL * zL = 1 from Subtype.ext hzz, map_one]
  have hφz1 : φ zL ≠ 1 := by
    intro h
    have h1 : zL = 1 := hinj (h.trans (map_one φ).symm)
    have h2 : z = 1 := congrArg Subtype.val h1
    rw [h2, orderOf_one] at hz2
    omega
  have hI4 : IsI4PlusIn (⊤ : Subgroup ↥(omegaGroup hQ)) (φ zL) :=
    (t5_isI4PlusIn_iff hL hφ hzL hz2).mp ⟨hz2, K₁, hK₁⟩
  have hztt : ((φ zL : omegaGroup hQ) : OGroup Q) * ((φ zL : omegaGroup hQ) : OGroup Q) = 1 :=
    congrArg Subtype.val hφzz
  have hzt4 : invType ((φ zL : omegaGroup hQ) : OGroup Q) = (4, 1) :=
    (t5_isI4PlusIn_omega_iff hdim hsgn hztt hφz1).mp hI4
  let D : Om6Par Q (sec5cdPhi φ zL) := Om6Par.mk' hQ hdim hsgn hztt hzt4
  obtain ⟨e, he⟩ := t5_exists_model hL hφ
  have h6 : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)) :=
    Or.inr ⟨hdim, Or.inr hsgn⟩
  have hLp : commutator ↥L = ⊤ := hL.1.1.commutator_eq_top
  have hYN : Y ≤ normalizer (L : Set G) := hY.trans inf_le_left
  rw [fg_relIndex_eq_card_range hQ h6 e hLp hYN]
  have hle : (fgThetaR hQ h6 e hYN).range ≤ (fgIotaP (FGSplit.comm D.nd D.htt)).range := by
    rintro _ ⟨y, rfl⟩
    have hyN : (y : G) ∈ normalizer (L : Set G) := hYN y.2
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (ffTheta hQ h6 e ⟨(y : G), hyN⟩)
    have hcov : CoverAct L φ (y : G) x :=
      t5_coverAct_of_inducesViaP hL hφ he (ffTheta_induces hQ h6 e ⟨(y : G), hyN⟩) hx
    have hfix : ∀ g ∈ D.q8Img, simAct Q x g = g := by
      intro g hg
      obtain ⟨l, hl⟩ := hsurj ⟨g, D.q8Img_le_omega hg⟩
      have hΦl : sec5cdPhi φ l = g := congrArg Subtype.val hl
      have hl' : (l : G) ∈ twoCoreIn (K₁ ⊔ K₂) := by
        rw [hprod]
        exact sec5cd_pull_q8_le_twoCoreIn hinj hsurj hzL D
          (mem_sec5cdPull_iff.mpr ⟨l, rfl, hΦl ▸ hg⟩)
      have hcomm : (y : G) * (l : G) = (l : G) * (y : G) :=
        ((Subgroup.mem_centralizer_iff.mp (hY y.2).2) (l : G) hl').symm
      rw [← hΦl]
      exact t5_cent_map_mem hcov hcomm
    obtain ⟨b, hb⟩ := sec5cd_core D
      (fun a ha => hfix _ (D.theta_left_mem_q8Img ha))
      (fun b hb => hfix _ (D.theta_right_mem_q8Img hb))
    exact ⟨b, hb.symm.trans hx⟩
  have hW : 0 < Module.finrank (ZMod 3) (FGSplit.comm D.nd D.htt).W := by
    show 0 < Module.finrank (ZMod 3) (commSp (sec5cdPhi φ zL))
    rw [D.dimW]
    norm_num
  calc Nat.card (fgThetaR hQ h6 e hYN).range ∣
        Nat.card (fgIotaP (FGSplit.comm D.nd D.htt)).range := Subgroup.card_dvd_of_le hle
    _ = Nat.card (OGroup (Q.restrict (FGSplit.comm D.nd D.htt).P)) :=
        Nat.card_congr (MonoidHom.ofInjective (fg_iotaP_injective _ hW)).toEquiv.symm
    _ = 8 := natCard_oGroup_two_minus (nondegenerate_restrict_fixSp D.nd D.htt) D.dimP D.signP

end CFSG.OddStandard.SmallF3.Omega
