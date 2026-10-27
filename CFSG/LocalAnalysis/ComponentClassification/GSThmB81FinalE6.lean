module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81E6d
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81FinalS3
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6P

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁} {v : H} (hv : d.IsV v) (I : In81) (F : d.Facts) (hJo : CFSec8JOrder)
  (hL0 : CF81L0) (hCls : CF81E6Cls) (hOut : CF81E6Out) (hFld : CF81E6Fld)
include hv I F hJo hL0 hCls hOut hFld

theorem concl81_of_exit6 (hSect : CF81E6Sect) (hP211 : CF81E6P211)
    (hGH : ClassicalInvolution.GH74SectionalModels)
    (hT₀ : ∃ T : Sylow 2 H, (T : Subgroup H) ≤ centralizer (h.B : Set H)) : h.Concl81 := by
  obtain ⟨hFeq, hsimp, hcent, -, -⟩ := h.generalizedFitting_simple
  have := hsimp
  obtain ⟨-, p, f, hp, hp2, hf, hK, hJ⟩ := Hyp52.Sec8Case.exists_params h.toHyp52 H₁.kloc.case8
  have hJF := h.J_le_fstar
  have hnab : ∃ u w : ↥(generalizedFitting H), u * w ≠ w * u := by
    by_contra hc
    push Not at hc
    have hJbot : ⁅h.J, h.J⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hc ⟨y, hJF hy⟩ ⟨x, hJF hx⟩)
    have : Nontrivial ↥h.J := B5a.nontrivial_of_isPComponent_subgroupOf h.J_le h.isPComponent_J
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥h.J)
    apply hx
    apply Subtype.ext
    have hx' : (x : H) ∈ ⁅h.J, h.J⁆ := by rw [h.e6_commutator_J]; exact x.2
    rw [hJbot, mem_bot] at hx'
    exact hx'
  have hlist : GH74List ↥(generalizedFitting H) := hGH _ hnab (three_le_twoRank_fstar I F)
    (sect_fstar hv I F hJo hL0 hCls hOut hFld hSect hT₀)
  have hcent' : centralizer (generalizedFitting H : Set H) = ⊥ := by
    rw [hFeq]
    exact hcent
  have ha1 : h.a ≠ 1 := fun h1 => by
    have h2 := h.orderOf_a
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hb1 : d.b ≠ 1 := fun h1 => by
    have h2 := d.b_ord
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hKb : h.K ≤ centralizer ({d.b} : Set H) := by
    rw [← d.normalizer_B_eq]
    exact h.isPComponent_K.1
  have hKc : IsPComponent 2 (h.K.subgroupOf (centralizer ({d.b} : Set H))) := by
    rw [← d.normalizer_B_eq]
    exact h.isPComponent_K.2
  rcases hP211 H hsimp hcent' hlist p f hp hp2 hf h.a h.J h.D (Six.a_mul_a_self h.toHyp52) ha1
      h.J_le h.isPComponent_J hJ hJF inf_le_right h.toHyp52.sec8_D_sylow
      (card_le_fstar hv I F hJo hL0 hCls hOut hFld hSect hT₀) d.b h.K d.b_mul_self hb1
      hKb hKc hK with hA | hL | hU
  · exact Or.inl hA
  · exact Or.inr ⟨p, f, hp, hp2, hf, hJ, Or.inl hL⟩
  · exact Or.inr ⟨p, f, hp, hp2, hf, hJ, Or.inr hU⟩

end Data

end L81Hyp

end Hyp59

theorem gs81Exit6Input (I : In81) (hAC : CFAutSmallCommutator) (hAQ : CFAutSmallQuotient)
    (hJo : CFSec8JOrder) (hF2 : CFSp4F2) (hL0 : CF81L0) (hConf : CF81Conf) (hCls : CF81E6Cls)
    (hOut : CF81E6Out) (hFld : CF81E6Fld) (hSect : CF81E6Sect) (hP211 : CF81E6P211) :
    GS81Exit6Input := by
  intro hGH H _ _ h H₁ hT₀
  obtain ⟨d⟩ := H₁.exists_data I.b1 I.b6 I.cf23 I.cf24 hAC hAQ suzukiTausskyInput I.cf1 I.cf2 hJo
    hF2
  have F := d.facts I.cf1 I.cf2 hJo hL0 hConf
  obtain ⟨v, hvN, hva, hvz, hvv, hv2⟩ :=
    d.exists_v I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 I.c F
  exact Hyp59.L81Hyp.Data.concl81_of_exit6 ⟨hvN, hva, hvz, hvv, hv2⟩ I F hJo hL0 hCls hOut hFld
    hSect hP211 hGH hT₀

structure Lemma81InputsE6 : Prop where
  in81 : In81
  cfi : CFProp23IndexReduced
  ac : CFAutSmallCommutator
  aq : CFAutSmallQuotient
  jo : CFSec8JOrder
  f2 : CFSp4F2
  l0 : CF81L0
  conf : CF81Conf
  noNilp : CF81NoNilp
  fieldOrd : CF81FieldOrd
  diag : CF81Diag
  cent2Nilp : CF81L2Cent2Nilp
  centPerfect : CF81L2CentPerfect
  nineCent : CF81L2NineCent
  sp4Three : CF81Sp4Three
  e6Cls : CF81E6Cls
  e6Out : CF81E6Out
  e6Fld : CF81E6Fld
  e6Sect : CF81E6Sect
  e6P211 : CF81E6P211
  exit10 : GS81Exit10Input
  exit11 : GS81Exit11Input
  gh74 : ClassicalInvolution.GH74SectionalModels
  ci : GSLit.ClassicalInvolutionInput
  rs : RestrictedStandardInput

theorem lemma81E6
    (I : Lemma81InputsE6) :
    Lemma81StatementK :=
  lemma81'''
    { in81 := I.in81
      cfi := I.cfi
      ac := I.ac
      aq := I.aq
      jo := I.jo
      f2 := I.f2
      l0 := I.l0
      conf := I.conf
      noNilp := I.noNilp
      fieldOrd := I.fieldOrd
      diag := I.diag
      cent2Nilp := I.cent2Nilp
      centPerfect := I.centPerfect
      nineCent := I.nineCent
      sp4Three := I.sp4Three
      exit6 := gs81Exit6Input I.in81 I.ac I.aq I.jo I.f2 I.l0 I.conf I.e6Cls I.e6Out I.e6Fld
        I.e6Sect I.e6P211
      exit10 := I.exit10
      exit11 := I.exit11
      gh74 := I.gh74
      ci := I.ci
      rs := I.rs }

end CFSG.ComponentClassification.GSThmB
