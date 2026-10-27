module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ASp68Grp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.Open.StatedDefs
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalSpEight
import CFSG.LieType.SeitzGeneration.OuterSpData
import CFSG.LocalAnalysis.GLTheoremA.Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ASp68Fix
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ASp68Z
import CFSG.LocalAnalysis.GLTheoremA.CatA.T263Rank
import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassical
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalRows
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.D4Dichotomy
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Isotropic
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.T1
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwo
import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Center
import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwLangConsumers
import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6Holds
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossReeF4Fam
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSuzFaithful
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Adj
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Facts
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
import CFSG.RankThree.PartOne.K133H.G2Plane
import CFSG.RankThree.PartOne.KE.E8D4Family
import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NormalFormStabilizer
import Certificates.Certificate9530

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265A
open CFSG.HardMathSupport.Solomon.Coordinator (mem_fixSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner_normal)

section Transfer

variable {Ω P : Type} [Group Ω] [Group P]

private theorem coe_symm_congr_conjNormal {S : Subgroup Ω} [S.Normal] (Φ : ↥S ≃* P) (g : Ω)
    (y : P) :
    ((Φ.symm (((MulAut.congr Φ).toMonoidHom.comp MulAut.conjNormal g) y) : ↥S) : Ω) =
      g * (Φ.symm y : Ω) * g⁻¹ := by
  simp [MulAut.conjNormal_apply]

private theorem inducesInnerMod_of_mem_range {S : Subgroup Ω} (f : P →* Ω) (hfS : ∀ z, f z ∈ S)
    (hSf : ∀ s ∈ S, ∃ z, f z = s) {α : Ω →* MulAut P}
    (hαf : ∀ g y, f (α g y) = g * f y * g⁻¹) {b : Ω}
    (hb : α b ∈ (MulAut.conj : P →* MulAut P).range) : InducesInnerMod 3 S b := by
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hb
  have key : ∀ y ∈ S, b * y * b⁻¹ = f p * y * (f p)⁻¹ := by
    intro y hy
    obtain ⟨z, rfl⟩ := hSf y hy
    rw [← hαf b z, ← hp, MulAut.conj_apply, map_mul, map_mul, map_inv]
  refine ⟨f p, hfS p, fun y hy => ?_⟩
  have h2 := key _ (S.mul_mem (S.mul_mem (S.inv_mem (hfS p)) hy) (hfS p))
  have h3 : b⁻¹ * y * b = (f p)⁻¹ * y * f p := by
    calc b⁻¹ * y * b = b⁻¹ * (b * ((f p)⁻¹ * y * f p) * b⁻¹) * b := by rw [h2]; group
      _ = (f p)⁻¹ * y * f p := by group
  rw [h3, inv_mul_cancel]
  exact one_mem _

end Transfer


theorem QUNL.false_of_sp68 {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x b : Ω}
    (h : QUNL 3 S B T x b) (hS : StatedClassicalModel (PSimple 3 S) .PSp 3 2 3)
    (hr : Nat.card B < 27 * Nat.card (Dgrp b x)) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := h.cfg.normal
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hS
  have hK8 : Nat.card K = 8 := by rw [hK]; norm_num
  obtain ⟨Φ⟩ := nonempty_mulEquiv_of_sp68 h.cfg.comp h.cfg.core hK8 e
  have hB := h.cfg.elem
  have hb3 : b ^ 3 = 1 := hB.2 b h.cfg.hb
  have hNI : ¬ InducesInnerMod 3 S b := by
    rcases h.cfg.prop with hF | ⟨-, -, hN⟩
    · exact not_inducesInnerMod_of_fieldOn h.cfg.comp hF
    · exact hN.2
  set κ : Ω →* MulAut (StatedProj (StatedSp 3 K)) :=
    (MulAut.congr Φ).toMonoidHom.comp MulAut.conjNormal
  have hκI : κ b ∉ (MulAut.conj : StatedProj (StatedSp 3 K) →* MulAut _).range := fun hin =>
    hNI (inducesInnerMod_of_mem_range (S.subtype.comp Φ.symm.toMonoidHom)
      (fun z => (Φ.symm z).2) (fun s hs => ⟨Φ ⟨s, hs⟩, by simp⟩) (α := κ)
      (fun g y => coe_symm_congr_conjNormal Φ g y) hin)
  obtain ⟨σ, h0, hσ, hκb⟩ := CFSG.HardMathSupport.Dickson.Bal207.outer_conj_fieldAut_eight
    (r := 3) (by norm_num) hK8 (x := κ b) (by rw [← map_pow, hb3, map_one]) hκI
  set Φ' : ↥S ≃* StatedProj (StatedSp 3 K) := Φ.trans (h0⁻¹ : MulAut _)
  set α : Ω →* MulAut (StatedProj (StatedSp 3 K)) :=
    (MulAut.congr Φ').toMonoidHom.comp MulAut.conjNormal
  have hακ : ∀ g, α g = h0⁻¹ * κ g * h0 := fun g => by
    ext y
    rfl
  have hαb : α b = fieldAut 3 K σ := by
    rw [hακ, hκb]
    group
  have hfσI : fieldAut 3 K σ ∉ (MulAut.conj : StatedProj (StatedSp 3 K) →* MulAut _).range :=
    fun hin => hκI (by rw [hκb]; exact (inner_normal _).conj_mem _ hin h0)
  have hfσ3 : fieldAut 3 K σ ^ 3 = 1 := by rw [← hαb, ← map_pow, hb3, map_one]
  have hconj : Function.Injective (MulAut.conj : StatedProj (StatedSp 3 K) →* MulAut _) :=
    CFSG.RankThree.CASymplecticSubfield.conj_injective_of_center_eq_bot
      (CFSG.LieType.SeitzGeneration.center_statedProj_statedSp_eq_bot (by norm_num))
  set f : StatedProj (StatedSp 3 K) →* Ω := S.subtype.comp Φ'.symm.toMonoidHom
  have hf : Function.Injective f := S.subtype_injective.comp Φ'.symm.injective
  have hαf : ∀ g y, f (α g y) = g * f y * g⁻¹ := fun g y => coe_symm_congr_conjNormal Φ' g y
  have hfS : ∀ z, f z ∈ S := fun z => (Φ'.symm z).2
  have hfΦ : ∀ s (hs : s ∈ S), f (Φ' ⟨s, hs⟩) = s := fun s hs => by
    show ((Φ'.symm (Φ' ⟨s, hs⟩) : ↥S) : Ω) = s
    rw [MulEquiv.symm_apply_apply]
  have hSmap : (⊤ : Subgroup (StatedProj (StatedSp 3 K))).map f = S := by
    ext s
    constructor
    · rintro ⟨z, -, rfl⟩
      exact hfS z
    · intro hs
      exact ⟨Φ' ⟨s, hs⟩, trivial, hfΦ s hs⟩
  have hαS : ∀ s (hs : s ∈ S), α s = MulAut.conj (Φ' ⟨s, hs⟩) := fun s hs => by
    ext y
    apply hf
    rw [hαf, MulAut.conj_apply, map_mul, map_mul, map_inv, hfΦ]
  have hαx : α x = 1 := by
    ext y
    apply hf
    rw [hαf, MulAut.one_apply, ← h.cfg.xcen, mul_inv_cancel_right]
  have hQfσ : orderOf (QuotientGroup.mk (fieldAut 3 K σ) : Outer (StatedProj (StatedSp 3 K))) =
      3 := by
    refine orderOf_eq_prime ?_ fun h1 => hfσI ((QuotientGroup.eq_one_iff _).mp h1)
    rw [← QuotientGroup.mk_pow, hfσ3, QuotientGroup.mk_one]
  have hzI : ∀ φ ∈ Subgroup.zpowers (fieldAut 3 K σ),
      φ ∈ (MulAut.conj : StatedProj (StatedSp 3 K) →* MulAut _).range → φ = 1 := by
    intro φ hφ hφI
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hφ
    have hQk : (QuotientGroup.mk (fieldAut 3 K σ) : Outer (StatedProj (StatedSp 3 K))) ^ k =
        1 := by
      rw [← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff]
      exact hφI
    have h3k := orderOf_dvd_iff_zpow_eq_one.mpr hQk
    rw [hQfσ] at h3k
    obtain ⟨m, rfl⟩ := h3k
    rw [zpow_mul, zpow_natCast, hfσ3, one_zpow]
  have hDB : Dgrp b x ≤ B := (Subgroup.closure_le _).mpr
    (Set.insert_subset_iff.mpr ⟨h.cfg.hb, Set.singleton_subset_iff.mpr h.cfg.xB⟩)
  have hDα : Dgrp b x ≤ (Subgroup.zpowers (fieldAut 3 K σ)).comap α := by
    refine (Subgroup.closure_le _).mpr
      (Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr ?_⟩)
    · show α b ∈ Subgroup.zpowers (fieldAut 3 K σ)
      rw [hαb]
      exact Subgroup.mem_zpowers _
    · show α x ∈ Subgroup.zpowers (fieldAut 3 K σ)
      rw [hαx]
      exact one_mem _
  have hDI : ∀ c ∈ Dgrp b x, α c ∈ (MulAut.conj : StatedProj (StatedSp 3 K) →* MulAut _).range →
      α c = 1 := fun c hc => hzI _ (hDα hc)
  have hDS : ∀ d ∈ Dgrp b x, d ∈ S → d = 1 := by
    intro d hdD hdS
    have h1 : α d = 1 := hDI d hdD (MonoidHom.mem_range.mpr ⟨_, (hαS d hdS).symm⟩)
    rw [hαS d hdS] at h1
    have h2 : Φ' ⟨d, hdS⟩ = 1 := hconj (h1.trans (map_one _).symm)
    rw [← hfΦ d hdS, h2, map_one]
  have hαT := h.map_eq_one_of_sp68 hK8 hσ hf hSmap hαf hαb hDI
  obtain ⟨E, hEfix, hE, hE27⟩ := exists_elemAbelian_fixSubgroup_fieldAut_eight hK8 hσ
  have hDcent : Dgrp b x ≤ Subgroup.centralizer ((E.map f : Subgroup Ω) : Set Ω) := by
    refine (Subgroup.closure_le _).mpr
      (Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr ?_⟩)
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      rintro _ ⟨y, hy, rfl⟩
      have h1 := hαf b y
      rw [hαb, mem_fixSubgroup.mp (hEfix hy)] at h1
      calc f y * b = b * f y * b⁻¹ * b := by rw [← h1]
        _ = b * f y := by group
    · exact Subgroup.mem_centralizer_iff.mpr fun z _ => h.cfg.xcen z
  have hE' : IsElemAbelian 3 (E.map f ⊔ Dgrp b x) :=
    (hE.map f).sup_of_commute (hB.mono hDB) fun z hz d hd =>
      Subgroup.mem_centralizer_iff.mp (hDcent hd) z hz
  have hE'card : Nat.card ↥(E.map f ⊔ Dgrp b x) = 27 * Nat.card (Dgrp b x) := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer
      (hDcent.trans (Subgroup.centralizer_le_normalizer _))
    have hinf : E.map f ⊓ Dgrp b x = ⊥ := by
      rw [eq_bot_iff]
      rintro z ⟨⟨y, -, rfl⟩, hzD⟩
      exact Subgroup.mem_bot.mpr (hDS _ hzD (hfS y))
    rwa [hinf, Subgroup.card_bot, mul_one, Subgroup.card_map_of_injective hf, hE27] at h1
  have hle : Nat.card ↥(E.map f ⊔ Dgrp b x) ≤ Nat.card B := by
    rcases h.cfg.maxc with hTB | hmax
    · have hT1 : T ≠ ⊥ := fun hT => hTB (by rw [hT, Subgroup.commutator_bot_left])
      have hEN : E.map f ⊔ Dgrp b x ≤ Subgroup.normalizer (T : Set Ω) := by
        refine sup_le (le_trans ?_ (Subgroup.centralizer_le_normalizer _))
          (hDB.trans h.cfg.bnorm)
        rintro _ ⟨y, -, rfl⟩
        refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
        have h1 := hαf t y
        rw [hαT t ht, MulAut.one_apply] at h1
        calc t * f y = t * f y * t⁻¹ * t := by group
          _ = f y * t := by rw [← h1]
      exact (T263.card_le_of_normalizes hT1 h.cfg.two hE' hEN).trans h.cfg.rank
    · exact hmax _ hE'
  exact absurd hle (not_le.mpr (by rw [hE'card]; exact hr))

end CFSG.LocalAnalysis.GLTheoremA.S265

end
