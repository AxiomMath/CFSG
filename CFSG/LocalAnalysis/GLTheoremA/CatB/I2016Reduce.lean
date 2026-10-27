module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016Inner
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016Trans

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2016

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 Subgroup

variable {G : Type} [Group G] [Finite G]

theorem coprime_card_of_le_glaPPrimeCoreOf {J H : Subgroup G} (hH : H ≤ GLAPPrimeCoreOf 3 J) :
    Nat.Coprime 3 (Nat.card H) := by
  have h4 : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 J)) := by
    have hJ : Nat.card (GLAPPrimeCoreOf 3 J) = Nat.card (CFSG.pPrimeCore 3 ↥J) :=
      Subgroup.card_map_of_injective Subtype.val_injective
    rw [hJ]
    exact CFSG.pPrimeCore_coprime_card
  exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hH) h4

theorem mem_normalizer_of_map_conj_eq {Q : Type} [Group Q] {R : Subgroup Q} {a : Q}
    (h : R.map (MulAut.conj a).toMonoidHom = R) : a ∈ Subgroup.normalizer (R : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hm : MulAut.conj a x ∈ R.map (MulAut.conj a).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [h] at hm
    exact hm
  · intro hx
    rw [← h] at hx
    obtain ⟨r, hr, hrx⟩ := Subgroup.mem_map.1 hx
    have hrx' : (MulAut.conj a) r = (MulAut.conj a) x := hrx
    have : r = x := (MulAut.conj a).injective hrx'
    rw [← this]
    exact hr

theorem config_TC {a y : G} {J I : Subgroup G} (hctx : S8.L89.Case2Ctx a y J I) :
    S8.IsTypeWithCenter 3
      ((I.comap J.subtype).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J))) S8.isPSp43 1 := by
  have hIJ : I ≤ J := hctx.hI.1.trans inf_le_left
  set IQ : Subgroup (PQ 3 J) := (I.comap J.subtype).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J))
    with hIQ
  let f0 : ↥I →* PQ 3 J :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J)).comp (Subgroup.inclusion hIJ)
  have hf0 : ∀ i : ↥I, f0 i ∈ IQ := fun i =>
    Subgroup.mem_map.2 ⟨Subgroup.inclusion hIJ i, i.2, rfl⟩
  let f : ↥I →* ↥IQ := f0.codRestrict IQ hf0
  have hfs : Function.Surjective f := by
    intro q
    obtain ⟨j, hj, hjq⟩ := Subgroup.mem_map.1 q.2
    refine ⟨⟨(j : G), hj⟩, Subtype.ext ?_⟩
    exact hjq
  have hker : Nat.Coprime 3 (Nat.card f.ker) := by
    have hmap : f.ker.map I.subtype ≤ GLAPPrimeCoreOf 3 J := by
      rintro _ ⟨i, hi, rfl⟩
      have hi' : f0 i = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hi)
      have hi2 : (QuotientGroup.mk (Subgroup.inclusion hIJ i) : PQ 3 J) = 1 := hi'
      rw [QuotientGroup.eq_one_iff] at hi2
      exact Subgroup.mem_map.2 ⟨Subgroup.inclusion hIJ i, hi2, rfl⟩
    have hcard : Nat.card (f.ker.map I.subtype) = Nat.card f.ker :=
      Subgroup.card_map_of_injective Subtype.val_injective
    rw [← hcard]
    exact coprime_card_of_le_glaPPrimeCoreOf hmap
  obtain ⟨e⟩ := pQuot_mulEquiv_of_surjective (p := 3) f hfs hker
  exact isTypeWithCenter_of_quotEquiv e hctx.hIt

theorem config_R {a y : G} {J I K T : Subgroup G} (hctx : S8.L89.Case2Ctx a y J I)
    (hloc : S8.L89.Case2Local y J K T) :
    ∃ R : Subgroup (PQ 3 J), R ≠ ⊥ ∧ IsPGroup 2 R ∧
      (KphiQ J K).range ≤ Subgroup.normalizer (R : Set (PQ 3 J)) ∧
      R.map (sigmaHom 3 J ⟨y, hctx.hyJ⟩).toMonoidHom = R := by
  obtain ⟨R, hR1, hR2, _, hinv⟩ := exists_inner_two_subgroup (H := TH J hloc.hTJ)
    (isPGroup_TH hloc.hTJ hloc.hT2) (inner_of_TH hloc.hTJ hloc.hinner)
    (TH_ne_bot hloc.hTJ hloc.hfaith hloc.hT1)
  refine ⟨R, hR1, hR2, ?_, ?_⟩
  · intro q hq
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.1 hq
    have hkJ : ((k.1 : ↥J) : G) ∈ J := (k.1).2
    have hgN : ((k.1 : ↥J) : G) ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer hkJ
    have hgT : ((k.1 : ↥J) : G) ∈ Subgroup.normalizer (T : Set G) := hloc.hKT k.2
    have hinvg := hinv _ (TH_conj_iff hloc.hTJ hgN hgT)
    have hc : MulAut.conj (KphiQ J K k) = sigmaHom 3 J ⟨((k.1 : ↥J) : G), hgN⟩ := by
      rw [sigmaHom_eq_conj hgN hkJ]
      rfl
    apply mem_normalizer_of_map_conj_eq
    rw [hc]
    exact hinvg
  · exact hinv _ (TH_conj_iff hloc.hTJ hctx.hyJ hloc.hyT)

theorem config_A {a y : G} {J I K T : Subgroup G} (hctx : S8.L89.Case2Ctx a y J I)
    (hloc : S8.L89.Case2Local y J K T) :
    (KphiQ J K).range ≤ fixSub (sigmaHom 3 J ⟨y, hctx.hyJ⟩) ∧ HasA6Quot (KphiQ J K).range := by
  refine ⟨?_, hasA6Quot_KphiQ hloc.hKJ hloc.hKt.1⟩
  intro q hq
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.1 hq
  have hcomm : y * ((k.1 : ↥J) : G) = ((k.1 : ↥J) : G) * y :=
    Subgroup.mem_centralizer_iff.1 (hloc.hKy k.2) y (Set.mem_singleton y)
  show (QuotientGroup.mk (conjJ J y hctx.hyJ k.1) : PQ 3 J) = QuotientGroup.mk k.1
  congr 1
  apply Subtype.ext
  rw [conjJ_val]
  calc y * ((k.1 : ↥J) : G) * y⁻¹ = (((k.1 : ↥J) : G) * y) * y⁻¹ := by rw [hcomm]
    _ = ((k.1 : ↥J) : G) := by group

theorem sigma_pow_three_eq_one {y : G} {J : Subgroup G} (hyJ : y ∈ Subgroup.normalizer (J : Set G))
    (hy3 : y ^ 3 = 1) : (sigmaHom 3 J ⟨y, hyJ⟩) ^ 3 = 1 := by
  rw [← map_pow]
  have h1 : (⟨y, hyJ⟩ : Subgroup.normalizer (J : Set G)) ^ 3 = 1 :=
    Subtype.ext (by simp [hy3])
  rw [h1, map_one]

theorem I2016_of_facts (hSp : I2016FactSp) (hU6 : I2016FactU6) :
    S8.L89.I2016At G := by
  refine ⟨fun a y J I K T hctx hloc hcat => ?_, fun a y J I K T hctx hloc hcat => ?_⟩
  · have hy3 : y ^ 3 = 1 := by
      rw [← hctx.hy]
      exact pow_orderOf_eq_one y
    obtain ⟨R, hR1, hR2, hAR, hRσ⟩ := config_R hctx hloc
    obtain ⟨hA, hA6⟩ := config_A hctx hloc
    exact hSp (PQ 3 J) (sigmaHom 3 J ⟨y, hctx.hyJ⟩) (KphiQ J K).range
      ((I.comap J.subtype).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J))) R
      (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hctx.hJ)
      (CFSG.LocalAnalysis.GLTheoremA.I2611.isPGroup_center_pQuot' Nat.prime_three J) hcat
      (sigma_pow_three_eq_one hctx.hyJ hy3) hA hA6
      (isSubnormal_image_fixSub hctx.hyJ hy3 hctx.hI.2.1) (config_TC hctx) hR1 hR2 hRσ hAR
  · have hy3 : y ^ 3 = 1 := by
      rw [← hctx.hy]
      exact pow_orderOf_eq_one y
    obtain ⟨R, hR1, hR2, hAR, hRσ⟩ := config_R hctx hloc
    obtain ⟨hA, hA6⟩ := config_A hctx hloc
    obtain ⟨R₂, hR₂1, hR₂2, hIR₂, hR₂σ⟩ :=
      hU6 (PQ 3 J) (sigmaHom 3 J ⟨y, hctx.hyJ⟩) (KphiQ J K).range
        ((I.comap J.subtype).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J))) R
        (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hctx.hJ) hcat
        (sigma_pow_three_eq_one hctx.hyJ hy3) hA hA6
        (isSubnormal_image_fixSub hctx.hyJ hy3 hctx.hI.2.1) (config_TC hctx) hR1 hR2 hRσ hAR
    obtain ⟨W, hWJ, hW2, hWn, hWsup⟩ := exists_lift_two J hR₂1 hR₂2
    refine ⟨W, hWJ, hW2, hWn, ?_⟩
    rw [hWsup]
    have hIJ : I ≤ J := hctx.hI.1.trans inf_le_left
    refine sup_le ?_ ?_
    · intro g hg
      have hgJ : g ∈ J := hIJ hg
      have hgN : g ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer hgJ
      have hmem : (QuotientGroup.mk ⟨g, hgJ⟩ : PQ 3 J) ∈
          (I.comap J.subtype).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J)) :=
        Subgroup.mem_map.2 ⟨⟨g, hgJ⟩, hg, rfl⟩
      have hconj : R₂.map (sigmaHom 3 J ⟨g, hgN⟩).toMonoidHom = R₂ := by
        rw [sigmaHom_eq_conj hgN hgJ]
        exact map_conj_eq_of_mem_normalizer (hIR₂ hmem)
      exact normalizer_Mset hgN hconj
    · exact Subgroup.zpowers_le.2 (normalizer_Mset hctx.hyJ hR₂σ)

end CFSG.LocalAnalysis.GLTheoremA.I2016


