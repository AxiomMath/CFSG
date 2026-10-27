module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O1517bDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointTypes
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O1517bLayer
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O1517bComponent
import CFSG.RankThree.GF2n.Stroth80.Sec4Comp
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Two
import CFSG.LocalAnalysis.GL83PartI.I_24_3.Gen
import CFSG.GroupTheory.ElemAbelianRank
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Reduced
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
import CFSG.RankThree.PartOne.CTP.StrongPGlue

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open Subgroup

private abbrev compN {X : Type} [Group X] (L : Subgroup X) : Subgroup X :=
  Subgroup.normalizer (L : Set X)

private abbrev compL {X : Type} [Group X] (L : Subgroup X) : Subgroup (compN L) :=
  L.subgroupOf (compN L)

private abbrev compAut {X : Type} [Group X] (L : Subgroup X) :
    ↥(compN L) →* MulAut ↥(compL L) :=
  MulAut.conjNormal

private lemma A_le_ker {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L) :
    A.subgroupOf (compN L) ≤ (compAut L).ker := by
  intro a ha
  rw [MonoidHom.mem_ker]
  ext x
  have haA : (a : X) ∈ A := Subgroup.mem_subgroupOf.mp ha
  have hc : (a : X) ∈ Subgroup.centralizer (L : Set X) :=
    Subgroup.mem_centralizer_iff.mp
      (Subgroup.le_centralizer_iff.mp (h.le_centralizer_A hL) haA)
  have hxL : (x : X) ∈ L := x.2
  have hcomm : (a : X) * (x : X) = (x : X) * (a : X) :=
    (Subgroup.mem_centralizer_iff.mp hc (x : X) hxL).symm
  change (a : X) * (x : X) * (a : X)⁻¹ = (x : X)
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

private lemma inf_ker_P_eq_A
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hLY : ¬ L ≤ Y) :
    (compAut L).ker ⊓ P.subgroupOf (compN L) = A.subgroupOf (compN L) := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxV, hxP⟩ := hx
    rw [MonoidHom.mem_ker] at hxV
    have hxX : (x : X) ∈ P := Subgroup.mem_subgroupOf.mp hxP
    have hxcent : (x : X) ∈ Subgroup.centralizer (L : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      let yN : compL L := ⟨⟨y, Subgroup.le_normalizer hy⟩, hy⟩
      have h1 : (compAut L) x yN = yN := by rw [hxV]; rfl
      have h2 : (x : X) * y * (x : X)⁻¹ = y := by
        have := congrArg (fun z : compL L => ((z : compN L) : X)) h1
        simpa [compAut, MulAut.conjNormal_apply] using this
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    have hxA : (x : X) ∈ A := by
      have hxinf : (x : X) ∈ P ⊓ Subgroup.centralizer (L : Set X) := ⟨hxX, hxcent⟩
      rwa [O1517bRed.inf_centralizer_eq hKA h hL hLY] at hxinf
    exact Subgroup.mem_subgroupOf.mpr hxA
  · exact le_inf (A_le_ker h hL) (Subgroup.subgroupOf_mono (compN L) h.le_P)

private lemma card_P₀
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hLY : ¬ L ≤ Y) :
    Nat.card ((P.subgroupOf (compN L)).map (compAut L)) = 9 := by
  have hPN : P ≤ compN L := O1517bRed.le_normalizer hKA h hL hLY
  have hformula : Nat.card (P.subgroupOf (compN L)) =
      Nat.card ((P.subgroupOf (compN L)).map (compAut L)) *
        Nat.card ↥((compAut L).ker ⊓ P.subgroupOf (compN L)) := by
    rw [← Subgroup.relIndex_ker (K := P.subgroupOf (compN L)) (f := compAut L)]
    exact (Subgroup.relIndex_mul_card _ _).symm
  rw [inf_ker_P_eq_A hKA h hL hLY,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (K := compN L)
      (h.le_P.trans hPN)).toEquiv, h.card_A] at hformula
  have hP27 := (O1517bRed.elem hKA h hL hLY).2
  rw [hP27] at hformula
  omega

private lemma isSylow_P₀
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hLY : ¬ L ≤ Y) :
    CFSG.ABGLocalTools.IsSylowOf 3
      ((P.subgroupOf (compN L)).map (compAut L)) (compAut L).range := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hPN : P ≤ compN L := O1517bRed.le_normalizer hKA h hL hLY
  have hleft : CFSG.ABGLocalTools.IsSylowOf 3
      ((P.subgroupOf (compN L)).map (compN L).subtype)
      ((⊤ : Subgroup ↥(compN L)).map (compN L).subtype) := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPN, Subgroup.map_top,
      Subgroup.range_subtype]
    exact h.sylow.of_le hPN le_top
  have hPNsyl : CFSG.ABGLocalTools.IsSylowOf 3 (P.subgroupOf (compN L)) ⊤ :=
    (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (compN L)).mp hleft
  simpa [Subgroup.map_top] using CFSG.ABGLocalTools.IsSylowOf.map hPNsyl (compAut L)

private lemma elem_P₀
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hLY : ¬ L ≤ Y) :
    CFSG.Open.IsElemAbelian 3 ((P.subgroupOf (compN L)).map (compAut L)) :=
  ((O1517bRed.elem hKA h hL hLY).1.subgroupOf (compN L)).map (compAut L)

private lemma catalog_range {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} :
    CFSG.AGLEmbedding.CatalogSimpleSections ↥(compAut L).range := by
  exact (h.catalog.subgroup (compN L)).of_surjective (compAut L).rangeRestrict
    (compAut L).rangeRestrict_surjective

private lemma center_compL_eq_bot
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hLY : ¬ L ≤ Y) :
    Subgroup.center ↥(compL L) = ⊥ := by
  have hZ : Subgroup.center ↥L = ⊥ := O1517bRed.center_eq_bot hKA h hL hLY
  have e : ↥(compL L) ≃* ↥L :=
    Subgroup.subgroupOfEquivOfLe (H := L) (K := compN L) Subgroup.le_normalizer
  have h := Subgroup.map_center_eq e
  rw [hZ] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h

private lemma simple_compL
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hLY : ¬ L ≤ Y) :
    IsSimpleGroup ↥(compL L) :=
  CFSG.RankThree.GF2n.Stroth80.isSimpleGroup_of_center_eq_bot
    (CFSG.LocalCores.component_overgroup hL Subgroup.le_normalizer)
    (center_compL_eq_bot hKA h hL hLY)

private lemma noncomm_compL {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L) :
    ∃ a b : ↥(compL L), a * b ≠ b * a :=
  CFSG.RankThree.GF2n.Stroth80.exists_noncomm_of_isComponent
    (CFSG.LocalCores.component_overgroup hL Subgroup.le_normalizer)

private lemma inn_le_range {X : Type} [Group X] {L : Subgroup X} :
    (MulAut.conj : ↥(compL L) →* MulAut ↥(compL L)).range ≤ (compAut L).range := by
  rintro _ ⟨l, rfl⟩
  refine ⟨l.1, ?_⟩
  ext x
  rfl

private lemma compAut_apply_compL {X : Type} [Group X] {L : Subgroup X} (l : compL L) :
    compAut L (l : compN L) = MulAut.conj l := by
  ext x
  rfl

private lemma coe_mem_centralizer_of_mem_ker {X : Type} [Group X] {L : Subgroup X}
    {v : compN L} (hv : v ∈ (compAut L).ker) :
    (v : X) ∈ Subgroup.centralizer (L : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  let yN : compL L := ⟨⟨y, Subgroup.le_normalizer hy⟩, hy⟩
  have h1 : (compAut L) v yN = yN := by rw [hv]; rfl
  have h2 : (v : X) * y * (v : X)⁻¹ = y := by
    have := congrArg (fun z : compL L => ((z : compN L) : X)) h1
    simpa [compAut, MulAut.conjNormal_apply] using this
  exact (mul_inv_eq_iff_eq_mul.mp h2).symm

private lemma inf_P_component_ne_bot
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hLY : ¬ L ≤ Y) : P ⊓ L ≠ ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPN : P ≤ compN L := O1517bRed.le_normalizer hKA h hL hLY
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P (compN L) := h.sylow.of_le hPN le_top
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ L) L :=
    hPsyl.inf_of_le_normalizer (N := L) (K := compN L) Subgroup.le_normalizer le_rfl
  have h3L : 3 ∣ Nat.card L :=
    CFSG.LocalAnalysis.RankThreeTheoremC.thc_dvd_card Nat.prime_three h.core hL
  intro hbot
  obtain ⟨S, hS⟩ := hsyl.exists_sylow_eq_subgroupOf
  have hSbot : (S : Subgroup L) = ⊥ := by
    rw [hS]
    simp [hbot]
  exact (Sylow.ne_bot_of_dvd_card S h3L) hSbot

private lemma exists_mem_Y_mul_centralizer
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hLY : ¬ L ≤ Y)
    (hInnY : (MulAut.conj : ↥(compL L) →* MulAut ↥(compL L)).range ≤
      (Y.subgroupOf (compN L)).map (compAut L))
    {g : X} (hgL : g ∈ L) :
    ∃ y : X, y ∈ Y ⊓ compN L ∧ ∃ v : X,
      v ∈ Subgroup.centralizer (L : Set X) ∧ g = y * v := by
  have hYN : Y ≤ compN L := O1517bRed.Y_le_normalizer hKA h hL hLY
  have hgN : g ∈ compN L := Subgroup.le_normalizer hgL
  let l : compL L := ⟨⟨g, hgN⟩, hgL⟩
  have hconj_in : MulAut.conj l ∈ (Y.subgroupOf (compN L)).map (compAut L) :=
    hInnY ⟨l, rfl⟩
  obtain ⟨yN, hyN, hmap⟩ := Subgroup.mem_map.mp hconj_in
  let v : compN L := (l : compN L)⁻¹ * yN
  have hvker : v ∈ (compAut L).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, compAut_apply_compL, hmap]
    exact inv_mul_cancel _
  have hvC : (v : X) ∈ Subgroup.centralizer (L : Set X) :=
    coe_mem_centralizer_of_mem_ker hvker
  refine ⟨(yN : X), ⟨Subgroup.mem_subgroupOf.mp hyN, yN.2⟩, ((v : X)⁻¹),
    Subgroup.inv_mem _ hvC, ?_⟩
  have h_eq : (l : compN L) * v = yN := by
    simp only [v, mul_inv_cancel_left]
  have hX : (l : X) * (v : X) = (yN : X) := congrArg (fun z : compN L => (z : X)) h_eq
  calc g = (l : X) := rfl
    _ = (yN : X) * (v : X)⁻¹ := by rw [← hX]; group

private lemma inf_Y_subgroupOf_normal
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hLY : ¬ L ≤ Y)
    (hInnY : (MulAut.conj : ↥(compL L) →* MulAut ↥(compL L)).range ≤
      (Y.subgroupOf (compN L)).map (compAut L)) :
    ((L ⊓ Y).subgroupOf L).Normal := by
  rw [Subgroup.normal_subgroupOf_iff inf_le_left]
  intro a k ha hk
  obtain ⟨y, hy, v, hvC, rfl⟩ := exists_mem_Y_mul_centralizer hKA h hL hLY hInnY hk
  have haL : a ∈ L := ha.1
  have haY : a ∈ Y := ha.2
  have hyY : y ∈ Y := hy.1
  have hyN : y ∈ compN L := hy.2
  have hvx : v * a * v⁻¹ = a := by
    rw [show v * a = a * v from (Subgroup.mem_centralizer_iff.mp hvC a haL).symm,
      mul_assoc, mul_inv_cancel, mul_one]
  rw [show y * v * a * (y * v)⁻¹ = y * (v * a * v⁻¹) * y⁻¹ by group, hvx]
  refine ⟨?_, ?_⟩
  · have hyL : y * a * y⁻¹ ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp hyN a).mp haL
      simpa using this
    exact hyL
  · exact Subgroup.mul_mem Y (Subgroup.mul_mem Y hyY haY) (Subgroup.inv_mem Y hyY)

private lemma not_inn_le
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hLY : ¬ L ≤ Y) :
    ¬ (MulAut.conj : ↥(compL L) →* MulAut ↥(compL L)).range ≤
      (Y.subgroupOf (compN L)).map (compAut L) := by
  intro hInnY
  have hPLne : P ⊓ L ≠ ⊥ := inf_P_component_ne_bot hKA h hL hLY
  have hne : L ⊓ Y ≠ ⊥ := by
    intro hbot
    apply hPLne
    rw [eq_bot_iff]
    exact (le_inf inf_le_right (inf_le_left.trans h.le_Y)).trans (le_of_eq hbot)
  have hnormal : ((L ⊓ Y).subgroupOf L).Normal :=
    inf_Y_subgroupOf_normal hKA h hL hLY hInnY
  have hne_sub : (L ⊓ Y).subgroupOf L ≠ ⊥ := by
    intro hbot
    apply hne
    have hmap := congrArg (Subgroup.map L.subtype) hbot
    rw [Subgroup.map_bot, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr inf_le_left] at hmap
    exact hmap
  haveI : IsSimpleGroup ↥L :=
    CFSG.RankThree.GF2n.Stroth80.isSimpleGroup_of_center_eq_bot hL
      (O1517bRed.center_eq_bot hKA h hL hLY)
  have htop : (L ⊓ Y).subgroupOf L = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L ⊓ Y).subgroupOf L) with hbot | htop
    · exact absurd hbot hne_sub
    · exact htop
  apply hLY
  intro x hxL
  have hxsub : (⟨x, hxL⟩ : ↥L) ∈ (L ⊓ Y).subgroupOf L := by rw [htop]; trivial
  exact (Subgroup.mem_subgroupOf.mp hxsub).2

private lemma P_le_normalizer_centralizer
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hLY : ¬ L ≤ Y) :
    P ≤ Subgroup.normalizer
      ((Subgroup.centralizer (L : Set X) : Subgroup X) : Set X) := by
  have hPN : P ≤ compN L := O1517bRed.le_normalizer hKA h hL hLY
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    exact GL83.I243.Gen.conj_mem_centralizer (hPN hp) hc
  · intro hc
    have h := GL83.I243.Gen.conj_mem_centralizer (Subgroup.inv_mem _ (hPN hp)) hc
    have heq : p⁻¹ * (p * c * p⁻¹) * p = c := by group
    simpa [heq] using h

private lemma ker_map_subtype_eq_centralizer {X : Type} [Group X] {L : Subgroup X} :
    (compAut L).ker.map (compN L).subtype =
      Subgroup.centralizer (L : Set X) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact coe_mem_centralizer_of_mem_ker hv
  · intro hx
    have hxN : x ∈ compN L :=
      Subgroup.centralizer_le_normalizer (L : Set X) hx
    refine ⟨⟨x, hxN⟩, ?_, rfl⟩
    change (compAut L) ⟨x, hxN⟩ = 1
    ext y
    change x * (y : X) * x⁻¹ = (y : X)
    have hcomm : x * (y : X) = (y : X) * x :=
      (Subgroup.mem_centralizer_iff.mp hx (y : X) y.2).symm
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

private lemma isSylow_A_ker
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hLY : ¬ L ≤ Y) :
    CFSG.ABGLocalTools.IsSylowOf 3 (A.subgroupOf (compN L)) (compAut L).ker := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hPC : P ≤ Subgroup.normalizer
      ((Subgroup.centralizer (L : Set X) : Subgroup X) : Set X) :=
    P_le_normalizer_centralizer hKA h hL hLY
  let C : Subgroup X := Subgroup.centralizer (L : Set X)
  have hPM : CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.normalizer (C : Set X)) :=
    h.sylow.of_le hPC le_top
  have hAsylC : CFSG.ABGLocalTools.IsSylowOf 3 A C := by
    have hP := hPM.inf_of_le_normalizer (N := C) (K := Subgroup.normalizer (C : Set X))
      Subgroup.le_normalizer le_rfl
    rwa [O1517bRed.inf_centralizer_eq hKA h hL hLY] at hP
  have hPN : P ≤ compN L := O1517bRed.le_normalizer hKA h hL hLY
  rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (compN L)]
  rw [ker_map_subtype_eq_centralizer, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (h.le_P.trans hPN)]
  exact hAsylC

private lemma factorization_card_ker
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hLY : ¬ L ≤ Y) :
    (Nat.card (compAut L).ker).factorization 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hPN : P ≤ compN L := O1517bRed.le_normalizer hKA h hL hLY
  have hAsyl : CFSG.ABGLocalTools.IsSylowOf 3 (A.subgroupOf (compN L))
      (compAut L).ker := isSylow_A_ker hKA h hL hLY
  have hcardA : Nat.card (A.subgroupOf (compN L)) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (K := compN L) (h.le_P.trans hPN)).toEquiv).trans h.card_A
  have hcard := hAsyl.card_eq
  rw [hcardA] at hcard
  refine Nat.pow_right_injective (by norm_num : 2 ≤ 3) ?_
  simpa using hcard.symm

private abbrev preW {X : Type} [Group X] {L : Subgroup X}
    (D : Subgroup (MulAut ↥(compL L))) : Subgroup (compN L) :=
  D.comap (compAut L)

private lemma map_preW {X : Type} [Group X] {L : Subgroup X}
    {D : Subgroup (MulAut ↥(compL L))} (hD : D ≤ (compAut L).range) :
    (preW D).map (compAut L) = D := by
  ext d
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hd
    obtain ⟨p, hpd⟩ := MonoidHom.mem_range.mp (hD hd)
    exact ⟨p, by change (compAut L) p ∈ D; rw [hpd]; exact hd, hpd⟩

private lemma map_inf_preW {X : Type} [Group X] {P : Subgroup X} {L : Subgroup X}
    {D : Subgroup (MulAut ↥(compL L))}
    (hD : D ≤ (P.subgroupOf (compN L)).map (compAut L)) :
    ((P.subgroupOf (compN L) ⊓ preW D).map (compAut L)) = D := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact hz.2
  · intro d hd
    obtain ⟨p, hp, hpd⟩ := Subgroup.mem_map.mp (hD hd)
    exact ⟨p, ⟨hp, by change (compAut L) p ∈ D; rw [hpd]; exact hd⟩, hpd⟩

private lemma card_preW
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hLY : ¬ L ≤ Y) {D : Subgroup (MulAut ↥(compL L))}
    (hD : D ≤ (P.subgroupOf (compN L)).map (compAut L)) :
    Nat.card ↥(preW D) = Nat.card ↥D * Nat.card ↥(compAut L).ker := by
  have hDrange : D ≤ (compAut L).range :=
    hD.trans (Subgroup.map_le_range (compAut L) (P.subgroupOf (compN L)))
  have hWmap : (preW D).map (compAut L) = D := map_preW hDrange
  have hkerle : (compAut L).ker ≤ preW D := by
    intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact D.one_mem
  have h1 : Nat.card ↥(preW D) = Nat.card ↥((preW D).map (compAut L)) *
      Nat.card ↥((compAut L).ker ⊓ preW D) := by
    rw [← Subgroup.relIndex_mul_card (H := (compAut L).ker) (K := preW D),
      Subgroup.relIndex_ker]
  rw [hWmap, inf_eq_left.mpr hkerle] at h1
  exact h1

private lemma card_inf_preW
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hLY : ¬ L ≤ Y) {D : Subgroup (MulAut ↥(compL L))}
    (hD : D ≤ (P.subgroupOf (compN L)).map (compAut L)) :
    Nat.card ↥(P.subgroupOf (compN L) ⊓ preW D) = Nat.card ↥D * 3 := by
  have hPN : P ≤ compN L := O1517bRed.le_normalizer hKA h hL hLY
  have hD₁map : ((P.subgroupOf (compN L) ⊓ preW D).map (compAut L)) = D :=
    map_inf_preW hD
  have hkerD₁ : (compAut L).ker ⊓ (P.subgroupOf (compN L) ⊓ preW D) =
      A.subgroupOf (compN L) := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      have hx' : x ∈ (compAut L).ker ⊓ P.subgroupOf (compN L) := ⟨hx.1, hx.2.1⟩
      rwa [inf_ker_P_eq_A hKA h hL hLY] at hx'
    · refine le_inf (A_le_ker h hL) (le_inf (Subgroup.subgroupOf_mono (compN L) h.le_P) ?_)
      intro a ha
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp (A_le_ker h hL ha)]
      exact D.one_mem
  have hcardA : Nat.card (A.subgroupOf (compN L)) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (K := compN L) (h.le_P.trans hPN)).toEquiv).trans h.card_A
  have h1 : Nat.card ↥(P.subgroupOf (compN L) ⊓ preW D) =
      Nat.card ↥((P.subgroupOf (compN L) ⊓ preW D).map (compAut L)) *
        Nat.card ↥((compAut L).ker ⊓ (P.subgroupOf (compN L) ⊓ preW D)) := by
    rw [← Subgroup.relIndex_mul_card
      (H := (compAut L).ker) (K := P.subgroupOf (compN L) ⊓ preW D),
      Subgroup.relIndex_ker]
  rwa [hD₁map, hkerD₁, hcardA] at h1

private lemma isSylow_inf_preW
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hLY : ¬ L ≤ Y) {D : Subgroup (MulAut ↥(compL L))}
    (hD : D ≤ (P.subgroupOf (compN L)).map (compAut L)) (hDne : D ≠ ⊥) :
    CFSG.ABGLocalTools.IsSylowOf 3 (P.subgroupOf (compN L) ⊓ preW D) (preW D) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hP₀3 : IsPGroup 3 ↥((P.subgroupOf (compN L)).map (compAut L)) :=
    (elem_P₀ hKA h hL hLY).isPGroup
  have hD3 : IsPGroup 3 ↥D := hP₀3.to_le hD
  obtain ⟨k, hk⟩ := hD3.exists_card_eq
  refine CFSG.ABGLocalTools.isSylowOf_of_card (p := 3) inf_le_right ?_
  rw [card_inf_preW hKA h hL hLY hD, card_preW hKA h hL hLY hD, hk,
    Nat.factorization_mul (pow_ne_zero k (by norm_num))
      (Nat.card_pos (α := ↥(compAut L).ker)).ne', Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    factorization_card_ker hKA h hL hLY, pow_succ]

private lemma two_le_pRank_inf_preW
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hLY : ¬ L ≤ Y) {D : Subgroup (MulAut ↥(compL L))}
    (hD : D ≤ (P.subgroupOf (compN L)).map (compAut L)) (hDne : D ≠ ⊥) :
    2 ≤ CFSG.Open.pRank 3
      (((P.subgroupOf (compN L) ⊓ preW D).map (compN L).subtype)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hD₁elem : CFSG.Open.IsElemAbelian 3 (P.subgroupOf (compN L) ⊓ preW D) :=
    ((O1517bRed.elem hKA h hL hLY).1.subgroupOf (compN L)).mono inf_le_left
  have hmapelem : CFSG.Open.IsElemAbelian 3
      ((P.subgroupOf (compN L) ⊓ preW D).map (compN L).subtype) :=
    hD₁elem.map (compN L).subtype
  have h3D : 3 ∣ Nat.card ↥D := by
    have hP₀3 : IsPGroup 3 ↥((P.subgroupOf (compN L)).map (compAut L)) :=
      (elem_P₀ hKA h hL hLY).isPGroup
    have hD3 : IsPGroup 3 ↥D := hP₀3.to_le hD
    rcases hD3.card_eq_or_dvd with h1 | h3
    · exact absurd (Subgroup.eq_bot_of_card_eq D h1) hDne
    · exact h3
  have h9 : 9 ∣ Nat.card ↥((P.subgroupOf (compN L) ⊓ preW D).map
      (compN L).subtype) := by
    rw [Subgroup.card_map_of_injective (f := (compN L).subtype)
      (K := P.subgroupOf (compN L) ⊓ preW D) (compN L).subtype_injective,
      card_inf_preW hKA h hL hLY hD]
    have h9' : 3 * 3 ∣ Nat.card ↥D * 3 := Nat.mul_dvd_mul_right h3D 3
    simpa [show (9 : ℕ) = 3 * 3 by norm_num] using h9'
  have hcard := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hmapelem
  rw [hcard] at h9
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp (by simpa using h9)

private lemma mem_normalizer_preW {X : Type} [Group X] {L : Subgroup X}
    {D : Subgroup (MulAut ↥(compL L))} {xN : ↥(compN L)}
    (hxnorm : (compAut L) xN ∈
      Subgroup.normalizer (D : Set (MulAut ↥(compL L)))) :
    xN ∈ Subgroup.normalizer (preW D : Set ↥(compN L)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    change (compAut L) (xN * w * xN⁻¹) ∈ D
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hxnorm ((compAut L) w)).mp hw
  · intro hw
    change (compAut L) w ∈ D
    exact (Subgroup.mem_normalizer_iff.mp hxnorm ((compAut L) w)).mpr (by
      change (compAut L) (xN * w * xN⁻¹) ∈ D at hw
      simpa [map_mul, map_inv] using hw)

private lemma normalizer_inter_le
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hLY : ¬ L ≤ Y) :
    ∀ D : Subgroup (MulAut ↥(compL L)),
      D ≤ (P.subgroupOf (compN L)).map (compAut L) → D ≠ ⊥ →
      (compAut L).range ⊓
        Subgroup.normalizer (D : Set (MulAut ↥(compL L))) ≤
        (Y.subgroupOf (compN L)).map (compAut L) := by
  intro D hD hDne x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxrange, hxnorm⟩ := hx
  obtain ⟨xN, rfl⟩ := MonoidHom.mem_range.mp hxrange
  let W : Subgroup ↥(compN L) := preW D
  let D₁ : Subgroup ↥(compN L) := P.subgroupOf (compN L) ⊓ W
  have hWN : xN ∈ Subgroup.normalizer (W : Set ↥(compN L)) := by
    simpa [W] using mem_normalizer_preW hxnorm
  have hD₁syl : CFSG.ABGLocalTools.IsSylowOf 3 D₁ W :=
    isSylow_inf_preW hKA h hL hLY hD hDne
  obtain ⟨w, hwW, n, hn, hwn⟩ :=
    CFSG.RankThree.PartTwo.Sec18.exists_mul_of_isSylowOf
      (B := D₁) (N := W) (K := Subgroup.normalizer (W : Set ↥(compN L)))
      hD₁syl le_rfl hWN
  have hPN : P ≤ compN L := O1517bRed.le_normalizer hKA h hL hLY
  have hD₁P : D₁.map (compN L).subtype ≤ P := by
    calc D₁.map (compN L).subtype
        ≤ (P.subgroupOf (compN L)).map (compN L).subtype := Subgroup.map_mono inf_le_left
      _ = P := by rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPN]
  have hnXnorm : (n : X) ∈ Subgroup.normalizer
      ((D₁.map (compN L).subtype : Subgroup X) : Set X) :=
    Subgroup.le_normalizer_map (H := D₁) (compN L).subtype
      (Subgroup.mem_map_of_mem (compN L).subtype hn)
  have hnΓ : (n : X) ∈ CFSG.Open.rankThreeGamma 2 3 P := by
    change (n : X) ∈ CFSG.Open.GLBCore 3 2 P
    have hmem : Subgroup.normalizer ((D₁.map (compN L).subtype : Subgroup X) : Set X) ∈
        {N : Subgroup X | ∃ Q : Subgroup X, Q ≤ P ∧ 2 ≤ CFSG.Open.pRank 3 Q ∧
          N = Subgroup.normalizer (Q : Set X)} :=
      ⟨D₁.map (compN L).subtype, hD₁P,
        two_le_pRank_inf_preW hKA h hL hLY hD hDne, rfl⟩
    exact (le_sSup hmem) hnXnorm
  have hnY : (n : X) ∈ Y := h.gamma hnΓ
  have hnY₀ : (compAut L) n ∈ (Y.subgroupOf (compN L)).map (compAut L) :=
    Subgroup.mem_map_of_mem (compAut L) (Subgroup.mem_subgroupOf.mpr hnY)
  have hP₀_le_Y₀ : (P.subgroupOf (compN L)).map (compAut L) ≤
      (Y.subgroupOf (compN L)).map (compAut L) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono (compN L) h.le_Y)
  have hwY₀ : (compAut L) w ∈ (Y.subgroupOf (compN L)).map (compAut L) :=
    hP₀_le_Y₀ (hD hwW)
  rw [hwn, map_mul]
  exact Subgroup.mul_mem _ hwY₀ hnY₀

private lemma strong_sylow_map_eq_bot
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hLY : ¬ L ≤ Y)
    (hprimes : ∀ r : ℕ, r.Prime →
      r ∣ Nat.card ((Y.subgroupOf (compN L)).map (compAut L)) → r = 2 ∨ r = 3) :
    ∃ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf p S ⊤ ∧ S ≤ Y ∧ S ≠ ⊥ ∧
      (S.subgroupOf (compN L)).map (compAut L) = ⊥ := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hYN : Y ≤ compN L := O1517bRed.Y_le_normalizer hKA h hL hLY
  obtain ⟨S, hS, hSY⟩ :=
    CFSG.RankThree.PartOne.IsStronglyPEmbedded.exists_isSylowOf_le h.strong
  have hSabg : CFSG.ABGLocalTools.IsSylowOf p S ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_iff.2 hS
  have hSYN : S ≤ compN L := hSY.trans hYN
  have hpX : p ∣ Nat.card X :=
    h.strong.2.1.trans (by
      simpa using Subgroup.card_dvd_of_le (le_top : Y ≤ (⊤ : Subgroup X)))
  have hSne : S ≠ ⊥ := by
    have hfac : 0 < (Nat.card X).factorization p :=
      h.prime.factorization_pos_of_dvd (Nat.card_pos.ne') hpX
    have hpS : p ∣ Nat.card S := by
      rw [hSabg.card_eq]
      exact dvd_pow_self p (by rw [Subgroup.card_top]; exact hfac.ne')
    intro hSbot
    rw [hSbot, Subgroup.card_bot] at hpS
    exact h.prime.not_dvd_one hpS
  have hSp : IsPGroup p (S.subgroupOf (compN L)) := hSabg.isPGroup.comap_subtype
  have hSmap_bot : (S.subgroupOf (compN L)).map (compAut L) = ⊥ := by
    by_contra hne
    have hSp' : IsPGroup p ((S.subgroupOf (compN L)).map (compAut L)) := hSp.map (compAut L)
    have hpcard : p ∣ Nat.card ((S.subgroupOf (compN L)).map (compAut L)) := by
      rcases hSp'.card_eq_or_dvd with h1 | h3
      · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hne
      · exact h3
    have hle : (S.subgroupOf (compN L)).map (compAut L) ≤
        (Y.subgroupOf (compN L)).map (compAut L) :=
      Subgroup.map_mono (Subgroup.subgroupOf_mono (compN L) hSY)
    have hpY : p ∣ Nat.card ((Y.subgroupOf (compN L)).map (compAut L)) :=
      hpcard.trans (Subgroup.card_dvd_of_le hle)
    have hp23 := hprimes p h.prime hpY
    have h5 : 5 ≤ p := h.five_le
    rcases hp23 with h2 | h3
    · omega
    · omega
  exact ⟨S, hSabg, hSY, hSne, hSmap_bot⟩

private lemma range_le_image_Y
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (hKB : KFactE9AutTwoThree)
    {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (h : O1517bRed X p P A Y) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hLY : ¬ L ≤ Y) :
    (compAut L).range ≤ (Y.subgroupOf (compN L)).map (compAut L) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hprimes : ∀ r : ℕ, r.Prime →
      r ∣ Nat.card ((Y.subgroupOf (compN L)).map (compAut L)) → r = 2 ∨ r = 3 :=
    hKB ↥(compL L) (simple_compL hKA h hL hLY) (noncomm_compL h hL)
      (compAut L).range ((P.subgroupOf (compN L)).map (compAut L))
      ((Y.subgroupOf (compN L)).map (compAut L)) inn_le_range (catalog_range h)
      (isSylow_P₀ hKA h hL hLY) (elem_P₀ hKA h hL hLY) (card_P₀ hKA h hL hLY)
      (Subgroup.map_le_range (compAut L) (Y.subgroupOf (compN L)))
      (normalizer_inter_le hKA h hL hLY) (not_inn_le hKA h hL hLY)
  obtain ⟨S, hSabg, hSY, hSne, hSmap_bot⟩ :=
    strong_sylow_map_eq_bot hKA h hL hLY hprimes
  have hYN : Y ≤ compN L := O1517bRed.Y_le_normalizer hKA h hL hLY
  have hSYN : S ≤ compN L := hSY.trans hYN
  let V : Subgroup ↥(compN L) := (compAut L).ker
  have hSker : S.subgroupOf (compN L) ≤ V :=
    (Subgroup.map_eq_bot_iff (S.subgroupOf (compN L)) (f := compAut L)).mp hSmap_bot
  have hSleV : S ≤ V.map (compN L).subtype := by
    intro x hx
    have hxN : x ∈ compN L := hSYN hx
    have hxsub : (⟨x, hxN⟩ : ↥(compN L)) ∈ S.subgroupOf (compN L) :=
      Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_map_of_mem (compN L).subtype (hSker hxsub)
  have hSVN : CFSG.ABGLocalTools.IsSylowOf p (S.subgroupOf (compN L)) V := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (compN L)]
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSYN]
    exact hSabg.of_le hSleV le_top
  haveI hVn : V.Normal := MonoidHom.normal_ker (compAut L)
  have hFrattiniN : (⊤ : Subgroup ↥(compN L)) ≤
      V ⊔ Subgroup.normalizer ((S.subgroupOf (compN L) : Subgroup ↥(compN L)) :
        Set ↥(compN L)) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.le_sup_normalizer_of_isSylowOf
      (H := ⊤) (Y := V) (S := S.subgroupOf (compN L))
      (le_of_eq (Subgroup.normalizer_eq_top V).symm) hSVN
  intro x hx
  obtain ⟨n, rfl⟩ := MonoidHom.mem_range.mp hx
  obtain ⟨v, hv, t, ht, hvt⟩ :=
    Subgroup.mem_sup_of_normal_left.mp (hFrattiniN (Subgroup.mem_top n))
  have hvker : (compAut L) v = 1 := MonoidHom.mem_ker.mp hv
  have htX : (t : X) ∈ Subgroup.normalizer (S : Set X) := by
    have h := Subgroup.le_normalizer_map (H := S.subgroupOf (compN L)) (compN L).subtype
      (Subgroup.mem_map_of_mem (compN L).subtype ht)
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSYN] at h
  have htY : (t : X) ∈ Y := h.strong.normalizer_le hSne hSabg.isPGroup hSY htX
  have htY₀ : (compAut L) t ∈ (Y.subgroupOf (compN L)).map (compAut L) :=
    Subgroup.mem_map_of_mem (compAut L) (Subgroup.mem_subgroupOf.mpr htY)
  rw [← hvt, map_mul, hvker, one_mul]
  exact htY₀

theorem O1517bRed.false {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (hKB : KFactE9AutTwoThree) (h : O1517bRed X p P A Y) : False := by
  obtain ⟨L, hL, hLY⟩ := h.exists_component_not_le
  exact not_inn_le hKA h hL hLY
    (inn_le_range.trans (range_le_image_Y hKA hKB h hL hLY))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
