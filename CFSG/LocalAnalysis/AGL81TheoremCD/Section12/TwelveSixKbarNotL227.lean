module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarInputs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixSigns
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarAut
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K4L227
import CFSG.Blueprint.LieModelAPI
import CFSG.RankThree.PartTwo.Sec15.F153L3C2Quot
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixInvariantX

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

private theorem center_eq_bot_of_kbar_l227
    (hK : IsTwoPrimeComponentIn (kSub p M H) H)
    (h27 : LieModel (kbarQuot p M H) .PSL 2 3 3) :
    center (modTwoCore (kSub p M H)) = ⊥ := by
  have hodd : Odd (Nat.card (center (modTwoCore (kSub p M H)))) :=
    CFSG.RankThree.PartTwo.Sec15.F153L3C2.odd_card_center_of_pCore_eq_bot
      (CFSG.RankThree.PartTwo.Sec15.F153L3C2.quot_pCore_two_eq_bot (kSub p M H))
  exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.center_eq_bot_of_k4a_hyp
    (modTwoCore (kSub p M H)) hK.2.2.1 hodd h27

private theorem kbarConj_injective_on_V
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hKH : ((kSub p M H).subgroupOf H).Normal)
    (hVX : D.V ⊓ xSub p M H = ⊥) :
    Function.Injective ((kbarConj hKH).comp (D.V.subgroupOf H).subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hxker : (x : ↥H) ∈ (kbarConj hKH).ker := by
    rw [MonoidHom.mem_ker]
    simpa using MonoidHom.mem_ker.mp hx
  have hxX : ((x : ↥H) : G) ∈ xSub p M H :=
    Subgroup.mem_subgroupOf.mp (TwelveCtx.ker_kbarConj_le hc.ctx hKH hxker)
  have hxV : ((x : ↥H) : G) ∈ D.V := Subgroup.mem_subgroupOf.mp x.2
  have hxbot : ((x : ↥H) : G) ∈ (⊥ : Subgroup G) := by
    rw [← hVX]
    exact ⟨hxV, hxX⟩
  exact Subtype.ext (Subtype.ext (Subgroup.mem_bot.mp hxbot))

private theorem kbarConj_ne_one
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hKH : ((kSub p M H).subgroupOf H).Normal)
    {V : Subgroup G} (hVX : V ⊓ xSub p M H = ⊥)
    {w : G} (hwV : w ∈ V) (hwH : w ∈ H) (hw1 : w ≠ 1) :
    kbarConj hKH ⟨w, hwH⟩ ≠ 1 := by
  intro h
  have hker : (⟨w, hwH⟩ : ↥H) ∈ (kbarConj hKH).ker := MonoidHom.mem_ker.mpr h
  have hX : w ∈ xSub p M H :=
    Subgroup.mem_subgroupOf.mp (TwelveCtx.ker_kbarConj_le hc.ctx hKH hker)
  have hbot : w ∈ (⊥ : Subgroup G) := by
    rw [← hVX]
    exact ⟨hwV, hX⟩
  exact hw1 (Subgroup.mem_bot.mp hbot)

private theorem kbarConj_t₁_mem_normalizer_V
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hKH : ((kSub p M H).subgroupOf H).Normal)
    (hVH : D.V ≤ H) :
    kbarConj hKH ⟨D.t₁, (D.t₁_mem hc.data).1⟩ ∈
      Subgroup.normalizer (((D.V.subgroupOf H).map (kbarConj hKH)) :
        Set (MulAut (modTwoCore (kSub p M H)))) := by
  have ht₁NV : D.t₁ ∈ Subgroup.normalizer (D.V : Set G) :=
    IsE27InvConfig.tripleNormalizer_le_normalizer D.cfg
      (IsE27InvConfig.t₁_mem_tripleNormalizer D.cfg)
  have ht₁NVH : (⟨D.t₁, (D.t₁_mem hc.data).1⟩ : ↥H) ∈
      Subgroup.normalizer ((D.V.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hVH]
    exact Subgroup.mem_subgroupOf.mpr ht₁NV
  have hmem : kbarConj hKH ⟨D.t₁, (D.t₁_mem hc.data).1⟩ ∈
      (Subgroup.normalizer ((D.V.subgroupOf H : Subgroup ↥H))).map (kbarConj hKH) :=
    Subgroup.mem_map.mpr ⟨⟨D.t₁, (D.t₁_mem hc.data).1⟩, ht₁NVH, rfl⟩
  exact Subgroup.le_normalizer_map (H := D.V.subgroupOf H) (kbarConj hKH) hmem

private theorem kbar_l227_image
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hKH : ((kSub p M H).subgroupOf H).Normal)
    (hVH : D.V ≤ H) (hVX : D.V ⊓ xSub p M H = ⊥) :
    ∃ E : Subgroup (MulAut (modTwoCore (kSub p M H))),
      IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
      E = (D.V.subgroupOf H).map (kbarConj hKH) := by
  let f := kbarConj hKH
  let VH := D.V.subgroupOf H
  let ψ := f.comp VH.subtype
  have hψinj : Function.Injective ψ := kbarConj_injective_on_V hc D hKH hVX
  have hErange : ψ.range = VH.map f := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact Subgroup.mem_map.mpr ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨⟨y, hy⟩, rfl⟩
  refine ⟨ψ.range, ?_, ?_, hErange⟩
  · rw [hErange]
    exact (D.cfg.elem.subgroupOf H).map f
  · rw [← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv, D.cfg.card]

private theorem kbarConj_inv_W₁
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hKH : ((kSub p M H).subgroupOf H).Normal)
    {w : G} (hw : w ∈ D.W₁) (hwH : w ∈ H) :
    kbarConj hKH ⟨D.t₁, (D.t₁_mem hc.data).1⟩ * kbarConj hKH ⟨w, hwH⟩ *
      (kbarConj hKH ⟨D.t₁, (D.t₁_mem hc.data).1⟩)⁻¹ =
      (kbarConj hKH ⟨w, hwH⟩)⁻¹ := by
  let t₁H : ↥H := ⟨D.t₁, (D.t₁_mem hc.data).1⟩
  let wH : ↥H := ⟨w, hwH⟩
  have ht : t₁H * wH * t₁H⁻¹ = wH⁻¹ := by
    apply Subtype.ext
    simpa [t₁H, wH] using D.cfg.inv₁ w hw
  calc
    kbarConj hKH t₁H * kbarConj hKH wH * (kbarConj hKH t₁H)⁻¹
        = kbarConj hKH (t₁H * wH) * (kbarConj hKH t₁H)⁻¹ := by rw [map_mul]
    _ = kbarConj hKH (t₁H * wH * t₁H⁻¹) := by simp only [map_mul, map_inv]
    _ = kbarConj hKH wH⁻¹ := by rw [ht]
    _ = (kbarConj hKH wH)⁻¹ := map_inv _ _

private theorem kbarConj_fix_W₂
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hKH : ((kSub p M H).subgroupOf H).Normal)
    {w : G} (hw : w ∈ D.W₂) (hwH : w ∈ H) :
    kbarConj hKH ⟨D.t₁, (D.t₁_mem hc.data).1⟩ * kbarConj hKH ⟨w, hwH⟩ *
      (kbarConj hKH ⟨D.t₁, (D.t₁_mem hc.data).1⟩)⁻¹ = kbarConj hKH ⟨w, hwH⟩ := by
  let t₁H : ↥H := ⟨D.t₁, (D.t₁_mem hc.data).1⟩
  let wH : ↥H := ⟨w, hwH⟩
  have ht : t₁H * wH * t₁H⁻¹ = wH := by
    have hcomm : t₁H * wH = wH * t₁H := by
      apply Subtype.ext
      simpa [t₁H, wH] using D.cfg.comm₁ w (Subgroup.mem_sup_left hw)
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  calc
    kbarConj hKH t₁H * kbarConj hKH wH * (kbarConj hKH t₁H)⁻¹
        = kbarConj hKH (t₁H * wH) * (kbarConj hKH t₁H)⁻¹ := by rw [map_mul]
    _ = kbarConj hKH (t₁H * wH * t₁H⁻¹) := by simp only [map_mul, map_inv]
    _ = kbarConj hKH wH := by rw [ht]

private theorem kbar_l227_elements
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hKH : ((kSub p M H).subgroupOf H).Normal)
    (hVH : D.V ≤ H) (hVX : D.V ⊓ xSub p M H = ⊥)
    (E : Subgroup (MulAut (modTwoCore (kSub p M H))))
    (hE : E = (D.V.subgroupOf H).map (kbarConj hKH)) :
    ∃ a v₁ v₂ : MulAut (modTwoCore (kSub p M H)),
      a ∈ Subgroup.normalizer (E : Set (MulAut (modTwoCore (kSub p M H)))) ∧
      v₁ ∈ E ∧ v₂ ∈ E ∧ v₁ ≠ 1 ∧ v₂ ≠ 1 ∧
      a * v₁ * a⁻¹ = v₁⁻¹ ∧ a * v₂ * a⁻¹ = v₂ := by
  have hW₁H : D.W₁ ≤ H := D.le₁.trans (D.le_inf₁.trans inf_le_left)
  have hW₂H : D.W₂ ≤ H := D.le₂.trans (D.le_inf₂.trans inf_le_left)
  have hW₁V : D.W₁ ≤ D.V := by
    rw [D.cfg.join]
    exact le_sup_left.trans le_sup_left
  have hW₂V : D.W₂ ≤ D.V := by
    rw [D.cfg.join]
    exact le_sup_right.trans le_sup_left
  haveI : Nontrivial ↥D.W₁ :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [D.cfg.card₁]; norm_num)
  obtain ⟨w₁, hw₁1⟩ := exists_ne (1 : ↥D.W₁)
  haveI : Nontrivial ↥D.W₂ :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [D.cfg.card₂]; norm_num)
  obtain ⟨w₂, hw₂1⟩ := exists_ne (1 : ↥D.W₂)
  let t₁H : ↥H := ⟨D.t₁, (D.t₁_mem hc.data).1⟩
  let w₁H : ↥H := ⟨(w₁ : G), hW₁H w₁.2⟩
  let w₂H : ↥H := ⟨(w₂ : G), hW₂H w₂.2⟩
  let a : MulAut (modTwoCore (kSub p M H)) := kbarConj hKH t₁H
  let v₁ : MulAut (modTwoCore (kSub p M H)) := kbarConj hKH w₁H
  let v₂ : MulAut (modTwoCore (kSub p M H)) := kbarConj hKH w₂H
  have hv₁E : v₁ ∈ E := by
    rw [hE]
    exact Subgroup.mem_map.mpr ⟨w₁H, Subgroup.mem_subgroupOf.mpr (hW₁V w₁.2), rfl⟩
  have hv₂E : v₂ ∈ E := by
    rw [hE]
    exact Subgroup.mem_map.mpr ⟨w₂H, Subgroup.mem_subgroupOf.mpr (hW₂V w₂.2), rfl⟩
  have hv₁1 : v₁ ≠ 1 :=
    kbarConj_ne_one hc hKH hVX (hW₁V w₁.2) (hW₁H w₁.2)
      (fun h => hw₁1 (Subtype.ext h))
  have hv₂1 : v₂ ≠ 1 :=
    kbarConj_ne_one hc hKH hVX (hW₂V w₂.2) (hW₂H w₂.2)
      (fun h => hw₂1 (Subtype.ext h))
  have haN : a ∈ Subgroup.normalizer (E : Set (MulAut (modTwoCore (kSub p M H)))) := by
    rw [hE]
    exact kbarConj_t₁_mem_normalizer_V hc D hKH hVH
  have hconj₁ : a * v₁ * a⁻¹ = v₁⁻¹ := kbarConj_inv_W₁ hc D hKH w₁.2 (hW₁H w₁.2)
  have hconj₂ : a * v₂ * a⁻¹ = v₂ :=
    kbarConj_fix_W₂ hc D hKH w₂.2 (hW₂H w₂.2)
  exact ⟨a, v₁, v₂, haN, hv₁E, hv₂E, hv₁1, hv₂1, hconj₁, hconj₂⟩

private theorem kbar_l227_config
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hKH : ((kSub p M H).subgroupOf H).Normal)
    (hVH : D.V ≤ H) (hVX : D.V ⊓ xSub p M H = ⊥) :
    ∃ (E : Subgroup (MulAut (modTwoCore (kSub p M H))))
      (a v₁ v₂ : MulAut (modTwoCore (kSub p M H))),
      IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
      a ∈ Subgroup.normalizer (E : Set (MulAut (modTwoCore (kSub p M H)))) ∧
      v₁ ∈ E ∧ v₂ ∈ E ∧ v₁ ≠ 1 ∧ v₂ ≠ 1 ∧
      a * v₁ * a⁻¹ = v₁⁻¹ ∧ a * v₂ * a⁻¹ = v₂ := by
  obtain ⟨E, hEelem, hEcard, hE⟩ := kbar_l227_image hc D hKH hVH hVX
  obtain ⟨a, v₁, v₂, haN, hv₁E, hv₂E, hv₁1, hv₂1, hconj₁, hconj₂⟩ :=
    kbar_l227_elements hc D hKH hVH hVX E hE
  exact ⟨E, a, v₁, v₂, hEelem, hEcard, haN, hv₁E, hv₂E, hv₁1, hv₂1,
    hconj₁, hconj₂⟩

theorem TwelveSixKCtx.false_of_kbar_l227
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hKH : ((kSub p M H).subgroupOf H).Normal)
    (hK : IsTwoPrimeComponentIn (kSub p M H) H)
    (hL27 : KFactL227AutE27)
    (h27 : LieModel (kbarQuot p M H) .PSL 2 3 3) : False := by
  have hZ : center (modTwoCore (kSub p M H)) = ⊥ :=
    center_eq_bot_of_kbar_l227 hK h27
  have hY : LieModel (modTwoCore (kSub p M H)) .PSL 2 3 3 :=
    LieModel.of_quotient_center hZ h27
  have hVH : D.V ≤ H := (D.V_le.trans (D.sup_le hc.data)).trans inf_le_left
  have hVX : D.V ⊓ xSub p M H = ⊥ :=
    hc.inf_xSub_eq_bot D.cfg (D.centralizer_le₁ hc) (D.centralizer_le₂ hc)
      (D.centralizer_le₃ hc) (D.t₁_mem hc.data) (D.t₂_mem hc.data) (D.t₃_mem hc.data)
  obtain ⟨E, a, v₁, v₂, hEelem, hEcard, haN, hv₁E, hv₂E, hv₁1, hv₂1,
    hconj₁, hconj₂⟩ := kbar_l227_config hc D hKH hVH hVX
  exact hL27 (modTwoCore (kSub p M H)) hY E hEelem hEcard a v₁ v₂ haN hv₁E hv₂E
    hv₁1 hv₂1 hconj₁ hconj₂

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
