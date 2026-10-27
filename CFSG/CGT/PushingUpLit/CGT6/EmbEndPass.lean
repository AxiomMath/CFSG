module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndQuot
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndStd

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG
open scoped commutatorElement

section Basic

variable {Γ : Type} [Group Γ]

theorem zc_eq_map_center (Λ : Subgroup Γ) :
    EndQuot.zc Λ = (Subgroup.center ↥Λ).map Λ.subtype := by
  ext x
  rw [EndQuot.mem_zc, Subgroup.mem_map]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun l => Subtype.ext ?_, rfl⟩
    exact hc l l.2
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, fun l hl => ?_⟩
    have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨l, hl⟩)
    exact this

theorem card_zc_eq (Λ : Subgroup Γ) : Nat.card (EndQuot.zc Λ) = Nat.card (Subgroup.center ↥Λ) := by
  rw [zc_eq_map_center, Subgroup.card_map_of_injective Λ.subtype_injective]

theorem card_center_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (Subgroup.center A) = Nat.card (Subgroup.center B) := by
  have h : (Subgroup.center A).map e.toMonoidHom = Subgroup.center B := Subgroup.map_center_eq e
  rw [← h, Subgroup.card_map_of_injective e.injective]

end Basic

section Pass

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

@[expose] def lamG (G Y : Subgroup (MulAut V)) : Subgroup ↥G :=
  Subgroup.normalClosure ((Y.subgroupOf G : Subgroup ↥G) : Set ↥G)

instance lamG_normal (G Y : Subgroup (MulAut V)) : (lamG G Y).Normal :=
  Subgroup.normalClosure_normal

abbrev quotG (G Y : Subgroup (MulAut V)) : Type := ↥G ⧸ EndQuot.zc (lamG G Y)

@[expose] def piG (G Y : Subgroup (MulAut V)) : ↥G →* quotG G Y :=
  QuotientGroup.mk' (EndQuot.zc (lamG G Y))

omit [Finite V] in
theorem normalClosure_subgroupOf_eq (hYG : Y ≤ G) :
    lamG G Y = (conjClosure Y G).subgroupOf G := by
  apply le_antisymm
  · have : ((conjClosure Y G).subgroupOf G).Normal :=
      ⟨fun n hn g => (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure g.2) n).mp hn⟩
    refine Subgroup.normalClosure_le_normal fun y hy => ?_
    exact Subgroup.mem_subgroupOf.mpr (le_conjClosure hy)
  · intro x hx
    have h1 : conjClosure Y G ≤ (lamG G Y).map G.subtype := by
      rw [conjClosure, Subgroup.closure_le]
      rintro _ ⟨g, hg, y, hy, rfl⟩
      refine ⟨⟨g, hg⟩ * ⟨y, hYG hy⟩ * ⟨g, hg⟩⁻¹, ?_, rfl⟩
      have hyN : (⟨y, hYG hy⟩ : ↥G) ∈ lamG G Y :=
        Subgroup.subset_normalClosure (show (⟨y, hYG hy⟩ : ↥G) ∈
          ((Y.subgroupOf G : Subgroup ↥G) : Set ↥G) from hy)
      exact (inferInstance : (lamG G Y).Normal).conj_mem _ hyN _
    obtain ⟨z, hz, hzx⟩ := h1 hx
    have : z = x := Subtype.ext hzx
    rwa [← this]

theorem EndCfg4.cfg (h : EndCfg4 G T Y) {f : ℕ} (hf : 2 ≤ f) (hY : YSL Y f) :
    EndQuot.Cfg ↥G (lamG G Y) (Y.subgroupOf G) (T.subgroupOf G) := by
  have hTG : T ≤ G := h.adm.hTG
  have hYG : Y ≤ G := fun y hy => (h.adm.hYC hy).1
  have hΛ := normalClosure_subgroupOf_eq (G := G) (Y := Y) hYG
  let eΛ : ↥(conjClosure Y G) ≃* ↥(lamG G Y) :=
    (Subgroup.subgroupOfEquivOfLe (conjClosure_le hYG)).symm.trans
      (MulEquiv.subgroupCongr hΛ.symm)
  let hYe : ↥(Y.subgroupOf G) ≃* ↥Y := Subgroup.subgroupOfEquivOfLe hYG
  have hq : CFSG.IsQuasisimple ↥(conjClosure Y G) :=
    (EndQuot.isQuasisimple_iff_open _).mpr h.quasi
  refine
    { le := fun x hx => Subgroup.subset_normalClosure hx
      qs := LocalCores.isQuasisimple_of_mulEquiv eΛ hq
      fs := h.fstar.trans hΛ.symm
      zodd := ?_
      perf := ?_
      cen := ?_
      evenΥ := ?_
      std := h.std_of_YSL hf hY
      gen := fun N hN hle => ?_
      hT := ?_
      T2 := h.adm.hT2.comap_subtype
      Tne := ?_
      Tmax := ?_ }
  · rw [card_zc_eq, ← card_center_congr eΛ]
    exact h.oddZ
  · apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hYG]
    exact h.adm.hperf
  · have h1 : (Subgroup.center ↥(Y.subgroupOf G)).map hYe.toMonoidHom = Subgroup.center ↥Y :=
      Subgroup.map_center_eq hYe
    rw [hY.center_eq_bot] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ hYe.injective).mp h1
  · rw [Nat.card_congr hYe.toEquiv, hY.card_eq (by omega)]
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_right _
  · exact Subgroup.normalClosure_le_normal (fun x hx => hle hx)
  · intro t ht y hy
    have := Subgroup.mem_centralizer_iff.mp (h.adm.hYC hy).2 (t : MulAut V) ht
    exact Subtype.ext this.symm
  · intro hbot
    apply h.adm.hT1
    have := Subgroup.map_subgroupOf_eq_of_le hTG
    rw [hbot, Subgroup.map_bot] at this
    exact this.symm
  · intro T' hTT' hT'c hT'2
    have hmap : T'.map G.subtype = T := by
      apply h.sylow (T'.map G.subtype)
      · intro x hx
        exact ⟨⟨x, hTG hx⟩, hTT' (show (⟨x, hTG hx⟩ : ↥G) ∈ T.subgroupOf G from hx), rfl⟩
      · rintro _ ⟨t, ht, rfl⟩
        refine ⟨t.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
        have := Subgroup.mem_centralizer_iff.mp (hT'c ht) ⟨y, hYG hy⟩
          (show (⟨y, hYG hy⟩ : ↥G) ∈ Y.subgroupOf G from hy)
        exact congrArg Subtype.val this
      · exact hT'2.map _
    calc T' = (T'.map G.subtype).comap G.subtype :=
          (Subgroup.comap_map_eq_self_of_injective G.subtype_injective T').symm
      _ = T.subgroupOf G := by rw [hmap]; rfl

theorem EndCfg4.nonempty_equiv_layerQ (h : EndCfg4 G T Y) {f : ℕ} (hf : 2 ≤ f) (hY : YSL Y f) :
    Nonempty (↥(CFSG.layer (quotG G Y)) ≃* LayerQ G Y) := by
  have hYG : Y ≤ G := fun y hy => (h.adm.hYC hy).1
  have hΛ := normalClosure_subgroupOf_eq (G := G) (Y := Y) hYG
  obtain ⟨e1⟩ := EndQuot.nonempty_equiv_layer (Λ := lamG G Y)
  let eΛ : ↥(conjClosure Y G) ≃* ↥(lamG G Y) :=
    (Subgroup.subgroupOfEquivOfLe (conjClosure_le hYG)).symm.trans
      (MulEquiv.subgroupCongr hΛ.symm)
  let e2 : (↥(conjClosure Y G) ⧸ Subgroup.center ↥(conjClosure Y G)) ≃*
      (↥(lamG G Y) ⧸ Subgroup.center ↥(lamG G Y)) :=
    QuotientGroup.congr _ _ eΛ (Subgroup.map_center_eq eΛ)
  exact ⟨(MulEquiv.subgroupCongr (h.cfg hf hY).layer_eq).trans (e1.trans e2.symm)⟩

end Pass

end CFSG.CGT.PushingUpLit.CGT6
