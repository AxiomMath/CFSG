module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Quot.Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Quot.FStar
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Embed.Links
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Links
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Cor23S
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Transfer
public import CFSG.SignalizerFunctorTheorem.Inheritance.Basic

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem junction_base (hcor : ∀ (G : Type) [Group G] [Finite G],
      CFSG.SignalizerFunctorTheorem.IsSectionOf G H → Nat.card G < Nat.card H → Cor23SAt G)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    {T V K M : Subgroup H} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hM : IsCompIn M (centralizer (T : Set H))) (hV2 : IsPGroup 2 V) (hTV : T ≤ V)
    (hVT : V ≤ normalizer (T : Set H)) (hVM : V ≤ normalizer (M : Set H))
    (hK : IsCompIn K (centralizer (V : Set H))) (hKM : K ≤ M) (hexc : NotExc K) :
    JConn K M := by
  by_cases hKM' : K = M
  · refine ⟨0, fun _ => K, fun _ => V, fun _ => 1, ⟨?_, ?_, ?_, ?_⟩, rfl, hKM', ?_, ?_⟩
    · intro i hi
      have : i = 0 := by omega
      subst this
      exact ⟨hV2, hK⟩
    · intro i h1 h2
      omega
    · intro i h1 h2
      omega
    · intro i h1 h2
      omega
    · intro i h1 h2
      omega
    · intro _ i h1 h2
      omega
  set Y : Subgroup H := M ⊔ V with hY
  have hMY : M ≤ Y := le_sup_left
  have hVY : V ≤ Y := le_sup_right
  have hTY : T ≤ Y := hTV.trans hVY
  have hKY : K ≤ Y := hKM.trans hMY
  have hYM : Y ≤ normalizer (M : Set H) := sup_le Subgroup.le_normalizer hVM
  have hMT : M ≤ normalizer (T : Set H) :=
    hM.1.trans (Subgroup.centralizer_le_normalizer (T : Set H))
  have hYT : Y ≤ normalizer (T : Set H) := sup_le hMT hVT
  set M₀ : Subgroup ↥Y := M.subgroupOf Y with hM₀
  set V₀ : Subgroup ↥Y := V.subgroupOf Y with hV₀
  set T₀ : Subgroup ↥Y := T.subgroupOf Y with hT₀
  set K₀ : Subgroup ↥Y := K.subgroupOf Y with hK₀
  have hM₀n : M₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hMY).2 hYM
  have hT₀n : T₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hTY).2 hYT
  have hMq₀ : CFSG.IsQuasisimple ↥M₀ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hMY).symm
      hM.isQuasisimple
  have hKq₀ : CFSG.IsQuasisimple ↥K₀ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKY).symm
      hK.isQuasisimple
  have hV₀2 : IsPGroup 2 ↥V₀ := hV2.comap_subtype
  have hT₀2 : IsPGroup 2 ↥T₀ := hT2.comap_subtype
  have hMV₀ : M₀ ⊔ V₀ = ⊤ := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hMY, map_subgroupOf_eq_of_le hVY,
      Subgroup.map_top, Subgroup.range_subtype]
  have hT₀M : T₀ ≤ centralizer (M₀ : Set ↥Y) := fun x hx =>
    mem_centralizer_iff.2 fun y hy =>
      Subtype.ext (mem_centralizer_iff.1 (hM.1 hy) (x : H) hx).symm
  have hKM₀ : K₀ ≤ M₀ := fun x hx => hKM hx
  have hperfY : ∀ P : Subgroup ↥Y, ⁅P, P⁆ = P → P ≤ M₀ := fun P hP =>
    perfect_le_of_sup_eq_top (N := M₀) hV₀2 hMV₀ hP
  have hKV₀ : IsCompIn K₀ (centralizer (V₀ : Set ↥Y)) := by
    refine isCompIn_comap_subtype Y hKY (Ut := V₀) ?_
    rw [hV₀, map_subgroupOf_eq_of_le hVY]
    exact isCompIn_of_le hK (le_inf hK.1 hKY) inf_le_left
  have hMqn : (M₀.map (cq M₀)).Normal :=
    Subgroup.Normal.map ‹_› _ (QuotientGroup.mk'_surjective _)
  have hVq2 : IsPGroup 2 ↥(V₀.map (cq M₀)) := hV₀2.map _
  have hsup : M₀.map (cq M₀) ⊔ V₀.map (cq M₀) = ⊤ := by
    rw [← Subgroup.map_sup, hMV₀, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hperf : ∀ P : Subgroup (CQ M₀), ⁅P, P⁆ = P → P ≤ M₀.map (cq M₀) := fun P hP =>
    perfect_le_of_sup_eq_top (N := M₀.map (cq M₀)) hVq2 hsup hP
  have hKcomp := isCompIn_map_cq M₀ V₀ hKM₀ hKV₀
  have hKp : ⁅K₀, K₀⁆ = K₀ := Subgroup.isPerfect_iff.1 hKq₀.1
  have hexc' : NotExc (K₀.map (cq M₀)) := by
    obtain ⟨e⟩ := cqEquiv_of_map_cq M₀ hKM₀ hKp (rfl : K₀.map (cq M₀) = K₀.map (cq M₀))
    exact NotExc.of_cqEquiv (e.symm.trans (cqEquivOfEquiv (Subgroup.subgroupOfEquivOfLe hKY))) hexc
  have hlt : Nat.card (CQ M₀) < Nat.card H := by
    have hT₀ne : T₀ ≠ ⊥ := fun h => hT (by
      rw [← map_subgroupOf_eq_of_le hTY, ← hT₀, h, Subgroup.map_bot])
    have h2 : 2 ≤ Nat.card (centralizer (M₀ : Set ↥Y)) :=
      ((Subgroup.one_lt_card_iff_ne_bot T₀).2 hT₀ne).trans_le (Subgroup.card_le_of_le hT₀M)
    have h1 := Subgroup.index_mul_card (centralizer (M₀ : Set ↥Y))
    have h3 : Nat.card ↥Y ≤ Nat.card H := Subgroup.card_le_card_group Y
    have h4 : 0 < Nat.card ↥Y := Nat.card_pos
    have h5 := Nat.mul_le_mul_left (centralizer (M₀ : Set ↥Y)).index h2
    have h6 : Nat.card (CQ M₀) = (centralizer (M₀ : Set ↥Y)).index := rfl
    omega
  have hkpq : CFSG.Assembly.KProper CFSG.Blueprint.Catalog (CQ M₀) :=
    Hyp.kProper_of_section hkp Y (cq M₀) (QuotientGroup.mk'_surjective _)
  obtain ⟨n, Lq, Tq, sq, hch, hfirst⟩ := hcor (CQ M₀) ⟨Y, cq M₀, QuotientGroup.mk'_surjective _⟩
    hlt hkpq (M₀.map (cq M₀))
    (fStarSimple_cq M₀ hMq₀) hperf (V₀.map (cq M₀)) (K₀.map (cq M₀)) hVq2 hKcomp hexc'.1 hexc'.2
  have hl := hch.toLinks
  have hlast := hch.last
  obtain ⟨L, T', s, hl', hL0, hLn, hLM, hT'0, hTT'⟩ := lift_links M₀ hMq₀ hperf hV₀2 hT₀n hT₀2
    hT₀M hKM₀ hKV₀ hl hlast hfirst
  have hTU : ∀ i ≤ n, T ≤ (T' i).map Y.subtype := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [hT'0, hV₀, map_subgroupOf_eq_of_le hVY]
      exact hTV
    · have := Subgroup.map_mono (f := Y.subtype) (hTT' i hpos hi)
      rwa [hT₀, map_subgroupOf_eq_of_le hTY] at this
  have hemb := embed_links Y hl' hMY hM₀n hM hperfY hLM hTU
  refine ⟨n, fun i => (L i).map Y.subtype, fun i => (T' i).map Y.subtype,
    fun i => ((s i : ↥Y) : H), hemb, ?_, ?_, ?_, ?_⟩
  · show (L 0).map Y.subtype = K
    rw [hL0, hK₀, map_subgroupOf_eq_of_le hKY]
  · show (L n).map Y.subtype = M
    rw [hLn, hM₀, map_subgroupOf_eq_of_le hMY]
  · intro i hi1 hi hbot
    have hbot' : (T' i).map Y.subtype = ⊥ := hbot
    have := hTU i hi
    rw [hbot', le_bot_iff] at this
    exact hT this
  · intro _ i hi1 hi
    have := Subgroup.map_mono (f := Y.subtype) (hLM i)
    rwa [hM₀, map_subgroupOf_eq_of_le hMY] at this

end CFSG.EvenSporadicStandard.Induction.Junction
