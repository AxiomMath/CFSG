module

import CFSG.CGT.Foote82.T66.Prop35
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupMap
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
import CFSG.GH74.Uniqueness.SU.SU4Quot
public import CFSG.CGT.Foote82.T66.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.CGT.Foote82

namespace MC2

open CFSG.Open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

section SubgroupOf

variable {Γ : Type*} [Group Γ]

theorem map_conj_subgroupOf (G X : Subgroup Γ) (g : ↥G) :
    (X.subgroupOf G).map (MulAut.conj g).toMonoidHom =
      (X.map (MulAut.conj (g : Γ)).toMonoidHom).subgroupOf G := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simp⟩
  · rintro ⟨y, hy, hyx⟩
    have hyG : y ∈ G := by
      have : y = (g : Γ)⁻¹ * (x : Γ) * g := by rw [← hyx]; group
      rw [this]
      exact G.mul_mem (G.mul_mem (G.inv_mem g.2) x.2) g.2
    refine ⟨⟨y, hyG⟩, hy, Subtype.ext ?_⟩
    simpa using hyx

theorem normalizer_subgroupOf {G X : Subgroup Γ} (hX : X ≤ G) :
    Subgroup.normalizer ((X.subgroupOf G : Subgroup ↥G) : Set ↥G) =
      (Subgroup.normalizer (X : Set Γ)).subgroupOf G := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h g
    constructor
    · intro hg
      have := (h ⟨g, hX hg⟩).1 (Subgroup.mem_subgroupOf.2 hg)
      exact Subgroup.mem_subgroupOf.1 this
    · intro hg
      have hgG : g ∈ G := by
        have h1 : (x : Γ) * g * (x : Γ)⁻¹ ∈ G := hX hg
        have : g = (x : Γ)⁻¹ * ((x : Γ) * g * (x : Γ)⁻¹) * x := by group
        rw [this]
        exact G.mul_mem (G.mul_mem (G.inv_mem x.2) h1) x.2
      have := (h ⟨g, hgG⟩).2 (Subgroup.mem_subgroupOf.2 hg)
      exact Subgroup.mem_subgroupOf.1 this
  · intro h g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact h g

theorem card_subgroupOf {G X : Subgroup Γ} (hX : X ≤ G) :
    Nat.card ↥(X.subgroupOf G) = Nat.card ↥X :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv

theorem subgroupOf_injective {G X Y : Subgroup Γ} (hX : X ≤ G) (hY : Y ≤ G)
    (h : X.subgroupOf G = Y.subgroupOf G) : X = Y := by
  rw [← Subgroup.map_subgroupOf_eq_of_le hX, ← Subgroup.map_subgroupOf_eq_of_le hY, h]

theorem commutator_le_of_le {G X Y : Subgroup Γ} (hX : X ≤ G) (hY : Y ≤ G) : ⁅X, Y⁆ ≤ G :=
  Subgroup.commutator_le.2 fun x hx y hy => by
    rw [commutatorElement_def]
    exact G.mul_mem (G.mul_mem (G.mul_mem (hX hx) (hY hy)) (G.inv_mem (hX hx))) (G.inv_mem (hY hy))

theorem inf_subgroupOf' (G X Y : Subgroup Γ) :
    (X ⊓ Y).subgroupOf G = X.subgroupOf G ⊓ Y.subgroupOf G := by
  ext x
  simp [Subgroup.mem_subgroupOf]

theorem commutator_subgroupOf {G X Y : Subgroup Γ} (hX : X ≤ G) (hY : Y ≤ G) :
    ⁅X.subgroupOf G, Y.subgroupOf G⁆ = (⁅X, Y⁆).subgroupOf G := by
  have hXY : ⁅X, Y⁆ ≤ G := commutator_le_of_le hX hY
  apply Subgroup.map_injective G.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hX,
    Subgroup.map_subgroupOf_eq_of_le hY, Subgroup.map_subgroupOf_eq_of_le hXY]

end SubgroupOf

theorem sq_dvd_card_of_two_le_pRank {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} (hp : 1 < p)
    {H : Subgroup Γ} (h : 2 ≤ CFSG.Open.pRank p H) : p ^ 2 ∣ Nat.card H := by
  obtain ⟨E, hEH, -, hE⟩ := CFSG.SectionRank.exists_pRank hp H
  have h1 : p ^ 2 ∣ Nat.card E := hE ▸ pow_dvd_pow p h
  exact h1.trans (Subgroup.card_dvd_of_le hEH)

theorem card_center_eq (G : Subgroup (GLV V)) :
    Nat.card ↥(Subgroup.center ↥G) = Nat.card ↥(G ⊓ Subgroup.centralizer (G : Set (GLV V))) := by
  have hmap : (Subgroup.center ↥G).map G.subtype = G ⊓ Subgroup.centralizer (G : Set (GLV V)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      have := Subgroup.mem_center_iff.1 hy ⟨g, hg⟩
      exact congrArg Subtype.val this
    · rintro ⟨hxG, hx⟩
      refine ⟨⟨x, hxG⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
      exact Subgroup.mem_centralizer_iff.1 hx g g.2
  rw [← hmap, Subgroup.card_map_of_injective G.subtype_injective]

theorem odd_card_center {G L : Subgroup (GLV V)} {s : GLV V} (h : StdForm G L s) :
    Odd (Nat.card ↥(Subgroup.center ↥G)) := by
  rw [card_center_eq]
  exact h.extremal.setup.odd_card_center

theorem stdForm_L_le {G L : Subgroup (GLV V)} {s : GLV V} (h : StdForm G L s) : L ≤ G :=
  h.extremal.toConf66.L_le

theorem centralizer_subgroupOf_eq {G L : Subgroup (GLV V)} (hLG : L ≤ G) :
    Subgroup.centralizer ((L.subgroupOf G : Subgroup ↥G) : Set ↥G) =
      (G ⊓ Subgroup.centralizer (L : Set (GLV V))).subgroupOf G := by
  rw [CFSG.StandardSubgroupAPI.centralizer_subgroupOf hLG]
  ext x
  simp [Subgroup.mem_subgroupOf]

theorem standard_subgroupOf {G L : Subgroup (GLV V)} {s : GLV V} (h : StdForm G L s)
    (hev : Even (Nat.card ↥(G ⊓ Subgroup.centralizer (L : Set (GLV V))))) :
    standardComponentIsStandard (L.subgroupOf G) := by
  have hLG : L ≤ G := stdForm_L_le h
  set K : Subgroup (GLV V) := G ⊓ Subgroup.centralizer (L : Set (GLV V)) with hKdef
  have hKG : K ≤ G := inf_le_left
  have hC : Subgroup.centralizer ((L.subgroupOf G : Subgroup ↥G) : Set ↥G) = K.subgroupOf G :=
    centralizer_subgroupOf_eq hLG
  have hNK : Subgroup.normalizer ((K.subgroupOf G : Subgroup ↥G) : Set ↥G) =
      (Subgroup.normalizer (K : Set (GLV V))).subgroupOf G := normalizer_subgroupOf hKG
  have hNL : Subgroup.normalizer ((L.subgroupOf G : Subgroup ↥G) : Set ↥G) =
      (Subgroup.normalizer (L : Set (GLV V))).subgroupOf G := normalizer_subgroupOf hLG
  have hNeq : (Subgroup.normalizer (K : Set (GLV V))).subgroupOf G =
      (Subgroup.normalizer (L : Set (GLV V))).subgroupOf G := by
    have := h.normalizer_eq
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact (this.le ⟨x.2, hx⟩).2
    · intro hx
      exact (this.ge ⟨x.2, hx⟩).2
  rw [CFSG.StandardSubgroupAPI.standardComponentIsStandard_iff_classical]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLG)
      h.extremal.setup.component.2.2
  · rw [hC, card_subgroupOf hKG]
    exact hev
  · intro g hg
    rw [hC] at hg ⊢
    rw [hNK, hNeq, Subgroup.mem_subgroupOf] at hg
    have hodd := h.tight g g.2 hg
    rw [map_conj_subgroupOf, ← inf_subgroupOf', card_subgroupOf (inf_le_left.trans hKG)]
    exact hodd
  · rw [hC, hNK, hNeq, hNL]
  · intro g hcomm
    apply h.commutator_ne_bot g g.2
    rw [map_conj_subgroupOf] at hcomm
    have hLg : L.map (MulAut.conj (g : GLV V)).toMonoidHom ≤ G := by
      rintro _ ⟨y, hy, rfl⟩
      exact G.mul_mem (G.mul_mem g.2 (hLG hy)) (G.inv_mem g.2)
    rw [commutator_subgroupOf hLG hLg] at hcomm
    have hle : ⁅L, L.map (MulAut.conj (g : GLV V)).toMonoidHom⁆ ≤ G := commutator_le_of_le hLG hLg
    apply subgroupOf_injective hle bot_le
    rw [hcomm, Subgroup.bot_subgroupOf]

abbrev Gbar (G : Subgroup (GLV V)) : Type := ↥G ⧸ Subgroup.center ↥G

abbrev Lbar (G L : Subgroup (GLV V)) : Subgroup (Gbar G) :=
  (L.subgroupOf G).map (QuotientGroup.mk' (Subgroup.center ↥G))

theorem quotData {G L : Subgroup (GLV V)} {s : GLV V} (h : StdForm G L s)
    (hrank : 2 ≤ CFSG.Open.pRank 2 (G ⊓ Subgroup.centralizer (L : Set (GLV V)))) :
    (G = layerIn G ∧ CFSG.IsQuasisimple ↥G) ∧ Odd (Nat.card ↥(Subgroup.center ↥G)) ∧
      IsSimpleGroup (Gbar G) ∧ (∃ a b : Gbar G, a * b ≠ b * a) ∧
      CFSG.Assembly.KProper CFSG.Assembly.InCatalog (Gbar G) ∧
      standardComponentIsStandard (Lbar G L) ∧
      2 ≤ CFSG.Open.pRank 2
        (Subgroup.centralizer ((Lbar G L : Subgroup (Gbar G)) : Set (Gbar G))) := by
  have hLG : L ≤ G := stdForm_L_le h
  set K : Subgroup (GLV V) := G ⊓ Subgroup.centralizer (L : Set (GLV V)) with hKdef
  have h4 : 4 ∣ Nat.card K := by
    have := sq_dvd_card_of_two_le_pRank (p := 2) (by norm_num) hrank
    simpa using this
  have hq := h.quasisimple h4
  have hodd := odd_card_center h
  have hsimple : IsSimpleGroup (Gbar G) := hq.2.2.1
  refine ⟨hq, hodd, hsimple, hq.2.2.2, ?_, ?_, ?_⟩
  · exact CFSG.ComponentClassification.CatalogueKProper.quotient h.extremal.kProper _
  ·
    have hev : Even (Nat.card K) := even_iff_two_dvd.2 ((by norm_num : 2 ∣ 4).trans h4)
    have hstd := standard_subgroupOf h hev
    rw [← CFSG.StandardSubgroupAPI.isStandardSubgroup_iff_standardComponentIsStandard] at hstd ⊢
    refine CFSG.ComponentClassification.GSThmB.isStandardSubgroup_map_of_surjective _
      (QuotientGroup.mk'_surjective _) hstd ?_ ?_
    · rw [QuotientGroup.ker_mk']
      exact hodd
    · rw [QuotientGroup.ker_mk']
      intro z hz
      exact Subgroup.mem_centralizer_iff.2 fun l _ => Subgroup.mem_center_iff.1 hz l
  ·
    have hC := centralizer_subgroupOf_eq hLG
    have h1 : CFSG.Open.pRank 2 (K.subgroupOf G) = CFSG.Open.pRank 2 K := by
      rw [← CFSG.GH74.Uniqueness.SU.SU4.pRank_map_of_injective G.subtype G.subtype_injective,
        Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    have h2 : CFSG.Open.pRank 2 ((K.subgroupOf G).map (QuotientGroup.mk' (Subgroup.center ↥G))) =
        CFSG.Open.pRank 2 (K.subgroupOf G) := by
      apply CFSG.GH74.Uniqueness.SU.SU4.pRank_map
      rw [QuotientGroup.ker_mk']
      exact hodd
    have h3 : (K.subgroupOf G).map (QuotientGroup.mk' (Subgroup.center ↥G)) ≤
        Subgroup.centralizer ((Lbar G L : Subgroup (Gbar G)) : Set (Gbar G)) := by
      rintro _ ⟨c, hc, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨l, hl, rfl⟩
      rw [← hC] at hc
      have := Subgroup.mem_centralizer_iff.1 hc l hl
      simp only [QuotientGroup.mk'_apply]
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]
    calc 2 ≤ CFSG.Open.pRank 2 K := hrank
      _ = CFSG.Open.pRank 2 ((K.subgroupOf G).map (QuotientGroup.mk' (Subgroup.center ↥G))) := by
        rw [h2, h1]
      _ ≤ _ := CFSG.SectionRank.pRank_mono (by norm_num) h3

end MC2

end CFSG.CGT.Foote82
