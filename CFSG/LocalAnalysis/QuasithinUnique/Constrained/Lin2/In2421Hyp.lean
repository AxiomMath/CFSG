module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_16
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_17
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_18
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_19
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_20c
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3TI
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Singer

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped Pointwise

structure Lin2Hyp0 : Prop where
  h8 : Lemma2_4_8
  h11 : Lemma2_4_11
  h12 : Lemma2_4_12
  h14 : Lemma2_4_14

namespace Lin2Hyp0

variable (E : Lin2Hyp0)

include E

theorem h16 : Lemma2_4_16 := lemma2_4_16 E.h8 E.h11 lemma244

theorem h17 : Lemma2_4_17 := lemma2_4_17 singerNormalizerCyclic E.h8 E.h12 E.h14 E.h16

theorem h18 : Lemma2_4_18 := lemma2_4_18 E.h8 E.h11 E.h14 E.h16 E.h17

theorem h19 : Lemma2_4_19 :=
  lemma2_4_19 tiAbelianTwoGroupCommute E.h8 E.h14 E.h16 E.h17 E.h18

theorem h20 : Lemma2_4_20 := lemma2_4_20 E.h8 E.h11 E.h16 E.h18 E.h19

section Acc

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}
  (hcfg : Lin2Cfg G T M H S L n D)

include hcfg

theorem idxTS : S.relIndex T = 2 :=
  (E.h8 G T M H S L D n hcfg).1.1

theorem TnS : T ≤ Subgroup.normalizer (S : Set G) :=
  (E.h8 G T M H S L D n hcfg).1.2.1

theorem TnR : T ≤ Subgroup.normalizer (thompsonJ S : Set G) :=
  (E.h8 G T M H S L D n hcfg).1.2.2

theorem OL : pCoreOf 2 L = blockU L :=
  (E.h8 G T M H S L D n hcfg).2.1.1

theorem UQ : blockU L = pCoreOf 2 H :=
  (E.h8 G T M H S L D n hcfg).2.1.2

theorem Rsyl : IsSylowTwoOf (thompsonJ S) L :=
  (E.h8 G T M H S L D n hcfg).2.2.1.2.1

theorem RUU {x : G} (hx : x ∈ T) (hxS : x ∉ S) :
    thompsonJ S = blockU L ⊔ conjR (blockU L) x ∧
      blockU L ⊓ conjR (blockU L) x = centerOf (thompsonJ S) :=
  ⟨((E.h8 G T M H S L D n hcfg).2.2.1.2.2 x hx hxS).1,
    ((E.h8 G T M H S L D n hcfg).2.2.1.2.2 x hx hxS).2.1⟩

theorem exists_B : ∃ B : Subgroup G, Lin2BProps T S (thompsonJ S) D B :=
  (E.h8 G T M H S L D n hcfg).2.2.2.2.1

theorem elemU {x : G} (hx : x ∈ T) (hxS : x ∉ S) :
    IsElemAbelian 2 (blockU L) ∧ IsElemAbelian 2 (conjR (blockU L) x) ∧
      ∀ E' : Subgroup G, E' ≤ thompsonJ S → IsElemAbelian 2 E' →
        E' ≤ blockU L ∨ E' ≤ conjR (blockU L) x :=
  (E.h8 G T M H S L D n hcfg).2.2.2.2.2.2.1 x hx hxS

theorem Zbasic {Z : Subgroup G} (hZ : Z = lin2Z L (thompsonJ S)) :
    IsElemAbelian 2 Z ∧ Nat.card Z = 2 ^ n ∧ S ≤ Subgroup.normalizer (Z : Set G) :=
  (E.h16 G T M H S L D n hcfg Z hZ).1

theorem Zcases {Z : Subgroup G} (hZ : Z = lin2Z L (thompsonJ S)) {x : G} (hx : x ∈ T)
    (hxS : x ∉ S) :
    (centerOf L = ⊥ ∧ conjR Z x = Z ∧ Z = centerOf (thompsonJ S)) ∨
      (centerOf L ≠ ⊥ ∧ centerOf (thompsonJ S) = Z ⊔ conjR Z x ∧ Z ⊓ conjR Z x = ⊥) :=
  (E.h16 G T M H S L D n hcfg Z hZ).2.1 x hx hxS

theorem ZTI {Z : Subgroup G} (hZ : Z = lin2Z L (thompsonJ S)) : fusionIsTI Z :=
  (E.h18 G T M H S L D n hcfg Z hZ).1

theorem N_Z_eq_M {Z : Subgroup G} (hZ : Z = lin2Z L (thompsonJ S)) (hc : centerOf L = ⊥) :
    Subgroup.normalizer (Z : Set G) = M :=
  (E.h18 G T M H S L D n hcfg Z hZ).2.1 hc

theorem Delta_not_fused {Z : Subgroup G} (hZ : Z = lin2Z L (thompsonJ S)) (hc : centerOf L ≠ ⊥)
    {x : G} (hx : x ∈ T) (hxS : x ∉ S) {u : G} (hu : u ∈ lin2Delta (thompsonJ S) Z x) (g : G) :
    g⁻¹ * u * g ∉ Z :=
  (((E.h20 G T M H S L D n hcfg Z hZ hc).2 x hx hxS).1 u hu).2.2 g

theorem L_le_normalizer_U : L ≤ Subgroup.normalizer (blockU L : Set G) := by
  rw [← E.OL hcfg]
  exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L

theorem blockZ_le_centerOf_R : blockZ L ≤ centerOf (thompsonJ S) := by
  rw [blockZ_eq_centerOf hcfg.charTwo_L (E.OL hcfg)]
  rcases lin2Z_cases (Z := lin2Z L (thompsonJ S)) rfl with ⟨hc, -⟩ | ⟨hc, hZ⟩
  · rw [hc]; exact bot_le
  · rw [← hZ]; exact lin2Z_le_centerOf E.h16 hcfg rfl

theorem centerOf_R_le_U : centerOf (thompsonJ S) ≤ blockU L := by
  obtain ⟨x, hx, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  rw [← (E.RUU hcfg hx hxS).2]
  exact inf_le_left

theorem exists_mem_centerOf_R_not_mem_blockZ :
    ∃ w ∈ centerOf (thompsonJ S), w ∉ blockZ L := by
  obtain ⟨x, hx, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  have hZne := lin2Z_ne_bot E.h16 hcfg (Z := lin2Z L (thompsonJ S)) rfl
  rcases lin2Z_cases (Z := lin2Z L (thompsonJ S)) rfl with ⟨hc, hZR⟩ | ⟨hc, hZL⟩
  · obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZne
    refine ⟨w, hZR ▸ hw, ?_⟩
    rw [blockZ_eq_centerOf hcfg.charTwo_L (E.OL hcfg), hc, Subgroup.mem_bot]
    exact fun h => hw1 (Subtype.ext h)
  · have hZ' : conjR (lin2Z L (thompsonJ S)) x ≠ ⊥ := fun h =>
      hZne (conjR_eq_bot_iff.1 h)
    obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZ'
    rcases E.Zcases hcfg (Z := lin2Z L (thompsonJ S)) rfl hx hxS with ⟨hc', -⟩ |
      ⟨-, hZR2, hZinf⟩
    · exact absurd hc' hc
    · refine ⟨w, hZR2 ▸ Subgroup.mem_sup_right hw, fun h => ?_⟩
      rw [blockZ_eq_centerOf hcfg.charTwo_L (E.OL hcfg), ← hZL] at h
      have : w ∈ lin2Z L (thompsonJ S) ⊓ conjR (lin2Z L (thompsonJ S)) x := ⟨h, hw⟩
      rw [hZinf, Subgroup.mem_bot] at this
      exact hw1 (Subtype.ext this)

theorem exists_conj_mem_centerOf_R {u : G} (hu : u ∈ blockU L) :
    ∃ ℓ ∈ L, ℓ * u * ℓ⁻¹ ∈ centerOf (thompsonJ S) := by
  by_cases huZ : u ∈ blockZ L
  · exact ⟨1, L.one_mem, by simpa using E.blockZ_le_centerOf_R hcfg huZ⟩
  · obtain ⟨w, hwR, hwZ⟩ := E.exists_mem_centerOf_R_not_mem_blockZ hcfg
    obtain ⟨ℓ, hℓ, hℓw⟩ := lin2_exists_conj_mem_coset hcfg.lin2 (E.L_le_normalizer_U hcfg) hu
      (E.centerOf_R_le_U hcfg hwR) huZ hwZ
    refine ⟨ℓ, hℓ, ?_⟩
    have : ℓ * u * ℓ⁻¹ = (ℓ * u * ℓ⁻¹ * w⁻¹) * w := by group
    rw [this]
    exact Subgroup.mul_mem _ (E.blockZ_le_centerOf_R hcfg hℓw) hwR

theorem conj_Z_le_U {g : G} (hne : conjR (lin2Z L (thompsonJ S)) g ⊓ blockU L ≠ ⊥) :
    conjR (lin2Z L (thompsonJ S)) g ≤ blockU L := by
  set Z := lin2Z L (thompsonJ S) with hZdef
  obtain ⟨x, hx, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  have hTI : fusionIsTI Z := E.ZTI hcfg rfl
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  obtain ⟨ℓ, hℓ, hw'⟩ := E.exists_conj_mem_centerOf_R hcfg hu.2
  have hw'1 : ℓ * u * ℓ⁻¹ ≠ 1 := by
    intro h
    apply hu1'
    have : u = ℓ⁻¹ * (ℓ * u * ℓ⁻¹) * ℓ := by group
    rw [this, h]; group
  have hw'B : ℓ * u * ℓ⁻¹ ∈ conjR Z (g * ℓ⁻¹) := by
    rw [mem_conjR]
    have e : g * ℓ⁻¹ * (ℓ * u * ℓ⁻¹) * (g * ℓ⁻¹)⁻¹ = g * u * g⁻¹ := by group
    rw [e]
    exact mem_conjR.mp hu.1
  have hℓU : conjR (blockU L) ℓ = blockU L :=
    conjR_eq_of_mem_normalizer (E.L_le_normalizer_U hcfg hℓ)
  have hZU : Z ≤ blockU L := (lin2Z_le_centerOf E.h16 hcfg rfl).trans (E.centerOf_R_le_U hcfg)
  have key : conjR Z (g * ℓ⁻¹) ≤ blockU L → conjR Z g ≤ blockU L := fun h => by
    have e : conjR (conjR Z (g * ℓ⁻¹)) ℓ = conjR Z g := by
      rw [conjR_conjR]; congr 1; group
    rw [← e]
    calc conjR (conjR Z (g * ℓ⁻¹)) ℓ ≤ conjR (blockU L) ℓ := conjR_mono h ℓ
      _ = blockU L := hℓU
  refine key ?_
  rcases lin2Z_cases (Z := Z) rfl with ⟨hc, hZR⟩ | ⟨hc, hZL⟩
  ·
    have hwZ : ℓ * u * ℓ⁻¹ ∈ Z := hZR ▸ hw'
    have hne' : Z ⊓ conjR Z (g * ℓ⁻¹) ≠ ⊥ := fun h => hw'1 (by
      have : ℓ * u * ℓ⁻¹ ∈ Z ⊓ conjR Z (g * ℓ⁻¹) := ⟨hwZ, hw'B⟩
      rw [h, Subgroup.mem_bot] at this; exact this)
    rw [conjR_eq_of_inf_ne_bot hTI hne']
    exact hZU
  ·
    rcases E.Zcases hcfg (Z := Z) rfl hx hxS with ⟨hc', -⟩ | ⟨-, hZR2, hZinf⟩
    · exact absurd hc' hc
    · have hw'ZR : ℓ * u * ℓ⁻¹ ∈ Z ⊔ conjR Z x := hZR2 ▸ hw'
      by_cases hwZ : ℓ * u * ℓ⁻¹ ∈ Z
      · have hne' : Z ⊓ conjR Z (g * ℓ⁻¹) ≠ ⊥ := fun h => hw'1 (by
          have : ℓ * u * ℓ⁻¹ ∈ Z ⊓ conjR Z (g * ℓ⁻¹) := ⟨hwZ, hw'B⟩
          rw [h, Subgroup.mem_bot] at this; exact this)
        rw [conjR_eq_of_inf_ne_bot hTI hne']
        exact hZU
      · by_cases hwZx : ℓ * u * ℓ⁻¹ ∈ conjR Z x
        · have hTIx : fusionIsTI (conjR Z x) := fusionIsTI_conjR hTI x
          have hB : conjR Z (g * ℓ⁻¹) = conjR (conjR Z x) (x⁻¹ * (g * ℓ⁻¹)) := by
            rw [conjR_conjR]; congr 1; group
          have hne' : conjR Z x ⊓ conjR (conjR Z x) (x⁻¹ * (g * ℓ⁻¹)) ≠ ⊥ := fun h => hw'1 (by
            have : ℓ * u * ℓ⁻¹ ∈ conjR Z x ⊓ conjR (conjR Z x) (x⁻¹ * (g * ℓ⁻¹)) :=
              ⟨hwZx, hB ▸ hw'B⟩
            rw [h, Subgroup.mem_bot] at this; exact this)
          rw [hB, conjR_eq_of_inf_ne_bot hTIx hne']
          exact (hZR2 ▸ le_sup_right : conjR Z x ≤ centerOf (thompsonJ S)).trans
            (E.centerOf_R_le_U hcfg)
        · exfalso
          have hΔ : ℓ * u * ℓ⁻¹ ∈ lin2Delta (thompsonJ S) Z x := ⟨hw', hwZ, hwZx⟩
          apply E.Delta_not_fused hcfg (Z := Z) rfl hc hx hxS hΔ (ℓ * g⁻¹)
          have := mem_conjR.mp hw'B
          have e : (ℓ * g⁻¹)⁻¹ * (ℓ * u * ℓ⁻¹) * (ℓ * g⁻¹) = g * ℓ⁻¹ * (ℓ * u * ℓ⁻¹) *
              (g * ℓ⁻¹)⁻¹ := by group
          rw [e]
          exact this

end Acc

end Lin2Hyp0

end CFSG.QuasithinUnique.Lin2
