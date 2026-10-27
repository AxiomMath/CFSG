module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG2C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG4A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {NQ : Subgroup G} {N : Subgroup ↥NQ} [N.Normal]

theorem z4j_V_char_lift {Vc Vsub : Subgroup ↥NQ} {Vh : Subgroup (↥NQ ⧸ N)}
    (hVc : Z4JLift N Vc Vh) (hVsub : Vsub ≤ Vc)
    (hn : ∀ g ∈ Vh, ∀ v ∈ Vsub.map (z4iπ N), g * v * g⁻¹ ∈ Vsub.map (z4iπ N))
    (hd : Vsub.map (z4iπ N) ≤ ⁅Vh, Vh⁆) (h4 : Nat.card (Vsub.map (z4iπ N)) = 4)
    (he : ∀ a ∈ Vsub.map (z4iπ N), ∀ b ∈ Vsub.map (z4iπ N), a * b = b * a ∧ a * a = 1)
    (hu : ∀ W : Subgroup (↥NQ ⧸ N), W ≤ Vh → (∀ g ∈ Vh, ∀ w ∈ W, g * w * g⁻¹ ∈ W) →
      W ≤ ⁅Vh, Vh⁆ → Nat.card W = 4 → (∀ a ∈ W, ∀ b ∈ W, a * b = b * a ∧ a * a = 1) →
      W = Vsub.map (z4iπ N)) :
    ∀ z ∈ normalizer ((Vc.map NQ.subtype : Subgroup G) : Set G), ∀ v ∈ Vsub.map NQ.subtype,
      z * v * z⁻¹ ∈ Vsub.map NQ.subtype := by
  have hmapc : (⁅Vc, Vc⁆).map NQ.subtype = ⁅Vc.map NQ.subtype, Vc.map NQ.subtype⁆ :=
    Subgroup.map_commutator Vc Vc NQ.subtype
  have hVV : Vsub.map NQ.subtype ≤ Vc.map NQ.subtype := Subgroup.map_mono hVsub
  have hcom_le : ⁅Vc, Vc⁆ ≤ Vc := by
    simpa using Subgroup.commutator_le_sup (H₁ := Vc) (H₂ := Vc)
  have hVd : Vsub.map NQ.subtype ≤ ⁅Vc.map NQ.subtype, Vc.map NQ.subtype⁆ := by
    have hle : Vsub ≤ ⁅Vc, Vc⁆ := by
      refine hVc.le_of_map_le hVsub hcom_le ?_
      rw [hVc.map_commutator]
      exact hd
    calc Vsub.map NQ.subtype ≤ (⁅Vc, Vc⁆).map NQ.subtype := Subgroup.map_mono hle
      _ = ⁅Vc.map NQ.subtype, Vc.map NQ.subtype⁆ := hmapc
  obtain ⟨hVn, hV4, hVe⟩ := z4j_V_facts_lift hVc hVsub hn h4 he
  have huniq : ∀ W : Subgroup G, W ≤ Vc.map NQ.subtype →
      (∀ g ∈ Vc.map NQ.subtype, ∀ w ∈ W, g * w * g⁻¹ ∈ W) →
      W ≤ ⁅Vc.map NQ.subtype, Vc.map NQ.subtype⁆ → Nat.card W = 4 →
      (∀ a ∈ W, ∀ b ∈ W, a * b = b * a ∧ a * a = 1) →
      W = Vsub.map NQ.subtype := by
    intro W hWVg hWn hWd hW4 hWe
    have hWleNQ : W ≤ NQ := hWVg.trans (Subgroup.map_subtype_le (H := NQ) Vc)
    have hW₀map : (W.subgroupOf NQ).map NQ.subtype = W :=
      Subgroup.map_subgroupOf_eq_of_le hWleNQ
    have hW₀Vc : W.subgroupOf NQ ≤ Vc := by
      intro w hw
      have hwVg : (w : G) ∈ Vc.map NQ.subtype := hWVg hw
      obtain ⟨c, hcVc, hc⟩ := Subgroup.mem_map.mp hwVg
      have hcw : c = w := Subtype.ext hc
      rwa [← hcw]
    have hW₀card : Nat.card (W.subgroupOf NQ) = Nat.card W := by
      rw [← Subgroup.card_subtype NQ (W.subgroupOf NQ), hW₀map]
    have hŴVh : (W.subgroupOf NQ).map (z4iπ N) ≤ Vh := by
      calc (W.subgroupOf NQ).map (z4iπ N) ≤ Vc.map (z4iπ N) :=
            Subgroup.map_mono hW₀Vc
        _ = Vh := hVc.map_eq
    have hŴn : ∀ g ∈ Vh, ∀ w ∈ (W.subgroupOf NQ).map (z4iπ N),
        g * w * g⁻¹ ∈ (W.subgroupOf NQ).map (z4iπ N) := by
      intro g hg w hw
      obtain ⟨c, hcVc, hc⟩ := hVc.exists_lift hg
      obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hw
      have hcVg : (c : G) ∈ Vc.map NQ.subtype := Subgroup.mem_map_of_mem NQ.subtype hcVc
      have hw₀W : (w₀ : G) ∈ W := hw₀
      have hmem : c * w₀ * c⁻¹ ∈ W.subgroupOf NQ :=
        hWn (c : G) hcVg (w₀ : G) hw₀W
      have hπ : z4iπ N (c * w₀ * c⁻¹) ∈ (W.subgroupOf NQ).map (z4iπ N) :=
        Subgroup.mem_map_of_mem (z4iπ N) hmem
      rw [map_mul, map_mul, map_inv] at hπ
      simpa [hc] using hπ
    have hŴd : (W.subgroupOf NQ).map (z4iπ N) ≤ ⁅Vh, Vh⁆ := by
      intro w hw
      obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hw
      have hw₀W : (w₀ : G) ∈ W := hw₀
      have hmem : (w₀ : G) ∈ ⁅Vc.map NQ.subtype, Vc.map NQ.subtype⁆ := hWd hw₀W
      rw [← hmapc] at hmem
      obtain ⟨c, hc, hcEq⟩ := Subgroup.mem_map.mp hmem
      have hcw : c = w₀ := Subtype.ext hcEq
      have hw₀comm : w₀ ∈ ⁅Vc, Vc⁆ := hcw ▸ hc
      have hπ : z4iπ N w₀ ∈ (⁅Vc, Vc⁆).map (z4iπ N) :=
        Subgroup.mem_map_of_mem (z4iπ N) hw₀comm
      rwa [hVc.map_commutator] at hπ
    have hŴ4 : Nat.card ((W.subgroupOf NQ).map (z4iπ N)) = 4 := by
      rw [hVc.card_map hW₀Vc, hW₀card, hW4]
    have hŴe : ∀ a ∈ (W.subgroupOf NQ).map (z4iπ N),
        ∀ b ∈ (W.subgroupOf NQ).map (z4iπ N), a * b = b * a ∧ a * a = 1 := by
      intro a ha b hb
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
      have ha'W : (a' : G) ∈ W := ha'
      have hb'W : (b' : G) ∈ W := hb'
      obtain ⟨hab, haa⟩ := hWe (a' : G) ha'W (b' : G) hb'W
      have hab' : a' * b' = b' * a' := Subtype.ext hab
      have haa' : a' * a' = 1 := Subtype.ext (by simpa using haa)
      constructor
      · rw [← map_mul, ← map_mul, hab']
      · rw [← map_mul, haa', map_one]
    have hŴeq : (W.subgroupOf NQ).map (z4iπ N) = Vsub.map (z4iπ N) :=
      hu ((W.subgroupOf NQ).map (z4iπ N)) hŴVh hŴn hŴd hŴ4 hŴe
    have hW₀eq : W.subgroupOf NQ = Vsub := hVc.eq_of_map_eq hW₀Vc hVsub hŴeq
    calc W = (W.subgroupOf NQ).map NQ.subtype := hW₀map.symm
      _ = Vsub.map NQ.subtype := by rw [hW₀eq]
  exact z4j_char_of_unique hVV hVd hVn hV4 hVe huniq

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
