module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.CSideFacts

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma centerOf_eq_map_center {C : Type*} [Group C] (Q : Subgroup C) :
    centerOf Q = (Subgroup.center ↥Q).map Q.subtype := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxQ, hxc⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxQ⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc (g : C) g.2)
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    rw [← hyx]
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨h, hh⟩)

theorem centerOf_eq_zpowers {G : Type} [Group G] {z : G} (hz2 : orderOf z = 2)
    {Q : Subgroup ↥(Gx z)} [Q.Normal] (hQ : IsExtraspecialPlusByA5WrTwoWith ↥(Gx z) Q) :
    centerOf Q = Subgroup.zpowers (GxSelf z) := by
  have hcent : GxSelf z ∈ Subgroup.centralizer (Q : Set ↥(Gx z)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact Subtype.ext (mem_Gx.mp y.2).symm
  have hmem : GxSelf z ∈ centerOf Q :=
    Subgroup.mem_inf.mpr ⟨hQ.centralizer_le hcent, hcent⟩
  have hcard_center : Nat.card ↥(centerOf Q) = 2 := by
    rw [centerOf_eq_map_center, Subgroup.card_map_of_injective Q.subtype_injective]
    exact hQ.plus.1.center_order_p
  have hcard_z : Nat.card ↥(Subgroup.zpowers (GxSelf z)) = 2 := by
    rw [Nat.card_zpowers]
    simpa [GxSelf] using hz2
  haveI : Finite ↥(centerOf Q) :=
    Nat.finite_of_card_ne_zero (by rw [hcard_center]; norm_num)
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem)
    (le_of_eq (hcard_center.trans hcard_z.symm))).symm

theorem cIrreducible_iff {G : Type} [Group G] {z : G} (hz2 : orderOf z = 2)
    {Q : Subgroup ↥(Gx z)} [Q.Normal] (hQ : IsExtraspecialPlusByA5WrTwoWith ↥(Gx z) Q)
    (hQz : Qz z = Q.map (Gx z).subtype) :
    CIrreducible ↥(Gx z) Q ↔
      ∀ W : Subgroup G, Subgroup.zpowers z ≤ W → W ≤ Qz z →
        (∀ g ∈ derivedOf (Gx z), ∀ w ∈ W, g * w * g⁻¹ ∈ W) →
          W = Subgroup.zpowers z ∨ W = Qz z := by
  have hcenter := centerOf_eq_zpowers hz2 hQ
  constructor
  · intro hC W hzW hWQ hinv
    have hWrange : W ≤ (Gx z).subtype.range := by
      have h1 : W ≤ Q.map (Gx z).subtype := hQz ▸ hWQ
      exact h1.trans (Subgroup.map_le_range (Gx z).subtype Q)
    have hW'center : centerOf Q ≤ W.comap (Gx z).subtype := by
      rw [hcenter, ← Subgroup.map_le_iff_le_comap, MonoidHom.map_zpowers]
      exact hzW
    have hW'Q : W.comap (Gx z).subtype ≤ Q := by
      rw [← Subgroup.map_le_map_iff_of_injective (Gx z).subtype_injective,
        Subgroup.map_comap_eq_self hWrange, ← hQz]
      exact hWQ
    have hW'inv : ∀ g ∈ _root_.commutator ↥(Gx z), ∀ w ∈ W.comap (Gx z).subtype,
        g * w * g⁻¹ ∈ W.comap (Gx z).subtype := by
      intro g hg w hw
      change (Gx z).subtype (g * w * g⁻¹) ∈ W
      rw [map_mul, map_mul, map_inv]
      exact hinv ((Gx z).subtype g) (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩) ((Gx z).subtype w) hw
    rcases hC (W.comap (Gx z).subtype) hW'center hW'Q hW'inv with h | h
    · left
      rw [← Subgroup.map_comap_eq_self hWrange, h, hcenter, MonoidHom.map_zpowers]
      rfl
    · right
      rw [← Subgroup.map_comap_eq_self hWrange, h, hQz]
  · intro hG W' hW'center hW'Q hinvW
    have hzW : Subgroup.zpowers z ≤ W'.map (Gx z).subtype := by
      have hle : Subgroup.zpowers (GxSelf z) ≤ W' := by
        rwa [← hcenter]
      calc Subgroup.zpowers z = Subgroup.zpowers ((Gx z).subtype (GxSelf z)) := rfl
        _ = (Subgroup.zpowers (GxSelf z)).map (Gx z).subtype :=
            (MonoidHom.map_zpowers (Gx z).subtype (GxSelf z)).symm
        _ ≤ W'.map (Gx z).subtype := Subgroup.map_mono hle
    have hWQ : W'.map (Gx z).subtype ≤ Qz z := by
      rw [hQz]
      exact Subgroup.map_mono hW'Q
    have hinv : ∀ g ∈ derivedOf (Gx z), ∀ w ∈ W'.map (Gx z).subtype,
        g * w * g⁻¹ ∈ W'.map (Gx z).subtype := by
      intro g hg w hw
      obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
      obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.mp hw
      rw [← map_mul, ← map_inv, ← map_mul]
      exact Subgroup.mem_map.mpr ⟨g' * w' * g'⁻¹, hinvW g' hg' w' hw', rfl⟩
    rcases hG (W'.map (Gx z).subtype) hzW hWQ hinv with h | h
    · left
      apply Subgroup.map_injective (Gx z).subtype_injective
      rw [h, hcenter, MonoidHom.map_zpowers]
      rfl
    · right
      apply Subgroup.map_injective (Gx z).subtype_injective
      rw [h, hQz]

end CFSG.EvenSporadicStandard.HNRecog.Section3
