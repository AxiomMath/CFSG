module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGStrong
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGQ
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGC

open CFSG.Open Subgroup
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (pElementSubgroup pElementSubgroup_le)

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem mem_normalizer_pES {L : Subgroup G} {g : G} (hg : g ∈ normalizer (L : Set G)) :
    g ∈ normalizer ((pElementSubgroup p L : Subgroup G) : Set G) := by
  have hg' := mem_normalizer_iff.mp hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, pElementSubgroup, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxL, k, hk⟩, rfl⟩
    refine ⟨(hg' x).mp hxL, k, ?_⟩
    rw [← hk]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  · rintro ⟨hyL, k, hk⟩
    have hx : g⁻¹ * y * g ∈ L := by
      have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      exact (hg' _).mpr (by rw [e]; exact hyL)
    refine ⟨g⁻¹ * y * g, ⟨hx, k, ?_⟩, ?_⟩
    · rw [← hk]
      have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective y
      simpa [MulAut.conj_apply] using this
    · show g * (g⁻¹ * y * g) * g⁻¹ = y
      group

theorem pES_pES (L : Subgroup G) : pElementSubgroup p (pElementSubgroup p L) =
    pElementSubgroup p L := by
  apply le_antisymm (pElementSubgroup_le _)
  refine Subgroup.closure_mono ?_
  rintro x ⟨hxL, hk⟩
  exact ⟨Subgroup.subset_closure ⟨hxL, hk⟩, hk⟩

variable {H D S B L M : Subgroup G} {z : G}

namespace KGData

variable (d : KGData p H D S B L M z) [hDn : (D.subgroupOf H).Normal]

include d

theorem img_pES_eq : img H D (pElementSubgroup p L) = img H D L := by
  have hJL : pElementSubgroup p L ≤ L := pElementSubgroup_le L
  have hzJ : z ∈ pElementSubgroup p L := by
    refine Subgroup.subset_closure ⟨d.z_mem_L, 1, ?_⟩
    rw [d.z_order, pow_one]
  apply le_antisymm
  · rintro _ hx
    obtain ⟨j, hj, rfl⟩ := mem_img.mp hx
    exact mem_img.mpr ⟨j, hJL hj, rfl⟩
  · haveI := d.simple_img
    set V : Subgroup ↥(img H D L) := (img H D (pElementSubgroup p L)).subgroupOf (img H D L)
    have hVn : V.Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨j, hj, hjn⟩ := mem_img.mp hn
      obtain ⟨l, hl, hlg⟩ := mem_img.mp g.2
      have hjl : (j : G) ∈ pElementSubgroup p L := hj
      have hlN : (l : G) ∈ normalizer (L : Set G) :=
        Subgroup.le_normalizer hl
      have hlJ : (l : G) ∈ normalizer ((pElementSubgroup p L : Subgroup G) : Set G) :=
        mem_normalizer_pES hlN
      have hmem : (l : G) * j * (l : G)⁻¹ ∈ pElementSubgroup p L :=
        (mem_normalizer_iff.mp hlJ _).mp hjl
      refine mem_img.mpr ⟨l * j * l⁻¹, hmem, ?_⟩
      show qmk H D (l * j * l⁻¹) = (g : QA H D) * (n : QA H D) * (g : QA H D)⁻¹
      rw [map_mul, map_mul, map_inv, hlg]
      have : qmk H D j = (n : QA H D) := hjn
      rw [this]
    have hz1 : (⟨qmk H D ⟨z, d.z_mem_H⟩, mem_img.mpr ⟨⟨z, d.z_mem_H⟩, d.z_mem_L, rfl⟩⟩ :
        ↥(img H D L)) ∈ V := mem_img.mpr ⟨⟨z, d.z_mem_H⟩, hzJ, rfl⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal V with hbot | htop
    · exfalso
      rw [hbot, Subgroup.mem_bot] at hz1
      have := congrArg Subtype.val hz1
      have hq : qmk H D ⟨z, d.z_mem_H⟩ = 1 := this
      exact d.z_not_mem_D (qmk_eq_one_iff.mp hq)
    · intro x hx
      have : (⟨x, hx⟩ : ↥(img H D L)) ∈ V := by rw [htop]; exact Subgroup.mem_top _
      exact this

theorem X_le_H : pElementSubgroup p L ⊔ S ≤ H :=
  sup_le ((pElementSubgroup_le L).trans d.L_le_H) d.S_le_H

theorem S_le_normalizer_pES : S ≤ normalizer ((pElementSubgroup p L : Subgroup G) : Set G) :=
  fun s hs => mem_normalizer_pES (d.M_le_L ⟨d.S_le_M hs, d.S_le_H hs⟩)

theorem X_le_normalizer_pES : pElementSubgroup p L ⊔ S ≤
    normalizer ((pElementSubgroup p L : Subgroup G) : Set G) :=
  sup_le Subgroup.le_normalizer d.S_le_normalizer_pES

theorem D_le_X : D ≤ pElementSubgroup p L ⊔ S := d.D_lt_S.le.trans le_sup_right

theorem img_X : img H D (pElementSubgroup p L ⊔ S) = img H D L ⊔ img H D S := by
  have hJH : pElementSubgroup p L ≤ H := (pElementSubgroup_le L).trans d.L_le_H
  have h1 : img H D (pElementSubgroup p L ⊔ S) =
      img H D (pElementSubgroup p L) ⊔ img H D S := by
    unfold img
    rw [Subgroup.subgroupOf_sup hJH d.S_le_H, Subgroup.map_sup]
  rw [h1, img_pES_eq d]

theorem N_le_D {X : Subgroup G} (hX : X = pElementSubgroup p L ⊔ S) {N : Subgroup ↥X}
    (hN : N.Normal) (hcop : Nat.Coprime p (Nat.card N)) : N.map X.subtype ≤ D := by
  have hXH : X ≤ H := hX ▸ d.X_le_H
  have himgX : img H D X = img H D L ⊔ img H D S := hX ▸ d.img_X
  have hKb := d.cfg
  haveI := d.simple_img
  set NG : Subgroup G := N.map X.subtype with hNG
  have hNGX : NG ≤ X := Subgroup.map_subtype_le N
  have hNGn : ∀ x ∈ X, ∀ n ∈ NG, x * n * x⁻¹ ∈ NG := by
    rintro x hx _ ⟨n', hn', rfl⟩
    exact ⟨⟨x, hx⟩ * n' * ⟨x, hx⟩⁻¹, hN.conj_mem n' hn' ⟨x, hx⟩, by simp⟩
  set Nb : Subgroup (QA H D) := img H D NG with hNb
  have hNbcop : Nat.Coprime p (Nat.card Nb) := by
    refine Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd (H := NG.subgroupOf H)
      (qmk H D)) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hNGX.trans hXH)).toEquiv,
      Subgroup.card_map_of_injective X.subtype_injective]
    exact hcop
  have hNbX : Nb ≤ img H D X := by
    rintro _ hx
    obtain ⟨n, hn, rfl⟩ := mem_img.mp hx
    exact mem_img.mpr ⟨n, hNGX hn, rfl⟩
  have hNbnorm : ∀ y ∈ img H D X, ∀ n ∈ Nb, y * n * y⁻¹ ∈ Nb := by
    intro y hy n hn
    obtain ⟨x, hxX, rfl⟩ := mem_img.mp hy
    obtain ⟨n', hn', rfl⟩ := mem_img.mp hn
    refine mem_img.mpr ⟨x * n' * x⁻¹, hNGn x hxX n' hn', ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hKbX : img H D L ≤ img H D X := by
    rw [himgX]
    exact le_sup_left
  have hXnK : img H D X ≤ normalizer ((img H D L : Subgroup (QA H D)) : Set (QA H D)) := by
    rw [himgX]
    exact sup_le Subgroup.le_normalizer d.img_S_le_K
  have hKbNb : img H D L ⊓ Nb = ⊥ := by
    set W : Subgroup ↥(img H D L) := Nb.subgroupOf (img H D L) with hW
    have hWn : W.Normal := by
      refine ⟨fun n hn g => ?_⟩
      exact hNbnorm g.1 (hKbX g.2) n.1 hn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W with hbot | htop
    · rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx.1⟩ : ↥(img H D L)) ∈ W := hx.2
      rw [hbot, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · exfalso
      have hle : img H D L ≤ Nb := fun x hx => by
        have : (⟨x, hx⟩ : ↥(img H D L)) ∈ W := by rw [htop]; exact Subgroup.mem_top _
        exact this
      have hpK : p ∣ Nat.card (img H D L) := by
        have h1 : orderOf (⟨qmk H D ⟨z, d.z_mem_H⟩, mem_img.mpr ⟨⟨z, d.z_mem_H⟩, d.z_mem_L, rfl⟩⟩ :
            ↥(img H D L)) = p := by
          rw [Subgroup.orderOf_mk]
          exact d.zb_order
        rw [← h1]
        exact orderOf_dvd_natCard _
      have := hpK.trans (Subgroup.card_dvd_of_le hle)
      exact (Nat.Prime.coprime_iff_not_dvd d.prime).mp hNbcop this
  have hNbtriv : ∀ x ∈ Nb, x = 1 := by
    intro x hx
    have hxX : x ∈ img H D L ⊔ img H D S := by
      rw [← himgX]
      exact hNbX hx
    refine KGQ.eq_one_of_centralizes hKb hxX fun k hk => ?_
    have hkX : k ∈ img H D X := hKbX hk
    have hc1 : x * k * x⁻¹ * k⁻¹ ∈ Nb := by
      have : k * x⁻¹ * k⁻¹ ∈ Nb := hNbnorm k hkX x⁻¹ (Nb.inv_mem hx)
      have h2 := Nb.mul_mem hx this
      simpa [mul_assoc] using h2
    have hc2 : x * k * x⁻¹ * k⁻¹ ∈ img H D L := by
      have hxk : x * k * x⁻¹ ∈ img H D L :=
        (mem_normalizer_iff.mp (hXnK (hNbX hx)) k).mp hk
      exact (img H D L).mul_mem hxk ((img H D L).inv_mem hk)
    have hc : x * k * x⁻¹ * k⁻¹ ∈ img H D L ⊓ Nb := ⟨hc2, hc1⟩
    rw [hKbNb, Subgroup.mem_bot] at hc
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc
    exact hc
  rintro _ ⟨n, hn, rfl⟩
  have hnH : n.1 ∈ H := hXH n.2
  have h1 : qmk H D ⟨n.1, hnH⟩ = 1 := hNbtriv _ (mem_img.mpr ⟨⟨n.1, hnH⟩, ⟨n, hn, rfl⟩, rfl⟩)
  exact (qmk_eq_one_iff (H := H) (D := D)).mp h1

end KGData

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGC
