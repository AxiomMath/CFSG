module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdMu
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Sec

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

theorem starOrb_of_typeR {X : Type} [Group X] [Finite X] {r : ℕ} {Φ : Set (Subgroup X)}
    (hR : TypeRFam r Φ) {L L' : Subgroup X} (hL : L ∈ Φ) (hs : L' ∈ omegaStarNbr Φ L)
    (hn : L' ∉ omegaNbr Φ L) {a b : X} (ha : IsUniqueInvolution L a)
    (hb : IsUniqueInvolution L' b) :
    ∃ g : X, g * a * g⁻¹ = b ∧ g * b * g⁻¹ = a * b := by
  have hΦ := hR.hyp
  obtain ⟨g, hg, hgL⟩ := aEmpty_of_noTwins hΦ hL (hR.noTwins L hL) L' hs hn a b ha hb
  have hga : g * a * g⁻¹ = b := by
    have h1 := ha.conj g
    rw [hgL] at h1
    exact h1.eq hb
  obtain ⟨u, v, R, T, c⟩ := Sec6Gen.exists_cfg64 hΦ hL hs.1 ha hb hs hn
  obtain ⟨k, hk, hku⟩ := c.exists_r
  have hkb : k * b * k⁻¹ = a * b := c.conj_j_of_not_mem hk hku
  have hka : k * a * k⁻¹ = a := by
    rw [← ha.commute_of_mem (c.hR.1 hk)]
    group
  have hab : b * a = a * b := c.UV_comm b c.j_mem_UV a c.z_mem_UV
  have hgN : g ∈ Subgroup.normalizer ((Subgroup.closure {a, b} : Subgroup X) : Set X) :=
    (sup_le inf_le_right inf_le_right :
      pairNormalizers L L' a b ≤ Subgroup.normalizer ((Subgroup.closure {a, b} : Subgroup X) :
        Set X)) hg
  have hBle : Subgroup.closure {a, b} ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v :=
    (Subgroup.closure_le _).mpr
      (Set.insert_subset_iff.mpr ⟨c.z_mem_UV, Set.singleton_subset_iff.mpr c.j_mem_UV⟩)
  have hgb : g * b * g⁻¹ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v :=
    hBle ((Subgroup.mem_normalizer_iff.mp hgN b).mp
      (Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)))
  have hsq : (g * b * g⁻¹) * (g * b * g⁻¹) = 1 := by
    calc (g * b * g⁻¹) * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
      _ = 1 := by rw [hb.sq]; group
  rcases c.sq_eq_one_of_mem_UV hgb hsq with h | h | h | h
  ·
    exfalso
    apply hb.ne_one
    calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  ·
    refine ⟨g * k, ?_, ?_⟩
    · calc g * k * a * (g * k)⁻¹ = g * (k * a * k⁻¹) * g⁻¹ := by group
        _ = b := by rw [hka, hga]
    · calc g * k * b * (g * k)⁻¹ = g * (k * b * k⁻¹) * g⁻¹ := by group
        _ = (g * a * g⁻¹) * (g * b * g⁻¹) := by rw [hkb]; group
        _ = a * b := by rw [hga, h, hab]
  ·
    exfalso
    apply c.z_ne_j
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = g⁻¹ * (g * b * g⁻¹) * g := by rw [hga, h]
      _ = b := by group
  · exact ⟨g, hga, h⟩

section Cit3


theorem secIdStarOrbId3_proved : SecIdStarOrbId3 := by
  intro X _ _ Φ hR _ _ _ _ L hL L' hs hn a b ha hb
  exact starOrb_of_typeR hR hL hs hn ha hb

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
