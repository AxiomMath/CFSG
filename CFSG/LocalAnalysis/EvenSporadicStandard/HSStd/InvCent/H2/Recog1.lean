module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.Two
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.AutA5G
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Layer

import CFSG.GroupTheory.NonabelianSimpleOrderSixty
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.ConfigJ

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG CFSG.EvenSporadicStandard.SolomonRed

namespace H2Two

variable {G : Type*} [Group G] [Finite G] {t v : G} {J S₁ : Subgroup G}

private theorem recog1_mem_jOne {x : G} :
    x ∈ jOne t S₁ ↔ x ∈ centralizer ({t} : Set G) ∧ x ∈ centralizer (S₁ : Set G) :=
  Iff.rfl

theorem centralizer_le_normalizer (cfg : H2Cfg G t v J) (hF : fittingSubgroup G = ⊥)
    (hs : H2Two G t v J S₁) {c : G} (hc : c ∈ centralizer ({t} : Set G)) :
    c ∈ normalizer (S₁ : Set G) := by
  have hcomp : IsComponent (S₁.map (MulAut.conj c).toMonoidHom) :=
    isComponent_conj hs.comp₁ c
  rcases hs.comps (S₁.map (MulAut.conj c).toMonoidHom) hcomp with h | h
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa using h)
  · exfalso
    have ht_mem : t ∈ S₁.map (MulAut.conj c).toMonoidHom := by
      rw [Subgroup.mem_map]
      refine ⟨t, hs.V_le cfg.t_mem_kleinV, ?_⟩
      change c * t * c⁻¹ = t
      rw [mem_centralizer_singleton_iff.mp hc]
      group
    have ht_inf : t ∈ S₁ ⊓ ⁅J, J⁆ := ⟨hs.V_le cfg.t_mem_kleinV, h ▸ ht_mem⟩
    rw [component_inf_eq_bot hF hs.comp₁ hs.comp₀ hs.ne, Subgroup.mem_bot] at ht_inf
    exact cfg.t_ne_one ht_inf

theorem exists_conj_eq (cfg : H2Cfg G t v J) (hF : fittingSubgroup G = ⊥)
    (hs : H2Two G t v J S₁) (φ : ↥S₁ ≃* alternatingGroup (Fin 5)) {c : G}
    (hc : c ∈ centralizer ({t} : Set G)) :
    ∃ x ∈ kleinV t v, ∀ s ∈ S₁, c * s * c⁻¹ = x * s * x⁻¹ := by
  obtain ⟨x, hx, hconj⟩ :=
    exists_inner_of_normalizes (S := S₁) (a := t) (b := v) φ
      (hs.V_le cfg.t_mem_kleinV) (hs.V_le cfg.v_mem_kleinV) cfg.t_ne_one cfg.v_ne_one
      (cfg.v_ne_t.symm) cfg.t_sq cfg.v_sq cfg.tv_comm
      (centralizer_le_normalizer cfg hF hs hc)
      (mem_centralizer_singleton_iff.mp hc)
      (cfg.kleinV_central hc cfg.v_mem_kleinV).symm
  exact ⟨x, cfg.mem_kleinV_iff.mpr hx, hconj⟩

theorem jOne_inf_kleinV (cfg : H2Cfg G t v J) (hF : fittingSubgroup G = ⊥)
    (hs : H2Two G t v J S₁) : jOne t S₁ ⊓ kleinV t v = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxj, hxV⟩
  by_contra hx1
  obtain ⟨hxC, hxcent⟩ := (recog1_mem_jOne).mp hxj
  have hS₁C : S₁ ≤ centralizer ({t} : Set G) := by
    rw [← cfg.centralizer_eq_of_mem hxV hx1]
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hxcent s hs
  have hS₁V : S₁ ≤ kleinV t v := by
    have hEq : S₁ ⊓ centralizer ({t} : Set G) = S₁ := inf_eq_left.mpr hS₁C
    rw [← hEq]
    exact hs.inf_le
  have hcardle : Nat.card ↥S₁ ≤ 4 := by
    have h := Subgroup.card_le_of_le hS₁V
    rwa [cfg.card_kleinV] at h
  have hnabS : ∃ x y : ↥S₁, x * y ≠ y * x := by
    obtain ⟨a, ha, b, hb, hab⟩ := component_nonab hF hs.comp₁
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have h60 : 60 ≤ Nat.card ↥S₁ :=
    CFSG.GroupTheory.nonabelian_simple_order_at_least_sixty (component_isSimple hF hs.comp₁) hnabS
  omega

theorem exists_mul_of_mem_centralizer (cfg : H2Cfg G t v J) (hF : fittingSubgroup G = ⊥)
    (hs : H2Two G t v J S₁) (φ : ↥S₁ ≃* alternatingGroup (Fin 5)) {c : G}
    (hc : c ∈ centralizer ({t} : Set G)) : ∃ x ∈ kleinV t v, ∃ j ∈ jOne t S₁, c = x * j := by
  obtain ⟨x, hxV, hconj⟩ := exists_conj_eq cfg hF hs φ hc
  refine ⟨x, hxV, x⁻¹ * c, ?_, ?_⟩
  · refine (recog1_mem_jOne).mpr ⟨?_, ?_⟩
    · exact (centralizer ({t} : Set G)).mul_mem
        ((centralizer ({t} : Set G)).inv_mem (cfg.kleinV_le_centralizer hxV)) hc
    · rw [Subgroup.mem_centralizer_iff]
      intro s hs'
      have hjs : (x⁻¹ * c) * s = s * (x⁻¹ * c) := by
        calc (x⁻¹ * c) * s = x⁻¹ * (c * s * c⁻¹) * c := by group
          _ = x⁻¹ * (x * s * x⁻¹) * c := by rw [hconj s hs']
          _ = s * (x⁻¹ * c) := by group
      exact hjs.symm
  · exact (mul_inv_cancel_left x c).symm

theorem eq_one_of_mem_jOne (cfg : H2Cfg G t v J) (hF : fittingSubgroup G = ⊥)
    (hs : H2Two G t v J S₁) {j : G} (hj : j ∈ jOne t S₁)
    (h : ∀ b ∈ ⁅J, J⁆, j * b = b * j) : j = 1 := by
  obtain ⟨hjc, hjcent⟩ := (recog1_mem_jOne).mp hj
  obtain ⟨a, haV, j', hj'J, rfl⟩ := cfg.exists_mul_of_mem_centralizer hjc
  have hj'1 : j' = 1 := by
    apply cfg.eq_one_of_centralizes_derived hj'J
    intro b hb
    have hbC : b ∈ centralizer ({t} : Set G) := cfg.derived_le_centralizer hb
    have hab : a * b = b * a := cfg.kleinV_central hbC haV
    have hjab : (a * j') * b = b * (a * j') := h b hb
    have h1 : a * (j' * b) = a * (b * j') := by
      calc a * (j' * b) = (a * j') * b := by group
        _ = b * (a * j') := hjab
        _ = (b * a) * j' := by group
        _ = (a * b) * j' := by rw [← hab]
        _ = a * (b * j') := by group
    exact mul_left_cancel h1
  rw [hj'1, mul_one]
  have hajOne : a ∈ jOne t S₁ :=
    (recog1_mem_jOne).mpr ⟨cfg.kleinV_le_centralizer haV, by simpa [hj'1] using hjcent⟩
  have hmem : a ∈ jOne t S₁ ⊓ kleinV t v := ⟨hajOne, haV⟩
  rw [jOne_inf_kleinV cfg hF hs, Subgroup.mem_bot] at hmem
  exact hmem

end H2Two

end CFSG.EvenSporadicStandard.HSStd.InvCent
