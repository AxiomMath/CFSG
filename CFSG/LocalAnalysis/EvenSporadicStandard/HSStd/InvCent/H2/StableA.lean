module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.H2.NormalC
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Dichotomy
import CFSG.GroupTheory.NonabelianSimpleOrderSixty

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG CFSG.EvenSporadicStandard.SolomonRed

namespace H2Cfg

variable {G : Type*} [Group G] {t v : G} {J : Subgroup G}

theorem stable_aux_A [Finite G] (cfg : H2Cfg G t v J) (hF : fittingSubgroup G = ⊥)
    {L : Subgroup G} (hL : IsComponent L) {w u : G} (hw : w ∈ kleinV t v)
    (hu : u ∈ kleinV t v) (hu1 : u ≠ 1) (hwL : w ∉ normalizer (L : Set G))
    (huL : u ∈ normalizer (L : Set G)) : False := by
  have hw1 : w ≠ 1 := by
    intro h
    exact hwL (by rw [h]; exact one_mem _)
  let L' : Subgroup G := L.map (MulAut.conj w).toMonoidHom
  have hL'_def : L' = L.map (MulAut.conj w).toMonoidHom := rfl
  have hL' : IsComponent L' := by rw [hL'_def]; exact isComponent_conj hL w
  have hne' : L' ≠ L := by
    intro h
    refine hwL ((Subgroup.mem_normalizer_iff_map_conj_eq (H := L) (g := w)).2 ?_)
    change L' = L
    exact h
  have hne : L ≠ L' := fun h => hne' h.symm
  have hcom := component_commute hL hL' hne
  have hdisj := component_inf_eq_bot hF hL hL' hne
  have huw : u * w = w * u := cfg.comm_of_mem hu hw
  have h_inv_uw : w⁻¹ * u⁻¹ = u⁻¹ * w⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, huw]
  have key : ∀ s ∈ L, u * s = s * u := by
    intro s hs
    have hswap : w * (s * (w * s * w⁻¹)) = (s * (w * s * w⁻¹)) * w :=
      swap_fixed (cfg.sq_eq_one_of_mem hw) hcom rfl hs
    have hdC : s * (w * s * w⁻¹) ∈ centralizer ({t} : Set G) := by
      rw [← cfg.centralizer_eq_of_mem hw hw1]
      rw [mem_centralizer_singleton_iff]
      exact hswap.symm
    have hud : u * (s * (w * s * w⁻¹)) = (s * (w * s * w⁻¹)) * u :=
      cfg.kleinV_central hdC hu
    have hs'L : u * s * u⁻¹ ∈ L :=
      ((Subgroup.mem_normalizer_iff (H := L) (g := u)).1 huL s).1 hs
    have hconj : u * (w * s * w⁻¹) * u⁻¹ = w * (u * s * u⁻¹) * w⁻¹ := by
      calc u * (w * s * w⁻¹) * u⁻¹
          = u * w * s * w⁻¹ * u⁻¹ := by group
        _ = w * u * s * w⁻¹ * u⁻¹ := by rw [huw]
        _ = w * u * s * (w⁻¹ * u⁻¹) := by group
        _ = w * u * s * (u⁻¹ * w⁻¹) := by rw [h_inv_uw]
        _ = w * (u * s * u⁻¹) * w⁻¹ := by group
    have heq : (u * s * u⁻¹) * (w * (u * s * u⁻¹) * w⁻¹) = s * (w * s * w⁻¹) := by
      have h1 : u * (s * (w * s * w⁻¹)) * u⁻¹ = s * (w * s * w⁻¹) := by
        rw [hud]; group
      calc (u * s * u⁻¹) * (w * (u * s * u⁻¹) * w⁻¹)
          = (u * s * u⁻¹) * (u * (w * s * w⁻¹) * u⁻¹) := by rw [← hconj]
        _ = u * (s * (w * s * w⁻¹)) * u⁻¹ := by group
        _ = s * (w * s * w⁻¹) := h1
    have hmem : s⁻¹ * (u * s * u⁻¹) ∈ L ⊓ L' := by
      refine ⟨L.mul_mem (L.inv_mem hs) hs'L, ?_⟩
      rw [hL'_def]
      have hrew : s⁻¹ * (u * s * u⁻¹) =
          (w * s * w⁻¹) * (w * (u * s * u⁻¹) * w⁻¹)⁻¹ := by
        calc s⁻¹ * (u * s * u⁻¹)
            = s⁻¹ * ((u * s * u⁻¹) * (w * (u * s * u⁻¹) * w⁻¹)) *
                (w * (u * s * u⁻¹) * w⁻¹)⁻¹ := by group
          _ = s⁻¹ * (s * (w * s * w⁻¹)) * (w * (u * s * u⁻¹) * w⁻¹)⁻¹ := by rw [heq]
          _ = (w * s * w⁻¹) * (w * (u * s * u⁻¹) * w⁻¹)⁻¹ := by group
      rw [hrew]
      exact (L.map (MulAut.conj w).toMonoidHom).mul_mem ⟨s, hs, rfl⟩
        ((L.map (MulAut.conj w).toMonoidHom).inv_mem ⟨u * s * u⁻¹, hs'L, rfl⟩)
    have hs'_eq : u * s * u⁻¹ = s := by
      have h1 : s⁻¹ * (u * s * u⁻¹) = 1 := by
        have := hmem
        rw [hdisj, mem_bot] at this
        exact this
      calc u * s * u⁻¹ = s * (s⁻¹ * (u * s * u⁻¹)) := by group
        _ = s * 1 := by rw [h1]
        _ = s := by simp
    exact conj_eq_self_iff.1 hs'_eq
  have hLcent : L ≤ centralizer ({u} : Set G) := by
    intro s hs
    rw [mem_centralizer_singleton_iff]
    exact (key s hs).symm
  have hLC : L ≤ centralizer ({t} : Set G) := by
    rw [← cfg.centralizer_eq_of_mem hu hu1]
    exact hLcent
  have hL'C : L' ≤ centralizer ({t} : Set G) := by
    rw [hL'_def]
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    exact (centralizer ({t} : Set G)).mul_mem
      ((centralizer ({t} : Set G)).mul_mem (cfg.kleinV_le_centralizer hw) (hLC hs))
      ((centralizer ({t} : Set G)).inv_mem (cfg.kleinV_le_centralizer hw))
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hL.1.1
  have hLle : L ≤ ⁅J, J⁆ := cfg.perfect_le_derived hLC hLperf
  have hL'perf : ⁅L', L'⁆ = L' := Subgroup.isPerfect_iff.mp hL'.1.1
  have hL'le : L' ≤ ⁅J, J⁆ := cfg.perfect_le_derived hL'C hL'perf
  have hnabL : ∃ x y : ↥L, x * y ≠ y * x := by
    obtain ⟨a, ha, b, hb, hab⟩ := component_nonab hF hL
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hnabL' : ∃ x y : ↥L', x * y ≠ y * x := by
    obtain ⟨a, ha, b, hb, hab⟩ := component_nonab hF hL'
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have h60 : 60 ≤ Nat.card ↥L :=
    CFSG.GroupTheory.nonabelian_simple_order_at_least_sixty (component_isSimple hF hL) hnabL
  have h60' : 60 ≤ Nat.card ↥L' :=
    CFSG.GroupTheory.nonabelian_simple_order_at_least_sixty (component_isSimple hF hL') hnabL'
  have hLeq : L = ⁅J, J⁆ :=
    Subgroup.eq_of_le_of_card_ge hLle (by rw [cfg.card_derived]; exact h60)
  have hL'eq : L' = ⁅J, J⁆ :=
    Subgroup.eq_of_le_of_card_ge hL'le (by rw [cfg.card_derived]; exact h60')
  exact hne' (hL'eq.trans hLeq.symm)

end H2Cfg

end CFSG.EvenSporadicStandard.HSStd.InvCent
