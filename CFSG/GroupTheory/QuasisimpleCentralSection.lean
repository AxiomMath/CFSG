module

public import CFSG.Foundations.Basic
import CFSG.GroupTheory.PerfectCentralExtensionUnique

public section

namespace CFSG.GroupTheory

open Subgroup

universe u v

theorem eq_top_and_exists_central_surjection_of_quasisimple_section :
    ∀ (U : Type u) (V : Type v) [Group U] [Group V] [Finite U] [Finite V],
      CFSG.IsQuasisimple U → CFSG.IsQuasisimple V →
      (U ⧸ Subgroup.center U ≃* V ⧸ Subgroup.center V) →
      ∀ (H : Subgroup V) (f : H →* U), Function.Surjective f →
        H = ⊤ ∧ ∃ F : V →* U,
          (Function.Surjective F ∧ F.ker ≤ Subgroup.center V) ∧
          F.comp H.subtype = f ∧
          Subgroup.map F (Subgroup.center V) = Subgroup.center U := by
  intro U V _ _ _ _ hU hV e H f hf
  classical
  let qV : V →* V ⧸ Subgroup.center V := QuotientGroup.mk' (Subgroup.center V)
  let qU : U →* U ⧸ Subgroup.center U := QuotientGroup.mk' (Subgroup.center U)
  let r : H →* V ⧸ Subgroup.center V := qV.comp H.subtype
  let g : H →* U ⧸ Subgroup.center U := qU.comp f
  have hqVker : qV.ker = Subgroup.center V :=
    QuotientGroup.ker_mk' (Subgroup.center V)
  have hg_surj : Function.Surjective g := by
    intro y
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center U) y
    obtain ⟨h, rfl⟩ := hf u
    exact ⟨h, rfl⟩
  have hK_le : r.ker ≤ g.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hxV : (x : V) ∈ Subgroup.center V := by
      have hmem : (x : V) ∈ (QuotientGroup.mk' (Subgroup.center V)).ker :=
        MonoidHom.mem_ker.mpr (by simpa [r, qV] using hx)
      simpa using hmem
    have hfx : f x ∈ Subgroup.center U := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨h, rfl⟩ := hf y
      have hcomm : h * x = x * h := by
        refine (Subgroup.subtype_injective H) ?_
        simpa using Subgroup.mem_center_iff.mp hxV (h : V)
      calc
        f h * f x = f (h * x) := (map_mul f h x).symm
        _ = f (x * h) := congrArg f hcomm
        _ = f x * f h := map_mul f x h
    have hmem : f x ∈ (QuotientGroup.mk' (Subgroup.center U)).ker := by
      rw [QuotientGroup.ker_mk']
      exact hfx
    simpa [g, qU] using MonoidHom.mem_ker.mp hmem
  let gbar : H ⧸ r.ker →* U ⧸ Subgroup.center U := QuotientGroup.lift r.ker g hK_le
  have hgbar : Function.Surjective gbar :=
    QuotientGroup.lift_surjective_of_surjective r.ker g hg_surj hK_le
  have hcard : Nat.card (V ⧸ Subgroup.center V) ≤ Nat.card r.range := by
    calc
      Nat.card (V ⧸ Subgroup.center V) = Nat.card (U ⧸ Subgroup.center U) :=
        (Nat.card_congr e.toEquiv).symm
      _ ≤ Nat.card (H ⧸ r.ker) := Nat.card_le_card_of_surjective gbar hgbar
      _ = Nat.card r.range :=
        Nat.card_congr (QuotientGroup.quotientKerEquivRange r).toEquiv
  have hrange : r.range = ⊤ := Subgroup.eq_top_of_le_card r.range hcard
  have hmap : H.map qV = ⊤ := by
    have h := hrange
    change (qV.comp H.subtype).range = ⊤ at h
    rw [← MonoidHom.map_range qV H.subtype, Subgroup.range_subtype] at h
    exact h
  have hsup : H ⊔ Subgroup.center V = ⊤ := by
    have h := Subgroup.comap_map_eq qV H
    rw [hmap, Subgroup.comap_top, hqVker] at h
    exact h.symm
  have hHtop : H = ⊤ := by
    exact @eq_top_of_sup_le_center_of_isPerfect V _ hV.1 H (Subgroup.center V) le_rfl hsup
  let eH : H ≃* V := MulEquiv.ofBijective H.subtype
    ⟨Subgroup.subtype_injective H,
      fun v => ⟨⟨v, by rw [hHtop]; exact Subgroup.mem_top v⟩, rfl⟩⟩
  let F : V →* U := f.comp eH.symm.toMonoidHom
  have hFsurj : Function.Surjective F := by
    intro u
    obtain ⟨h, rfl⟩ := hf u
    exact ⟨eH h, by simp [F]⟩
  have hFker : F.ker ≤ Subgroup.center V := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups (Q := V) hV
      (MonoidHom.normal_ker F) with htop | hle
    · exfalso
      obtain ⟨u, hu⟩ := @exists_ne U (CFSG.LocalCores.isQuasisimple_nontrivial hU) 1
      obtain ⟨v, rfl⟩ := hFsurj u
      have hv : v ∈ F.ker := by
        rw [htop]
        exact Subgroup.mem_top v
      exact hu (MonoidHom.mem_ker.mp hv)
    · exact hle
  have hFcomp : F.comp H.subtype = f := by
    ext x
    have hx : H.subtype x = eH x := rfl
    simp only [MonoidHom.comp_apply, F, MulEquiv.coe_toMonoidHom, hx,
      MulEquiv.symm_apply_apply]
  have hcenter : Subgroup.map F (Subgroup.center V) = Subgroup.center U := by
    rw [← CFSG.LocalCores.comap_center_eq_of_perfect hV.1 F hFsurj hFker,
      Subgroup.map_comap_eq_self_of_surjective hFsurj (Subgroup.center U)]
  exact ⟨hHtop, F, ⟨hFsurj, hFker⟩, hFcomp, hcenter⟩

end CFSG.GroupTheory
