module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec4_t_not_conj_z [Finite G] (h43 : Asc82Lemma43) {t : G} {L S : Subgroup G} {z : G}
    (hctx : Sec4Ctx G t L S z) (g : G) : g⁻¹ * z * g ≠ t := by
  intro hg
  have ht : t ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => by rw [Set.mem_singleton_iff.mp hh]
  have h1 := h43 G t L S z hctx g (by rw [hg]; exact ht)
  rw [hg] at h1
  have hzL : z ∈ L := hctx.pocket.mem
  have htL : t ∉ L := sec4_t_not_mem hctx.toSec4Setting
  have hLt : L ≤ centralizer ({t} : Set G) := hctx.component.le
  rcases h1 with ⟨l, hl, hlt⟩ | ⟨l, hl, hlt⟩
  · exact htL (by rw [hlt]; exact mul_mem (mul_mem hl hzL) (inv_mem hl))
  · have hcomm : t * l = l * t :=
      Subgroup.mem_centralizer_iff.mp (hLt hl) t (Set.mem_singleton t)
    have h2 : t = t * (l * z * l⁻¹) := by
      calc t = l * (t * z) * l⁻¹ := hlt
        _ = (l * t) * z * l⁻¹ := by group
        _ = (t * l) * z * l⁻¹ := by rw [hcomm]
        _ = t * (l * z * l⁻¹) := by group
    have h3 : l * z * l⁻¹ = 1 := mul_left_cancel (a := t) (by rw [mul_one]; exact h2.symm)
    have h4 : z = 1 := by
      have := congrArg (fun x => l⁻¹ * x * l) h3
      simpa [mul_assoc] using this
    have h5 := hctx.pocket.1
    rw [h4, orderOf_one] at h5
    exact absurd h5 (by decide)

theorem sec4_tz_not_conj_z [Finite G] (h43 : Asc82Lemma43) {t : G} {L S : Subgroup G} {z : G}
    (hctx : Sec4Ctx G t L S z) (htz : ∃ h : G, h⁻¹ * t * h = t * z) (g : G) :
    g⁻¹ * z * g ≠ t * z := by
  obtain ⟨h, hh⟩ := htz
  intro hg
  refine sec4_t_not_conj_z h43 hctx (g * h⁻¹) ?_
  calc (g * h⁻¹)⁻¹ * z * (g * h⁻¹) = h * (g⁻¹ * z * g) * h⁻¹ := by group
    _ = h * (t * z) * h⁻¹ := by rw [hg]
    _ = h * (h⁻¹ * t * h) * h⁻¹ := by rw [hh]
    _ = t := by group

end CFSG.OddStandard.SmallF3.Omega
