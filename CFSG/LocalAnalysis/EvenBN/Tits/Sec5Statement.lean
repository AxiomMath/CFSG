module

public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4Nine

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem Hyp.thm49Statement_iff
    (hd : d.Hyp) : d.Thm49Statement ↔ d.t * d.v ∈ d.tG := by
  refine ⟨t_mul_v_mem_tG_of_thm49Statement, fun htv => ?_⟩
  have htz : d.t * d.z ∈ d.tG := hd.exists_conj_eq_t_mul_z
  have hconj : ∀ l ∈ d.L, ∀ x, x ∈ d.tG → x ∈ centralizer ({d.t} : Set G) →
      l * x * l⁻¹ ∈ d.tG ∩ centralizer ({d.t} : Set G) := by
    intro l hl x hx hxC
    obtain ⟨g, rfl⟩ := hx
    refine ⟨⟨l * g, by group⟩, ?_⟩
    exact mul_mem (mul_mem (hd.L_le hl) hxC) (inv_mem (hd.L_le hl))
  have htzC : d.t * d.z ∈ centralizer ({d.t} : Set G) :=
    mul_mem d.t_mem_centralizer (hd.L_le d.z_mem)
  have htvC : d.t * d.v ∈ centralizer ({d.t} : Set G) :=
    mul_mem d.t_mem_centralizer (hd.L_le d.v_mem)
  ext s
  constructor
  · rintro ⟨⟨g, rfl⟩, hsC⟩
    rcases hd.conj_t_cases hsC with h | ⟨m, hm, h | h⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨m, hm, h.symm⟩)
    · exact Or.inr ⟨m, hm, h.symm⟩
  · rintro ((h | ⟨l, hl, rfl⟩) | ⟨l, hl, rfl⟩)
    · rw [Set.mem_singleton_iff.1 h]
      exact ⟨⟨1, by group⟩, d.t_mem_centralizer⟩
    · exact hconj l hl _ htz htzC
    · exact hconj l hl _ htv htvC

theorem Hyp.thm49Statement
    (hF : Thm49FailureExclusion) (hd : d.Hyp) : d.Thm49Statement :=
  hd.thm49Statement_iff.2 (hd.t_mul_v_mem_tG hF)

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
