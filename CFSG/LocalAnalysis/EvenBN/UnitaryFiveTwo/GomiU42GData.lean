module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42K3
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Model1
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4YPrelim

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer

variable {G : Type} [Group G] (d : Data G)

theorem Data.K₃_eq_pull_StabSub : d.K₃ = d.pull StabSub := by
  unfold Data.K₃
  rw [K₃sub_eq_StabSub_cert]

theorem Data.orderOf_e₂ : orderOf d.e₂ = 3 := by
  rw [Data.e₂, orderOf_injective _ d.ι_injective, orderOf_e₂SU]

theorem Data.e₂_ne_one : d.e₂ ≠ 1 := fun h1 => by
  have := d.orderOf_e₂
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem Data.K₃_le_centralizer_e₂ :
    d.K₃ ≤ centralizer ({d.e₂} : Set G) := by
  rw [d.K₃_eq_pull_StabSub]
  rintro _ ⟨g, hg, rfl⟩
  rw [mem_centralizer_singleton_iff, Data.e₂, ← map_mul, ← map_mul,
    commute_e₂SU_of_mem_StabSub hg]

theorem Data.zpowers_e₂_inf_K₃ : zpowers d.e₂ ⊓ d.K₃ = ⊥ := by
  have e1 : zpowers d.e₂ = d.pull (zpowers e₂SU) := by
    rw [Data.pull, Data.e₂, MonoidHom.map_zpowers]
  rw [e1, d.K₃_eq_pull_StabSub, ← d.pull_inf, zpowers_e₂SU_inf_StabSub]
  exact Subgroup.map_bot _

theorem Data.inf_centralizer_e₂ :
    d.L ⊓ centralizer ({d.e₂} : Set G) = zpowers d.e₂ ⊔ d.K₃ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxL, hxC⟩ := mem_inf.1 hx
    obtain ⟨g, rfl⟩ : ∃ g : SU52, d.ι g = x := ⟨d.η ⟨x, hxL⟩, d.ι_η ⟨x, hxL⟩⟩
    have hcomm : g * e₂SU = e₂SU * g := by
      apply d.ι_injective
      rw [map_mul, map_mul]
      exact mem_centralizer_singleton_iff.1 hxC
    have hg : g ∈ zpowers e₂SU ⊔ StabSub := by
      rw [← centralizer_e₂SU_eq]
      exact mem_centralizer_singleton_iff.2 hcomm
    have e1 : d.pull (zpowers e₂SU ⊔ StabSub) = zpowers d.e₂ ⊔ d.K₃ := by
      rw [d.pull_sup, d.K₃_eq_pull_StabSub, Data.pull, Data.pull, Data.e₂,
        ← MonoidHom.map_zpowers]
    rw [← e1]
    exact ⟨g, hg, rfl⟩
  · refine sup_le (le_inf ?_ ?_) (le_inf (d.pull_le_L _) d.K₃_le_centralizer_e₂)
    · exact zpowers_le.2 (d.ι_mem _)
    · exact zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)

namespace Data.Hyp

variable {d : Data G} [Finite G]

theorem centralizer_e₂_inf_H (h : d.Hyp) :
    centralizer ({d.e₂} : Set G) ⊓ d.H = zpowers d.t ⊔ (zpowers d.e₂ ⊔ d.K₃) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxC, hxH⟩ := mem_inf.1 hx
    by_cases hσ : h.fieldFactor ⟨x, hxH⟩ = 1
    · obtain ⟨l, hl, c, hc, hxlc⟩ := (h.fieldFactor_eq_one_iff ⟨x, hxH⟩).1 hσ
      change x = l * c at hxlc
      have hc' : c ∈ zpowers d.t := by
        rw [← h.centralizer_inf_H_eq]
        exact hc
      have hcC : c ∈ centralizer ({d.e₂} : Set G) := by
        have ht : d.t ∈ centralizer ({d.e₂} : Set G) :=
          mem_centralizer_singleton_iff.2 h.e₂_comm_t.symm
        exact (zpowers_le.2 ht) hc'
      have hlC : l ∈ centralizer ({d.e₂} : Set G) := by
        have e : l = x * c⁻¹ := by rw [hxlc]; group
        rw [e]
        exact mul_mem hxC (inv_mem hcC)
      have hl' : l ∈ zpowers d.e₂ ⊔ d.K₃ := by
        rw [← d.inf_centralizer_e₂]
        exact mem_inf.2 ⟨hl, hlC⟩
      rw [hxlc]
      exact mul_mem (mem_sup_right hl') (mem_sup_left hc')
    · exfalso
      have hσ' : UnitaryFiveTwo.fieldFactor (h.act ⟨x, hxH⟩) ≠ 1 := hσ
      obtain ⟨s, hs⟩ := exists_eq_conj_mul_fld hσ'
      have h1 : h.act ⟨x, hxH⟩ e₂SU = e₂SU := by
        apply d.ι_injective
        rw [h.ι_act_apply]
        change x * d.e₂ * x⁻¹ = d.e₂
        have hx' : x * d.e₂ = d.e₂ * x := mem_centralizer_singleton_iff.1 hxC
        rw [hx']
        group
      rw [hs, MulAut.mul_apply, fld_e₂SU, MulAut.conj_apply] at h1
      apply not_conj_e₂SU_inv s
      have h2 := congrArg (fun y => y⁻¹) h1
      simpa [mul_assoc] using h2
  · have ht : d.t ∈ centralizer ({d.e₂} : Set G) ⊓ d.H :=
      mem_inf.2 ⟨mem_centralizer_singleton_iff.2 h.e₂_comm_t.symm, h.t_mem_H⟩
    have he : d.e₂ ∈ centralizer ({d.e₂} : Set G) ⊓ d.H :=
      mem_inf.2 ⟨mem_centralizer_singleton_iff.2 rfl, h.L_le_H (d.ι_mem e₂SU)⟩
    exact sup_le (zpowers_le.2 ht) (sup_le (zpowers_le.2 he)
      (le_inf d.K₃_le_centralizer_e₂ ((d.pull_le_L _).trans h.L_le_H)))

theorem t_not_mem_e₂_sup_K₃ (h : d.Hyp) : d.t ∉ zpowers d.e₂ ⊔ d.K₃ := fun ht => by
  have hle : zpowers d.e₂ ⊔ d.K₃ ≤ d.L :=
    sup_le (zpowers_le.2 (d.ι_mem e₂SU)) (d.pull_le_L _)
  exact h.t_not_mem_L (hle ht)

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
