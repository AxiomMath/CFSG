module

public import CFSG.LocalAnalysis.ZStar
public import CFSG.GF2Type.Aschbacher1976Common.NotZStar
public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_conj_mem_centralizer_ne (h : StdHyp G L) {t : G} (ht2 : orderOf t = 2) :
    ∃ g : G, g * t * g⁻¹ ∈ centralizer ({t} : Set G) ∧ g * t * g⁻¹ ≠ t := by
  by_contra hne
  push_neg at hne
  haveI := Fintype.ofFinite G
  haveI := h.simple
  have ht1 : t ≠ 1 := by rintro rfl; simp at ht2
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  exact CFSG.GF2Type.Aschbacher1976Common.not_inZStar_of_isSimpleGroup h.nonabelian ht2
    (CFSG.ZStar.glauberman_zStar G t ht1 htt fun g hc =>
      hne g (Subgroup.mem_centralizer_singleton_iff.mpr hc))

end CFSG.EvenSporadicStandard.M12Std.PropA
