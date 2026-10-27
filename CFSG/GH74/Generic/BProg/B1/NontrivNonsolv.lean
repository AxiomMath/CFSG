module

public import CFSG.GH74.Generic.BProg.B1.Nontriv
public import CFSG.GH74.Generic.BProg.B1.Lift2
public import CFSG.GH74.Generic.BProg.B1.ThetaPrime

public section

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup

theorem kgroup_centralizers {G : Type} [Group G] [Finite G] (hyp : Hyp2 G) :
    ∀ e : G, orderOf e = 2 →
      Gen4 ↥(centralizer ({e} : Set G)) ∧ IsKGroupNative ↥(centralizer ({e} : Set G)) := by
  intro e he
  refine ⟨Gen4.subgroup _ hyp.gen4, isKGroupNative_of_kgh hyp.kgh ?_⟩
  intro htop
  have hz : ∀ g : G, g * e = e * g := fun g =>
    Subgroup.mem_centralizer_singleton_iff.1 ((htop ▸ Subgroup.mem_top g : g ∈ centralizer ({e} : Set G)))
  have hcen : e ∈ Subgroup.center G := Subgroup.mem_center_iff.2 hz
  have : Subgroup.center G = ⊥ := by
    rcases hyp.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hyp.nonab
      exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm
  rw [this, Subgroup.mem_bot] at hcen
  rw [hcen, orderOf_one] at he
  omega

theorem stage1NontrivNonsolv_of_b2 (hB : B_B2_g4) : Stage1NontrivNonsolv := by
  intro G _ _ hyp _ x K hcirc _ A hsrc y Lb E Ib hE hn hns hbot
  rcases nonsolvAdm_dichotomy hB (kgroup_centralizers hyp) hcirc.1.1.1.1 hcirc.1.1.1.2.2 hn with h1 | h2
  · exact h1 (le_bot_iff.1 (hbot ▸ thetaHalf_le_thetaHalfPrime hsrc.2.1 hE))
  · exact hns h2

end CFSG.GH74.Generic.BProg.B1
