module

public import CFSG.GH74.GLS.NT44.RigidSelection
public import CFSG.GH74.GLS.NT44.RigidActorExclusion
public import CFSG.GH74.GLS.NT44.RigidInnerExclusion

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG CFSG.GH74.GLS CFSG.ABGLocalTools
open CFSG.GH74.GLS.Stage1.Thm4

theorem false_of_isTwoTerminal_center_card_sixteen
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (x₀ : G) (K₀ : Subgroup G) (hterm : IsTwoTerminal x₀ K₀)
    (hL34 : IsL34Quotient (kBar K₀)) (h16 : Nat.card (center (kBar K₀)) = 16) :
    False := by
  classical
  obtain ⟨z, v, J, T, hz2, hJ, hmax, -, -, -, -, -, -, hzZ, -, hv2, hzv, hvz, hvN, hvact⟩ :=
    exists_rigid_actor_of_center_card_sixteen G hnonab hKP x₀ K₀ hterm hL34 h16
  have hzP : z ∈ Kz (kBar K₀) z := (Subgroup.mem_inf.mp hzZ).1
  exact false_of_rigid_actor_of_not_inner_conj hnonab hKP hL34 h16 hz2 hv2 hzv hvz hJ hvN hvact
    hzP hmax fun y hzy hyz hyJ hyact =>
      not_inner_of_rigid_actor hnonab hKP hL34 h16 hz2 (hzy.orderOf_eq.symm.trans hz2) hzy hyz
        hJ hyJ hyact hzP hmax

end CFSG.GH74.GLS.NT44

end
