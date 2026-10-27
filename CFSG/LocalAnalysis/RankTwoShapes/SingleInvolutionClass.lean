module

public import CFSG.LocalAnalysis.RankTwoShapes.SylowShapes
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralDerivedInvolutions
public import CFSG.CharacterTheory.Semidihedral.Local.DerivedInvolutionsConjugate
public import CFSG.CharacterTheory.Wreathed.SimpleFusion
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Local

public section

namespace CFSG.RankTwoShapes

universe u

theorem involutions_isConj_of_twoRank_eq_two
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrank : CFSG.Assembly.twoRank G = 2) {x y : G}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  have hperfect : commutator G = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
    · obtain ⟨a, b, hab⟩ := hnonab
      exact absurd (((commutator_eq_bot_iff G).mp h).is_comm.comm a b) hab
    · exact h
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 G))
  rcases rank_two_sylow_shapes hnonab hrank S with
    ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨H, _, U, hH, hSU⟩
  · obtain ⟨-, -, -, -, hall⟩ :=
      CFSG.Semidihedral.Principal.dihedral_derived_involutions_conjugate S hn ⟨e.symm⟩
    exact hall hperfect x y hx hy
  · obtain ⟨-, -, hall⟩ :=
      CFSG.Semidihedral.Local.semidihedral_derived_involutions_conjugate n hn S e.symm
    exact ((hall hperfect x).mp hx).trans ((hall hperfect y).mp hy).symm
  · obtain ⟨-, -, hall, -, -⟩ :=
      CFSG.Wreathed.simple_wreathed_one_involution_class_and_local_S3 hnonab n hn S e
    exact hall x y hx hy
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, hall, -⟩ :=
      CFSG.LyonsUnitaryFour.lyons_unitary_four_fusion_and_centralizers hnonab hH S U hSU
    exact hall x y hx hy

theorem rank_two_simple_involutions_conjugate
    {G : Type u} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hrank : CFSG.Assembly.twoRank G = 2) :
    ∃ z : G, orderOf z = 2 ∧ ∀ t : G, orderOf t = 2 → ∃ g : G, g⁻¹ * t * g = z := by
  let e : Shrink.{0} G ≃* G := Shrink.mulEquiv
  have : Finite (Shrink.{0} G) := Finite.of_equiv G e.toEquiv.symm
  have : IsSimpleGroup (Shrink.{0} G) := e.isSimpleGroup
  have hnonab' : ∃ a b : Shrink.{0} G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e h
  have hrank' : CFSG.Assembly.twoRank (Shrink.{0} G) = 2 :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 2) (by norm_num) e).trans hrank
  obtain ⟨E, -, hEcard⟩ := exists_elementary_four_of_twoRank hrank'
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := E) 2 (by rw [hEcard]; norm_num)
  have hx' : orderOf (x : Shrink.{0} G) = 2 := (Subgroup.orderOf_coe x).trans hx
  refine ⟨e x, (MulEquiv.orderOf_eq e _).trans hx', fun t ht => ?_⟩
  have hconj := involutions_isConj_of_twoRank_eq_two hnonab' hrank'
    (x := e.symm t) (y := (x : Shrink.{0} G)) (by rwa [MulEquiv.orderOf_eq]) hx'
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  refine ⟨(e c)⁻¹, ?_⟩
  have h := congrArg e hc
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply] at h
  rwa [inv_inv]

end CFSG.RankTwoShapes
