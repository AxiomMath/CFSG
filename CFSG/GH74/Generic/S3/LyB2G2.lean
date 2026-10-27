module

public import CFSG.GH74.Generic.S3.LyB2L3
public import CFSG.GH74.Generic.S3.LyVert

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.Blueprint
  CFSG.BenderSuzuki.MatrixGroups Subgroup CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem blockData_of_kcent {L : Type} [Group L] (h : S45.KCent L) : BlockData L := by
  apply blockData_of_psl2_subgroup
  intro s hs2 hs1
  have hord : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hs2) hs1
  obtain ⟨-, -, p, f, hp, hf, hodd, hL⟩ := h s hord
  obtain ⟨-, F, hFf, hFfin, hF, ⟨e⟩⟩ := stated_of_lieModel_PSL hL
  exact ⟨F, hFf, hFfin, ⁅centralizer ({s} : Set L), centralizer ({s} : Set L)⁆,
    ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩, hF ▸ hodd,
    fun a ha b hb => Subgroup.commutator_mem_commutator ha hb⟩

theorem g2Table_of_jmax
    (hF : GenericKnownFacts) {G : Type} [Group G] [Finite G] {x : G}
    {K : Subgroup (CentralizerBar x)} (hset : S3Setup G x K) (hmax : IsJMax x K) : G2Table G := by
  intro u hu L hL hG2
  have hsh := generic_shapes_of_inG2 hF hset.simple hset.nonab hset.gen4 hset.kgh hu hG2
  have h7 : d2 ↥K = 7 := d2_eq_seven_of_shapeS3 hset.comp hset.g2 hset.shape
  have hle := (hmax.2 u L ⟨hu, hL, hG2⟩).1
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := S45.exists_noncomm_of_isQuasisimple hL.1
  rcases hsh with h1 | h2 | h3 | h4 | h5
  · exfalso
    have := d2_le_six_of_shapeS1 hL hG2 h1
    omega
  · exfalso
    have hZ : center ↥L ≠ ⊥ := by
      intro hbot
      have hmem : (⟨xbar u, h2.2⟩ : ↥L) ∈ center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_center_iff.1 (xbar_mem_center u) g)
      rw [hbot, Subgroup.mem_bot] at hmem
      exact xbar_ne_one hu (congrArg Subtype.val hmem)
    have := d2_le_six_of_shapeS2 hL hG2 hZ h2
    omega
  · obtain ⟨⟨p, f, hp, hp2, -, hmodel⟩, hxL⟩ := h3
    exact ⟨hxL, center_eq_bot_of_quasisimple_lieModel_L3 hL.1 hmodel,
      blockData_of_l3 hp hp2 hmodel⟩
  · obtain ⟨⟨f, hmodel⟩, hxL⟩ := h4
    have hsimple : IsSimpleGroup ↥L := CFSG.Timmesfeld.isSimpleGroup_of_lieModel hmodel
    exact ⟨hxL, center_eq_bot_of_simple_nonab hsimple hnab,
      blockData_of_kcent (S45.kCent_of_isJ1OrRee (Or.inr ⟨f, hmodel⟩))⟩
  · obtain ⟨hJ1, hxL⟩ := h5
    have hsimple : IsSimpleGroup ↥L := by
      obtain ⟨e⟩ := hJ1
      exact (MulEquiv.isSimpleGroup_congr e).2 CFSG.Sporadic.J1.isSimpleGroup_J1
    exact ⟨hxL, center_eq_bot_of_simple_nonab hsimple hnab,
      blockData_of_kcent (S45.kCent_of_isJ1OrRee (Or.inl hJ1))⟩

end CFSG.GH74.Generic.S3
