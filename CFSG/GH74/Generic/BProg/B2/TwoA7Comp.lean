module

public import CFSG.GH74.Generic.BProg.B2.Defs
public import CFSG.GH74.Generic.GKFAlt

public section

namespace CFSG.GH74.Generic.BProg.B2.SD.TwoA7

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

variable {G : Type} [Group G] [Finite G]

theorem J_doubleCover {M : Subgroup G} (J : Subgroup (Mbar M)) (hJ : IsComponent J)
    (hA7 : Nonempty (↥J ⧸ center ↥J ≃* alternatingGroup (Fin 7))) (hZ : center ↥J ≠ ⊥) :
    IsDoubleCoverOfAlt ↥J 7 := by
  have hX : pPrimeCore 2 (Mbar M) = ⊥ := CFSG.GH74.GLS.pPrimeCore_quotient_eq_bot ↥M
  have h2 : IsPGroup 2 ↥(center ↥J) := CFSG.GH74.GLS.isPGroup_two_center_of_subnormal hX hJ.2
  have hle : Nat.card ↥(center ↥J) ≤ 2 :=
    CFSG.GH74.Generic.alt_cover_of_central_kernel (by norm_num) hJ.1 h2 hA7.some
  have hpos : 0 < Nat.card ↥(center ↥J) := Nat.card_pos
  have hne : Nat.card ↥(center ↥J) ≠ 1 := fun h => hZ (Subgroup.card_eq_one.mp h)
  exact ⟨hJ.1, by omega, hA7⟩

theorem J_commute_barK {x : G} {K M Q H : Subgroup G} (h1 : Stage2Concl1Core x K M Q H)
    (J : Subgroup (Mbar M)) (hJ : IsComponent J) (hdc : IsDoubleCoverOfAlt ↥J 7) :
    ∀ j ∈ J, ∀ k ∈ (barIn M K : Subgroup (Mbar M)), j * k = k * j := by
  have hHsub : (barIn M H).IsSubnormal :=
    Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective _) h1.H_min.2.1.2
  rcases CFSG.LocalCores.component_subnormal_subgroup hJ hHsub with hJH | hcomm
  · exact absurd ⟨hdc.1, Or.inr (Or.inr (Or.inr (Or.inl ⟨7, le_rfl, by norm_num, hdc⟩)))⟩
      (h1.H_G2 J hJ hJH).2.2
  · have hKH : barIn M K ≤ barIn M H :=
      Subgroup.map_mono (Subgroup.subgroupOf_mono M h1.H_min.1)
    have hJc : ⁅J, barIn M K⁆ = ⊥ :=
      le_bot_iff.mp (hcomm ▸ Subgroup.commutator_mono le_rfl hKH)
    intro j hj k hk
    exact ((mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hJc hj)) k hk).symm

end CFSG.GH74.Generic.BProg.B2.SD.TwoA7
