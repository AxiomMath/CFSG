module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.SharedTarget

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3

@[expose] def ExLie (Y : Type) [Group Y] [Finite Y] : Prop :=
  CFSG.Blueprint.LieModel Y .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel Y .POmegaPlus 4 2 1

theorem tightE4_of_exLie_quotient {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y} [N.Normal]
    (h2 : IsPGroup 2 ↥N) (hN : N ≠ ⊥) (h : ExLie (Y ⧸ N)) : TightE4 Y := by
  refine ⟨Y ⧸ N, inferInstance, QuotientGroup.mk' N, QuotientGroup.mk'_surjective N, ?_, ?_, h⟩
  · rw [QuotientGroup.ker_mk']; exact h2
  · rw [QuotientGroup.ker_mk']; exact hN


theorem tightCentTwinLift_of_q8RecogLie (h : Q8TwinRecogEx (fun Y _ _ => ExLie Y)) (n : ℕ) :
    TightCentTwinLift n := by
  intro hA hb Y _ _ hn R S t hd hc hE2 hQ _ c hcZ hc1 hy hE4
  obtain ⟨y, hy⟩ := hy
  have B := q8Bridge_of_centTwin hd hc hE2 hQ hcZ hc1 hy
  have hle : Nat.card (Y ⧸ TA3.fstarCenter Y) ≤ n := by rw [← hn]; exact B.quot.card_lt.le
  have hcN : c ∈ TA3.fstarCenter Y := by
    have hcC : c ∈ Subgroup.centralizer (genFittingFStar Y : Set Y) :=
      Subgroup.mem_centralizer_iff.mpr fun g _ => Subgroup.mem_center_iff.mp hcZ g
    have hcF : c ∈ genFittingFStar Y := CFSG.Adapters.generalized_fitting_self_centralizing Y hcC
    refine ⟨⟨c, hcF⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hcZ g)
  have hNbot : TA3.fstarCenter Y ≠ ⊥ := fun hb' => hc1 (by simpa [hb'] using hcN)
  rcases h _ B.simple B.nonab (cit3Below_mono hle hA) (tightBelow_mono hle hb) _ _ _
      B.quot.datum B.quot.cls.1 B.quot.cls.2.1 B.quot.hyp B.aEmpty
      (isSubnormal_tightCore_map hd B.central B.two B.not_mem) B.quot.twin with hl | hx
  · exact good_of_hasLift_twin hd B.central B.two B.not_mem hl
  · exact absurd (tightE4_of_exLie_quotient B.two hNbot hx) hE4

end CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
