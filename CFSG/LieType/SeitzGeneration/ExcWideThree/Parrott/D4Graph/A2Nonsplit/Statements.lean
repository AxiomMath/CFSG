module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.Defs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.TwistDiag
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.StandardPairFacts

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator CFSG.HardMathSupport.Seitz.Proving


@[expose] def NonsplitSylowCentral : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 → 4 ≤ Nat.card K →
    ∀ x : ↥(adjointGroup Tag.D4 K), gammaP K (orderThreeSL K) x = x → x ^ 3 = 1 →
      ∃ c : ↥(adjointGroup Tag.D4 K), gammaP K (orderThreeSL K) c = c ∧
        Commute (c⁻¹ * x * c) (frameD K (orderThreeSL K))

variable {K : Type} [Field K] [Finite K]

theorem orderThreeSL_not_mem_center : orderThreeSL K ∉ Subgroup.center (SL2 K) := by
  intro h
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h
  have h01 := congrFun (congrFun hr 0) 1
  rw [orderThreeSL_val] at h01
  simp at h01

theorem closure_fixedSubgroup_frameD (hF : D4GraphA2FrameGen) (hK3 : ringChar K ≠ 3)
    (hK4 : 4 ≤ Nat.card K) :
    Subgroup.closure ((fixedSubgroup (gammaP K (orderThreeSL K)) :
      Set ↥(adjointGroup Tag.D4 K)) ∪ {frameD K (orderThreeSL K)}) = ⊤ := by
  rw [eq_top_iff, ← hF K hK3 hK4 (orderThreeSL K) (orderThreeSL_pow_three K)
    (orderThreeSL_ne_one K), Subgroup.closure_le]
  rintro g (hg | ⟨β, hβ, c, rfl | rfl⟩)
  · exact Subgroup.subset_closure (Or.inl hg)
  · exact (xPar_frame_mem_closure hK4 orderThreeSL_not_mem_center
      (exists_witness_orderThreeSL hK4) hβ c).1
  · exact (xPar_frame_mem_closure hK4 orderThreeSL_not_mem_center
      (exists_witness_orderThreeSL hK4) hβ c).2

theorem pairGenAt_orderThreeSL_of (hF : D4GraphA2FrameGen) (hS : NonsplitSylowCentral)
    (hq : Nat.card K % 3 = 2) (hK4 : 4 ≤ Nat.card K) :
    PairGenAt (gammaP K (orderThreeSL K)) := by
  have hK3 : ringChar K ≠ 3 := by
    intro h3
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
    rw [Nat.card_eq_fintype_card, hn, h3] at hq
    have : (3 : ℕ) ^ (n : ℕ) % 3 = 0 := by
      rw [Nat.pow_mod]; simp [Nat.zero_pow n.pos]
    omega
  intro x hx3 _ hαx
  obtain ⟨c, hcα, hc⟩ := hS K hq hK4 x hαx hx3
  have hcα' : gammaP K (orderThreeSL K) c⁻¹ = c⁻¹ := by rw [map_inv, hcα]
  refine closure_eq_top_of_conj hcα' ?_
  rw [inv_inv, eq_top_iff, ← closure_fixedSubgroup_frameD hF hK3 hK4]
  refine Subgroup.closure_mono ?_
  rintro y (hy | hy)
  · exact Or.inr hy
  · left
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact hc.symm.eq

theorem d4GraphA2PairGenNonsplit_of (hF : D4GraphA2FrameGen) (hS : NonsplitSylowCentral) :
    D4GraphA2PairGenNonsplit := by
  intro K _ _ hq hK4 B hB3 hB1
  have h3 : 3 ∣ Nat.card K + 1 := by omega
  obtain ⟨S, hS'⟩ := exists_conj_eq_orderThreeSL h3 hB3 hB1
  refine pairGenAt_of_conj_eq (MulAut.conj (sl2At K ⟨2, by decide⟩ S))
    (pairGenAt_orderThreeSL_of hF hS hq hK4) (Or.inl ?_)
  rw [conj_gammaP, hS']

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit
