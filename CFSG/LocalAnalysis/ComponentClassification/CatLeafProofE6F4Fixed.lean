module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6F4Frame
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddExc

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (range_le_of_tv)
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem mem_orbitField_id
    (a : Fin TwistTag.E6.foldedTag.rank) (c : K) :
    c ∈ orbitField TwistTag.E6 K (RingHom.id K) a := by
  rw [mem_orbitField, show RingHom.id K = 1 from rfl, one_pow]
  rfl

@[expose] def e6OrbitToF4 : Fin TwistTag.E6.foldedTag.rank → Fin 4 :=
  ![3, 2, 1, 0]

theorem e6OrbitToF4_values :
    e6OrbitToF4 ⟨0, by decide⟩ = 3 ∧ e6OrbitToF4 ⟨1, by decide⟩ = 2 ∧
      e6OrbitToF4 ⟨2, by decide⟩ = 1 ∧ e6OrbitToF4 ⟨3, by decide⟩ = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem e6F4Rho_values
    (K : Type) [Field K] :
    e6F4Rho K 0 = simpleRootSL2 TwistTag.E6.tag K ⟨1, by decide⟩ ∧
      e6F4Rho K 1 = simpleRootSL2 TwistTag.E6.tag K ⟨3, by decide⟩ ∧
      e6F4Rho K 2 = pairHom (simpleRootSL2 TwistTag.E6.tag K ⟨2, by decide⟩)
        (simpleRootSL2 TwistTag.E6.tag K ⟨4, by decide⟩) (commute_e6_sl2_two_four K) ∧
      e6F4Rho K 3 = pairHom (simpleRootSL2 TwistTag.E6.tag K ⟨0, by decide⟩)
        (simpleRootSL2 TwistTag.E6.tag K ⟨5, by decide⟩) (commute_e6_sl2_zero_five K) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem coe_orbitX_orbitY_id
    (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K (RingHom.id K) a) :
    ((orbitX TwistTag.E6 K (RingHom.id K) a c : adjointGroup TwistTag.E6.tag K) :
        ModGL TwistTag.E6.tag K) = e6F4Rho K (e6OrbitToF4 a) (tv 0 1 (c : K)) ∧
      ((orbitY TwistTag.E6 K (RingHom.id K) a c : adjointGroup TwistTag.E6.tag K) :
        ModGL TwistTag.E6.tag K) = e6F4Rho K (e6OrbitToF4 a) (tv 1 0 (c : K)) := by
  have hpow : ∀ (k : ℕ) (x : K), ((RingHom.id K) ^ k) x = x := fun k x => by
    rw [show RingHom.id K = 1 from rfl, one_pow]
    rfl
  obtain ⟨o0, o1, o2, o3⟩ := e6OrbitToF4_values
  obtain ⟨r0, r1, r2, r3⟩ := e6F4Rho_values K
  rw [coe_orbitX, coe_orbitY]
  fin_cases a <;>
    simp [o0, o1, o2, o3, r0, r1, r2, r3, pairHom_apply, simpleRootSL2_tv01, simpleRootSL2_tv10,
      show (TwistTag.E6.orbit ⟨0, by decide⟩).card = 2 by decide,
      show (TwistTag.E6.orbit ⟨1, by decide⟩).card = 2 by decide,
      show (TwistTag.E6.orbit ⟨2, by decide⟩).card = 1 by decide,
      show (TwistTag.E6.orbit ⟨3, by decide⟩).card = 1 by decide,
      show TwistTag.E6.orbitMin ⟨0, by decide⟩ = ⟨0, by decide⟩ by decide,
      show TwistTag.E6.orbitMin ⟨1, by decide⟩ = ⟨2, by decide⟩ by decide,
      show TwistTag.E6.orbitMin ⟨2, by decide⟩ = ⟨3, by decide⟩ by decide,
      show TwistTag.E6.orbitMin ⟨3, by decide⟩ = ⟨1, by decide⟩ by decide, List.range_succ, hpow,
      show TwistTag.E6.perm ⟨0, by decide⟩ = ⟨5, by decide⟩ by decide,
      show TwistTag.E6.perm ⟨2, by decide⟩ = ⟨4, by decide⟩ by decide]

theorem orbitRankOneGroup_id_eq
    (a : Fin TwistTag.E6.foldedTag.rank) :
    orbitRankOneGroup TwistTag.E6 K (RingHom.id K) a = (e6F4Rho K (e6OrbitToF4 a)).range := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) (range_le_of_tv _ _ (fun c => ?_) fun c => ?_)
  · rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨_, ((coe_orbitX_orbitY_id a c).1).symm⟩
    · exact ⟨_, ((coe_orbitX_orbitY_id a c).2).symm⟩
  · rw [← (coe_orbitX_orbitY_id a ⟨c, mem_orbitField_id a c⟩).1]
    exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
  · rw [← (coe_orbitX_orbitY_id a ⟨c, mem_orbitField_id a c⟩).2]
    exact Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)

theorem iSup_e6F4Rho_range_eq :
    (⨆ k, (e6F4Rho K k).range) = graphFixedRootGroup TwistTag.E6 K (RingHom.id K) := by
  have h := (exceptional_fixed_simple_pair_generation TwistTag.E6 K (RingEquiv.refl K)).1
  rw [RingEquiv.toRingHom_refl'] at h
  rw [h]
  simp only [orbitRankOneGroup_id_eq]
  have hs : Function.Surjective e6OrbitToF4 := by decide
  exact (hs.iSup_comp fun k => (e6F4Rho K k).range).symm

variable [Finite K]

theorem graphFixedRootGroup_E6_id_recognition
    {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    IsQuasisimple ↥(graphFixedRootGroup TwistTag.E6 K (RingHom.id K)) ∧
      LieModel (↥(graphFixedRootGroup TwistTag.E6 K (RingHom.id K)) ⧸
        Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K (RingHom.id K))) .F4 0 p f := by
  obtain ⟨hqs, hlie⟩ := e6F4_frame_recognition (K := K) hp2 hK
  let e := MulEquiv.subgroupCongr (iSup_e6F4Rho_range_eq (K := K))
  exact ⟨LocalCores.isQuasisimple_of_mulEquiv e hqs,
    LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) hlie⟩

theorem oddLieCentralQuotient_graphFixedRootGroup_E6_id
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    OddLieCentralQuotient p ↥(graphFixedRootGroup TwistTag.E6 K (RingHom.id K)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  exact ⟨.F4, 0, f, ⟨hp, hf, rfl⟩, (graphFixedRootGroup_E6_id_recognition hp2 hK).2⟩

end CFSG.ComponentClassification.CatLeafProof
