module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.RootFacts

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3


private theorem conj_kill_aux {G : Type*} [Group G] {P U V Z : G}
    (hPV : Commute P V) (hZU : Commute Z U) (hZV : Z * V = 1) (hc : ⁅P, U⁆ = Z) :
    P * (U * V) * P⁻¹ = U := by
  have h1 : P * U * P⁻¹ = Z * U := by
    rw [← hc, commutatorElement_def]
    group
  have h2 : P * V * P⁻¹ = V := by
    rw [hPV.eq]
    group
  calc P * (U * V) * P⁻¹ = (P * U * P⁻¹) * (P * V * P⁻¹) := by group
    _ = Z * U * V := by rw [h1, h2]
    _ = U * Z * V := by rw [hZU.eq]
    _ = U := by rw [mul_assoc, hZV, mul_one]

section PosMem

variable {K : Type} [Field K]

private theorem pinnedX_mem_posUnipotent_of_pos {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α) (hpos : 0 < height α) (c : K) :
    pinnedX TwistTag.D4.tag K α c ∈ posUnipotent TwistTag.D4.tag K :=
  rootSpan_le_posUnipotent (τ := TwistTag.D4.tag) (K := K)
    (S := {β | IsRoot TwistTag.D4.tag β ∧ 0 < height β}) (fun _ h => h)
    (pinnedX_mem_rootSpan (τ := TwistTag.D4.tag) (K := K)
      (S := {β | IsRoot TwistTag.D4.tag β ∧ 0 < height β}) ⟨hα, hpos⟩ c)

end PosMem

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
  (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
include hf hK hσ

private theorem fieldActor_longElt_fixed {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : γ = rootB ∨ γ = rootC ∨ γ = rootD) {c : K} (hc : σ c = c) :
    fieldActor (t := TwistTag.D4) σ σ (longElt hf hK σ hσ hγ c hc) =
      longElt hf hK σ hσ hγ c hc := by
  apply Subtype.ext
  rw [coe_fieldActor]
  apply Units.ext
  rw [Units.coe_map]
  change entrywise σ.toRingHom
      (pinnedX TwistTag.D4.tag K γ c : Module.End K (RootModule TwistTag.D4.tag K)) =
    (pinnedX TwistTag.D4.tag K γ c : Module.End K (RootModule TwistTag.D4.tag K))
  have hc' : σ.toRingHom c = c := hc
  rw [entrywise_pinnedX, hc']

theorem conj_mul_fieldActor_of_fixed (j y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hj : fieldActor (t := TwistTag.D4) σ σ j = j) :
    MulAut.conj j * (MulAut.conj y * fieldActor (t := TwistTag.D4) σ σ) * (MulAut.conj j)⁻¹ =
      MulAut.conj (j * y * j⁻¹) * fieldActor (t := TwistTag.D4) σ σ := by
  have hj' : fieldActor (t := TwistTag.D4) σ σ j⁻¹ = j⁻¹ := by
    rw [map_inv, hj]
  refine MulEquiv.ext fun x => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, map_mul, hj, hj']
  group

theorem exists_commutator_rootB_rootC : ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ m r : K,
    ⁅pinnedX TwistTag.D4.tag K rootB m, pinnedX TwistTag.D4.tag K rootC r⁆ =
      pinnedX TwistTag.D4.tag K rootD (ε * m * r) :=
  exists_commutator_pinnedX_of_sum (K := K) isRoot_rootB isRoot_rootC (by decide) (by decide)
    (by decide) isRoot_rootD

theorem exists_conj_kill_D_of_B {s r' : K} (hs : σ s = s) (hr' : σ r' = r') (hs0 : s ≠ 0) :
    ∃ j : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, fieldActor (t := TwistTag.D4) σ σ j = j ∧
      j * (longElt hf hK σ hσ (Or.inl rfl) s hs * longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r' hr') *
        j⁻¹ = longElt hf hK σ hσ (Or.inl rfl) s hs := by
  obtain ⟨ε, hε, h⟩ : ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∀ c d : K,
      ⁅pinnedX TwistTag.D4.tag K rootC c, pinnedX TwistTag.D4.tag K rootB d⁆ =
        pinnedX TwistTag.D4.tag K rootD (ε * c * d) :=
    exists_commutator_pinnedX_of_sum (K := K) isRoot_rootC isRoot_rootB (by decide) (by decide)
      (by decide) isRoot_rootD
  have hεε : ε * ε = 1 := by
    rcases hε with rfl | rfl <;> norm_num
  obtain ⟨m, hm_def⟩ : ∃ m : K, m = -(ε * r') * s⁻¹ := ⟨_, rfl⟩
  have hm : σ m = m := by
    rw [hm_def]
    rcases hε with rfl | rfl <;> simp [hs, hr']
  have hεms : ε * m * s = -r' := by
    rw [hm_def]
    calc ε * (-(ε * r') * s⁻¹) * s = -(ε * ε) * r' * (s⁻¹ * s) := by ring
      _ = -r' := by rw [hεε, inv_mul_cancel₀ hs0]; ring
  have hU : pinnedX TwistTag.D4.tag K rootB s ∈ posUnipotent TwistTag.D4.tag K :=
    pinnedX_mem_posUnipotent_of_pos isRoot_rootB (by rw [height_rootB]; norm_num) s
  have hP : pinnedX TwistTag.D4.tag K rootC m ∈ posUnipotent TwistTag.D4.tag K :=
    pinnedX_mem_posUnipotent_of_pos isRoot_rootC (by rw [height_rootC]; norm_num) m
  refine ⟨longElt hf hK σ hσ (Or.inr (Or.inl rfl)) m hm,
    fieldActor_longElt_fixed hf hK σ hσ (Or.inr (Or.inl rfl)) hm, ?_⟩
  apply Subtype.ext
  change pinnedX TwistTag.D4.tag K rootC m *
      (pinnedX TwistTag.D4.tag K rootB s * pinnedX TwistTag.D4.tag K rootD r') *
      (pinnedX TwistTag.D4.tag K rootC m)⁻¹ = pinnedX TwistTag.D4.tag K rootB s
  refine conj_kill_aux (commute_pinnedX_rootD_of_mem_posUnipotent hf hK σ hσ hP r') ?_ ?_ (h m s)
  · exact (commute_pinnedX_rootD_of_mem_posUnipotent hf hK σ hσ hU _).symm
  · rw [← pinnedX_add, hεms, neg_add_cancel, pinnedX_zero]

theorem exists_conj_kill_D_of_C {r r' : K} (hr : σ r = r) (hr' : σ r' = r') (hr0 : r ≠ 0) :
    ∃ j : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, fieldActor (t := TwistTag.D4) σ σ j = j ∧
      j * (longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr *
          longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r' hr') * j⁻¹ =
        longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr := by
  obtain ⟨ε, hε, h⟩ := exists_commutator_rootB_rootC hf hK σ hσ
  have hεε : ε * ε = 1 := by
    rcases hε with rfl | rfl <;> norm_num
  obtain ⟨m, hm_def⟩ : ∃ m : K, m = -(ε * r') * r⁻¹ := ⟨_, rfl⟩
  have hm : σ m = m := by
    rw [hm_def]
    rcases hε with rfl | rfl <;> simp [hr, hr']
  have hεmr : ε * m * r = -r' := by
    rw [hm_def]
    calc ε * (-(ε * r') * r⁻¹) * r = -(ε * ε) * r' * (r⁻¹ * r) := by ring
      _ = -r' := by rw [hεε, inv_mul_cancel₀ hr0]; ring
  have hB : pinnedX TwistTag.D4.tag K rootB m ∈ posUnipotent TwistTag.D4.tag K :=
    pinnedX_mem_posUnipotent_of_pos isRoot_rootB (by rw [height_rootB]; norm_num) m
  have hC : pinnedX TwistTag.D4.tag K rootC r ∈ posUnipotent TwistTag.D4.tag K :=
    pinnedX_mem_posUnipotent_of_pos isRoot_rootC (by rw [height_rootC]; norm_num) r
  refine ⟨longElt hf hK σ hσ (Or.inl rfl) m hm,
    fieldActor_longElt_fixed hf hK σ hσ (Or.inl rfl) hm, ?_⟩
  apply Subtype.ext
  change pinnedX TwistTag.D4.tag K rootB m *
      (pinnedX TwistTag.D4.tag K rootC r * pinnedX TwistTag.D4.tag K rootD r') *
      (pinnedX TwistTag.D4.tag K rootB m)⁻¹ = pinnedX TwistTag.D4.tag K rootC r
  refine conj_kill_aux (commute_pinnedX_rootD_of_mem_posUnipotent hf hK σ hσ hB r') ?_ ?_ (h m r)
  · exact (commute_pinnedX_rootD_of_mem_posUnipotent hf hK σ hσ hC _).symm
  · rw [← pinnedX_add, hεmr, neg_add_cancel, pinnedX_zero]

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
