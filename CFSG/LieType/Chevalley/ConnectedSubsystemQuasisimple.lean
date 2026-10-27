module

public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4StandardQuasisimple

public noncomputable section

namespace CFSG.LieType.Chevalley.ConnSubsys

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open scoped Pointwise

@[expose] def IsDynkinConnected (τ : Tag) (A : Set (Fin τ.rank)) : Prop :=
  ∀ S : Set (Fin τ.rank), (∃ i ∈ A, i ∈ S) →
    (∀ i ∈ A, ∀ j ∈ A, i ∈ S → i ≠ j → τ.cartan i j ≠ 0 → j ∈ S) → A ⊆ S

variable {τ : Tag} {K : Type} [Field K] {A : Set (Fin τ.rank)}

section Lengths


theorem height_reflect (j : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    height (reflect τ j v) = height v - ∑ k, τ.cartan j k * v k := by
  simp [reflect, height, Finset.sum_sub_distrib, Pi.single_apply]

theorem adjacent_lengths {i j : Fin τ.rank} (hij : i ≠ j) (hc : τ.cartan i j ≠ 0) :
    (coxeterSystem τ).length (simple τ i * simple τ j) =
        (coxeterSystem τ).length (simple τ j) + 1 ∧
      (coxeterSystem τ).length (simple τ j * (simple τ i * simple τ j)) =
        (coxeterSystem τ).length (simple τ i * simple τ j) + 1 := by
  have hA := isFiniteType_cartan τ
  have hji : τ.cartan j i ≠ 0 := fun h => hc ((hA.apply_eq_zero_iff).2 h)
  have hle1 : τ.cartan i j ≤ 0 := hA.apply_le_zero_of_ne hij
  have hle2 : τ.cartan j i ≤ 0 := hA.apply_le_zero_of_ne hij.symm
  have hjj : τ.cartan j j = 2 := hA.apply_self j
  rw [length_simple_mul_eq_add_one_iff, length_simple_mul_eq_add_one_iff, mul_inv_rev,
    simple_inv, simple_inv, mul_smul, simple_smul, simple_smul, simple_smul]
  refine ⟨?_, ?_⟩
  · rw [height_reflect, height_single]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    omega
  · rw [height_reflect]
    have h1 : height (reflect τ i (Pi.single j 1)) = 1 - τ.cartan i j := by
      rw [height_reflect, height_single]
      simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    have hr : reflect τ i (Pi.single j 1) = Pi.single j 1 - τ.cartan i j • Pi.single i 1 := by
      simp [reflect, Pi.single_apply]
    have h2 : ∑ k, τ.cartan j k * reflect τ i (Pi.single j 1) k =
        τ.cartan j j - τ.cartan i j * τ.cartan j i := by
      rw [hr]
      have e : ∀ k, τ.cartan j k * (Pi.single j 1 - τ.cartan i j • Pi.single i 1 :
          Fin τ.rank → ℤ) k =
          τ.cartan j k * (Pi.single j 1 : Fin τ.rank → ℤ) k -
            τ.cartan i j * (τ.cartan j k * (Pi.single i 1 : Fin τ.rank → ℤ) k) := by
        intro k
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, Pi.single_apply, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [h1, h2, hjj]
    have h3 : τ.cartan i j ≤ -1 := by omega
    have h4 : τ.cartan j i ≤ -1 := by omega
    have : 1 ≤ τ.cartan i j * τ.cartan j i := by nlinarith
    omega

end Lengths

section Tits


theorem subsystemGroup_le_center_or_eq_top_of_connected
    (hperf : Group.IsPerfect (subsystemGroup τ K A)) (hconn : IsDynkinConnected τ A)
    (M : Subgroup (subsystemGroup τ K A)) [hM : M.Normal] :
    M ≤ Subgroup.center (subsystemGroup τ K A) ∨ M = ⊤ := by
  classical
  have hMmQ : M.map (subsystemGroup τ K A).subtype ≤ subsystemGroup τ K A :=
    Subgroup.map_subtype_le _
  have hconjM : ∀ g ∈ subsystemGroup τ K A, ∀ x ∈ M.map (subsystemGroup τ K A).subtype,
      g * x * g⁻¹ ∈ M.map (subsystemGroup τ K A).subtype := by
    intro g hg x hx
    obtain ⟨m, hmM, hmx⟩ := hx
    have h1 := hM.conj_mem m hmM ⟨g, hg⟩
    refine ⟨_, h1, ?_⟩
    rw [← hmx]
    rfl
  have hnorm : subsystemGroup τ K A ≤
      Subgroup.normalizer (M.map (subsystemGroup τ K A).subtype : Set (ModGL τ K)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconjM g hg x, fun hx => ?_⟩
    have h1 := hconjM g⁻¹ (inv_mem hg) _ hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1
  by_cases hex : ∃ i₀ ∈ A,
      weylElt τ K i₀ 1 ∈ M.map (subsystemGroup τ K A).subtype ⊔ subsystemBorel τ K A
  · right
    obtain ⟨i₀, hi₀, hn₀⟩ := hex
    have hall : ∀ k ∈ A,
        weylElt τ K k 1 ∈ M.map (subsystemGroup τ K A).subtype ⊔ subsystemBorel τ K A :=
      hconn {k | weylElt τ K k 1 ∈
        M.map (subsystemGroup τ K A).subtype ⊔ subsystemBorel τ K A} ⟨i₀, hi₀, hn₀⟩
        fun i hi j hj hiS hij hc =>
          weylElt_mem_sup_of_adjacent hnorm hi hj (adjacent_lengths hij hc).1
            (adjacent_lengths hij hc).2 hiS
    have hQP := subsystemGroup_le_of_forall_weylElt_mem le_sup_right hall
    have : Group.IsSolvable ((subsystemBorel τ K A).subgroupOf (subsystemGroup τ K A)) := by
      have := isSolvable_subsystemBorel (τ := τ) (K := K) (A := A)
      have e := Subgroup.subgroupOfEquivOfLe (subsystemBorel_le_subsystemGroup (τ := τ) (K := K)
        (A := A))
      exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hsup : M ⊔ (subsystemBorel τ K A).subgroupOf (subsystemGroup τ K A) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      have hg : (g : ModGL τ K) ∈
          M.map (subsystemGroup τ K A).subtype ⊔ subsystemBorel τ K A := hQP g.2
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _
        (subsystemBorel_le_subsystemGroup.trans hnorm)] at hg
      obtain ⟨_, ⟨m, hm, rfl⟩, b, hb, hmb⟩ := hg
      have hbQ : b ∈ subsystemGroup τ K A := subsystemBorel_le_subsystemGroup hb
      have hg' : g = m * ⟨b, hbQ⟩ := Subtype.ext (by rw [← hmb]; rfl)
      rw [hg']
      exact mul_mem (Subgroup.mem_sup_left hm) (Subgroup.mem_sup_right
        (show (⟨b, hbQ⟩ : subsystemGroup τ K A) ∈
          (subsystemBorel τ K A).subgroupOf (subsystemGroup τ K A) from hb))
    exact CFSG.LieType.TitsSimplicity.eq_top_of_sup_eq_top hperf inferInstance hsup
  · left
    push Not at hex
    have hPB := le_subsystemBorel_of_forall_weylElt_notMem le_sup_right
      (sup_le hMmQ subsystemBorel_le_subsystemGroup) hex
    have h1 := (le_subsystemTorus_of_le_subsystemBorel hnorm (le_sup_left.trans hPB)).2
    intro m hm
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (h1 m ⟨m, hm, rfl⟩ g g.2).symm

theorem isQuasisimple_subsystemGroup (hK : ∃ s : Finset K, s.card = 4) (hA : A.Nonempty)
    (hconn : IsDynkinConnected τ A) : CFSG.IsQuasisimple (subsystemGroup τ K A) := by
  have := nontrivial_subsystemGroup (τ := τ) (K := K) hA
  have hperf := isPerfect_subsystemGroup (τ := τ) (A := A) hK
  exact CFSG.LieType.TitsSimplicity.isQuasisimple_of_forall hperf fun M _ =>
    subsystemGroup_le_center_or_eq_top_of_connected hperf hconn M

theorem isQuasisimple_subsystemGroup_of_isPerfect (hperf : Group.IsPerfect (subsystemGroup τ K A))
    (hA : A.Nonempty) (hconn : IsDynkinConnected τ A) :
    CFSG.IsQuasisimple (subsystemGroup τ K A) := by
  have := nontrivial_subsystemGroup (τ := τ) (K := K) hA
  exact CFSG.LieType.TitsSimplicity.isQuasisimple_of_forall hperf fun M _ =>
    subsystemGroup_le_center_or_eq_top_of_connected hperf hconn M

end Tits

end CFSG.LieType.Chevalley.ConnSubsys
