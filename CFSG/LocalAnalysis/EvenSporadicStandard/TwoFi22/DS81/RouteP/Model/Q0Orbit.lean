module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Q0Card
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Q0Masks
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.CocodeOrder
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Dictionary

public section

open scoped Pointwise

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.Blueprint CFSG.Sporadic.Mathieu
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

section Fix

theorem fix_planes_E0_subset :
    {e : Q3 | e ∈ E0 ∧ ∀ i : Fin 891, e • planeX i = planeX i} ⊆
      {epsMask 0, epsMask 256, epsMask 1216, epsMask 1472} := by
  rintro e ⟨he, hfix⟩
  obtain ⟨m, hm, rfl⟩ := exists_epsMask_of_mem_E0 he
  rcases eq_of_epsMask_fix hm hfix with rfl | rfl | rfl | rfl <;> simp

theorem finite_fix_planes_E0 :
    Set.Finite {e : Q3 | e ∈ E0 ∧ ∀ i : Fin 891, e • planeX i = planeX i} :=
  Set.Finite.subset (Set.toFinite _) fix_planes_E0_subset

theorem card_fix_planes_E0_le :
    Nat.card ↥{e : Q3 | e ∈ E0 ∧ ∀ i : Fin 891, e • planeX i = planeX i} ≤ 4 := by
  classical
  rw [Nat.card_coe_set_eq]
  calc Set.ncard {e : Q3 | e ∈ E0 ∧ ∀ i : Fin 891, e • planeX i = planeX i}
      ≤ Set.ncard ({epsMask 0, epsMask 256, epsMask 1216, epsMask 1472} : Set Q3) :=
        Set.ncard_le_ncard fix_planes_E0_subset (Set.toFinite _)
    _ ≤ 4 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
        rw [Set.ncard_singleton]

end Fix

section Chain

theorem card_Q0_le_value : Nat.card Q0 ≤ 36787322880 := by
  have h := card_Q0_le
  have hL := card_L0_le
  exact Nat.le_of_mul_le_mul_right (h.trans (hL.trans (by norm_num))) (by norm_num)

theorem card_D0_ge_value : 41287680 ≤ Nat.card D0 := by
  have h := card_D0_ge
  have hZ := card_Zq_ge
  have h24 : Nat.card (NativeSporadic.Carrier .M24) = 244823040 := card_M24
  rw [h24] at hZ
  omega

theorem card_orbit_ge : 891 ≤ Nat.card (MulAction.orbit ↥Q0 plane) := by
  have hinj : Function.Injective
      (fun i : Fin 891 => (⟨planeX i, planeX_mem_orbit i⟩ : MulAction.orbit ↥Q0 plane)) := by
    intro i j h
    exact planeX_injective (congrArg Subtype.val h)
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

theorem finite_Q0 : Finite ↥Q0 := by
  haveI := finite_L0
  exact Finite.of_injective (Subgroup.inclusion Q0_le_L0) (Subgroup.inclusion_injective _)

theorem card_D0_le_card_stabilizer :
    Nat.card D0 ≤ Nat.card (MulAction.stabilizer ↥Q0 plane) := by
  haveI := finite_Q0
  have hle : D0.subgroupOf Q0 ≤ MulAction.stabilizer ↥Q0 plane := by
    intro q hq
    rw [MulAction.mem_stabilizer_iff]
    exact D0_smul_plane (Subgroup.mem_subgroupOf.1 hq)
  calc Nat.card D0 = Nat.card (D0.subgroupOf Q0) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe D0_le_Q0).toEquiv).symm
    _ ≤ Nat.card (MulAction.stabilizer ↥Q0 plane) := Subgroup.card_le_of_le hle

theorem card_chain :
    Nat.card Q0 = 36787322880 ∧ Nat.card D0 = 41287680 ∧
      Nat.card (MulAction.orbit ↥Q0 plane) = 891 ∧
      Nat.card (MulAction.stabilizer ↥Q0 plane) = 41287680 := by
  have hA := card_Q0_le_value
  have hB := card_D0_ge_value
  have hN := card_orbit_ge
  have hS := card_D0_le_card_stabilizer
  have hprod := card_orbit_mul_card_stabilizer (G := ↥Q0) plane
  have hN' : Nat.card (MulAction.orbit ↥Q0 plane) = 891 := by
    by_contra hne
    have h892 : 892 ≤ Nat.card (MulAction.orbit ↥Q0 plane) := by omega
    have := Nat.mul_le_mul h892 (hB.trans hS)
    omega
  rw [hN'] at hprod
  omega

theorem card_D0 : Nat.card D0 = 41287680 := card_chain.2.1

theorem card_orbit_plane : Nat.card (MulAction.orbit ↥Q0 plane) = 891 := card_chain.2.2.1

theorem exists_planeX_eq_of_mem_orbit {P : Finset Ω} (hP : P ∈ MulAction.orbit ↥Q0 plane) :
    ∃ i : Fin 891, planeX i = P := by
  have hrange : Set.range planeX ⊆ (MulAction.orbit ↥Q0 plane : Set (Finset Ω)) := by
    rintro _ ⟨i, rfl⟩
    exact planeX_mem_orbit i
  have hcard : (MulAction.orbit ↥Q0 plane : Set (Finset Ω)).ncard ≤ (Set.range planeX).ncard := by
    rw [← Nat.card_coe_set_eq, card_orbit_plane, ← Nat.card_coe_set_eq,
      Nat.card_range_of_injective planeX_injective]
    simp
  have heq := Set.eq_of_subset_of_ncard_le hrange hcard (Set.toFinite _)
  rw [← heq] at hP
  exact hP

theorem stabilizer_plane_eq : MulAction.stabilizer ↥Q0 plane = D0.subgroupOf Q0 := by
  haveI := finite_Q0
  have hle : D0.subgroupOf Q0 ≤ MulAction.stabilizer ↥Q0 plane := by
    intro q hq
    rw [MulAction.mem_stabilizer_iff]
    exact D0_smul_plane (Subgroup.mem_subgroupOf.1 hq)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_chain.2.2.2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe D0_le_Q0).toEquiv, card_D0]

theorem sup_commutator_eq_top : D0.subgroupOf Q0 ⊔ commutator ↥Q0 = ⊤ := by
  set K : Subgroup ↥Q0 := D0.subgroupOf Q0 ⊔ commutator ↥Q0 with hK
  have hgen : ∀ s < 14, planeGen s ∈ K.map Q0.subtype := by
    intro s hs
    refine Subgroup.mem_map.2 ⟨⟨planeGen s, planeGen_mem_Q0 hs⟩, ?_, rfl⟩
    by_cases h13 : s < 13
    · exact Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 (planeGen_mem_D0 h13))
    · have hs13 : s = 13 := by omega
      subst hs13
      exact Subgroup.mem_sup_right planeGen_thirteen_mem_commutator
  refine eq_top_of_stabilizer_le_of_orbit_subset K plane ?_ ?_
  · rw [stabilizer_plane_eq]
    exact le_sup_left
  · intro y hy
    obtain ⟨i, rfl⟩ := exists_planeX_eq_of_mem_orbit hy
    obtain ⟨k, hk, hkp⟩ := exists_mem_smul_plane_eq_planeX (K.map Q0.subtype) hgen i
    obtain ⟨q, hqK, rfl⟩ := Subgroup.mem_map.1 hk
    exact ⟨⟨q, hqK⟩, hkp⟩

end Chain

section Kernel

theorem mem_E0_of_fix_planes {k : Q3} (hk : k ∈ Q0)
    (h : ∀ i : Fin 891, k • planeX i = planeX i) : k ∈ E0 := by
  have hstab : (⟨k, hk⟩ : ↥Q0) ∈ MulAction.stabilizer ↥Q0 plane := by
    rw [MulAction.mem_stabilizer_iff]
    have h0 := h 0
    rw [planeX_zero] at h0
    exact h0
  rw [stabilizer_plane_eq] at hstab
  have hkD : k ∈ D0 := Subgroup.mem_subgroupOf.1 hstab
  have hkZ : k ∈ Zq := D0_le_Zq hkD
  obtain ⟨hk0, hk1, hk2⟩ := mem_Q0_iff_of_fix.1 hk
  have hpt : ∀ p ∈ plane, k • p = p := by
    intro p hp
    by_cases hp0 : p = x0
    · rw [hp0]
      exact hk0
    by_cases hp1 : p = x1
    · rw [hp1]
      exact hk1
    by_cases hp2 : p = x2
    · rw [hp2]
      exact hk2
    obtain ⟨i, hi, hiff⟩ := exists_planeXN_inter_plane hp hp0 hp1 hp2
    have hpi : p ∈ planeXN i := (hiff p hp).2 (Or.inr (Or.inr (Or.inr rfl)))
    have hkp : k • p ∈ planeXN i := by
      have hfix : k • planeXN i = planeXN i := h ⟨i, hi⟩
      rw [← hfix]
      exact Finset.smul_mem_smul_finset hpi
    have hkpl : k • p ∈ plane := Zq_preserves_plane hkZ hp
    rcases (hiff _ hkpl).1 hkp with e | e | e | e
    · exact absurd (smul_left_cancel k (e.trans hk0.symm)) hp0
    · exact absurd (smul_left_cancel k (e.trans hk1.symm)) hp1
    · exact absurd (smul_left_cancel k (e.trans hk2.symm)) hp2
    · exact e
  have hker : planeHom ⟨k, hkZ⟩ = 1 := by
    refine Equiv.Perm.ext fun a => planePt_injective ?_
    rw [planePt_planeHom, Equiv.Perm.one_apply]
    exact hpt _ (planePt_mem a)
  have hmem : (⟨k, hkZ⟩ : Zq) ∈ planeHom.ker := MonoidHom.mem_ker.2 hker
  rw [planeHom_ker_eq] at hmem
  exact hmem

end Kernel

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
