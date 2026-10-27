module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Q0Orbit

public section

open scoped Pointwise

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

section Gen

noncomputable def planeGenQ (s : ℕ) : ↥Q0 :=
  if h : s < 14 then ⟨planeGen s, planeGen_mem_Q0 h⟩ else 1

theorem planeGenQ_val {s : ℕ} (hs : s < 14) : ((planeGenQ s : ↥Q0) : Q3) = planeGen s := by
  simp [planeGenQ, hs]

theorem planeGenQ_mem_D0 {s : ℕ} (hs : s < 13) : planeGenQ s ∈ D0.subgroupOf Q0 :=
  Subgroup.mem_subgroupOf.2 (by rw [planeGenQ_val (by omega)]; exact planeGen_mem_D0 hs)

end Gen

section Act

theorem exists_planeX_smul_eq (q : ↥Q0) (i : Fin 891) :
    ∃ j : Fin 891, (q : Q3) • planeX i = planeX j := by
  obtain ⟨a, ha⟩ := planeX_mem_orbit i
  have ha' : a • plane = planeX i := ha
  have h : (q : Q3) • planeX i ∈ MulAction.orbit ↥Q0 plane := by
    refine ⟨q * a, ?_⟩
    show (q * a) • plane = (q : Q3) • planeX i
    rw [mul_smul, ha']
    rfl
  obtain ⟨j, hj⟩ := exists_planeX_eq_of_mem_orbit h
  exact ⟨j, hj.symm⟩

noncomputable def planeXIdx (q : ↥Q0) (i : Fin 891) : Fin 891 :=
  Classical.choose (exists_planeX_smul_eq q i)

theorem planeXIdx_spec (q : ↥Q0) (i : Fin 891) : (q : Q3) • planeX i = planeX (planeXIdx q i) :=
  Classical.choose_spec (exists_planeX_smul_eq q i)

theorem planeXIdx_eq_iff {q : ↥Q0} {i j : Fin 891} :
    planeXIdx q i = j ↔ (q : Q3) • planeX i = planeX j := by
  rw [planeXIdx_spec q i]
  exact ⟨fun h => by rw [h], fun h => planeX_injective h⟩

theorem planeXIdx_one (i : Fin 891) : planeXIdx 1 i = i :=
  planeXIdx_eq_iff.2 (by rw [Subgroup.coe_one, one_smul])

theorem planeXIdx_mul (q q' : ↥Q0) (i : Fin 891) :
    planeXIdx (q * q') i = planeXIdx q (planeXIdx q' i) :=
  planeXIdx_eq_iff.2 (by rw [Subgroup.coe_mul, mul_smul, planeXIdx_spec q' i, planeXIdx_spec q])

noncomputable def planeXAct : ↥Q0 →* Equiv.Perm (Fin 891) where
  toFun q :=
    { toFun := planeXIdx q
      invFun := planeXIdx q⁻¹
      left_inv := fun i => by
        show planeXIdx q⁻¹ (planeXIdx q i) = i
        rw [← planeXIdx_mul, inv_mul_cancel, planeXIdx_one]
      right_inv := fun i => by
        show planeXIdx q (planeXIdx q⁻¹ i) = i
        rw [← planeXIdx_mul, mul_inv_cancel, planeXIdx_one] }
  map_one' := Equiv.ext planeXIdx_one
  map_mul' q q' := Equiv.ext (planeXIdx_mul q q')

theorem smul_planeX (q : ↥Q0) (i : Fin 891) : (q : Q3) • planeX i = planeX (planeXAct q i) :=
  planeXIdx_spec q i

theorem planeXAct_eq_iff {q : ↥Q0} {i j : Fin 891} :
    planeXAct q i = j ↔ (q : Q3) • planeX i = planeX j :=
  planeXIdx_eq_iff

theorem exists_planeXAct_eq (i j : Fin 891) : ∃ q : ↥Q0, planeXAct q i = j := by
  obtain ⟨a, ha⟩ := planeX_mem_orbit i
  obtain ⟨b, hb⟩ := planeX_mem_orbit j
  have ha' : a • plane = planeX i := ha
  have hb' : b • plane = planeX j := hb
  refine ⟨b * a⁻¹, planeXAct_eq_iff.2 ?_⟩
  have h : (b * a⁻¹) • planeX i = planeX j := by
    rw [← ha', ← hb', ← mul_smul, inv_mul_cancel_right]
  exact h

theorem planeXAct_zero_eq_iff {q : ↥Q0} : planeXAct q 0 = 0 ↔ q ∈ D0.subgroupOf Q0 := by
  rw [planeXAct_eq_iff, planeX_zero, ← stabilizer_plane_eq, MulAction.mem_stabilizer_iff]
  rfl

noncomputable abbrev planeXMulAction : MulAction ↥Q0 (Fin 891) :=
  MulAction.compHom (Fin 891) planeXAct

theorem planeXMulAction_isPretransitive :
    @MulAction.IsPretransitive ↥Q0 (Fin 891) planeXMulAction.toSMul := by
  letI := planeXMulAction
  exact ⟨fun i j => exists_planeXAct_eq i j⟩

theorem stabilizer_planeXMulAction_zero :
    @MulAction.stabilizer ↥Q0 (Fin 891) _ planeXMulAction 0 = D0.subgroupOf Q0 := by
  ext q
  rw [@MulAction.mem_stabilizer_iff]
  exact planeXAct_zero_eq_iff

theorem planeXAct_planeGenQ {s : ℕ} (hs : s < 14) (i : Fin 891) :
    ((planeXAct (planeGenQ s) i : Fin 891) : ℕ) = ((planeTabs ())[s]!)[i.val]! := by
  have h : planeXAct (planeGenQ s) i =
      ⟨((planeTabs ())[s]!)[i.val]!, planeTabs_lt hs i.isLt⟩ := by
    rw [planeXAct_eq_iff, planeGenQ_val hs]
    exact gen_smul_planeX ⟨s, hs⟩ i
  exact congrArg Fin.val h

theorem planeDTabs_getElem_eq {s : ℕ} (hs : s < 13) (i : Fin 891) :
    ((planeDTabs ())[s]!)[i.val]! = ((planeXAct (planeGenQ s) i : Fin 891) : ℕ) := by
  rw [planeDTabs_getElem hs, planeXAct_planeGenQ (by omega) i]

theorem card_inter_planeXAct (q : ↥Q0) (a b : Fin 891) :
    (planeX (planeXAct q a) ∩ planeX (planeXAct q b)).card = (planeX a ∩ planeX b).card := by
  rw [← smul_planeX q a, ← smul_planeX q b, ← Finset.smul_finset_inter, Finset.card_smul_finset]

theorem planeInterCount_planeXAct (q : ↥Q0) (a b : Fin 891) :
    planeInterCount (planeXData ()) (planeXAct q a).val (planeXAct q b).val =
      planeInterCount (planeXData ()) a.val b.val := by
  rw [← card_planeX_inter, ← card_planeX_inter, card_inter_planeXAct]

theorem planeXAct_forall_eq_iff {q : ↥Q0} :
    (∀ i, planeXAct q i = i) ↔ ∀ i : Fin 891, (q : Q3) • planeX i = planeX i :=
  ⟨fun h i => planeXAct_eq_iff.1 (h i), fun h i => planeXAct_eq_iff.2 (h i)⟩

section Kernel

theorem mem_E0_of_planeXAct_fixes {q : ↥Q0} (h : ∀ i, planeXAct q i = i) : (q : Q3) ∈ E0 :=
  mem_E0_of_fix_planes q.2 (planeXAct_forall_eq_iff.1 h)

end Kernel

end Act

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
