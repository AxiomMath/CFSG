module

public import CFSG.LargeExtraspecial.S63AJ2CentAbs
public import CFSG.LargeExtraspecial.S8CBFCrit
public import CFSG.Sporadic.SmallOddCore.J2Local
public import CFSG.GH74.Generic.S45.LSporWit
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelCentralizers

public section

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Blueprint CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier (j2P j2PermEquiv)

namespace S63

section ModelB

open CFSG.ComponentClassification.J2Cover (P permA permTwoA inner_classes OrderFourClassSizes)

theorem fourClassesAtLeast_of_orderFourClassSizes {K : Subgroup (Equiv.Perm (Fin 315))}
    {sizes : List ℕ} (h : OrderFourClassSizes K sizes) (h20 : ∀ s ∈ sizes, 20 ≤ s) :
    FourClassesAtLeast 20 K := by
  obtain ⟨reps, -, hcov, -, hsz⟩ := h
  intro x hx4
  obtain ⟨r, hr, c, hc, hxc⟩ := hcov x x.2 (by rw [Subgroup.orderOf_coe, hx4])
  rw [ComponentClassification.M12Cover.card_conj_eq_ncard, hxc,
    ComponentClassification.M12Cover.conjClass_conj _ hc]
  exact h20 _ (hsz ▸ List.mem_map.2 ⟨r, hr, rfl⟩)

theorem fourClassesAtLeast_P {v : Equiv.Perm (Fin 315)} (hv : v ∈ P) (h2 : orderOf v = 2) :
    FourClassesAtLeast 20 (Sporadic.Schreier.centralizerIn P v) := by
  obtain ⟨r, hr, c, hc, rfl⟩ := inner_classes.1 v hv h2
  refine FourClassesAtLeast.of_mulEquiv
    (ComponentClassification.M12Cover.centralizerInConjEquiv P hc r).symm ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact fourClassesAtLeast_of_orderFourClassSizes
      ComponentClassification.J2Cover.Kernel.centralizerIn_P_permA.2.2 (by simp)
  · exact fourClassesAtLeast_of_orderFourClassSizes
      ComponentClassification.J2Cover.Kernel.centralizerIn_P_permTwoA.2.2 (by simp)

theorem fourClassesAtLeast_j2P {τ : Equiv.Perm (Fin 315)} (hτ : τ ∈ j2P) (h2 : orderOf τ = 2) :
    FourClassesAtLeast 20 ↥(j2P ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 315)))) := by
  let φ : j2P ≃* P := j2PermEquiv.symm.trans ComponentClassification.J2Cover.nativeEquivP
  let t : j2P := ⟨τ, hτ⟩
  have hv2 : orderOf ((φ t : P) : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, h2]
  have e : ↥(Sporadic.Schreier.centralizerIn j2P τ) ≃*
      ↥(Sporadic.Schreier.centralizerIn P ((φ t : P) : Equiv.Perm (Fin 315))) :=
    (ComponentClassification.M12Cover.centralizerSubgroupEquiv j2P t).symm.trans
      ((ComponentClassification.M12Cover.centralizerEquiv φ t).trans
        (ComponentClassification.M12Cover.centralizerSubgroupEquiv P (φ t)))
  exact FourClassesAtLeast.of_mulEquiv e (fourClassesAtLeast_P (φ t).2 hv2)

end ModelB

section ModelA

theorem centConcl_j2_t₁ :
    CentConcl (j2P ⊓ centralizer ({tp 315 (j2CentTbl 17)} : Set (Equiv.Perm (Fin 315))))
      (tp 315 (j2CentTbl 17)) := by
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨hDcard, hDC1, hC1D, hDsimple, hC1cent⟩ := j2_D_facts
  have hr := hrows _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hC1 : genOf 315 j2C1Gens = j2P ⊓ centralizer ({tp 315 (j2CentTbl 17)} : Set _) := by
    have h := hr.2.2.2.1
    dsimp only [Sporadic.SmallOddCore.j2C] at h
    rw [genOf, j2C1Gens]
    exact h
  rw [← hC1]
  intro N hNC hNn hN2 _ hN16
  exact (false_of_twoB hDC1 hC1D hDsimple hDcard hC1cent hNC hNn hN2 hN16).elim

theorem centConcl_j2_t₂ :
    CentConcl (j2P ⊓ centralizer ({tp 315 (j2CentTbl 31)} : Set (Equiv.Perm (Fin 315))))
      (tp 315 (j2CentTbl 31)) := by
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨hQcard, hQC2, hC2Q, hC2cent⟩ := j2_Q_facts
  have hmem : _ ∈ j2Rows := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hr := hrows _ hmem
  have hC2 : genOf 315 j2C2Gens = j2P ⊓ centralizer ({tp 315 (j2CentTbl 31)} : Set _) := by
    have h := hr.2.2.2.1
    dsimp only [Sporadic.SmallOddCore.j2C] at h
    rw [genOf, j2C2Gens]
    exact h
  have hcard : Nat.card ↥(j2P ⊓ centralizer ({tp 315 (j2CentTbl 31)} : Set _)) = 1920 := by
    have h := hr.2.2.2.2.1
    dsimp only at h
    exact h
  have ht2 : orderOf (tp 315 (j2CentTbl 31)) = 2 := by
    have h := hr.2.1
    dsimp only at h
    exact h
  have htP : tp 315 (j2CentTbl 31) ∈ j2P := by
    have h := hr.2.2.1
    dsimp only at h
    simpa using h
  have hperf : ⁅genOf 315 j2C2Gens, genOf 315 j2C2Gens⁆ = genOf 315 j2C2Gens :=
    (GH74.Generic.S45.perfWitOK_spec (by norm_num)
      (GH74.Generic.S45.perfWit_of_all GH74.Generic.S45.perfWit_j2_2A _ hmem rfl)).1
  have hfour := fourClassesAtLeast_j2P htP ht2
  have htC : tp 315 (j2CentTbl 31) ∈ j2P ⊓ centralizer ({tp 315 (j2CentTbl 31)} : Set _) :=
    mem_inf.mpr ⟨htP, mem_centralizer_singleton_iff.mpr rfl⟩
  rw [← hC2] at hcard hfour htC ⊢
  have hCt : genOf 315 j2C2Gens ≤ centralizer ({tp 315 (j2CentTbl 31)} : Set _) :=
    hC2 ▸ inf_le_right
  exact centConcl_of_twoA htC hCt ht2 hcard hperf hQC2 hC2Q hQcard
    (IsPGroup.of_card (n := 5) (by rw [hQcard]; norm_num)) hC2cent hfour

theorem centConcl_j2P {τ : Equiv.Perm (Fin 315)} (hτP : τ ∈ j2P) (hτ : orderOf τ = 2) :
    CentConcl (j2P ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 315)))) τ := by
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨r, hr, g, hg, rfl⟩ := hcover τ (j2P_le_j2R hτP) hτ
  have htrP : tp 315 r.rep ∈ j2P := by
    have := j2P.mul_mem (j2P.mul_mem (j2P.inv_mem hg) hτP) hg
    rwa [show g⁻¹ * (g * tp 315 r.rep * g⁻¹) * g = tp 315 r.rep by group] at this
  have hrows' := hrows
  rw [S8.inf_centralizer_conj_eq_map j2P hg]
  simp only [j2Rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have := (hrows' _ List.mem_cons_self).2.2.1
    exact absurd htrP (this.1 rfl)
  · dsimp only
    exact centConcl_j2_t₁.conj g
  · dsimp only
    exact centConcl_j2_t₂.conj g

end ModelA

end S63

end CFSG.LargeExtraspecial
