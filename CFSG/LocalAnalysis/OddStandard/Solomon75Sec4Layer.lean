module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Cent

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

namespace AhatData

variable {n : ℕ} {K : Type} [Group K]

theorem CoverSetup.Induces.component_map_le_altFix [Finite K] {C : CoverSetup n K}
    {α : MulAut K} {k : ℕ} {hk : 2 * k ≤ n} (h : C.Induces α (stdInv n k hk))
    {Q : Subgroup ↥(fixSub α)} (hQ : IsComponent Q) :
    (Q.map (fixSub α).subtype).map C.ρ ≤ altFix n k hk := by
  classical
  let ρX : ↥(fixSub α) →* Perm (Fin n) := C.ρ.comp (fixSub α).subtype
  have hρXσ : ∀ x : ↥(fixSub α), ρX x * stdInv n k hk = stdInv n k hk * ρX x := fun x =>
    h.ρ_comm_of_mem_fixSub x.2
  let Y : Subgroup ↥(fixSub α) := (invSwapGrp (stdInv n k hk) stdInv_mul_self).comap ρX
  have hYn : Y.Normal := by
    refine ⟨fun y hy x => ?_⟩
    rw [Subgroup.mem_comap] at hy ⊢
    rw [map_mul, map_mul, map_inv]
    exact invSwapGrp_conj_mem stdInv_mul_self (hρXσ x) hy
  have hYp : IsPGroup 2 ↥Y := by
    intro y
    refine ⟨2, ?_⟩
    have h1 : ρX y * ρX y = 1 := invSwapGrp_mul_self stdInv_mul_self y.2
    have h2 : C.ρ (((y : ↥(fixSub α)) : K)) * C.ρ (((y : ↥(fixSub α)) : K)) = 1 := h1
    have h3 : ((y : ↥(fixSub α)) : K) * ((y : ↥(fixSub α)) : K) ∈ center K := C.sq_mem_center h2
    have h4 := C.sq_of_mem_center h3
    apply Subtype.ext
    apply Subtype.ext
    show ((y : ↥(fixSub α)) : K) ^ 2 ^ 2 = 1
    calc ((y : ↥(fixSub α)) : K) ^ 2 ^ 2 = (((y : ↥(fixSub α)) : K) * ((y : ↥(fixSub α)) : K)) *
          (((y : ↥(fixSub α)) : K) * ((y : ↥(fixSub α)) : K)) := by simp [pow_succ, mul_assoc]
      _ = 1 := h4
  have hYs : Group.IsSolvable ↥Y := by
    have : Group.IsNilpotent ↥Y := hYp.isNilpotent
    infer_instance
  have hQY : ⁅Q, Y⁆ = ⊥ :=
    (CFSG.LocalCores.component_solvable_centralizer hYs hYn.isSubnormal).1 Q hQ
  have hPeq : (Q.map (fixSub α).subtype).map C.ρ = Q.map ρX := by
    rw [Subgroup.map_map]
  have hσ' : ∀ g ∈ Q.map ρX, g * stdInv n k hk = stdInv n k hk * g := by
    intro g hg
    obtain ⟨q, -, rfl⟩ := hg
    exact hρXσ q
  have hδ : ∀ g ∈ Q.map ρX, ∀ i l : Fin k, i ≠ l →
      g * dblPair n k hk i l = dblPair n k hk i l * g := by
    intro g hg i l hil
    obtain ⟨q, hq, rfl⟩ := hg
    obtain ⟨x, hxX, hxρ⟩ := h.exists_dblPair_mem_fixSub i l hil
    have hxρ' : ρX ⟨x, hxX⟩ = dblPair n k hk i l := hxρ
    have hxY : (⟨x, hxX⟩ : ↥(fixSub α)) ∈ Y := by
      rw [Subgroup.mem_comap, hxρ']
      exact dblPair_mem_invSwapGrp i l
    have hc : ⁅q, (⟨x, hxX⟩ : ↥(fixSub α))⁆ ∈ ⁅Q, Y⁆ :=
      Subgroup.commutator_mem_commutator hq hxY
    rw [hQY, Subgroup.mem_bot] at hc
    have := congrArg ρX (commutatorElement_eq_one_iff_mul_comm.1 hc)
    simp only [map_mul] at this
    rw [hxρ'] at this
    exact this
  have hQperf : ⁅Q, Q⁆ = Q := Subgroup.isPerfect_iff.1 hQ.1.1
  have hPperf : ⁅Q.map ρX, Q.map ρX⁆ = Q.map ρX := by
    rw [← Subgroup.map_commutator, hQperf]
  rw [hPeq]
  by_cases hk3 : 3 ≤ k
  · exact perfect_le_altFix_of_preserves hPperf (fun g hg i j =>
      preserves_pairs_of_comm_dbl hk3 (hσ' g hg) (hδ g hg) i j)
  · exact perfect_le_altFix_of_small (by omega) hPperf hσ'

theorem CoverSetup.Induces.fixedComp_conj_mem {C : CoverSetup n K} {α : MulAut K} {k : ℕ}
    {hk : 2 * k ≤ n} (h : C.Induces α (stdInv n k hk)) {x : K} (hx : x ∈ fixSub α) {l : K}
    (hl : l ∈ C.fixedComp k hk) : x * l * x⁻¹ ∈ C.fixedComp k hk := by
  have hE : ((altFix n k hk).comap C.ρ).map (MulAut.conj x).toMonoidHom ≤
      (altFix n k hk).comap C.ρ := by
    rintro _ ⟨e, he, rfl⟩
    have he' : C.ρ e ∈ altFix n k hk := he
    rw [Subgroup.mem_comap]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
    exact altFix_conj_mem (h.ρ_comm_of_mem_fixSub hx) he'
  have h1 : (C.fixedComp k hk).map (MulAut.conj x).toMonoidHom ≤ C.fixedComp k hk := by
    unfold CoverSetup.fixedComp
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hE hE
  exact h1 ⟨l, hl, by simp [MulAut.conj_apply]⟩

theorem CoverSetup.Induces.layer_fixSub_map_eq [Finite K] (C : CoverSetup n K) (hn : 8 ≤ n)
    {α : MulAut K} {k : ℕ} {hk : 2 * k ≤ n} (h : C.Induces α (stdInv n k hk))
    (hm : 5 ≤ n - 2 * k) :
    (layer ↥(fixSub α)).map (fixSub α).subtype = C.fixedComp k hk := by
  obtain ⟨hLX, hLdc, hLmap⟩ := h.fixedComp_isDoubleCover C hn hm
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun Q hQ => ?_
    have hQ' := h.component_map_le_altFix hQ
    set Q' := Q.map (fixSub α).subtype with hQ'def
    have hQE : Q' ≤ (altFix n k hk).comap C.ρ := fun x hx =>
      Subgroup.mem_comap.2 (hQ' ⟨x, hx, rfl⟩)
    have hQperf : ⁅Q, Q⁆ = Q := Subgroup.isPerfect_iff.1 hQ.1.1
    have hQ'perf : ⁅Q', Q'⁆ = Q' := by
      rw [hQ'def, ← Subgroup.map_commutator, hQperf]
    have hle : Q' ≤ C.fixedComp k hk := by
      calc Q' = ⁅Q', Q'⁆ := hQ'perf.symm
        _ ≤ C.fixedComp k hk := Subgroup.commutator_mono hQE hQE
    intro q hq
    exact hle ⟨q, hq, rfl⟩
  ·
    have hcomp : IsComponent ((C.fixedComp k hk).subgroupOf (fixSub α)) := by
      refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hLX).symm hLdc.1, ?_⟩
      refine Subgroup.Normal.isSubnormal ?_
      refine ⟨fun a ha g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      exact h.fixedComp_conj_mem g.2 ha
    have hle : (C.fixedComp k hk).subgroupOf (fixSub α) ≤ layer ↥(fixSub α) :=
      le_sSup hcomp
    calc C.fixedComp k hk = ((C.fixedComp k hk).subgroupOf (fixSub α)).map (fixSub α).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hLX).symm
      _ ≤ (layer ↥(fixSub α)).map (fixSub α).subtype := Subgroup.map_mono hle

end AhatData

end CFSG.OddStandard.Solomon75
