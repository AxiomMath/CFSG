module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.Defs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellJ.ThmB

public section

namespace CFSG.QuasithinUnique.Setup.CampbellJ

open CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type*} [Group G] [Finite G] {k : Type*} [Field k] [Finite k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

private theorem WJ_eq_iSup_Six1 (S : Sylow 2 G)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G))) :
    WJ S α = ⨆ u : ↥(Hone S),
      cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) (u : G) := by
  unfold WJ
  exact (iSup_subtype'' (Hone S : Set G)
    (fun u => cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) u)).symm

private theorem WJ_le_thompsonJ_core_Six1 (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G) :
    WJ S α ≤ CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) := by
  unfold WJ
  refine iSup_le fun u => iSup_le fun _ => ?_
  calc cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) u
      ≤ cj (CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G)) u :=
        cj_mono (aimgJ_Fcore_le_thompsonJ_core h α hV)
    _ = CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) := cj_eq_self_of_normal

private theorem WJ_normalized_Six1 (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G) :
    ∀ u ∈ Hone S, ∀ w ∈ WJ S α, u * w * u⁻¹ ∈ WJ S α := by
  have hFaH : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≤ Hone S :=
    (aimgJ_Fcore_le_thompsonJ_core h α hV).trans
      (h.thompsonJ_core_le_thompsonJ_sylow.trans Subgroup.le_normalClosure)
  intro u hu w hw
  rw [WJ_eq_iSup_Six1] at hw ⊢
  refine Subgroup.iSup_induction (fun v : ↥(Hone S) =>
    cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) (v : G))
    (C := fun w => u * w * u⁻¹ ∈ ⨆ v : ↥(Hone S),
      cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) (v : G)) hw ?_ ?_ ?_
  · intro v x hx
    rw [mem_cj] at hx
    refine Subgroup.mem_iSup_of_mem
      ⟨(v : G) * u⁻¹, (Hone S).mul_mem v.2 ((Hone S).inv_mem hu)⟩ (mem_cj.mpr ?_)
    have hx' : ((v : G) * u⁻¹) * (u * x * u⁻¹) * ((v : G) * u⁻¹)⁻¹ =
        (v : G) * x * (v : G)⁻¹ := by group
    rw [hx']
    exact hx
  · simp
  · intro a b ha hb
    have e : u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha hb

private theorem WJ_Zfix_cj_Six1 (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G) :
    ∀ u ∈ Hone S,
      cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S)) u =
        aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := by
  have hZ := aimgJ_Zfix_le_center_Hone h α hV hF
  intro u hu
  apply cj_eq_of_forall_mem
  intro z hz
  have hcomm : u * z = z * u := Subgroup.mem_centralizer_iff.mp (hZ hz).2 u hu
  have : u * z * u⁻¹ = z := by rw [hcomm]; group
  rwa [this]

private theorem WJ_Zfix_normal_Six1 (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G) :
    ∀ n ∈ Hone S, ∀ v ∈ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S),
      n * v * n⁻¹ ∈ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := by
  have hZ := aimgJ_Zfix_le_center_Hone h α hV hF
  intro n hn v hv
  have hcomm : n * v = v * n := Subgroup.mem_centralizer_iff.mp (hZ hv).2 n hn
  have : n * v * n⁻¹ = v := by rw [hcomm]; group
  rwa [this]

private theorem WJ_Fa_commutator_le_Six1 (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G) :
    ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G), WJ S α⁆ ≤
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := by
  have hWT : WJ S α ≤ CFSG.Quasithin.thompsonJ (S : Subgroup G) :=
    (WJ_le_thompsonJ_core_Six1 h α hV).trans h.thompsonJ_core_le_thompsonJ_sylow
  calc ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G), WJ S α⁆
      ≤ ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G),
          CFSG.Quasithin.thompsonJ (S : Subgroup G)⁆ :=
        Subgroup.commutator_mono le_rfl hWT
    _ = ⁅CFSG.Quasithin.thompsonJ (S : Subgroup G),
          aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)⁆ :=
        Subgroup.commutator_comm _ _
    _ = aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) :=
        commutator_thompsonJ_aimgJ_Fcore h α

private theorem WJ_cj_Fa_commutator_le_Six1 (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G) :
    ∀ u ∈ Hone S,
      ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) u, WJ S α⁆ ≤
        aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := by
  intro u hu
  have hWu : cj (WJ S α) u = WJ S α :=
    cj_eq_of_forall_mem fun x hx => WJ_normalized_Six1 h α hV u hu x hx
  calc ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) u, WJ S α⁆
      = ⁅cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) u,
          cj (WJ S α) u⁆ := by rw [hWu]
    _ = cj ⁅aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G), WJ S α⁆ u :=
          cj_commutator.symm
    _ ≤ cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S)) u :=
          cj_mono (WJ_Fa_commutator_le_Six1 h α hV)
    _ = aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) :=
          WJ_Zfix_cj_Six1 h α hV hF u hu

private theorem WJ_commutator_inner_Six1 (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G) :
    ∀ u : G, ⁅WJ S α, ⨆ (_ : u ∈ Hone S),
      cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) u⁆ ≤
        aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := by
  have hFaH : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≤ Hone S :=
    (aimgJ_Fcore_le_thompsonJ_core h α hV).trans
      (h.thompsonJ_core_le_thompsonJ_sylow.trans Subgroup.le_normalClosure)
  intro u
  refine commutator_iSup_le (fun _ : u ∈ Hone S =>
    cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) u)
    (WJ_Zfix_normal_Six1 h α hV hF) (fun _ => ?_) (fun hu => ?_)
  · exact (cj_mono hFaH).trans (le_of_eq (cj_eq_self_of_normal (Y := Hone S) (g := u)))
  · have := WJ_cj_Fa_commutator_le_Six1 h α hV hF u hu
    rwa [Subgroup.commutator_comm] at this

private theorem WJ_commutator_le_Six1 (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G) :
    ⁅WJ S α, WJ S α⁆ ≤ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := by
  have hFaH : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≤ Hone S :=
    (aimgJ_Fcore_le_thompsonJ_core h α hV).trans
      (h.thompsonJ_core_le_thompsonJ_sylow.trans Subgroup.le_normalClosure)
  refine commutator_iSup_le (fun u : G => ⨆ (_ : u ∈ Hone S),
    cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) u)
    (WJ_Zfix_normal_Six1 h α hV hF) ?_ (WJ_commutator_inner_Six1 h α hV hF)
  intro u
  refine iSup_le fun _ => ?_
  exact (cj_mono hFaH).trans (le_of_eq (cj_eq_self_of_normal (Y := Hone S) (g := u)))

private theorem mul_sq_eq_Six1 {a b : G}
    (hc : b * (b⁻¹ * a⁻¹ * b * a) = (b⁻¹ * a⁻¹ * b * a) * b) :
    (a * b) ^ 2 = a ^ 2 * b ^ 2 * (b⁻¹ * a⁻¹ * b * a) := by
  have e1 : b * a = a * b * (b⁻¹ * a⁻¹ * b * a) := by group
  calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
    _ = a * (a * b * (b⁻¹ * a⁻¹ * b * a)) * b := by rw [e1]
    _ = a ^ 2 * (b * ((b⁻¹ * a⁻¹ * b * a) * b)) := by group
    _ = a ^ 2 * (b * (b * (b⁻¹ * a⁻¹ * b * a))) := by rw [← hc]
    _ = a ^ 2 * b ^ 2 * (b⁻¹ * a⁻¹ * b * a) := by group

private theorem WJ_sq_mem_Six1 (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G) :
    ∀ w ∈ WJ S α, w ^ 2 ∈ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := by
  have hWH : WJ S α ≤ Hone S :=
    ((WJ_le_thompsonJ_core_Six1 h α hV).trans h.thompsonJ_core_le_thompsonJ_sylow).trans
      Subgroup.le_normalClosure
  have hZ := aimgJ_Zfix_le_center_Hone h α hV hF
  have hWW := WJ_commutator_le_Six1 h α hV hF
  intro w hw
  have hw' : w ∈ ⨆ v : ↥(Hone S),
      cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) (v : G) := by
    simpa only [WJ_eq_iSup_Six1] using hw
  have key : w ∈ WJ S α ∧ w ^ 2 ∈
      aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := by
    refine Subgroup.iSup_induction (fun v : ↥(Hone S) =>
      cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) (v : G))
      (C := fun w => w ∈ WJ S α ∧ w ^ 2 ∈
        aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S)) hw' ?_ ?_ ?_
    · intro v x hx
      refine ⟨?_, ?_⟩
      · have : x ∈ ⨆ v : ↥(Hone S),
            cj (aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G)) (v : G) :=
          Subgroup.mem_iSup_of_mem v hx
        rwa [← WJ_eq_iSup_Six1] at this
      · have hel := isElemAbelian_cj (isElemAbelian_aimg α isElemAbelian_Fcore) (v : G)
        rw [(isElemAbelian_iff.mp hel).2 x hx]
        exact one_mem _
    · exact ⟨one_mem _, by simp⟩
    · rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
      refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
      have hcmem : b⁻¹ * a⁻¹ * b * a ∈
          aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) := by
        have := hWW (Subgroup.commutator_mem_commutator ((WJ S α).inv_mem hb)
          ((WJ S α).inv_mem ha))
        simpa [commutatorElement_def] using this
      have hcc : b * (b⁻¹ * a⁻¹ * b * a) = (b⁻¹ * a⁻¹ * b * a) * b :=
        Subgroup.mem_centralizer_iff.mp (hZ hcmem).2 b (hWH hb)
      rw [mul_sq_eq_Six1 hcc]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha2 hb2) hcmem
  exact key.2

theorem WJ_facts (h : IsSeed S ρ (Ecore G) ψ)
    (α : MulAut ↥(CFSG.Quasithin.thompsonJ (S : Subgroup G)))
    (hV : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Vmod G) ≤ CFSG.pCore 2 G)
    (hF : aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Fcore G) ≠ Fcore G) :
    WJ S α ≤ CFSG.Quasithin.thompsonJ (CFSG.pCore 2 G) ∧
    (∀ u ∈ Hone S, ∀ w ∈ WJ S α, u * w * u⁻¹ ∈ WJ S α) ∧
    ⁅WJ S α, WJ S α⁆ ≤ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) ∧
    ∀ w ∈ WJ S α, w ^ 2 ∈ aimg (CFSG.Quasithin.thompsonJ (S : Subgroup G)) α (Zfix S) :=
  ⟨WJ_le_thompsonJ_core_Six1 h α hV, WJ_normalized_Six1 h α hV,
    WJ_commutator_le_Six1 h α hV hF, WJ_sq_mem_Six1 h α hV hF⟩

end CFSG.QuasithinUnique.Setup.CampbellJ

end
