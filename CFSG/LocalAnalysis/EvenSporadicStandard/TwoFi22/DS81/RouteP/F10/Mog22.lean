module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10.Assemble
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10.H1Mog22
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10.EndMog22
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.Twist
public import CFSG.Milestones.ASVolI.H13

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Monster.Code CFSG.Monster.B.TwoA CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Code22

@[expose] def duadStabPlus (i j : Fin 24) : Subgroup ↥AutPerm where
  carrier := {σ | (((σ : ↥AutPerm) : Equiv.Perm (Fin 24)) i = i ∧
      ((σ : ↥AutPerm) : Equiv.Perm (Fin 24)) j = j) ∨
    (((σ : ↥AutPerm) : Equiv.Perm (Fin 24)) i = j ∧
      ((σ : ↥AutPerm) : Equiv.Perm (Fin 24)) j = i)}
  mul_mem' {σ τ} hσ hτ := by
    simp only [Set.mem_ofPred_eq, Subgroup.coe_mul, Equiv.Perm.mul_apply] at hσ hτ ⊢
    rcases hτ with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1] <;> tauto
  one_mem' := Or.inl ⟨rfl, rfl⟩
  inv_mem' {σ} hσ := by
    simp only [Set.mem_ofPred_eq, Subgroup.coe_inv] at hσ ⊢
    rcases hσ with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · left
      exact ⟨by rw [Equiv.Perm.inv_eq_iff_eq, h0], by rw [Equiv.Perm.inv_eq_iff_eq, h1]⟩
    · right
      exact ⟨by rw [Equiv.Perm.inv_eq_iff_eq, h1], by rw [Equiv.Perm.inv_eq_iff_eq, h0]⟩

theorem mem_duadStabPlus_iff {i j : Fin 24} {σ : ↥AutPerm} :
    σ ∈ duadStabPlus i j ↔
      (((σ : Equiv.Perm (Fin 24)) i = i ∧ (σ : Equiv.Perm (Fin 24)) j = j) ∨
        ((σ : Equiv.Perm (Fin 24)) i = j ∧ (σ : Equiv.Perm (Fin 24)) j = i)) := Iff.rfl

theorem conj_mem_duadStabPlus_iff {τ : ↥AutPerm} {i j : Fin 24}
    (hτ0 : (τ : Equiv.Perm (Fin 24)) 0 = i) (hτ1 : (τ : Equiv.Perm (Fin 24)) 1 = j)
    (σ : ↥AutPerm) :
    τ⁻¹ * σ * τ ∈ duadStabPlus 0 1 ↔ σ ∈ duadStabPlus i j := by
  rw [mem_duadStabPlus_iff, mem_duadStabPlus_iff]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, hτ0, hτ1,
    Equiv.Perm.inv_eq_iff_eq]

@[expose] def eK22 : ↥K22 ≃* ↥mog22 := Subgroup.subgroupOfEquivOfLe mog22_le_autPerm

theorem rho11_comp_K22 (q : ↥K22) :
    ((rho11 AutPerm le_rfl).comp K22.subtype) q = rho11 mog22 mog22_le_autPerm (eK22 q) := rfl

theorem isSimpleGroup_K22 :
    IsSimpleGroup ↥K22 := by
  haveI := isSimpleGroup_mog22
  exact eK22.isSimpleGroup

theorem K22_nonabelian : ∃ a b : ↥K22, a * b ≠ b * a := by
  refine ⟨eK22.symm ⟨mogA, mogA_mem22⟩, eK22.symm ⟨mogB, mogB_mem22⟩, fun h => ?_⟩
  have h1 := congrArg (fun q : ↥K22 => ((eK22 q : ↥mog22) : Equiv.Perm (Fin 24))) h
  simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h1
  have h2 : (mogA * mogB) 2 = (mogB * mogA) 2 := congrArg (fun σ : Equiv.Perm (Fin 24) => σ 2) h1
  revert h2
  decide

theorem modH1Trivial_K22 :
    ModH1Trivial ((rho11 AutPerm le_rfl).comp K22.subtype) := by
  intro f hf
  obtain ⟨w, hw⟩ := h1_mog22 (fun g => f (eK22.symm g)) (fun g h => by
    have := hf (eK22.symm g) (eK22.symm h)
    rw [map_mul, this]
    rfl)
  refine ⟨w, fun q => ?_⟩
  have := hw (eK22 q)
  rw [MulEquiv.symm_apply_apply] at this
  exact this

theorem modEquivAutTrivial_K22 :
    ModEquivAutTrivial ((rho11 AutPerm le_rfl).comp K22.subtype) := by
  intro ψ hψ
  refine equivAut_mog22 ψ fun g w => ?_
  have := hψ (eK22.symm g) w
  exact this

theorem exists_conj_of_aut_K22_aux
    (α : ↥K22 ≃* ↥K22) :
    ∃ k' ∈ duadStabPlus 0 1, ∀ q : ↥K22,
      (((α q : ↥K22) : ↥AutPerm) : Equiv.Perm (Fin 24)) =
        (k' : Equiv.Perm (Fin 24)) * ((q : ↥AutPerm) : Equiv.Perm (Fin 24)) *
          (k' : Equiv.Perm (Fin 24))⁻¹ := by
  obtain ⟨g, hg⟩ := CFSG.ASVolI.conjHom22_bijective.2 (eK22.symm.trans (α.trans eK22))
  refine ⟨⟨(g : Equiv.Perm (Fin 24)), g.2.1⟩, g.2.2, fun q => ?_⟩
  have h1 := congrArg (fun f : ↥mog22 ≃* ↥mog22 => ((f (eK22 q) : ↥mog22) : Equiv.Perm (Fin 24))) hg
  exact h1.symm

namespace ExtData

variable {N : Type*} [Group N]

theorem exists_conj_of_aut_K22
    (X : ExtData (rho11 AutPerm le_rfl) N) {B : Subgroup N} (hB : ∀ n, n ∈ B ↔ X.π n ∈ K22)
    (γ : ↥B ≃* ↥B) :
    ∃ c : N, X.π c ∈ duadStabPlus 0 1 ∧ ∀ b : ↥B, ((γ b : ↥B) : N) = c * (b : N) * c⁻¹ := by
  haveI := isSimpleGroup_K22
  exact X.exists_conj_of_aut_preimage hB K22_nonabelian modH1Trivial_K22 modEquivAutTrivial_K22
    (fun α => by
      obtain ⟨k', hk', hq⟩ := exists_conj_of_aut_K22_aux α
      exact ⟨k', hk', fun q => Subtype.ext (hq q)⟩) γ

theorem exists_conj_of_aut_duad
    (X : ExtData (rho11 AutPerm le_rfl) N) {i j : Fin 24} (hij : i ≠ j) {B : Subgroup N}
    (hB : ∀ n, n ∈ B ↔ ((X.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) i = i ∧
      ((X.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) j = j)
    (γ : ↥B ≃* ↥B) :
    ∃ c : N, X.π c ∈ duadStabPlus i j ∧ ∀ b : ↥B, ((γ b : ↥B) : N) = c * (b : N) * c⁻¹ := by
  obtain ⟨τ, hτ, hτ0, hτ1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two i j hij
  let t : ↥AutPerm := ⟨τ, hτ⟩
  have hB' : ∀ n, n ∈ B ↔ (X.twist t).π n ∈ K22 := fun n =>
    (hB n).trans (conj_mem_K22_iff hτ0 hτ1 (X.π n)).symm
  obtain ⟨c, hc, hγ⟩ := (X.twist t).exists_conj_of_aut_K22 hB' γ
  exact ⟨c, (conj_mem_duadStabPlus_iff hτ0 hτ1 (X.π c)).1 hc, hγ⟩

end ExtData

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
