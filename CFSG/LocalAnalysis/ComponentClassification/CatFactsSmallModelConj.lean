module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallModel

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG.GH74.KGroups Subgroup

variable {K G : Type*} [Group K] [Group G]

theorem conj_mem_P_of_mem_A (M : AutModel K G) {k : G} (hk : k ∈ M.A) {x : G} (hx : x ∈ M.P) :
    k * x * k⁻¹ ∈ M.P := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MulAut K, (M.Φ ψ : G) = k := ⟨M.Φ.symm ⟨k, hk⟩, by simp⟩
  obtain ⟨l, rfl⟩ : ∃ l, modelEmb M l = x := ⟨M.e.symm ⟨x, hx⟩, modelEmb_symm M x hx⟩
  rw [← hψ, modelEmb_apply, ← M.spec ψ l]
  exact (M.e (ψ l)).2

@[expose] def subgroupConj (H : Subgroup G) (k : G) (h : ∀ x ∈ H, k * x * k⁻¹ ∈ H)
    (h' : ∀ x ∈ H, k⁻¹ * x * k ∈ H) : H ≃* H where
  toFun x := ⟨k * x * k⁻¹, h x x.2⟩
  invFun x := ⟨k⁻¹ * x * k, h' x x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem subgroupConj_apply (H : Subgroup G) (k : G) (h h') (x : H) :
    ((subgroupConj H k h h' x : H) : G) = k * x * k⁻¹ := rfl

@[expose] def conjModel (M : AutModel K G) (k : G) (hk : k ∈ M.A) : AutModel K G where
  P := M.P
  A := M.A
  e := M.e.trans (subgroupConj M.P k (fun _ hx => conj_mem_P_of_mem_A M hk hx)
    (fun x hx => by simpa using conj_mem_P_of_mem_A M (M.A.inv_mem hk) hx))
  Φ := M.Φ.trans (subgroupConj M.A k (fun x hx => M.A.mul_mem (M.A.mul_mem hk hx)
    (M.A.inv_mem hk)) (fun x hx => M.A.mul_mem (M.A.mul_mem (M.A.inv_mem hk) hx) hk))
  spec := by
    intro φ x
    simp only [MulEquiv.trans_apply, subgroupConj_apply]
    rw [M.spec φ x]
    group

theorem conjModel_P (M : AutModel K G) (k : G) (hk : k ∈ M.A) : (conjModel M k hk).P = M.P :=
  rfl

theorem conjModel_A (M : AutModel K G) (k : G) (hk : k ∈ M.A) : (conjModel M k hk).A = M.A :=
  rfl

theorem conjModel_Φ (M : AutModel K G) (k : G) (hk : k ∈ M.A) (θ : MulAut K) :
    ((conjModel M k hk).Φ θ : G) = k * (M.Φ θ : G) * k⁻¹ := rfl

theorem conjModel_e (M : AutModel K G) (k : G) (hk : k ∈ M.A) (x : K) :
    ((conjModel M k hk).e x : G) = k * (M.e x : G) * k⁻¹ := rfl

theorem exists_model_eq (M : AutModel K G) (θ : MulAut K) {σ₀ k : G} (hk : k ∈ M.A)
    (h : k⁻¹ * (M.Φ θ : G) * k = σ₀) :
    ∃ M' : AutModel K G, M'.P = M.P ∧ M'.A = M.A ∧ (M'.Φ θ : G) = σ₀ := by
  refine ⟨conjModel M k⁻¹ (M.A.inv_mem hk), rfl, rfl, ?_⟩
  rw [conjModel_Φ, inv_inv, h]

end CFSG.ComponentClassification.CatFactsSmall
