module

public import CFSG.ClassicalInvolution.Solomon73.YamakiAmalgam
public import CFSG.ClassicalInvolution.Solomon73.YamakiRelations
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.Open

theorem lieModel_psp_three_two_of_mulEquiv {G : Type} [Group G]
    (e : G ≃* StatedSp 3 (ZMod 2)) : CFSG.Blueprint.LieModel G .PSp 3 2 1 :=
  Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, ZMod 2, inferInstance,
    inferInstance, by simp,
    ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq
      StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot).trans QuotientGroup.quotientBot).symm⟩⟩


theorem nonempty_mulEquiv_of_amalgam {G : Type*} [Group G] {N H : Subgroup G}
    (ν : ↥N ≃* ↥N0) (θ : ↥H ≃* ↥Hhat)
    (hνX : ∀ x (hx : x ∈ N), x ∈ H ↔ (ν ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0)
    (hθX : ∀ x (hx : x ∈ H), x ∈ N ↔ (θ ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0)
    (hrig : ¬ IsConj ((θ.symm ⟨pi12, S0_le_Hhat pi12_mem_S0⟩ : ↥H) : G)
      ((θ.symm ⟨pi3, S0_le_Hhat pi3_mem_S0⟩ : ↥H) : G))
    (hC : Subgroup.centralizer {((θ.symm ⟨alpha, S0_le_Hhat alpha_mem_S0⟩ : ↥H) : G)} ≤ H)
    (hgen : N ⊔ H = ⊤) : Nonempty (G ≃* StatedSp 3 (ZMod 2)) := by
  obtain ⟨ν', θ', hagree, hνX', -, hα⟩ := exists_compat_of_rigid ν θ hνX hθX hrig
  have hC' : Subgroup.centralizer
      {((θ'.symm ⟨alpha, S0_le_Hhat alpha_mem_S0⟩ : ↥H) : G)} ≤ H := by
    rw [hα]
    exact hC
  obtain ⟨f, -⟩ := exists_mulEquiv_sup (ν := ν') (θ := θ') hagree
    (fun x hx h => (hνX' x hx).mpr h) hC'
  exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hgen.symm)).trans f⟩

theorem lieModel_of_amalgam {G : Type} [Group G] {N H : Subgroup G}
    (ν : ↥N ≃* ↥N0) (θ : ↥H ≃* ↥Hhat)
    (hνX : ∀ x (hx : x ∈ N), x ∈ H ↔ (ν ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0)
    (hθX : ∀ x (hx : x ∈ H), x ∈ N ↔ (θ ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0)
    (hrig : ¬ IsConj ((θ.symm ⟨pi12, S0_le_Hhat pi12_mem_S0⟩ : ↥H) : G)
      ((θ.symm ⟨pi3, S0_le_Hhat pi3_mem_S0⟩ : ↥H) : G))
    (hC : Subgroup.centralizer {((θ.symm ⟨alpha, S0_le_Hhat alpha_mem_S0⟩ : ↥H) : G)} ≤ H)
    (hgen : N ⊔ H = ⊤) : CFSG.Blueprint.LieModel G .PSp 3 2 1 :=
  let ⟨e⟩ := nonempty_mulEquiv_of_amalgam ν θ hνX hθX hrig hC hgen
  lieModel_psp_three_two_of_mulEquiv e

end CFSG.ClassicalInvolution.Sp62Rec
