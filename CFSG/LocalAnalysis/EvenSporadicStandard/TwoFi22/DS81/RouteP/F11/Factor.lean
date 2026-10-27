module

public import Mathlib.Algebra.Group.Subgroup.Map
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F11.Rigid

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

theorem exists_conj_of_aut_inf {G : Type*} [Group G] {L N : Subgroup G} {K T : Subgroup ↥N}
    (hK : (L ⊓ N).subgroupOf N = K)
    (hKT : ∀ γ' : ↥K ≃* ↥K,
      ∃ c ∈ T, ∀ b : ↥K, ((γ' b : ↥K) : ↥N) = c * (b : ↥N) * c⁻¹)
    (γ : ↥(L ⊓ N) ≃* ↥(L ⊓ N)) :
    ∃ c ∈ T, ∀ b : ↥(L ⊓ N),
      ((γ b : ↥(L ⊓ N)) : G) = ((c : ↥N) : G) * (b : G) * ((c : ↥N) : G)⁻¹ := by
  let e : ↥K ≃* ↥(L ⊓ N) :=
    (MulEquiv.subgroupCongr hK).symm.trans (Subgroup.subgroupOfEquivOfLe inf_le_right)
  have he_coe : ∀ x : ↥K, ((e x : ↥(L ⊓ N)) : G) = (((x : ↥K) : ↥N) : G) := fun _ => rfl
  let γ' : ↥K ≃* ↥K := (e.trans γ).trans e.symm
  obtain ⟨c, hcT, hc⟩ := hKT γ'
  refine ⟨c, hcT, fun b => ?_⟩
  let b' : ↥K := e.symm b
  have hb' : e b' = b := e.apply_symm_apply b
  have hb'_coe : (((b' : ↥K) : ↥N) : G) = (b : G) := by
    rw [← he_coe b', hb']
  have hstep : γ' b' = e.symm (γ b) := congrArg (fun z => e.symm (γ z)) hb'
  calc
    ((γ b : ↥(L ⊓ N)) : G)
        = ((e (e.symm (γ b)) : ↥(L ⊓ N)) : G) := by rw [MulEquiv.apply_symm_apply]
    _ = (((e.symm (γ b) : ↥K) : ↥N) : G) := he_coe _
    _ = (((γ' b' : ↥K) : ↥N) : G) := by rw [hstep]
    _ = (((c * (b' : ↥N) * c⁻¹ : ↥N) : G)) := by rw [hc b']
    _ = ((c : ↥N) : G) * (b : G) * (((c : ↥N) : G))⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hb'_coe]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
