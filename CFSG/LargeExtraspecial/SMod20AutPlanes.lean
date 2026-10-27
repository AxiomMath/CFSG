module

public import CFSG.LargeExtraspecial.SMod20AutMbar
import CFSG.Fischer.F4

public section

namespace CFSG.LargeExtraspecial.SMod20.Aut

open CFSG.Fischer CFSG.F4.Native CFSG.SmithE Matrix Module

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec

theorem planePoints_injective
    {i j : ℕ} (hi : i < 891) (hj : j < 891) (h : planePoints i = planePoints j) : i = j := by
  apply planeSub_injective hi hj
  apply Submodule.eq_of_le_of_finrank_eq _ (by rw [finrank_planeSub hi, finrank_planeSub hj])
  rw [planeSub, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  have hk := planeVec_mem i k
  have hk0 : planeVec i k ≠ 0 := (planeVec_linearIndependent hi).ne_zero k
  have hki := hermStd_planeSub hi hk hk
  have hp : ptOf _ hk0 hki ∈ planePoints i := by
    rw [mem_planePoints]
    obtain ⟨c, hc, hcw⟩ := uVec_ptOf _ hk0 hki
    rw [hcw]
    exact (planeSub i).smul_mem c hk
  rw [h, mem_planePoints] at hp
  obtain ⟨c, hc, hcw⟩ := uVec_ptOf _ hk0 hki
  rw [hcw] at hp
  have := (planeSub j).smul_mem c⁻¹ hp
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

end CFSG.LargeExtraspecial.SMod20.Aut

namespace CFSG.LargeExtraspecial.SMod20

open CFSG.Fischer Aut

section Planes

theorem planes_unique {π : Equiv.Perm (Fin 693)} {i j j' : ℕ} (hj : j < 891) (hj' : j' < 891)
    (h : ∀ p : Fin 693, p ∈ planePoints i ↔ π p ∈ planePoints j)
    (h' : ∀ p : Fin 693, p ∈ planePoints i ↔ π p ∈ planePoints j') : j = j' := by
  apply planePoints_injective hj hj'
  ext q
  rw [← π.apply_symm_apply q, ← h, ← h']

@[expose] noncomputable def autPlaneFun (α : MulAut T46) (i : Fin 891) : Fin 891 :=
  ⟨Classical.choose (autPerm_planes α i.2), (Classical.choose_spec (autPerm_planes α i.2)).1⟩

theorem autPlaneFun_spec (α : MulAut T46) (i : Fin 891) (p : Fin 693) :
    p ∈ planePoints i ↔ autPerm α p ∈ planePoints (autPlaneFun α i) :=
  (Classical.choose_spec (autPerm_planes α i.2)).2 p

theorem autPlaneFun_eq {α : MulAut T46} {i j : Fin 891}
    (h : ∀ p : Fin 693, p ∈ planePoints i ↔ autPerm α p ∈ planePoints j) :
    autPlaneFun α i = j :=
  Fin.ext (planes_unique (autPlaneFun α i).2 j.2 (autPlaneFun_spec α i) h)

theorem autPlaneFun_mul (α β : MulAut T46) (i : Fin 891) :
    autPlaneFun (α * β) i = autPlaneFun α (autPlaneFun β i) := by
  apply autPlaneFun_eq
  intro p
  rw [map_mul, Equiv.Perm.mul_apply, autPlaneFun_spec β i, autPlaneFun_spec α]

theorem autPlaneFun_one (i : Fin 891) : autPlaneFun 1 i = i := by
  apply autPlaneFun_eq
  intro p
  rw [map_one, Equiv.Perm.one_apply]

@[expose] noncomputable def autPlane : MulAut T46 →* Equiv.Perm (Fin 891) where
  toFun α :=
    { toFun := autPlaneFun α
      invFun := autPlaneFun α⁻¹
      left_inv := fun i => by rw [← autPlaneFun_mul, inv_mul_cancel, autPlaneFun_one]
      right_inv := fun i => by rw [← autPlaneFun_mul, mul_inv_cancel, autPlaneFun_one] }
  map_one' := Equiv.ext autPlaneFun_one
  map_mul' α β := Equiv.ext (autPlaneFun_mul α β)

theorem autPlane_spec (α : MulAut T46) (i : Fin 891) (p : Fin 693) :
    p ∈ planePoints i ↔ autPerm α p ∈ planePoints (autPlane α i) :=
  autPlaneFun_spec α i p

theorem autPerm_mem_UAloc_of_commute {i : ℕ} (hi : i < 891) (α : MulAut T46)
    (h : ∀ u ∈ UAloc i, autPerm α * u = u * autPerm α) : autPerm α ∈ UAloc i := by
  obtain ⟨u₀, hu₀, hα⟩ := (centralizer_UA_aut hi α).1 fun u hu => by
    apply Subtype.ext
    rw [autPerm_conj_apply, h _ hu, mul_inv_cancel_right]
  rw [hα, autPerm_conj]
  exact hu₀

end Planes

theorem autPerm_mbarHom_of_mem
    {G : Type} [Group G] [Finite G] (S : Setting G)
    (ψ : S14.Mbar0 S ≃* T46) (m : S14.Mbar0 S) :
    autPerm (mbarHom S ψ m) = ψ m := by
  rw [mbarHom_of_mem, autPerm_conj]

end CFSG.LargeExtraspecial.SMod20
