module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaGElt

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

theorem exists_conj_action_of_swap (hC : CentData z ι) {g₀ : G} (hz : g₀ * z * g₀⁻¹ = ι τ₀)
    (hx : g₀ * ι τ₀ * g₀⁻¹ = z) :
    ∃ σ : Perm (Fin 8), ∀ ρ : Perm (Fin 8), ∃ e ∈ Egrp z ι,
      g₀ * ι (liftS8 ρ) * g₀⁻¹ = e * ι (liftS8 (σ * ρ * σ⁻¹)) := by
  have hgzi : g₀⁻¹ * z * g₀ = ι τ₀ := by rw [← hx]; group
  have hgxi : g₀⁻¹ * (ι τ₀) * g₀ = z := by rw [← hz]; group
  have hconjC : ∀ c ∈ CEgrp z ι, g₀ * c * g₀⁻¹ ∈ CEgrp z ι := by
    intro c hc
    have hcz : c * z = z * c := mem_centralizer_singleton_iff.1 (mem_inf.1 hc).1
    have hcx : c * (ι τ₀) = (ι τ₀) * c := mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2
    rw [CEgrp, mem_inf]
    constructor
    · rw [mem_centralizer_singleton_iff]
      calc (g₀ * c * g₀⁻¹) * z = g₀ * (c * (g₀⁻¹ * z * g₀)) * g₀⁻¹ := by group
        _ = g₀ * (c * (ι τ₀)) * g₀⁻¹ := by rw [hgzi]
        _ = g₀ * ((ι τ₀) * c) * g₀⁻¹ := by rw [hcx]
        _ = g₀ * ((g₀⁻¹ * z * g₀) * c) * g₀⁻¹ := by rw [hgzi]
        _ = z * (g₀ * c * g₀⁻¹) := by group
    · rw [mem_centralizer_singleton_iff]
      calc (g₀ * c * g₀⁻¹) * (ι τ₀) = g₀ * (c * (g₀⁻¹ * (ι τ₀) * g₀)) * g₀⁻¹ := by group
        _ = g₀ * (c * z) * g₀⁻¹ := by rw [hgxi]
        _ = g₀ * (z * c) * g₀⁻¹ := by rw [hcz]
        _ = g₀ * ((g₀⁻¹ * (ι τ₀) * g₀) * c) * g₀⁻¹ := by rw [hgxi]
        _ = (ι τ₀) * (g₀ * c * g₀⁻¹) := by group
  have hconjCinv : ∀ c ∈ CEgrp z ι, g₀⁻¹ * c * g₀ ∈ CEgrp z ι := by
    intro c hc
    have hcz : c * z = z * c := mem_centralizer_singleton_iff.1 (mem_inf.1 hc).1
    have hcx : c * (ι τ₀) = (ι τ₀) * c := mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2
    rw [CEgrp, mem_inf]
    constructor
    · rw [mem_centralizer_singleton_iff]
      calc (g₀⁻¹ * c * g₀) * z = g₀⁻¹ * (c * (g₀ * z * g₀⁻¹)) * g₀ := by group
        _ = g₀⁻¹ * (c * (ι τ₀)) * g₀ := by rw [hz]
        _ = g₀⁻¹ * ((ι τ₀) * c) * g₀ := by rw [hcx]
        _ = g₀⁻¹ * ((g₀ * z * g₀⁻¹) * c) * g₀ := by rw [hz]
        _ = z * (g₀⁻¹ * c * g₀) := by group
    · rw [mem_centralizer_singleton_iff]
      calc (g₀⁻¹ * c * g₀) * (ι τ₀) = g₀⁻¹ * (c * (g₀ * (ι τ₀) * g₀⁻¹)) * g₀ := by group
        _ = g₀⁻¹ * (c * z) * g₀ := by rw [hx]
        _ = g₀⁻¹ * (z * c) * g₀ := by rw [hcz]
        _ = g₀⁻¹ * ((g₀ * (ι τ₀) * g₀⁻¹) * c) * g₀ := by rw [hx]
        _ = (ι τ₀) * (g₀⁻¹ * c * g₀) := by group
  have hCmap : (CEgrp z ι).map (MulAut.conj g₀).toMonoidHom = CEgrp z ι := by
    apply le_antisymm
    · intro c hc
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hc
      exact hconjC d hd
    · intro c hc
      refine Subgroup.mem_map.2 ⟨g₀⁻¹ * c * g₀, hconjCinv c hc, ?_⟩
      show g₀ * (g₀⁻¹ * c * g₀) * g₀⁻¹ = c
      group
  have hAeq : (Agrp ι).map (MulAut.conj g₀).toMonoidHom = Agrp ι := by
    rw [← commutator_CEgrp hC, Subgroup.map_commutator, hCmap]
  let F : alternatingGroup (Fin 8) →* G := (ι.comp liftS8).comp (alternatingGroup (Fin 8)).subtype
  have hFinj : Function.Injective F := (hC.inj.comp liftS8_injective).comp Subtype.coe_injective
  have hFrange : F.range = Agrp ι := by
    ext a
    constructor
    · rintro ⟨α, rfl⟩
      exact mem_Agrp_iff.2 ⟨(α : Perm (Fin 8)), α.2, rfl⟩
    · rintro ha
      obtain ⟨ρ, hρ, hρa⟩ := mem_Agrp_iff.1 ha
      exact ⟨⟨ρ, hρ⟩, hρa⟩
  let eA : alternatingGroup (Fin 8) ≃* ↥(Agrp ι) :=
    (MonoidHom.ofInjective hFinj).trans (MulEquiv.subgroupCongr hFrange)
  have eA_apply : ∀ α : alternatingGroup (Fin 8),
      ((eA α : ↥(Agrp ι)) : G) = ι (liftS8 (α : Perm (Fin 8))) := by
    intro α
    simp only [eA, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      MonoidHom.ofInjective_apply, F, MonoidHom.comp_apply, Subtype.coe_mk]
    rfl
  let c₀ : MulAut ↥(Agrp ι) :=
    (Subgroup.equivMapOfInjective (Agrp ι) (MulAut.conj g₀).toMonoidHom
      (MulAut.conj g₀).injective).trans (MulEquiv.subgroupCongr hAeq)
  have c₀_apply : ∀ x : ↥(Agrp ι), ((c₀ x : ↥(Agrp ι)) : G) = g₀ * (x : G) * g₀⁻¹ := by
    intro x
    simp only [c₀, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
    rfl
  let θ : alternatingGroup (Fin 8) ≃* alternatingGroup (Fin 8) := eA.trans (c₀.trans eA.symm)
  have hstar : ∀ α : alternatingGroup (Fin 8),
      g₀ * ι (liftS8 (α : Perm (Fin 8))) * g₀⁻¹ =
        ι (liftS8 ((θ α : alternatingGroup (Fin 8)) : Perm (Fin 8))) := by
    intro α
    have h1 : eA (θ α) = c₀ (eA α) := by simp [θ]
    have h2 : ((eA (θ α) : ↥(Agrp ι)) : G) = ((c₀ (eA α) : ↥(Agrp ι)) : G) :=
      congrArg Subtype.val h1
    rw [eA_apply (θ α), c₀_apply (eA α), eA_apply α] at h2
    exact h2.symm
  obtain ⟨σ, hσ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8
      (by norm_num) (by norm_num)).2 θ
  have hθs : ∀ (s : Perm (Fin 8)) (hs : s ∈ alternatingGroup (Fin 8)),
      ((θ ⟨s, hs⟩ : alternatingGroup (Fin 8)) : Perm (Fin 8)) = σ * s * σ⁻¹ := by
    intro s hs
    rw [← hσ]
    simpa using MulAut.conjNormal_apply σ (⟨s, hs⟩ : alternatingGroup (Fin 8))
  have hstar2 : ∀ s : Perm (Fin 8), s ∈ alternatingGroup (Fin 8) →
      g₀ * ι (liftS8 s) * g₀⁻¹ = ι (liftS8 (σ * s * σ⁻¹)) := by
    intro s hs
    have h := hstar ⟨s, hs⟩
    rw [hθs s hs] at h
    simpa using h
  refine ⟨σ, ?_⟩
  intro ρ
  let X : G := g₀ * ι (liftS8 ρ) * g₀⁻¹
  let Y : G := ι (liftS8 (σ * ρ * σ⁻¹))
  have hY_CE : Y ∈ CEgrp z ι :=
    Siggrp_le_CEgrp hC (mem_Siggrp_iff.2 ⟨σ * ρ * σ⁻¹, rfl⟩)
  have hX_CE : X ∈ CEgrp z ι := by
    have hmem : (MulAut.conj g₀) (ι (liftS8 ρ)) ∈
        (CEgrp z ι).map (MulAut.conj g₀).toMonoidHom :=
      Subgroup.mem_map.2 ⟨ι (liftS8 ρ),
        Siggrp_le_CEgrp hC (mem_Siggrp_iff.2 ⟨ρ, rfl⟩), rfl⟩
    rw [hCmap] at hmem
    simpa [X, MulAut.conj_apply] using hmem
  let e : G := Y⁻¹ * X
  have heC : e ∈ CEgrp z ι := by
    simp only [e]
    exact mul_mem (inv_mem hY_CE) hX_CE
  have hecent : e ∈ centralizer (Agrp ι : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨β, hβ, hβa⟩ := mem_Agrp_iff.1 ha
    rw [← hβa]
    set α : Perm (Fin 8) := σ⁻¹ * β * σ with hαdef
    have hαA : α ∈ alternatingGroup (Fin 8) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      have hβs : sign β = 1 := Equiv.Perm.mem_alternatingGroup.1 hβ
      simp [hαdef, map_mul, map_inv, hβs]
    have hαβ : σ * α * σ⁻¹ = β := by rw [hαdef]; group
    have hgα : g₀ * ι (liftS8 α) * g₀⁻¹ = ι (liftS8 β) := by
      rw [hstar2 α hαA, hαβ]
    have hραρA : ρ * α * ρ⁻¹ ∈ alternatingGroup (Fin 8) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      have hαs : sign α = 1 := Equiv.Perm.mem_alternatingGroup.1 hαA
      simp [map_mul, map_inv, hαs]
    have hXaY : X * ι (liftS8 β) * X⁻¹ = Y * ι (liftS8 β) * Y⁻¹ := by
      have hL : X * ι (liftS8 β) * X⁻¹ = g₀ * ι (liftS8 (ρ * α * ρ⁻¹)) * g₀⁻¹ := by
        rw [← hgα]
        simp only [X]
        rw [show g₀ * ι (liftS8 ρ) * g₀⁻¹ * (g₀ * ι (liftS8 α) * g₀⁻¹) *
              (g₀ * ι (liftS8 ρ) * g₀⁻¹)⁻¹ =
              g₀ * (ι (liftS8 ρ) * ι (liftS8 α) * (ι (liftS8 ρ))⁻¹) * g₀⁻¹ by group]
        rw [show ι (liftS8 ρ) * ι (liftS8 α) * (ι (liftS8 ρ))⁻¹ =
              ι (liftS8 (ρ * α * ρ⁻¹)) by simp only [map_mul, map_inv]]
      have hR : Y * ι (liftS8 β) * Y⁻¹ = g₀ * ι (liftS8 (ρ * α * ρ⁻¹)) * g₀⁻¹ := by
        have hperm : (σ * ρ * σ⁻¹) * β * (σ * ρ * σ⁻¹)⁻¹ = σ * (ρ * α * ρ⁻¹) * σ⁻¹ := by
          rw [hαdef]; group
        calc Y * ι (liftS8 β) * Y⁻¹
            = ι (liftS8 ((σ * ρ * σ⁻¹) * β * (σ * ρ * σ⁻¹)⁻¹)) := by
                simp only [Y, map_mul, map_inv]
          _ = ι (liftS8 (σ * (ρ * α * ρ⁻¹) * σ⁻¹)) := by rw [hperm]
          _ = g₀ * ι (liftS8 (ρ * α * ρ⁻¹)) * g₀⁻¹ := (hstar2 (ρ * α * ρ⁻¹) hραρA).symm
      exact hL.trans hR.symm
    have hea : e * ι (liftS8 β) = ι (liftS8 β) * e := by
      calc e * ι (liftS8 β) = Y⁻¹ * (X * ι (liftS8 β) * X⁻¹) * X := by
            simp only [e]; group
        _ = Y⁻¹ * (Y * ι (liftS8 β) * Y⁻¹) * X := by rw [hXaY]
        _ = ι (liftS8 β) * e := by simp only [e]; group
    exact hea.symm
  have heE : e ∈ Egrp z ι := by
    have hres := centralizer_Agrp_inf_CEgrp hC
    rw [← hres]
    exact Subgroup.mem_inf.2 ⟨hecent, heC⟩
  refine ⟨e, heE, ?_⟩
  calc X = Y * e := by simp only [e]; group
    _ = e * Y := (mul_comm_of_mem_Egrp_of_mem_CEgrp hC heE hY_CE).symm

theorem gElt_of_conj_action (hC : CentData z ι) {g₀ : G} {σ : Perm (Fin 8)}
    (hz : g₀ * z * g₀⁻¹ = ι τ₀) (hx : g₀ * ι τ₀ * g₀⁻¹ = z)
    (hact : ∀ ρ : Perm (Fin 8), ∃ e ∈ Egrp z ι,
      g₀ * ι (liftS8 ρ) * g₀⁻¹ = e * ι (liftS8 (σ * ρ * σ⁻¹))) :
    GElt z ι ((ι (liftS8 σ))⁻¹ * g₀) := by
  set σt : G := ι (liftS8 σ) with hσt
  have hσtinv : σt⁻¹ = ι (liftS8 σ⁻¹) := by rw [hσt, ← map_inv, ← map_inv]
  have hσz : σt⁻¹ * z * σt = z := by
    have hzcomm : σt * z = z * σt := (hC.comm (liftS8 σ)).symm
    rw [mul_assoc, ← hzcomm]; group
  have hστ : σt⁻¹ * (ι τ₀) * σt = ι τ₀ := by
    have htcomm : σt * (ι τ₀) = (ι τ₀) * σt := by
      rw [hσt, ← map_mul, ← map_mul, liftS8_mul_τ₀]
    rw [mul_assoc, ← htcomm]; group
  haveI hEcomm : IsMulCommutative ↥(Egrp z ι) :=
    IsMulCommutative.of_setLike_mul_comm fun a ha b hb => by
      obtain ⟨i, j, rfl⟩ := (mem_Egrp_iff hC).1 ha
      obtain ⟨k, l, rfl⟩ := (mem_Egrp_iff hC).1 hb
      have hzx : Commute z (ι τ₀) := hC.comm τ₀
      exact (Commute.mul_left
        (Commute.mul_right ((Commute.refl z).pow_pow (i : ℕ) (k : ℕ))
          (hzx.pow_pow (i : ℕ) (l : ℕ)))
        (Commute.mul_right (hzx.symm.pow_pow (j : ℕ) (k : ℕ))
          ((Commute.refl (ι τ₀)).pow_pow (j : ℕ) (l : ℕ)))).eq
  choose e heE heq using hact
  have e_one : e 1 = 1 := by
    have h := heq 1
    simpa using h.symm
  have e_mul : ∀ ρ τ, e (ρ * τ) = e ρ * e τ := by
    intro ρ τ
    have h := heq (ρ * τ)
    have h2 : g₀ * ι (liftS8 (ρ * τ)) * g₀⁻¹ =
        (g₀ * ι (liftS8 ρ) * g₀⁻¹) * (g₀ * ι (liftS8 τ) * g₀⁻¹) := by
      rw [map_mul, map_mul]; group
    rw [h2, heq ρ, heq τ] at h
    have hcomm : ι (liftS8 (σ * ρ * σ⁻¹)) * e τ = e τ * ι (liftS8 (σ * ρ * σ⁻¹)) :=
      (mul_comm_of_mem_Egrp_of_mem_CEgrp hC (heE τ)
        (Siggrp_le_CEgrp hC (mem_Siggrp_iff.2 ⟨σ * ρ * σ⁻¹, rfl⟩))).symm
    have hY : ι (liftS8 (σ * (ρ * τ) * σ⁻¹)) =
        ι (liftS8 (σ * ρ * σ⁻¹)) * ι (liftS8 (σ * τ * σ⁻¹)) := by
      have hp : σ * (ρ * τ) * σ⁻¹ = (σ * ρ * σ⁻¹) * (σ * τ * σ⁻¹) := by group
      rw [hp, map_mul, map_mul]
    rw [hY] at h
    have h' : (e ρ * e τ) *
          (ι (liftS8 (σ * ρ * σ⁻¹)) * ι (liftS8 (σ * τ * σ⁻¹))) =
        e (ρ * τ) * (ι (liftS8 (σ * ρ * σ⁻¹)) * ι (liftS8 (σ * τ * σ⁻¹))) := by
      calc (e ρ * e τ) * (ι (liftS8 (σ * ρ * σ⁻¹)) * ι (liftS8 (σ * τ * σ⁻¹)))
          = e ρ * (e τ * ι (liftS8 (σ * ρ * σ⁻¹))) * ι (liftS8 (σ * τ * σ⁻¹)) := by
            group
        _ = e ρ * (ι (liftS8 (σ * ρ * σ⁻¹)) * e τ) * ι (liftS8 (σ * τ * σ⁻¹)) := by
            rw [← hcomm]
        _ = (e ρ * ι (liftS8 (σ * ρ * σ⁻¹))) * (e τ * ι (liftS8 (σ * τ * σ⁻¹))) := by
            group
        _ = e (ρ * τ) * (ι (liftS8 (σ * ρ * σ⁻¹)) * ι (liftS8 (σ * τ * σ⁻¹))) := h
    exact (mul_right_cancel h').symm
  let ehom : Perm (Fin 8) →* ↥(Egrp z ι) :=
    { toFun := fun ρ => ⟨e ρ, heE ρ⟩
      map_one' := Subtype.ext e_one
      map_mul' := fun ρ τ => Subtype.ext (e_mul ρ τ) }
  have hker : commutator (Perm (Fin 8)) ≤ ehom.ker := Abelianization.commutator_subset_ker ehom
  have hgz : σt⁻¹ * (g₀ * z * g₀⁻¹) * σt = ι τ₀ := by rw [hz, hστ]
  have hgx : σt⁻¹ * (g₀ * (ι τ₀) * g₀⁻¹) * σt = z := by rw [hx, hσz]
  have hz' : (σt⁻¹ * g₀) * z * (σt⁻¹ * g₀)⁻¹ = ι τ₀ := by
    have h1 : (σt⁻¹ * g₀) * z * (σt⁻¹ * g₀)⁻¹ =
        σt⁻¹ * (g₀ * z * g₀⁻¹) * σt := by group
    rw [h1, hgz]
  have hx' : (σt⁻¹ * g₀) * (ι τ₀) * (σt⁻¹ * g₀)⁻¹ = z := by
    have h1 : (σt⁻¹ * g₀) * (ι τ₀) * (σt⁻¹ * g₀)⁻¹ =
        σt⁻¹ * (g₀ * (ι τ₀) * g₀⁻¹) * σt := by group
    rw [h1, hgx]
  have hA : ∀ ρ ∈ alternatingGroup (Fin 8),
      (σt⁻¹ * g₀) * ι (liftS8 ρ) = ι (liftS8 ρ) * (σt⁻¹ * g₀) := by
    intro ρ hρ
    have hρcomm : ρ ∈ commutator (Perm (Fin 8)) := by
      rw [alternatingGroup.commutator_perm_eq (α := Fin 8) (by simp : 5 ≤ Nat.card (Fin 8))]
      exact hρ
    have heρ : e ρ = 1 := by
      have h1 : ehom ρ = 1 := MonoidHom.mem_ker.1 (hker hρcomm)
      have h2 := congrArg Subtype.val h1
      simpa [ehom] using h2
    have hσe : σt⁻¹ * e ρ * σt = e ρ := by
      have h := mul_comm_of_mem_Egrp_of_mem_CEgrp hC (heE ρ)
        (Siggrp_le_CEgrp hC (mem_Siggrp_iff.2 ⟨σ, rfl⟩))
      calc σt⁻¹ * e ρ * σt = σt⁻¹ * (e ρ * σt) := by group
        _ = σt⁻¹ * (σt * e ρ) := by rw [h]
        _ = e ρ := by group
    have hσY : σt⁻¹ * ι (liftS8 (σ * ρ * σ⁻¹)) * σt = ι (liftS8 ρ) := by
      have hYeq : σt * ι (liftS8 ρ) * σt⁻¹ = ι (liftS8 (σ * ρ * σ⁻¹)) := by
        rw [hσt]
        simp only [map_mul, map_inv]
      calc σt⁻¹ * ι (liftS8 (σ * ρ * σ⁻¹)) * σt
          = σt⁻¹ * (σt * ι (liftS8 ρ) * σt⁻¹) * σt := by rw [← hYeq]
        _ = ι (liftS8 ρ) := by group
    have hconj : (σt⁻¹ * g₀) * ι (liftS8 ρ) * (σt⁻¹ * g₀)⁻¹ = ι (liftS8 ρ) := by
      have h1 : (σt⁻¹ * g₀) * ι (liftS8 ρ) * (σt⁻¹ * g₀)⁻¹ =
          σt⁻¹ * (g₀ * ι (liftS8 ρ) * g₀⁻¹) * σt := by group
      rw [h1, heq ρ]
      calc σt⁻¹ * (e ρ * ι (liftS8 (σ * ρ * σ⁻¹))) * σt
          = (σt⁻¹ * e ρ * σt) * (σt⁻¹ * ι (liftS8 (σ * ρ * σ⁻¹)) * σt) := by group
        _ = e ρ * ι (liftS8 ρ) := by rw [hσe, hσY]
        _ = ι (liftS8 ρ) := by rw [heρ, one_mul]
    have h2 := congrArg (fun t => t * (σt⁻¹ * g₀)) hconj
    simpa [mul_assoc] using h2
  exact GElt.of_swap_of_comm_A hC hz' hx' hA

end CFSG.OddStandard.AltStdSec.SwapPartner
