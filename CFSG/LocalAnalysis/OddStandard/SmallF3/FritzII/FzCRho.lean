module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCStepsDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

private theorem fzc_base_le_wreath : baseGrp x₁ x₂ ≤ wreathGrp x₁ x₂ lam := by
  rw [baseGrp, wreathGrp]
  apply Subgroup.closure_mono
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
  tauto

private theorem fzc_four_le_base : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
  rw [fourGrp, baseGrp, Subgroup.closure_le]
  intro y hy
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · exact pow_mem (Subgroup.subset_closure (by simp)) 2
  · exact pow_mem (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) 2

theorem fzc_comm_conj_mem {H : Subgroup G} {ρ g : G} (hH : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hρ : g * ρ * g⁻¹ ∈ zpowers ρ) {x : G} (hx : x ∈ ⁅H, zpowers ρ⁆) :
    g * x * g⁻¹ ∈ ⁅H, zpowers ρ⁆ := by
  rw [Subgroup.commutator_def] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hy
      rw [conjugate_commutatorElement]
      refine Subgroup.commutator_mem_commutator (hH a ha) ?_
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
      rw [← hk, ← conj_zpow]
      exact (zpowers ρ).zpow_mem hρ k
  | one => simp
  | mul y z hy hz ihy ihz =>
      rw [show g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) by group]
      exact Subgroup.mul_mem _ ihy ihz
  | inv y hy ihy =>
      rw [show g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ihy

theorem fzc_rho_norm_W (hs : FzCSteps t L S x₁ x₂ lam rho) {w : G} (hw : w ∈ ctxW t x₁ x₂) :
    rho * w * rho⁻¹ ∈ ctxW t x₁ x₂ := by
  exact (Subgroup.mem_set_normalizer_iff.mp hs.ctx.rho_normalizes w).mp hw

theorem fzc_rho_norm_base (hs : FzCSteps t L S x₁ x₂ lam rho) {e : G}
    (he : e ∈ baseGrp x₁ x₂) : rho * e * rho⁻¹ ∈ baseGrp x₁ x₂ := by
  have hmain : rho * e * rho⁻¹ ∈ ⁅ctxW t x₁ x₂, zpowers rho⁆ :=
    fzc_comm_conj_mem (H := ctxW t x₁ x₂) (ρ := rho) (g := rho)
      (fun x hx => fzc_rho_norm_W hs hx)
      (by simpa [mul_assoc] using Subgroup.mem_zpowers rho)
      (by rw [hs.ctx.comm_rho]; exact he)
  rwa [hs.ctx.comm_rho] at hmain

theorem fzc_base_sq_mem_four (hs : FzCSteps t L S x₁ x₂ lam rho) {e : G}
    (he : e ∈ baseGrp x₁ x₂) : e * e ∈ fourGrp x₁ x₂ := by
  rw [WreathRel.fourGrp_eq_mho hs.ctx.wreath]
  exact Subgroup.subset_closure ⟨e, he, (sq e).symm⟩

theorem fzc_rho_norm_four (hs : FzCSteps t L S x₁ x₂ lam rho) {f : G}
    (hf : f ∈ fourGrp x₁ x₂) : rho * f * rho⁻¹ ∈ fourGrp x₁ x₂ := by
  rw [fourGrp] at hf
  induction hf using Subgroup.closure_induction with
  | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · have hmem : rho * x₁ * rho⁻¹ ∈ baseGrp x₁ x₂ :=
          fzc_rho_norm_base hs (Subgroup.subset_closure (by simp))
        have hsq := fzc_base_sq_mem_four hs hmem
        rwa [show rho * x₁ ^ 2 * rho⁻¹ =
          (rho * x₁ * rho⁻¹) * (rho * x₁ * rho⁻¹) by rw [sq]; group]
      · have hmem : rho * (x₁ * x₂) * rho⁻¹ ∈ baseGrp x₁ x₂ :=
          fzc_rho_norm_base hs (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp)))
        have hsq := fzc_base_sq_mem_four hs hmem
        rwa [show rho * (x₁ * x₂) ^ 2 * rho⁻¹ =
          (rho * (x₁ * x₂) * rho⁻¹) * (rho * (x₁ * x₂) * rho⁻¹) by rw [sq]; group]
  | one => simp
  | mul y z hy hz ihy ihz =>
      rw [show rho * (y * z) * rho⁻¹ = (rho * y * rho⁻¹) * (rho * z * rho⁻¹) by group]
      exact Subgroup.mul_mem _ ihy ihz
  | inv y hy ihy =>
      rw [show rho * y⁻¹ * rho⁻¹ = (rho * y * rho⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ihy

theorem fzc_K_inf_base (hs : FzCSteps t L S x₁ x₂ lam rho) :
    twoCore t ⊓ baseGrp x₁ x₂ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxL : x ∈ L := by
    have hxw : x ∈ wreathGrp x₁ x₂ lam := fzc_base_le_wreath hx.2
    rw [← hs.ctx.inf_eq] at hxw
    exact hxw.2
  have hxKL : x ∈ twoCore t ⊓ L := ⟨hx.1, hxL⟩
  rwa [hs.ctx.hyp.twoCore_inf, Subgroup.mem_bot] at hxKL

theorem fzc_rho_fpf_base (hs : FzCSteps t L S x₁ x₂ lam rho) {e : G}
    (he : e ∈ baseGrp x₁ x₂) (h : rho * e * rho⁻¹ = e) : e = 1 := by
  have hcomm : rho * e = e * rho := by
    have := congrArg (fun x => x * rho) h
    simpa [mul_assoc] using this
  have hcent : e ∈ Subgroup.centralizer ({rho} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hcomm
  have heW : e ∈ ctxW t x₁ x₂ := Subgroup.mem_sup_right he
  have heK : e ∈ twoCore t := by
    have hmem : e ∈ ctxW t x₁ x₂ ⊓ Subgroup.centralizer ({rho} : Set G) := ⟨heW, hcent⟩
    rwa [hs.ctx.cent_rho] at hmem
  have heKE : e ∈ twoCore t ⊓ baseGrp x₁ x₂ := ⟨heK, he⟩
  rwa [fzc_K_inf_base hs, Subgroup.mem_bot] at heKE

theorem fzc_rho_fpf_four (hs : FzCSteps t L S x₁ x₂ lam rho) {f : G}
    (hf : f ∈ fourGrp x₁ x₂) (h : rho * f * rho⁻¹ = f) : f = 1 :=
  fzc_rho_fpf_base hs (fzc_four_le_base hf) h

theorem fzc_exists_comm_four (hs : FzCSteps t L S x₁ x₂ lam rho) {f : G}
    (hf : f ∈ fourGrp x₁ x₂) : ∃ ζ ∈ fourGrp x₁ x₂, rho * ζ * rho⁻¹ * ζ⁻¹ = f := by
  let Z := fourGrp x₁ x₂
  haveI : IsMulCommutative (↥Z) := ((WreathRel.fourGrp_eq_omega hs.ctx.wreath).2.1).1
  let φ : ↥Z → ↥Z := fun ζ =>
    ⟨rho * ζ.1 * rho⁻¹ * ζ.1⁻¹, Subgroup.mul_mem _
      (fzc_rho_norm_four hs ζ.2) (Subgroup.inv_mem _ ζ.2)⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    have hca : rho * a.1 * rho⁻¹ ∈ Z := fzc_rho_norm_four hs a.2
    have hcb : rho * b.1 * rho⁻¹ ∈ Z := fzc_rho_norm_four hs b.2
    let ca : ↥Z := ⟨rho * a.1 * rho⁻¹, hca⟩
    let cb : ↥Z := ⟨rho * b.1 * rho⁻¹, hcb⟩
    have h' : ca * a⁻¹ = cb * b⁻¹ := by
      apply Subtype.ext
      show (rho * a.1 * rho⁻¹) * a.1⁻¹ = (rho * b.1 * rho⁻¹) * b.1⁻¹
      have hh : rho * a.1 * rho⁻¹ * a.1⁻¹ = rho * b.1 * rho⁻¹ * b.1⁻¹ :=
        congrArg Subtype.val hab
      simpa only [mul_assoc] using hh
    have h1 : cb⁻¹ * (ca * a⁻¹) = b⁻¹ := by
      rw [h']
      group
    have h2 : cb⁻¹ * ca = b⁻¹ * a := by
      have := congrArg (fun z : ↥Z => z * a) h1
      convert this using 1 <;> group
    have h3 : ca * cb⁻¹ = a * b⁻¹ := by
      rw [mul_comm' cb⁻¹ ca, mul_comm' b⁻¹ a] at h2
      exact h2
    have h4 : rho * (a.1 * b.1⁻¹) * rho⁻¹ = a.1 * b.1⁻¹ := by
      have hh : (ca * cb⁻¹).1 = (a * b⁻¹).1 := congrArg Subtype.val h3
      change (rho * a.1 * rho⁻¹) * (rho * b.1 * rho⁻¹)⁻¹ = a.1 * b.1⁻¹ at hh
      calc rho * (a.1 * b.1⁻¹) * rho⁻¹
          = (rho * a.1 * rho⁻¹) * (rho * b.1 * rho⁻¹)⁻¹ := by group
        _ = a.1 * b.1⁻¹ := hh
    have hmem : a.1 * b.1⁻¹ ∈ Z := Subgroup.mul_mem _ a.2 (Subgroup.inv_mem _ b.2)
    have hfpf := fzc_rho_fpf_four hs hmem h4
    calc a.1 = a.1 * b.1⁻¹ * b.1 := by group
      _ = 1 * b.1 := by rw [hfpf]
      _ = b.1 := by group
  have hsurj : Function.Surjective φ := Finite.surjective_of_injective hinj
  obtain ⟨ζ, hζ⟩ := hsurj ⟨f, hf⟩
  exact ⟨ζ.1, ζ.2, congrArg Subtype.val hζ⟩

end CFSG.OddStandard.SmallF3.FritzII
