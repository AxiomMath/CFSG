module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

variable {L : Type*} [Group L]

variable (Q : Subgroup L) in
@[expose] def pointwiseFixingAut : Subgroup (MulAut L) where
  carrier := {α | ∀ q ∈ Q, α q = q}
  one_mem' := fun _ _ => rfl
  mul_mem' {α β} hα hβ q hq := by rw [MulAut.mul_apply, hβ q hq, hα q hq]
  inv_mem' {α} hα q hq := by
    rw [MulAut.inv_apply]
    conv_lhs => rw [← hα q hq]
    exact α.symm_apply_apply q

theorem mem_pointwiseFixingAut {Q : Subgroup L} {α : MulAut L} :
    α ∈ pointwiseFixingAut Q ↔ ∀ q ∈ Q, α q = q :=
  Iff.rfl

variable {Q : Subgroup L}

theorem inv_mul_apply_mem_centralizer [Q.Normal] {α : MulAut L} (hα : α ∈ pointwiseFixingAut Q)
    (x : L) : x⁻¹ * α x ∈ Subgroup.centralizer (Q : Set L) := by
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have h1 : x * q * x⁻¹ ∈ Q := Subgroup.Normal.conj_mem ‹_› q hq x
  have h2 : α (x * q * x⁻¹) = x * q * x⁻¹ := hα _ h1
  rw [map_mul, map_mul, map_inv, hα q hq] at h2
  have h3 : q * (x⁻¹ * α x) = (x⁻¹ * α x) * q := by
    calc q * (x⁻¹ * α x) = x⁻¹ * (x * q * x⁻¹) * α x := by group
      _ = x⁻¹ * (α x * q * (α x)⁻¹) * α x := by rw [h2]
      _ = (x⁻¹ * α x) * q := by group
  exact h3

theorem inv_mul_apply_mem_center [Q.Normal] (hQ : Subgroup.centralizer (Q : Set L) ≤ Q)
    {α : MulAut L} (hα : α ∈ pointwiseFixingAut Q) (x : L) :
    ∃ hx : x⁻¹ * α x ∈ Q, (⟨x⁻¹ * α x, hx⟩ : Q) ∈ Subgroup.center Q := by
  have hc := inv_mul_apply_mem_centralizer hα x
  refine ⟨hQ hc, Subgroup.mem_center_iff.2 fun q => Subtype.ext ?_⟩
  exact (Subgroup.mem_centralizer_iff.1 hc q q.2)

variable [Q.Normal] (hQ : Subgroup.centralizer (Q : Set L) ≤ Q)

@[expose] noncomputable def selfCentralizingKernel (α : pointwiseFixingAut Q) (x : L) :
    Subgroup.center Q :=
  ⟨⟨x⁻¹ * (α : MulAut L) x, (inv_mul_apply_mem_center hQ α.2 x).1⟩,
    (inv_mul_apply_mem_center hQ α.2 x).2⟩

theorem coe_selfCentralizingKernel (α : pointwiseFixingAut Q) (x : L) :
    (((selfCentralizingKernel hQ α x : Subgroup.center Q) : Q) : L) =
      x⁻¹ * (α : MulAut L) x :=
  rfl

@[expose] noncomputable def selfCentralizingKernelHom :
    pointwiseFixingAut Q →* (L → Subgroup.center Q) where
  toFun := selfCentralizingKernel hQ
  map_one' := funext fun x => Subtype.ext (Subtype.ext (by
    simp [coe_selfCentralizingKernel]))
  map_mul' α β := funext fun x => Subtype.ext (Subtype.ext (by
    simp only [Pi.mul_apply, Subgroup.coe_mul, coe_selfCentralizingKernel, Subgroup.coe_mul,
      MulAut.mul_apply]
    have hfix : (α : MulAut L) (x⁻¹ * (β : MulAut L) x) = x⁻¹ * (β : MulAut L) x :=
      α.2 _ (inv_mul_apply_mem_center hQ β.2 x).1
    rw [map_mul, map_inv] at hfix
    calc x⁻¹ * (α : MulAut L) ((β : MulAut L) x) =
          (x⁻¹ * (α : MulAut L) x) * ((α : MulAut L) x⁻¹ * (α : MulAut L) ((β : MulAut L) x)) := by
            rw [map_inv]; group
      _ = (x⁻¹ * (α : MulAut L) x) * (x⁻¹ * (β : MulAut L) x) := by rw [map_inv, hfix]))

theorem selfCentralizingKernelHom_injective :
    Function.Injective (selfCentralizingKernelHom hQ) := by
  rw [injective_iff_map_eq_one]
  intro α hα
  refine Subtype.ext (MulEquiv.ext fun x => ?_)
  have h := congrArg (fun f => ((f x : Subgroup.center Q) : Q)) hα
  have h' := congrArg Subtype.val h
  change x⁻¹ * (α : MulAut L) x = 1 at h'
  rw [inv_mul_eq_one] at h'
  exact h'.symm

include hQ in
theorem Tits_self_centralizing_core_automorphism_kernel [Finite L] (p : ℕ) [Fact p.Prime]
    (hp : IsPGroup p Q) :
    (∀ α ∈ pointwiseFixingAut Q, ∀ x : L,
      ∃ hx : x⁻¹ * α x ∈ Q, (⟨x⁻¹ * α x, hx⟩ : Q) ∈ Subgroup.center Q) ∧
    (∃ f : pointwiseFixingAut Q →* (L → Subgroup.center Q), Function.Injective f ∧
      ∀ α x, (((f α x : Subgroup.center Q) : Q) : L) = x⁻¹ * (α : MulAut L) x) ∧
    IsPGroup p (pointwiseFixingAut Q) ∧
    ∀ α β : pointwiseFixingAut Q, α * β = β * α := by
  have hinj := selfCentralizingKernelHom_injective hQ
  have hZ : IsPGroup p (Subgroup.center Q) := hp.to_subgroup _
  have hmap : IsPGroup p (L → Subgroup.center Q) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hZ
    exact IsPGroup.of_card (n := n * Nat.card L) (by rw [Nat.card_fun, hn, ← pow_mul])
  refine ⟨fun α hα x => inv_mul_apply_mem_center hQ hα x,
    ⟨_, hinj, fun α x => rfl⟩, hmap.of_injective _ hinj, fun α β => hinj ?_⟩
  rw [map_mul, map_mul]
  funext x
  exact Subtype.ext (Subgroup.mem_center_iff.1 (selfCentralizingKernelHom hQ β x).2
    (selfCentralizingKernelHom hQ α x))

end CFSG.LocalAnalysis.ComponentInitial
