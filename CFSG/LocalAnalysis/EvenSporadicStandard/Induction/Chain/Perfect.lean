module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H]

theorem commutes_of_commutator_mem {A Z : Subgroup H} [Group.IsPerfect ↥A] {n : H}
    (hZ : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z) (hZA : ∀ z ∈ Z, ∀ a ∈ A, z * a = a * z)
    (hc : ∀ a ∈ A, a * n * a⁻¹ * n⁻¹ ∈ Z) : ∀ a ∈ A, a * n = n * a := by
  let δ : ↥A →* ↥Z :=
    { toFun := fun a => ⟨a * n * a⁻¹ * n⁻¹, hc a a.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have h1 := hZA ((b : H) * n * (b : H)⁻¹ * n⁻¹) (hc b b.2) a a.2
        show (a : H) * b * n * ((a : H) * b)⁻¹ * n⁻¹ =
          ((a : H) * n * (a : H)⁻¹ * n⁻¹) * ((b : H) * n * (b : H)⁻¹ * n⁻¹)
        calc (a : H) * b * n * ((a : H) * b)⁻¹ * n⁻¹
            = (a : H) * ((b : H) * n * (b : H)⁻¹ * n⁻¹) * (n * (a : H)⁻¹ * n⁻¹) := by group
          _ = ((b : H) * n * (b : H)⁻¹ * n⁻¹) * (a : H) * (n * (a : H)⁻¹ * n⁻¹) := by
              rw [← mul_assoc, ← h1]; group
          _ = ((b : H) * n * (b : H)⁻¹ * n⁻¹) * ((a : H) * n * (a : H)⁻¹ * n⁻¹) := by group
          _ = _ := hZ _ (hc b b.2) _ (hc a a.2) }
  have hδ : ∀ x ∈ commutator ↥A, δ x = 1 := by
    intro x hx
    rw [_root_.commutator_def] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, -, b, -, rfl⟩ := hx
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2
        (Subtype.ext (hZ _ (hc a a.2) _ (hc b b.2)))
    | one => exact map_one δ
    | mul a b _ _ ha hb => rw [map_mul, ha, hb, one_mul]
    | inv a _ ha => rw [map_inv, ha, inv_one]
  intro a ha
  have h1 := congrArg Subtype.val (hδ ⟨a, ha⟩ Group.IsPerfect.mem_commutator)
  have h2 : a * n * a⁻¹ * n⁻¹ = 1 := h1
  calc a * n = (a * n * a⁻¹ * n⁻¹) * (n * a) := by group
    _ = n * a := by rw [h2]; group

theorem central_kernel_of_surj {A : Type*} {B : Type*} [Group A] [Group B]
    (hA : CFSG.IsQuasisimple A) [Nontrivial B] (π : A →* B) (hπ : Function.Surjective π) :
    π.ker ≤ center A := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hA (π.normal_ker) with htop | hle
  · exfalso
    obtain ⟨b, hb⟩ := exists_ne (1 : B)
    obtain ⟨a, rfl⟩ := hπ b
    apply hb
    have : a ∈ π.ker := by rw [htop]; exact Subgroup.mem_top a
    exact this
  · exact hle

theorem card_quot_center_le_card_range {G Y : Type*} [Group G] [Finite G] [Group Y] (f : G →* Y)
    (hker : f.ker ≤ center G) : Nat.card (G ⧸ center G) ≤ Nat.card f.range := by
  let ψ : G ⧸ f.ker →* G ⧸ center G := QuotientGroup.map f.ker (center G) (MonoidHom.id _) hker
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk a, rfl⟩
  have h1 : Nat.card (G ⧸ center G) ≤ Nat.card (G ⧸ f.ker) := Nat.card_le_card_of_surjective ψ hψ
  have h2 : Nat.card (G ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  exact h2 ▸ h1

@[expose] def prodSub (A C : Subgroup H) (h : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) : Subgroup H where
  carrier := {x | ∃ a ∈ A, ∃ c ∈ C, x = a * c}
  mul_mem' := by
    rintro _ _ ⟨a, ha, c, hc, rfl⟩ ⟨a', ha', c', hc', rfl⟩
    refine ⟨a * a', A.mul_mem ha ha', c * c', C.mul_mem hc hc', ?_⟩
    have := h a' ha' c hc
    calc a * c * (a' * c') = a * (c * a') * c' := by group
      _ = a * (a' * c) * c' := by rw [this.symm]
      _ = a * a' * (c * c') := by group
  one_mem' := ⟨1, A.one_mem, 1, C.one_mem, by simp⟩
  inv_mem' := by
    rintro _ ⟨a, ha, c, hc, rfl⟩
    refine ⟨a⁻¹, A.inv_mem ha, c⁻¹, C.inv_mem hc, ?_⟩
    have := h a⁻¹ (A.inv_mem ha) c hc
    calc (a * c)⁻¹ = c⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * c⁻¹ := by
          have h2 := h a⁻¹ (A.inv_mem ha) c⁻¹ (C.inv_mem hc)
          exact h2.symm

theorem mem_prodSub {A C : Subgroup H} {h : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a} {x : H} :
    x ∈ prodSub A C h ↔ ∃ a ∈ A, ∃ c ∈ C, x = a * c := Iff.rfl

end CFSG.EvenSporadicStandard.Induction
