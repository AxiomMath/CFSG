module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

public section

namespace CFSG.LinearAlgebra

open Module

private theorem card_le_pow_of_injective_prod_linearMap
    {K H : Type*} [Field K] [Finite K] [AddCommGroup H] [Module K H]
    [FiniteDimensional K H] {A : Type*} {P C ℓ : Submodule K H}
    (hPC : IsCompl P C) (hℓ : Module.finrank K ℓ ≤ 1)
    (f : A → P × (C →ₗ[K] ℓ)) (hf : Function.Injective f) :
    Nat.card A ≤ Nat.card K ^ Module.finrank K H := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype H := Fintype.ofEquiv (Fin (Module.finrank K H) → K)
    (Module.finBasis K H).equivFun.toEquiv.symm
  haveI : Finite (C →ₗ[K] ℓ) :=
    Finite.of_injective (fun f : C →ₗ[K] ℓ => (f : C → ℓ))
      (fun f g h => LinearMap.ext (congrFun h))
  calc
    Nat.card A ≤ Nat.card (P × (C →ₗ[K] ℓ)) := Nat.card_le_card_of_injective f hf
    _ = Nat.card P * Nat.card (C →ₗ[K] ℓ) := Nat.card_prod _ _
    _ = Nat.card K ^ Module.finrank K P * Nat.card K ^ Module.finrank K (C →ₗ[K] ℓ) := by
      have h1 : Nat.card P = Nat.card K ^ Module.finrank K P :=
        Module.natCard_eq_pow_finrank (K := K) (V := P)
      have h2 : Nat.card (C →ₗ[K] ℓ) = Nat.card K ^ Module.finrank K (C →ₗ[K] ℓ) :=
        Module.natCard_eq_pow_finrank (K := K) (V := C →ₗ[K] ℓ)
      rw [h1, h2]
    _ = Nat.card K ^ (Module.finrank K P + Module.finrank K (C →ₗ[K] ℓ)) := by
      rw [pow_add]
    _ = Nat.card K ^ (Module.finrank K P + Module.finrank K C * Module.finrank K ℓ) := by
      rw [Module.finrank_linearMap K K C ℓ]
    _ ≤ Nat.card K ^ (Module.finrank K P + Module.finrank K C) := by
      refine Nat.pow_le_pow_right (Nat.card_pos (α := K)) ?_
      have hmul : Module.finrank K C * Module.finrank K ℓ ≤ Module.finrank K C := by
        simpa using Nat.mul_le_mul_left (Module.finrank K C) hℓ
      omega
    _ = Nat.card K ^ Module.finrank K H := by
      rw [Submodule.finrank_add_eq_of_isCompl hPC]

private theorem apply_delta_comm
    {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (A : Subgroup (W ≃ₗ[K] W)) (hA : ∀ s ∈ A, ∀ t ∈ A, s * t = t * s)
    {H : Submodule K W} {w₀ : W} (δ : A → H) (N : A → H →ₗ[K] H)
    (hδcoe : ∀ t : A, (δ t : W) = (t : W ≃ₗ[K] W) w₀ - w₀)
    (hNcoe : ∀ (t : A) (h : H), (N t h : W) = (t : W ≃ₗ[K] W) h - h)
    (s t : A) : N s (δ t) = N t (δ s) := by
  apply Subtype.ext
  have hst : (s : W ≃ₗ[K] W) ((t : W ≃ₗ[K] W) w₀) =
      (t : W ≃ₗ[K] W) ((s : W ≃ₗ[K] W) w₀) := by
    have h := congrArg (fun e : W ≃ₗ[K] W => e w₀) (hA s s.2 t t.2)
    simpa using h
  simp only [hNcoe, hδcoe, map_sub, Submodule.coe_sub, hst]
  abel

private theorem eqOn_span_delta_sup
    {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (A : Subgroup (W ≃ₗ[K] W)) {H : Submodule K W} {ℓH : Submodule K H}
    (δ : A → H) (N : A → H →ₗ[K] H)
    (hD : ∀ s t : A, N s (δ t) = N t (δ s))
    (hNcoe : ∀ (t : A) (h : H), (N t h : W) = (t : W ≃ₗ[K] W) h - h)
    (h3H : ∀ t ∈ A, ∀ l ∈ ℓH, (t : W ≃ₗ[K] W) (l : W) = (l : W))
    {s t : A} (hδ : δ s = δ t) :
    ∀ p ∈ Submodule.span K (Set.range δ) ⊔ ℓH, N s p = N t p := by
  intro p hp
  rw [Submodule.mem_sup] at hp
  obtain ⟨a, ha, b, hb, rfl⟩ := hp
  have hgen : Set.EqOn (N s) (N t) (Set.range δ) := by
    rintro _ ⟨u, rfl⟩
    rw [hD s u, hδ, hD t u]
  have hb0s : N s b = 0 := by
    apply Subtype.ext
    rw [hNcoe, h3H s s.2 b hb, sub_self]
    rfl
  have hb0t : N t b = 0 := by
    apply Subtype.ext
    rw [hNcoe, h3H t t.2 b hb, sub_self]
    rfl
  rw [map_add, map_add, hb0s, hb0t, add_zero, add_zero]
  exact LinearMap.eqOn_span hgen ha

private theorem eq_of_delta_eq_and_N_eq_on_compl
    {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (A : Subgroup (W ≃ₗ[K] W)) {H : Submodule K W} {w₀ : W}
    (hH : Module.finrank K H + 1 = Module.finrank K W) (hw₀ : w₀ ∉ H)
    (δ : A → H) (N : A → H →ₗ[K] H)
    (hδcoe : ∀ t : A, (δ t : W) = (t : W ≃ₗ[K] W) w₀ - w₀)
    (hNcoe : ∀ (t : A) (h : H), (N t h : W) = (t : W ≃ₗ[K] W) h - h)
    {P C : Submodule K H} (hPC : P ⊔ C = ⊤)
    (hP : ∀ s t : A, δ s = δ t → ∀ p ∈ P, N s p = N t p)
    {s t : A} (hδ : δ s = δ t)
    (hC : ∀ c ∈ C, N s c = N t c) : s = t := by
  have hNst : N s = N t := by
    ext h
    have hh : h ∈ P ⊔ C := by rw [hPC]; exact Submodule.mem_top
    rw [Submodule.mem_sup] at hh
    obtain ⟨p, hp, c, hc, hpc⟩ := hh
    rw [← hpc, map_add, map_add, hP s t hδ p hp, hC c hc]
  have htop : H ⊔ Submodule.span K {w₀} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Submodule.finrank_sup_span_singleton hw₀, hH]
  have heq : (s : W ≃ₗ[K] W) = (t : W ≃ₗ[K] W) := by
    ext w
    have hw : w ∈ H ⊔ Submodule.span K {w₀} := by rw [htop]; exact Submodule.mem_top
    rw [Submodule.mem_sup] at hw
    obtain ⟨h, hh, y, hy, hwy⟩ := hw
    rw [Submodule.mem_span_singleton] at hy
    obtain ⟨c, rfl⟩ := hy
    rw [← hwy, map_add, map_smul, map_add, map_smul]
    have hs : (s : W ≃ₗ[K] W) h = h + (N s ⟨h, hh⟩ : W) := by
      rw [hNcoe]; abel
    have ht : (t : W ≃ₗ[K] W) h = h + (N t ⟨h, hh⟩ : W) := by
      rw [hNcoe]; abel
    have hsw : (s : W ≃ₗ[K] W) w₀ = w₀ + (δ s : W) := by
      rw [hδcoe]; abel
    have htw : (t : W ≃ₗ[K] W) w₀ = w₀ + (δ t : W) := by
      rw [hδcoe]; abel
    rw [hs, ht, hsw, htw, hNst, hδ]
  exact Subtype.ext heq

theorem card_le_of_commute_of_flag {K W : Type*} [Field K] [Finite K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (A : Subgroup (W ≃ₗ[K] W))
    (hA : ∀ s ∈ A, ∀ t ∈ A, s * t = t * s) {H ℓ : Submodule K W}
    (hH : Module.finrank K H + 1 = Module.finrank K W) (hℓ : Module.finrank K ℓ ≤ 1)
    (hℓH : ℓ ≤ H) (h1 : ∀ t ∈ A, ∀ w, t w - w ∈ H) (h2 : ∀ t ∈ A, ∀ h ∈ H, t h - h ∈ ℓ)
    (h3 : ∀ t ∈ A, ∀ l ∈ ℓ, t l = l) :
    Nat.card A ≤ Nat.card K ^ (Module.finrank K W - 1) := by
  have hHne : H ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top] at hH
    omega
  obtain ⟨w₀, hw₀⟩ := SetLike.exists_not_mem_of_ne_top H hHne rfl
  let δ : A → H := fun t => ⟨(t : W ≃ₗ[K] W) w₀ - w₀, h1 t t.2 w₀⟩
  have hδcoe : ∀ t : A, (δ t : W) = (t : W ≃ₗ[K] W) w₀ - w₀ := fun _ => rfl
  let N : A → H →ₗ[K] H := fun t =>
    (((t : W ≃ₗ[K] W).toLinearMap.comp H.subtype).codRestrict H (fun h => by
      change (t : W ≃ₗ[K] W) (h : W) ∈ H
      have hdh : (t : W ≃ₗ[K] W) (h : W) - (h : W) ∈ H := hℓH (h2 t t.2 h h.2)
      have ht : (t : W ≃ₗ[K] W) (h : W) =
          (h : W) + ((t : W ≃ₗ[K] W) (h : W) - (h : W)) := by abel
      rw [ht]
      exact H.add_mem h.2 hdh)) - LinearMap.id
  have hNcoe : ∀ (t : A) (h : H), (N t h : W) = (t : W ≃ₗ[K] W) h - h := fun _ _ => rfl
  have hD : ∀ s t : A, N s (δ t) = N t (δ s) :=
    apply_delta_comm A hA δ N hδcoe hNcoe
  let ℓH : Submodule K H := ℓ.comap H.subtype
  have hℓHfin : Module.finrank K ℓH ≤ 1 := by
    calc Module.finrank K ℓH = Module.finrank K ℓ :=
          (Submodule.comapSubtypeEquivOfLe hℓH).finrank_eq
      _ ≤ 1 := hℓ
  have h3H : ∀ t ∈ A, ∀ l ∈ ℓH, (t : W ≃ₗ[K] W) (l : W) = (l : W) := by
    intro t ht l hl
    exact h3 t ht (l : W) hl
  let P : Submodule K H := Submodule.span K (Set.range δ) ⊔ ℓH
  have hP : ∀ s t : A, δ s = δ t → ∀ p ∈ P, N s p = N t p := by
    intro s t hst p hp
    exact eqOn_span_delta_sup A δ N hD hNcoe h3H hst p hp
  obtain ⟨C, hPC⟩ := Submodule.exists_isCompl P
  let Nc : A → C →ₗ[K] ℓH := fun t =>
    ((N t).comp C.subtype).codRestrict ℓH (fun c => by
      have hc : ((c : H) : W) ∈ H := (c : H).2
      have h := h2 t t.2 (c : H) hc
      simpa [ℓH, LinearMap.comp_apply, hNcoe t (c : H)] using h)
  let g : A → P × (C →ₗ[K] ℓH) := fun t =>
    (⟨δ t, Submodule.mem_sup_left (Submodule.subset_span ⟨t, rfl⟩)⟩, Nc t)
  have hg : Function.Injective g := by
    intro s t hst
    have hδval : (⟨δ s, Submodule.mem_sup_left (Submodule.subset_span ⟨s, rfl⟩)⟩ : P) =
        ⟨δ t, Submodule.mem_sup_left (Submodule.subset_span ⟨t, rfl⟩)⟩ :=
      congrArg Prod.fst hst
    have hδ : δ s = δ t := congrArg (fun x : P => (x : H)) hδval
    have hNc : Nc s = Nc t := congrArg Prod.snd hst
    have hC : ∀ c ∈ C, N s c = N t c := by
      intro c hc
      have h := congrArg (fun f : C →ₗ[K] ℓH => ((f ⟨c, hc⟩ : ℓH) : W)) hNc
      simpa [Nc, ℓH, LinearMap.codRestrict_apply, LinearMap.comp_apply] using h
    exact eq_of_delta_eq_and_N_eq_on_compl A hH hw₀ δ N hδcoe hNcoe
      hPC.sup_eq_top hP hδ hC
  have hcard : Nat.card A ≤ Nat.card K ^ Module.finrank K H :=
    card_le_pow_of_injective_prod_linearMap (A := A) (P := P) (C := C) (ℓ := ℓH)
      hPC hℓHfin g hg
  calc
    Nat.card A ≤ Nat.card K ^ Module.finrank K H := hcard
    _ = Nat.card K ^ (Module.finrank K W - 1) := by
      congr 1
      omega

end CFSG.LinearAlgebra

end
