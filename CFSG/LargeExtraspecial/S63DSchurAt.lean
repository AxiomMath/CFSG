module

public import CFSG.LargeExtraspecial.S63CD4At
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LargeExtraspecial.S63

open Subgroup

structure AdmAt {H : Type*} [Group H] (s : H) (N : Subgroup H) : Prop where
  le_centralizer : N ≤ centralizer ({s} : Set H)
  conj_mem : ∀ c ∈ centralizer ({s} : Set H), ∀ n ∈ N, c * n * c⁻¹ ∈ N
  isPGroup : IsPGroup 2 N
  mem : s ∈ N
  center_le : ∀ n ∈ N, (∀ m ∈ N, n * m = m * n) → n = 1 ∨ n = s
  card : 2 ^ 5 ≤ Nat.card N

theorem AdmAt.map {H H' : Type*} [Group H] [Group H'] (e : H ≃* H') {s : H} {N : Subgroup H}
    (h : AdmAt s N) : AdmAt (e s) (N.map e.toMonoidHom) := by
  have hC := map_centralizer_singleton e s
  have hf : Function.Injective e.toMonoidHom := e.injective
  refine ⟨?_, ?_, h.isPGroup.map _, ⟨s, h.mem, rfl⟩, ?_, ?_⟩
  · rw [← hC]
    exact map_mono h.le_centralizer
  · intro c hc n hn
    rw [← hC] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    obtain ⟨n', hn', rfl⟩ := hn
    exact ⟨c' * n' * c'⁻¹, h.conj_mem c' hc' n' hn', by simp⟩
  · rintro _ ⟨n, hn, rfl⟩ hcomm
    have hn' : ∀ m ∈ N, n * m = m * n := by
      intro m hm
      apply e.injective
      have := hcomm (e m) ⟨m, hm, rfl⟩
      simpa using this
    rcases h.center_le n hn hn' with h0 | h0
    · left; simp [h0]
    · right; simp [h0]
  · rw [card_map_of_injective hf]
    exact h.card

@[expose] def D42SplitAt (H : Type*) [Group H] (s : H) : Prop :=
  ∀ N : Subgroup H, AdmAt s N → ∃ x₁ x₂ x₃ y : H,
    x₁ ∈ centralizer ({s} : Set H) ∧ x₂ ∈ centralizer ({s} : Set H) ∧
    x₃ ∈ centralizer ({s} : Set H) ∧ Commute x₁ x₂ ∧ Commute x₁ x₃ ∧ Commute x₂ x₃ ∧
    y * x₁ * y⁻¹ = x₂ ∧ y * x₂ * y⁻¹ = x₃ ∧ y * x₃ * y⁻¹ = x₂ * x₁ ∧
    Odd (N ⊔ closure ({x₁, x₂, x₃} : Set H)).index

@[expose] def D42SplitInput : Prop :=
  ∀ (Y : Type) [Group Y], Blueprint.LieModel Y .trialityD4 0 2 1 →
    ∀ s : Y, orderOf s = 2 → D42SplitAt Y s

theorem mem_centralizer_symm_apply {H H' : Type*} [Group H] [Group H'] (e : H ≃* H') {s : H}
    {x : H'} (hx : x ∈ centralizer ({e s} : Set H')) : e.symm x ∈ centralizer ({s} : Set H) := by
  rw [mem_centralizer_singleton_iff] at hx ⊢
  apply e.injective
  simpa using hx

theorem conj_symm_apply {H H' : Type*} [Group H] [Group H'] (e : H ≃* H') {x y z : H'}
    (h : y * x * y⁻¹ = z) : e.symm y * e.symm x * (e.symm y)⁻¹ = e.symm z := by
  rw [← map_inv, ← map_mul, ← map_mul, h]

theorem D42SplitAt.of_mulEquiv {H H' : Type*} [Group H] [Group H'] (e : H ≃* H') {s : H}
    (h : D42SplitAt H' (e s)) : D42SplitAt H s := by
  intro N hN
  obtain ⟨x₁, x₂, x₃, y, h1, h2, h3, c12, c13, c23, r1, r2, r3, hodd⟩ := h _ (hN.map e)
  refine ⟨e.symm x₁, e.symm x₂, e.symm x₃, e.symm y, mem_centralizer_symm_apply e h1,
    mem_centralizer_symm_apply e h2, mem_centralizer_symm_apply e h3, c12.map e.symm,
    c13.map e.symm, c23.map e.symm, conj_symm_apply e r1, conj_symm_apply e r2, ?_, ?_⟩
  · rw [conj_symm_apply e r3, map_mul]
  · have hmap : (N ⊔ closure ({e.symm x₁, e.symm x₂, e.symm x₃} : Set H)).map e.toMonoidHom =
        N.map e.toMonoidHom ⊔ closure ({x₁, x₂, x₃} : Set H') := by
      rw [Subgroup.map_sup, MonoidHom.map_closure]
      congr 2
      simp [Set.image_insert_eq, Set.image_singleton]
    have hker : e.toMonoidHom.ker ≤ N ⊔ closure ({e.symm x₁, e.symm x₂, e.symm x₃} : Set H) := by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
      exact bot_le
    rw [← index_map_eq _ e.surjective hker, hmap]
    exact hodd

theorem D42SplitAt.conj {H : Type*} [Group H] {x : H} (h : D42SplitAt H x) (g : H) :
    D42SplitAt H (g * x * g⁻¹) := by
  refine D42SplitAt.of_mulEquiv (MulAut.conj g⁻¹) ?_
  rw [MulAut.conj_apply, inv_inv, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
  exact h

end CFSG.LargeExtraspecial.S63
