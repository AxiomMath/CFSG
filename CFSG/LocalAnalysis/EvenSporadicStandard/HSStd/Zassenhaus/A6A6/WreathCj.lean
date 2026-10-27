module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.Config

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

open Subgroup

variable {G : Type} [Group G]

@[expose] def cj (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

theorem mem_cj {g : G} {H : Subgroup G} {y : G} : y ∈ cj g H ↔ g⁻¹ * y * g ∈ H := by
  unfold cj
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem card_cj (g : G) (H : Subgroup G) : Nat.card (cj g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem cj_inv_cj (g : G) (H : Subgroup G) : cj g⁻¹ (cj g H) = H := by
  ext y
  rw [mem_cj, mem_cj]
  simp [mul_assoc]

theorem sup_mem_normalizer {C D : Subgroup G} (hcomm : ∀ x ∈ C, ∀ y ∈ D, x * y = y * x) :
    ∀ k ∈ C ⊔ D, ∀ n, n ∈ C ↔ k * n * k⁻¹ ∈ C := by
  intro k hk
  have h1 : C ≤ normalizer (C : Set G) := by
    intro k hk n
    constructor
    · intro hn
      exact mul_mem (mul_mem hk hn) (inv_mem hk)
    · intro h
      have := mul_mem (mul_mem (inv_mem hk) h) hk
      simpa [mul_assoc] using this
  have h2 : D ≤ normalizer (C : Set G) := by
    intro k hk n
    constructor
    · intro hn
      have h := hcomm n hn k hk
      have e : k * n * k⁻¹ = n := by rw [← h]; simp
      rw [e]
      exact hn
    · intro h
      have hc := hcomm _ h k⁻¹ (inv_mem hk)
      have e : n = k * n * k⁻¹ := by
        calc n = k⁻¹ * (k * n * k⁻¹) * k := by group
          _ = (k * n * k⁻¹) * k⁻¹ * k := by rw [← hc]
          _ = k * n * k⁻¹ := by group
      rw [e]
      exact h
  exact (sup_le h1 h2 : C ⊔ D ≤ normalizer (C : Set G)) hk

theorem inf_eq_bot_or_le {X Y K : Subgroup G} [IsSimpleGroup Y] (hY : Y ≤ K)
    (hX : ∀ k ∈ K, ∀ n ∈ X, k * n * k⁻¹ ∈ X) : X ⊓ Y = ⊥ ∨ Y ≤ X := by
  have hN : ((X ⊓ Y).subgroupOf Y).Normal := by
    rw [normal_subgroupOf_iff inf_le_right]
    intro h k hh hk
    exact Subgroup.mem_inf.2 ⟨hX k (hY hk) h hh.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hh.2) (Subgroup.inv_mem _ hk)⟩
  rcases Subgroup.Normal.eq_bot_or_eq_top ((X ⊓ Y).subgroupOf Y) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, (Subgroup.mem_inf.1 hx).2⟩ : Y) ∈ (X ⊓ Y).subgroupOf Y := hx
    rw [h, Subgroup.mem_bot] at hx'
    have := congrArg Subtype.val hx'
    exact (Subgroup.mem_bot).2 this
  · right
    intro y hy
    have : (⟨y, hy⟩ : Y) ∈ (X ⊓ Y).subgroupOf Y := by rw [h]; trivial
    exact (Subgroup.mem_inf.1 this).1

theorem comm_of_inf_eq_bot {X Y K : Subgroup G} (hXK : X ≤ K) (hYK : Y ≤ K)
    (hX : ∀ k ∈ K, ∀ n ∈ X, k * n * k⁻¹ ∈ X) (hY : ∀ k ∈ K, ∀ n ∈ Y, k * n * k⁻¹ ∈ Y)
    (h : X ⊓ Y = ⊥) : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := by
  intro x hx y hy
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ X ⊓ Y := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have := Subgroup.mul_mem _ hx (hX y (hYK hy) x⁻¹ (Subgroup.inv_mem _ hx))
      simpa [mul_assoc] using this
    · exact Subgroup.mul_mem _ (hY x (hXK hx) y hy) (Subgroup.inv_mem _ hy)
  rw [h, Subgroup.mem_bot] at h1
  calc x * y = (x * y * x⁻¹ * y⁻¹) * y * x := by group
    _ = y * x := by rw [h1]; simp

theorem cj_eq_or [Finite G] {C D : Subgroup G} [IsSimpleGroup C] [IsSimpleGroup D]
    (hcomm : ∀ x ∈ C, ∀ y ∈ D, x * y = y * x) (hcard : Nat.card C = Nat.card D)
    (hnc : ∃ x ∈ C, ∃ y ∈ C, x * y ≠ y * x) (hKn : (C ⊔ D).Normal) (g : G) :
    cj g C = C ∨ cj g C = D := by
  have hCK : C ≤ C ⊔ D := le_sup_left
  have hDK : D ≤ C ⊔ D := le_sup_right
  have hXK : cj g C ≤ C ⊔ D := by
    intro y hy
    rw [mem_cj] at hy
    have := hKn.conj_mem _ (hCK hy) g
    simpa [mul_assoc] using this
  have hXn : ∀ k ∈ C ⊔ D, ∀ n ∈ cj g C, k * n * k⁻¹ ∈ cj g C := by
    intro k hk n hn
    rw [mem_cj] at hn ⊢
    have hk' : g⁻¹ * k * g ∈ C ⊔ D := by
      have := hKn.conj_mem k hk g⁻¹
      simpa [mul_assoc] using this
    have := (sup_mem_normalizer hcomm _ hk' _).1 hn
    simpa [mul_assoc] using this
  have hCn : ∀ k ∈ C ⊔ D, ∀ n ∈ C, k * n * k⁻¹ ∈ C := fun k hk n hn =>
    (sup_mem_normalizer hcomm k hk n).1 hn
  have hDn : ∀ k ∈ C ⊔ D, ∀ n ∈ D, k * n * k⁻¹ ∈ D := by
    have h' : ∀ x ∈ D, ∀ y ∈ C, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
    have hsw : D ⊔ C = C ⊔ D := sup_comm D C
    intro k hk n hn
    rw [← hsw] at hk
    exact (sup_mem_normalizer h' k hk n).1 hn
  have hcX : Nat.card (cj g C) = Nat.card C := card_cj g C
  rcases inf_eq_bot_or_le hCK hXn with hC | hC
  · rcases inf_eq_bot_or_le hDK hXn with hD | hD
    · exfalso
      have h1 := comm_of_inf_eq_bot hXK hCK hXn hCn hC
      have h2 := comm_of_inf_eq_bot hXK hDK hXn hDn hD
      obtain ⟨x, hx, y, hy, hxy⟩ := hnc
      have hgx : g * x * g⁻¹ ∈ cj g C := by
        rw [mem_cj]; simpa [mul_assoc] using hx
      have hgy : g * y * g⁻¹ ∈ cj g C := by
        rw [mem_cj]; simpa [mul_assoc] using hy
      have hK : C ⊔ D ≤ centralizer ({g * y * g⁻¹} : Set G) := by
        refine sup_le (fun z hz => ?_) (fun z hz => ?_)
        · rw [Subgroup.mem_centralizer_iff]
          intro h hh
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact h1 _ hgy z hz
        · rw [Subgroup.mem_centralizer_iff]
          intro h hh
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact h2 _ hgy z hz
      have hc := (Subgroup.mem_centralizer_iff.1 (hK (hXK hgx))) _ rfl
      apply hxy
      have hc' : g * y * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * y * g⁻¹) := hc
      have e1 : g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
      have e2 : g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
      rw [e1, e2] at hc'
      exact (mul_left_cancel (mul_right_cancel hc')).symm
    · right
      exact (Subgroup.eq_of_le_of_card_ge hD (by rw [hcX, hcard])).symm
  · left
    exact (Subgroup.eq_of_le_of_card_ge hC (by rw [hcX])).symm

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6
