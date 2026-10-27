module

import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs

public section

namespace CFSG.GroupTheory.StronglyClosedTI

open Subgroup

variable {G : Type*} [Group G]

section Frattini

variable [Finite G]

theorem normalizer_inf_le_normalizer (S : Sylow 2 G) {Y M : Subgroup G}
    (hYS : Y ≤ (S : Subgroup G)) (hYM : Y ≤ M)
    (hsc : ∀ a ∈ Y, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g ∈ Y) :
    normalizer (((S : Subgroup G) ⊓ M : Subgroup G) : Set G) ≤ normalizer (Y : Set G) := by
  have key : ∀ g ∈ normalizer (((S : Subgroup G) ⊓ M : Subgroup G) : Set G), ∀ y ∈ Y,
      g * y * g⁻¹ ∈ Y := by
    intro g hg y hy
    have h1 : g * y * g⁻¹ ∈ (S : Subgroup G) ⊓ M :=
      (mem_normalizer_iff.mp hg y).mp ⟨hYS hy, hYM hy⟩
    have h2 := hsc y hy g⁻¹ (by rw [inv_inv]; exact h1.1)
    simpa using h2
  intro g hg
  rw [mem_normalizer_iff]
  intro y
  constructor
  · exact key g hg y
  · intro h
    have := key g⁻¹ (inv_mem hg) _ h
    simpa [mul_assoc] using this

theorem sup_normalizer_eq_top (S : Sylow 2 G) {Y M : Subgroup G} [M.Normal]
    (hYS : Y ≤ (S : Subgroup G)) (hYM : Y ≤ M)
    (hsc : ∀ a ∈ Y, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g ∈ Y) :
    M ⊔ normalizer (Y : Set G) = ⊤ := by
  obtain ⟨P, hP⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal S M
  have h := Sylow.normalizer_sup_eq_top P
  rw [hP] at h
  rw [eq_top_iff, ← h]
  exact sup_le ((normalizer_inf_le_normalizer S hYS hYM hsc).trans le_sup_right) le_sup_left

theorem inf_centralizer_eq_bot {M H N : Subgroup G} [M.Normal] (hO2 : CFSG.pCore 2 G = ⊥)
    (hMH : M ⊔ H = ⊤) (hHN : H ≤ normalizer (N : Set G)) (hN2 : ∀ x ∈ N, x * x = 1) :
    N ⊓ centralizer (M : Set G) = ⊥ := by
  set K := N ⊓ centralizer (M : Set G) with hK
  have hKn : K.Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff, ← hMH]
    refine sup_le ?_ ?_
    · intro m hm
      rw [mem_normalizer_iff]
      intro k
      constructor
      · intro hk
        have h1 : m * k = k * m := (mem_centralizer_iff.mp hk.2 m hm)
        rwa [h1, mul_inv_cancel_right]
      · intro hk
        have h1 : m * (m * k * m⁻¹) = m * k * m⁻¹ * m := mem_centralizer_iff.mp hk.2 m hm
        have h2 : m * k * m⁻¹ = k := by
          have h3 : m * (m * k * m⁻¹) = m * k := by rw [h1]; group
          exact mul_left_cancel h3
        rw [← h2]
        exact hk
    · intro h hh
      have hC : h ∈ normalizer (centralizer (M : Set G) : Set G) := by
        rw [normalizer_eq_top_iff.mpr (inferInstance : (centralizer (M : Set G)).Normal)]
        exact mem_top h
      rw [mem_normalizer_iff]
      intro k
      rw [mem_inf, mem_inf, ← mem_normalizer_iff.mp (hHN hh) k, ← mem_normalizer_iff.mp hC k]
  have hK2 : IsPGroup 2 K := fun k => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (hN2 _ k.2.1)⟩
  have hle : K ≤ CFSG.pCore 2 G := le_sSup ⟨hKn, hK2⟩
  rw [hO2] at hle
  exact le_bot_iff.mp hle

end Frattini

section Centralizer

theorem conj_eq_of_mem {C : Subgroup G} (hCodd : Odd (Nat.card C)) {v g : G} (hv : v * v = 1)
    (hCv : ∀ c ∈ C, c * v = v * c) (hg : v⁻¹ * (g * v * g⁻¹) ∈ C) : g * v * g⁻¹ = v := by
  set o := v⁻¹ * (g * v * g⁻¹) with ho
  have hov : o * v = v * o := hCv o hg
  have hgv : g * v * g⁻¹ = v * o := by rw [ho]; group
  have ho2 : o * o = 1 := by
    have h1 : (g * v * g⁻¹) * (g * v * g⁻¹) = 1 := by
      calc (g * v * g⁻¹) * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
        _ = 1 := by rw [hv]; group
    rw [hgv] at h1
    calc o * o = v * v * (o * o) := by rw [hv, one_mul]
      _ = v * (v * o) * o := by group
      _ = v * (o * v) * o := by rw [hov]
      _ = v * o * (v * o) := by group
      _ = 1 := h1
  have ho1 : o = 1 := by
    have h2 : orderOf o ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ho2)
    have h3 := Nat.dvd_gcd h2 (Subgroup.orderOf_dvd_natCard C hg)
    rw [(Nat.coprime_two_left.mpr hCodd).gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3
  rw [hgv, ho1, mul_one]

theorem mem_centralizer_closure {s : Set G} (hs : ∀ v ∈ s, v * v = 1) {C : Subgroup G}
    (hCodd : Odd (Nat.card C)) (hCs : ∀ c ∈ C, ∀ v ∈ s, c * v = v * c) {g : G}
    (hg : ∀ v ∈ s, v⁻¹ * (g * v * g⁻¹) ∈ C) : g ∈ centralizer (closure s : Set G) := by
  rw [mem_centralizer_iff]
  intro x hx
  have hle : closure s ≤ centralizer ({g} : Set G) := by
    rw [closure_le]
    intro v hv
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have := conj_eq_of_mem hCodd (hs v hv) (fun c hc => hCs c hc v hv) (hg v hv)
    exact mul_inv_eq_iff_eq_mul.mp this
  exact (mem_centralizer_iff.mp (hle hx) g rfl).symm

end Centralizer

end CFSG.GroupTheory.StronglyClosedTI

end
