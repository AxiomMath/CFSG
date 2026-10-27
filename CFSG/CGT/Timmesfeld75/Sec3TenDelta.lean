module

public import CFSG.CGT.Timmesfeld75.Sec3TenBasic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open DihedralGroup

section Quotient

variable {G : Type} [Group G] {T T₁ : Subgroup G}
  [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]

theorem Sec3.centralizes_of_delta [Finite G] (hS : Sec3 T T₁) {n : ℕ} (hn : Odd n) (hn3 : 3 < n)
    (e : ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁) ≃* DihedralGroup n) {κ : G}
    (hκM : ∀ m ∈ cfgM T T₁, κ * m * κ⁻¹ ∈ cfgM T T₁)
    (hκX : ∀ x ∈ T ⊔ T₁, κ * x * κ⁻¹ * x⁻¹ ∈ cfgM T T₁) {u : G}
    (hu : ∀ l ∈ normIn T T₁, κ * l * κ⁻¹ * l⁻¹ = 1 ∨ κ * l * κ⁻¹ * l⁻¹ = u) :
    ∀ m ∈ cfgM T T₁, κ * m * κ⁻¹ = m := by
  have hc := hS.cfg
  have hM : IsElemAbelian 2 (cfgM T T₁) := hc.isElemAbelian_cfgM
  obtain ⟨s, hsX, hss, hsT, hsT₁⟩ := hS.exists_swap
  have hL₁ : normIn T₁ T = conjSubgroup s (normIn T T₁) := by
    have := normIn_conj s T T₁
    rwa [hsT, hsT₁] at this
  have hδM : ∀ m ∈ cfgM T T₁, κ * m * κ⁻¹ * m⁻¹ ∈ cfgM T T₁ := fun m hm =>
    (cfgM T T₁).mul_mem (hκM m hm) ((cfgM T T₁).inv_mem hm)
  have hequi : ∀ x ∈ T ⊔ T₁, ∀ m ∈ cfgM T T₁,
      x * (κ * m * κ⁻¹ * m⁻¹) * x⁻¹ = κ * (x * m * x⁻¹) * κ⁻¹ * (x * m * x⁻¹)⁻¹ := by
    intro x hx m hm
    have hcx := hκX x hx
    have hy : x * (κ * m * κ⁻¹) * x⁻¹ ∈ cfgM T T₁ := hc.conj_mem_cfgM hx (hκM m hm)
    have hcomm := elemAbelian_mul_comm hM hcx hy
    calc x * (κ * m * κ⁻¹ * m⁻¹) * x⁻¹
        = (x * (κ * m * κ⁻¹) * x⁻¹) * (x * m * x⁻¹)⁻¹ := by group
      _ = ((κ * x * κ⁻¹ * x⁻¹) * (x * (κ * m * κ⁻¹) * x⁻¹) * (κ * x * κ⁻¹ * x⁻¹)⁻¹) *
            (x * m * x⁻¹)⁻¹ := by rw [hcomm]; group
      _ = κ * (x * m * x⁻¹) * κ⁻¹ * (x * m * x⁻¹)⁻¹ := by group
  have hval : ∀ m ∈ cfgM T T₁, κ * m * κ⁻¹ * m⁻¹ = 1 ∨ κ * m * κ⁻¹ * m⁻¹ = u ∨
      κ * m * κ⁻¹ * m⁻¹ = s * u * s⁻¹ ∨ κ * m * κ⁻¹ * m⁻¹ = u * (s * u * s⁻¹) := by
    intro m hm
    obtain ⟨l, hl, y, hy, rfl⟩ := hc.mem_cfgM_iff.1 hm
    have hlM : l ∈ cfgM T T₁ := Cfg.normIn_le_cfgM_left T T₁ hl
    have hyM : y ∈ cfgM T T₁ := Cfg.normIn_le_cfgM_right T T₁ hy
    obtain ⟨l', hl', hyeq⟩ := mem_conjSubgroup_iff_exists.1 (hL₁ ▸ hy)
    have hsδ := hequi s hsX l' (Cfg.normIn_le_cfgM_left T T₁ hl')
    rw [← hyeq] at hsδ
    have hcomm := elemAbelian_mul_comm hM ((cfgM T T₁).inv_mem hlM) (hδM _ hyM)
    have hsplit : κ * (l * y) * κ⁻¹ * (l * y)⁻¹ =
        (κ * l * κ⁻¹ * l⁻¹) * (κ * y * κ⁻¹ * y⁻¹) := by
      calc κ * (l * y) * κ⁻¹ * (l * y)⁻¹
          = (κ * l * κ⁻¹) * ((κ * y * κ⁻¹ * y⁻¹) * l⁻¹) := by group
        _ = (κ * l * κ⁻¹) * (l⁻¹ * (κ * y * κ⁻¹ * y⁻¹)) := by rw [← hcomm]
        _ = (κ * l * κ⁻¹ * l⁻¹) * (κ * y * κ⁻¹ * y⁻¹) := by group
    rw [hsplit, ← hsδ]
    rcases hu l hl with h1 | h1 <;> rcases hu l' hl' with h2 | h2 <;> rw [h1, h2] <;> simp
  intro m₀ hm₀
  by_contra hne
  set V : Set G := {w | w ≠ 1 ∧ ∃ m ∈ cfgM T T₁, w = κ * m * κ⁻¹ * m⁻¹} with hV
  have hw₀ : κ * m₀ * κ⁻¹ * m₀⁻¹ ∈ V := by
    refine ⟨fun h => hne ?_, m₀, hm₀, rfl⟩
    have : κ * m₀ * κ⁻¹ = m₀ := by
      calc κ * m₀ * κ⁻¹ = (κ * m₀ * κ⁻¹ * m₀⁻¹) * m₀ := by group
        _ = m₀ := by rw [h, one_mul]
    exact this
  have hVM : ∀ w ∈ V, w ∈ cfgM T T₁ ∧ w ≠ 1 := by
    rintro w ⟨hw1, m, hm, rfl⟩
    exact ⟨hδM m hm, hw1⟩
  have hVinv : ∀ x ∈ T ⊔ T₁, ∀ w ∈ V, x * w * x⁻¹ ∈ V := by
    rintro x hx w ⟨hw1, m, hm, rfl⟩
    refine ⟨fun h => hw1 ?_, x * m * x⁻¹, hc.conj_mem_cfgM hx hm, hequi x hx m hm⟩
    calc κ * m * κ⁻¹ * m⁻¹ = x⁻¹ * (x * (κ * m * κ⁻¹ * m⁻¹) * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  have hsub : V ⊆ {u, s * u * s⁻¹, u * (s * u * s⁻¹)} := by
    rintro w ⟨hw1, m, hm, rfl⟩
    rcases hval m hm with h | h | h | h
    · exact absurd h hw1
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hcard := hS.card_le_of_invariant_dihedral hn e hVM hVinv hw₀
  have h3 : V.ncard ≤ 3 := by
    refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
    refine (Set.ncard_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
    rw [Set.ncard_singleton]
  omega

end Quotient

end CFSG.CGT.Timmesfeld75
