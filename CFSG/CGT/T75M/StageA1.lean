module

public import CFSG.CGT.T75M.SzPair
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.CGT.T75M

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.BenderSuzuki
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

section Basic

variable {T T₁ : Subgroup G}

theorem inf_centralizer_eq_normIn (c : Cfg T T₁) {x : G} (hx : x ∈ normIn T₁ T) (hx1 : x ≠ 1) :
    T ⊓ Subgroup.centralizer ({x} : Set G) = normIn T T₁ := by
  apply le_antisymm
  · rintro y ⟨hyT, hyC⟩
    have hyx : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.1 hyC
    by_cases hyM : y ∈ cfgM T T₁
    · rw [← c.inf_cfgM]; exact ⟨hyT, hyM⟩
    · exfalso
      have hxL : x ∈ normIn T T₁ := by
        rw [← c.cfgM_inf_centralizer hyT hyM]
        exact ⟨Cfg.normIn_le_cfgM_right T T₁ hx,
          Subgroup.mem_centralizer_singleton_iff.2 hyx.symm⟩
      have h : x ∈ T ⊓ T₁ := ⟨normIn_le _ _ hxL, normIn_le _ _ hx⟩
      rw [c.inf, Subgroup.mem_bot] at h
      exact hx1 h
  · intro l hl
    exact ⟨normIn_le _ _ hl, Subgroup.mem_centralizer_singleton_iff.2 (c.comm_L_L₁ hl hx)⟩

theorem inf_centralizer_conj (c : Cfg T T₁) {x : G} (hx : x ∈ normIn T₁ T) (hx1 : x ≠ 1) {h : G}
    (hh : h ∈ Subgroup.normalizer (T : Set G)) :
    T ⊓ Subgroup.centralizer ({h * x * h⁻¹} : Set G) = conjSubgroup h (normIn T T₁) := by
  have hhT : conjSubgroup h T = T := mem_normalizer_iff_conjSubgroup_eq.1 hh
  have key := inf_centralizer_eq_normIn c hx hx1
  ext y
  rw [mem_conjSubgroup, ← key, Subgroup.mem_inf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have hyT : y ∈ T ↔ h⁻¹ * y * h ∈ T := by
    rw [← mem_conjSubgroup, hhT]
  refine and_congr hyT ⟨fun h1 => ?_, fun h1 => ?_⟩
  · calc h⁻¹ * y * h * x = h⁻¹ * (y * (h * x * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * x * h⁻¹) * y) * h := by rw [h1]
      _ = x * (h⁻¹ * y * h) := by group
  · calc y * (h * x * h⁻¹) = h * ((h⁻¹ * y * h) * x) * h⁻¹ := by group
      _ = h * (x * (h⁻¹ * y * h)) * h⁻¹ := by rw [h1]
      _ = (h * x * h⁻¹) * y := by group

end Basic


section Card

variable {T T₁ : Subgroup G}

theorem card_inf_centralizer_conj (c : Cfg T T₁) {x : G} (hx : x ∈ normIn T₁ T) (hx1 : x ≠ 1)
    {h : G} (hh : h ∈ Subgroup.normalizer (T : Set G)) :
    Nat.card ↥(T ⊓ Subgroup.centralizer ({h * x * h⁻¹} : Set G)) = Nat.card (normIn T T₁) := by
  rw [inf_centralizer_conj c hx hx1 hh, card_conjSubgroup]

theorem exists_mul_of_mem_sup_of_commute {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {n : G} (hn : n ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, n = a * b := by
  have hle : A ≤ Subgroup.normalizer (B : Set G) := fun a ha => by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have : a * b * a⁻¹ = b := by rw [hAB a ha b hb]; group
      rw [this]; exact hb
    · intro hb
      have h1 : a⁻¹ * (a * b * a⁻¹) = (a * b * a⁻¹) * a⁻¹ := hAB a⁻¹ (A.inv_mem ha) _ hb
      have h2 : b = a * b * a⁻¹ := by
        calc b = a⁻¹ * (a * b * a⁻¹) * a := by group
          _ = (a * b * a⁻¹) * a⁻¹ * a := by rw [h1]
          _ = a * b * a⁻¹ := by group
      rw [h2]; exact hb
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right A B hle
  have : n ∈ ((A : Set G) * (B : Set G)) := by rw [← hmul]; exact hn
  obtain ⟨a, ha, b, hb, h⟩ := this
  exact ⟨a, ha, b, hb, h.symm⟩

theorem isElemAbelian_sup_of_commute {A B : Subgroup G} (hA : IsElemAbelian 2 A)
    (hB : IsElemAbelian 2 B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian 2 (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB hAB

end Card


section Mech

variable [Finite G] {T T₁ : Subgroup G} {a : ℕ}

omit [Finite G] in
theorem mem_normalizer_sup_of_mem_normalizer {u : G} (huT : u ∈ Subgroup.normalizer (T : Set G))
    (huT₁ : u ∈ Subgroup.normalizer (T₁ : Set G)) :
    u ∈ Subgroup.normalizer ((T ⊔ T₁ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSubgroup_eq, conjSubgroup_sup_eq_sup,
    mem_normalizer_iff_conjSubgroup_eq.1 huT, mem_normalizer_iff_conjSubgroup_eq.1 huT₁]

omit [Finite G] in
theorem mem_normalizer_cfgM_of_mem_normalizer {u : G} (huT : u ∈ Subgroup.normalizer (T : Set G))
    (huT₁ : u ∈ Subgroup.normalizer (T₁ : Set G)) :
    u ∈ Subgroup.normalizer ((cfgM T T₁ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSubgroup_eq, ← cfgM_conj,
    mem_normalizer_iff_conjSubgroup_eq.1 huT, mem_normalizer_iff_conjSubgroup_eq.1 huT₁]

theorem SzData.centralizes_of_normalizes (hD : SzData T T₁ a)
    {u : G} (huT : u ∈ Subgroup.normalizer (T : Set G))
    (huT₁ : u ∈ Subgroup.normalizer (T₁ : Set G)) (hu2 : u * u = 1)
    (hc : Nat.card T ≤ 2 ^ (2 * a + 1) * Nat.card ↥(T ⊓ Subgroup.centralizer ({u} : Set G))) :
    (∀ x ∈ T ⊔ T₁, ⁅u, x⁆ ∈ cfgM T T₁) ∧ ∀ m ∈ cfgM T T₁, m * u = u * m := by
  have huX := mem_normalizer_sup_of_mem_normalizer huT huT₁
  have huM := mem_normalizer_cfgM_of_mem_normalizer huT huT₁
  obtain ⟨y, -, hy, hyM⟩ := hD.exists_comm_of_normalizes huX huM huT hu2
  have hyM' := hyM huT₁
  have hX : ∀ x ∈ T ⊔ T₁, ⁅u, x⁆ ∈ cfgM T T₁ := by
    intro x hx
    have h1 := hy x hx
    have h2 : x * y * x⁻¹ ∈ cfgM T T₁ := hD.sec3.cfg.conj_mem_cfgM hx hyM'
    have e : ⁅u, x⁆ = y⁻¹ * ⁅y * u, x⁆ * (x * y * x⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (cfgM T T₁).mul_mem ((cfgM T T₁).mul_mem ((cfgM T T₁).inv_mem hyM') h1) h2
  refine ⟨hX, hD.comm_of_index_le huM (fun x hx => ?_) hc⟩
  have := (cfgM T T₁).inv_mem (hX x hx)
  rwa [commutatorElement_inv] at this

end Mech

end CFSG.CGT.T75M
