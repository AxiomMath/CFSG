module

public import CFSG.LargeExtraspecial.S14W4LocNoA2
public import CFSG.LargeExtraspecial.S14W4LocRed

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.W4Loc

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.RankThree.OrthogonalInvolutions

variable {X : Type} [Group X] [Finite X] {T : Setting X} {R : Subgroup X}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {π : T.M →* (V ≃ₗ[ZMod 2] V)}

theorem map_Lbar_le_omega (hM8 : WeaklyClosedE8Stmt) (A : Act T R π)
    (hcard : Nat.card T.Qt = 2 ^ 8) (hL : Lat T R) [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 6) {q : QuadraticForm (ZMod 2) V}
    (hq : q.polarBilin.Nondegenerate) (hR : (R.subgroupOf T.M).map π = omegaGroup q hq)
    (hO : ∀ k, π k ∈ TauCeti.QuadraticMap.orthogonalGroup q) {g₀ : X}
    (haQ : g₀ * T.z * g₀⁻¹ ∈ T.QG) (C : Cons311 T g₀) (hw : T.width = 4) :
    ((T.Lbar g₀).subgroupOf T.Mbar).map (πbar T π A.Q_le_ker) ≤ omegaGroup q hq := by
  set f := πbar T π A.Q_le_ker with hfdef
  set Lb := (T.Lbar g₀).subgroupOf T.Mbar with hLb
  have hLM := T.Lbar_le_Mbar g₀
  have hLb2 : IsPGroup 2 Lb :=
    (isPGroup_Lbar T haQ).of_equiv (Subgroup.subgroupOfEquivOfLe hLM).symm
  have hcardLb : Nat.card Lb = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv, C.card_Lbar, hw]
    norm_num
  have hf : ∀ y : T.Mbar, (∃ n : ℕ, y ^ 2 ^ n = 1) → f y = 1 → y = 1 :=
    fun y hy h1 => eq_one_of_πbar_eq_one A hcard hL y hy h1
  refine (hM8 hV hq (H := f.range) (E := Lb.map f) ?_ ?_ (map_le_range f Lb) ?_ ?_ ?_ ?_).2
  · intro x hx
    obtain ⟨r, -, rfl⟩ := Subgroup.mem_map.mp (hR.ge hx)
    exact ⟨⟨T.ρ r, ρ_mem_Mbar r⟩, πbar_ρ A.Q_le_ker r⟩
  · rw [MonoidHom.range_eq_map]
    exact map_πbar_le A.Q_le_ker hO ⊤
  · rw [card_map_πbar A hcard hL Lb hLb2, hcardLb]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Lbar_comm T haQ (Subgroup.mem_subgroupOf.mp ha)
      (Subgroup.mem_subgroupOf.mp hb))
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow]
    have h2 : a ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, pow_two]
      exact mul_self_of_mem_Lbar T haQ (Subgroup.mem_subgroupOf.mp ha))
    rw [h2, map_one]
  · rintro _ ⟨x, rfl⟩ hle
    rw [← map_conj_map]
    refine map_conj_eq_of_weaklyClosed f hf hLb2 (weaklyClosed_Lbar C) x fun a ha => ?_
    exact hle (by rw [← map_conj_map]; exact Subgroup.mem_map_of_mem f ha)

theorem Lbar_mapsTo (hM8 : WeaklyClosedE8Stmt) (A : Act T R π)
    (hcard : Nat.card T.Qt = 2 ^ 8) (hL : Lat T R) [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 6) {q : QuadraticForm (ZMod 2) V}
    (hq : q.polarBilin.Nondegenerate) (hR : (R.subgroupOf T.M).map π = omegaGroup q hq)
    (hO : ∀ k, π k ∈ TauCeti.QuadraticMap.orthogonalGroup q) {g₀ : X}
    (haQ : g₀ * T.z * g₀⁻¹ ∈ T.QG) (C : Cons311 T g₀) (hw : T.width = 4)
    {W : Submodule (ZMod 2) T.Qt} (hWR : W4Dict.IsInv T R W)
    (hWc : ∀ c : T.M, π c = 1 → ∀ v ∈ W, ((T.ρ c : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) v ∈ W) :
    ∀ ℓ ∈ T.Lbar g₀, ∀ v ∈ W, (ℓ : T.Qt ≃ₗ[ZMod 2] T.Qt) v ∈ W := by
  intro ℓ hℓ v hv
  have hLM := T.Lbar_le_Mbar g₀
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp (hLM hℓ)
  subst hk
  have h1 : πbar T π A.Q_le_ker ⟨T.ρ k, ρ_mem_Mbar k⟩ ∈ omegaGroup q hq :=
    map_Lbar_le_omega hM8 A hcard hL hV hq hR hO haQ C hw
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hℓ))
  rw [πbar_ρ] at h1
  obtain ⟨r, hr, he⟩ := Subgroup.mem_map.mp (hR.ge h1)
  have hc : π (r⁻¹ * k) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
  have e : ((T.ρ k : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) v = ((T.ρ r : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt)
      (((T.ρ (r⁻¹ * k) : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) v) := by
    conv_lhs => rw [show k = r * (r⁻¹ * k) by group]
    rw [map_mul]
    rfl
  rw [e]
  exact hWR r hr _ (hWc _ hc v hv)

theorem false_of_cons311_plus (hM8 : WeaklyClosedE8Stmt) (A : Act T R π)
    (hcard : Nat.card T.Qt = 2 ^ 8) [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 6) {q : QuadraticForm (ZMod 2) V}
    (hq : q.polarBilin.Nondegenerate) (hR : (R.subgroupOf T.M).map π = omegaGroup q hq)
    (hO : ∀ k, π k ∈ TauCeti.QuadraticMap.orthogonalGroup q)
    {W₁ W₂ : Submodule (ZMod 2) T.Qt} (h1 : W4Dict.IsInv T R W₁) (h2 : W4Dict.IsInv T R W₂)
    (h12 : W₁ ⊓ W₂ = ⊥) (hc1 : Nat.card W₁ = 2 ^ 4) (hc2 : Nat.card W₂ = 2 ^ 4)
    (hall : ∀ W : Submodule (ZMod 2) T.Qt, W4Dict.IsInv T R W → W = ⊥ ∨ W = W₁ ∨ W = W₂ ∨ W = ⊤)
    {g₀ : X} (H : Hyp4 T g₀) (C : Cons311 T g₀) (hw : T.width = 4) : False := by
  have hL : Lat T R := Or.inr ⟨W₁, W₂, h1, h2, h12, hc1, hc2, hall⟩
  have haQ := H.conj_mem
  have hall' : ∀ W : Submodule (ZMod 2) T.Qt, W4Dict.IsInv T R W →
      W = ⊥ ∨ W = W₂ ∨ W = W₁ ∨ W = ⊤ := fun W hW => by
    rcases hall W hW with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  have hfix : ∀ {W : Submodule (ZMod 2) T.Qt}, W4Dict.IsInv T R W →
      (∀ c : T.M, π c = 1 → ∀ v ∈ W, ((T.ρ c : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) v ∈ W) →
      Nat.card W = 2 ^ 4 → ∃ u ∈ W, u ≠ 0 ∧ u ∈ fixSub T (T.Lbar g₀) := by
    intro W hWR hWc hcW
    have hW0 : W ≠ ⊥ := fun h0 => by
      rw [h0, card_bot_submodule] at hcW
      norm_num at hcW
    obtain ⟨u, huW, hu0, hu⟩ := exists_fixed_of_isPGroup T (isPGroup_Lbar T haQ)
      (Lbar_mapsTo hM8 A hcard hL hV hq hR hO haQ C hw hWR hWc) hW0
    exact ⟨u, huW, hu0, hu⟩
  obtain ⟨u₁, hu₁, hu₁0, hf₁⟩ := hfix h1
    (fun c hc v hv => map_W₁_eq A hcard hL h1 h2 h12 hc1 hc2 hall hc v hv) hc1
  obtain ⟨u₂, hu₂, hu₂0, hf₂⟩ := hfix h2
    (fun c hc v hv => map_W₁_eq A hcard hL h2 h1 (inf_comm W₂ W₁ ▸ h12) hc2 hc1 hall' hc v hv)
    hc2
  rw [H.fixSub_eq] at hf₁ hf₂
  obtain ⟨a₁, rfl⟩ := Submodule.mem_span_singleton.mp hf₁
  obtain ⟨a₂, rfl⟩ := Submodule.mem_span_singleton.mp hf₂
  have hone : ∀ a : ZMod 2, a • T.cl (g₀ * T.z * g₀⁻¹) ≠ 0 →
      a • T.cl (g₀ * T.z * g₀⁻¹) = T.cl (g₀ * T.z * g₀⁻¹) := by
    intro a ha
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases a with rfl | rfl
    · exact absurd (zero_smul _ _) ha
    · exact one_smul _ _
  have hu : T.cl (g₀ * T.z * g₀⁻¹) ∈ W₁ ⊓ W₂ :=
    ⟨hone a₁ hu₁0 ▸ hu₁, hone a₂ hu₂0 ▸ hu₂⟩
  rw [h12] at hu
  exact hu₁0 (by rw [hone a₁ hu₁0]; exact (Submodule.mem_bot (ZMod 2)).mp hu)

end CFSG.LargeExtraspecial.S14.W4Loc
