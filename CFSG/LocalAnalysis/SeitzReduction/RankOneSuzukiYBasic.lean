module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.SeitzReduction.RankOneEndingsTransfer
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiCoordsAut
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiStartBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

section Cand

variable {K : Type*} [Field K]

@[expose] def szCand (a : ℕ) (c : K) : Set (K × K × K) :=
  {z | z.2.2 = 1 ∧ z.1 ^ (2 ^ (a + 1) + 1) + (c + 1) * z.2.1 = 0}

theorem mem_szCand {a : ℕ} {c : K} {z : K × K × K} :
    z ∈ szCand a c ↔ z.2.2 = 1 ∧ z.1 ^ (2 ^ (a + 1) + 1) + (c + 1) * z.2.1 = 0 :=
  Iff.rfl

theorem ncard_szCand [Fintype K] (a : ℕ) (c : K) : (szCand a c).ncard = Fintype.card K := by
  by_cases hc : c + 1 = 0
  · have heq : szCand a c = Set.range fun r : K => ((0 : K), r, (1 : K)) := by
      ext ⟨s, r, e⟩
      simp only [mem_szCand, hc, zero_mul, add_zero, Set.mem_range, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, hs⟩
        exact ⟨r, (pow_eq_zero_iff (Nat.succ_ne_zero _)).mp hs ▸ rfl, rfl, rfl⟩
      · rintro ⟨r', rfl, rfl, rfl⟩
        exact ⟨rfl, zero_pow (Nat.succ_ne_zero _)⟩
    rw [heq, Set.ncard_range_of_injective, Nat.card_eq_fintype_card]
    intro r r' h
    simpa using h
  · have heq : szCand a c =
        Set.range fun s : K => (s, -(s ^ (2 ^ (a + 1) + 1)) / (c + 1), (1 : K)) := by
      ext ⟨s, r, e⟩
      simp only [mem_szCand, Set.mem_range, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, hs⟩
        refine ⟨s, rfl, ?_, rfl⟩
        field_simp
        linear_combination -hs
      · rintro ⟨s', rfl, rfl, rfl⟩
        refine ⟨rfl, ?_⟩
        field_simp
        ring
    rw [heq, Set.ncard_range_of_injective, Nat.card_eq_fintype_card]
    intro s s' h
    simpa using congrArg Prod.fst h

theorem exists_szTorusSmul_eq_of_mem_szCand [Fintype K] {a : ℕ}
    (hK : Fintype.card K = 2 ^ (2 * a + 1)) {c : K} {z z' : K × K × K} (hz : z ∈ szCand a c)
    (hz' : z' ∈ szCand a c) (hz0 : z ≠ (0, 0, 1)) (hz0' : z' ≠ (0, 0, 1)) :
    ∃ l : K, l ≠ 0 ∧ szTorusSmul a l z = z' := by
  obtain ⟨s, r, e⟩ := z
  obtain ⟨s', r', e'⟩ := z'
  obtain ⟨he, hs⟩ := hz
  obtain ⟨he', hs'⟩ := hz'
  simp only at he he' hs hs'
  subst he he'
  by_cases hc : c + 1 = 0
  · rw [hc, zero_mul, add_zero] at hs hs'
    have hs0 : s = 0 := (pow_eq_zero_iff (Nat.succ_ne_zero _)).mp hs
    have hs0' : s' = 0 := (pow_eq_zero_iff (Nat.succ_ne_zero _)).mp hs'
    subst hs0 hs0'
    have hr : r ≠ 0 := fun h => hz0 (by rw [h])
    have hr' : r' ≠ 0 := fun h => hz0' (by rw [h])
    obtain ⟨l, hl⟩ := SzStartField.exists_pow_theta_succ_eq hK (r' / r)
    have hl0 : l ≠ 0 := by
      rintro rfl
      rw [zero_pow (Nat.succ_ne_zero _)] at hl
      exact div_ne_zero hr' hr hl.symm
    refine ⟨l, hl0, ?_⟩
    simp only [szTorusSmul, mul_zero, hl, Prod.mk.injEq, true_and, and_true]
    field_simp
  · have hsr : ∀ {s r : K}, s ^ (2 ^ (a + 1) + 1) + (c + 1) * r = 0 → s = 0 → r = 0 := by
      intro s r h hs0
      rw [hs0, zero_pow (Nat.succ_ne_zero _), zero_add] at h
      exact (mul_eq_zero.mp h).resolve_left hc
    have hs0 : s ≠ 0 := fun h => hz0 (by rw [h, hsr hs h])
    have hs0' : s' ≠ 0 := fun h => hz0' (by rw [h, hsr hs' h])
    refine ⟨s' / s, div_ne_zero hs0' hs0, ?_⟩
    simp only [szTorusSmul, Prod.mk.injEq, and_true]
    refine ⟨by field_simp, ?_⟩
    have key : (c + 1) * ((s' / s) ^ (2 ^ (a + 1) + 1) * r) = (c + 1) * r' := by
      have e1 : (c + 1) * ((s' / s) ^ (2 ^ (a + 1) + 1) * r) =
          (s' / s) ^ (2 ^ (a + 1) + 1) * ((c + 1) * r) := by ring
      rw [e1, show (c + 1) * r = -(s ^ (2 ^ (a + 1) + 1)) by linear_combination hs,
        show (c + 1) * r' = -(s' ^ (2 ^ (a + 1) + 1)) by linear_combination hs', div_pow]
      field_simp
    exact mul_left_cancel₀ hc key

end Cand

theorem exists_smul_eq_smul_eq_of_stabilizer {H X : Type*} [Group H] [MulAction H X] (x₀ : X)
    (htrans : ∀ x : X, ∃ g : H, g • x₀ = x)
    (hstab : ∀ x y : X, x ≠ x₀ → y ≠ x₀ → ∃ g : H, g • x₀ = x₀ ∧ g • x = y)
    {a b c d : X} (hab : a ≠ b) (hcd : c ≠ d) : ∃ g : H, g • a = c ∧ g • b = d := by
  obtain ⟨g₁, hg₁⟩ := htrans a
  obtain ⟨g₂, hg₂⟩ := htrans c
  have h1 : g₁⁻¹ • b ≠ x₀ := fun h => hab (by rw [← hg₁, ← h, smul_inv_smul])
  have h2 : g₂⁻¹ • d ≠ x₀ := fun h => hcd (by rw [← hg₂, ← h, smul_inv_smul])
  obtain ⟨n, hn₀, hn⟩ := hstab _ _ h1 h2
  refine ⟨g₂ * n * g₁⁻¹, ?_, ?_⟩
  · rw [mul_smul, mul_smul, ← hg₁, inv_smul_smul, hn₀, hg₂]
  · rw [mul_smul, mul_smul, hn, smul_inv_smul]

theorem relIndex_sup_zpowers_eq_two_of_mul_self_mem {G : Type*} [Group G] {W : Subgroup G}
    {g : G} (hgW : g ∉ W) (hgN : g ∈ normalizer (W : Set G)) (hg2 : g * g ∈ W) :
    W.relIndex (W ⊔ zpowers g) = 2 := by
  rw [relIndex_eq_two_iff]
  refine ⟨g, mem_sup_right (mem_zpowers g), fun b hb => ?_⟩
  obtain ⟨w, hw, z, hz, rfl⟩ := Endings.exists_mul_eq_of_mem_sup (zpowers_le.mpr hgN) hb
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
  have hpow : ∀ j : ℤ, g ^ (2 * j) ∈ W := fun j => by
    rw [zpow_mul, zpow_two]
    exact zpow_mem hg2 j
  rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have hb' : w * g ^ (2 * j) ∈ W := mul_mem hw (hpow j)
    refine Or.inr ⟨hb', fun h => hgW ?_⟩
    have e' : g = (w * g ^ (2 * j))⁻¹ * (w * g ^ (2 * j) * g) := by group
    rw [e']
    exact mul_mem (inv_mem hb') h
  · have e : w * g ^ (2 * j + 1) * g = w * g ^ (2 * j) * (g * g) := by
      rw [zpow_add, zpow_one]
      group
    refine Or.inl ⟨by rw [e]; exact mul_mem (mul_mem hw (hpow j)) hg2, fun h => hgW ?_⟩
    have e' : g = (w * g ^ (2 * j))⁻¹ * (w * g ^ (2 * j + 1)) := by
      rw [zpow_add, zpow_one]
      group
    rw [e']
    exact mul_mem (inv_mem (mul_mem hw (hpow j))) h

section Coords

variable {G : Type*} [Group G] {K : Type*} [Field K] [CharP K 2] {T₁ R₂ : Subgroup G}
  {t d : G} {a : ℕ} {u v : G → K} {φ : G → K × K × K} {γ c : K}

theorem SzRCoords2.card_R₂ [Fintype K] (hS : SzR2 T₁ R₂ t d)
    (h : SzRCoords2 T₁ R₂ t a u v φ γ c) :
    Nat.card R₂ = Fintype.card K * Nat.card (szA₁ T₁) := by
  have hR₂ : ∀ r ∈ R₂, r ∈ szR T₁ R₂ t := fun r hr => le_szR_mid T₁ R₂ t hr
  let ρ : R₂ →* Multiplicative K :=
    { toFun := fun r => Multiplicative.ofAdd (φ r).2.1
      map_one' := by
        show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
        rw [OneMemClass.coe_one, h.map_one]
        rfl
      map_mul' := fun r r' => by
        rw [← ofAdd_add, Subgroup.coe_mul, h.mul _ (hR₂ _ r.2) _ (hR₂ _ r'.2)]
        rfl }
  have hsurj : Function.Surjective ρ := by
    intro w
    obtain ⟨b, hb, hbw⟩ := h.v_surj (Multiplicative.toAdd w)
    obtain ⟨r, hr, hrb⟩ := hS.rho_surj b hb
    refine ⟨⟨r, hr⟩, ?_⟩
    show Multiplicative.ofAdd _ = w
    rw [h.snd_eq r (hR₂ r hr), hrb, hbw, ofAdd_toAdd]
  have hker : ρ.ker = (szA₁ T₁).subgroupOf R₂ := by
    ext r
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro hr
      have h0 : (φ r).2.1 = 0 := by
        have h1 := congrArg Multiplicative.toAdd hr
        simpa [ρ] using h1
      rw [h.snd_eq r (hR₂ r r.2)] at h0
      exact hS.rho_ker r r.2 (h.v_inj _ (hS.rho_mem r r.2) h0)
    · intro hr
      show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
      rw [(h.ker r (hR₂ r r.2)).mpr hr]
      rfl
  have h1 := Subgroup.card_mul_index ρ.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hker,
    Nat.card_congr (subgroupOfEquivOfLe hS.le_R₂).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K),
    Nat.card_eq_fintype_card (α := K)] at h1
  rw [← h1, mul_comm]

end Coords

end CFSG.SeitzReduction.RankOne
