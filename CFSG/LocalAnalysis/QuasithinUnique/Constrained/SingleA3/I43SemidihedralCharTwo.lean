module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

private theorem centralizer_singleton_eq_normalizer_zpowers_of_orderOf_two {G : Type*} [Group G]
    {z : G} (hz : orderOf z = 2) :
    Subgroup.centralizer ({z} : Set G) =
      Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hg h
    have key : ∀ x ∈ Subgroup.zpowers z, g * x * g⁻¹ = x := by
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hc : Commute g (z ^ k) := (show Commute g z from hg).zpow_right k
      rw [hc.eq, mul_inv_cancel_right]
    have key' : ∀ x ∈ Subgroup.zpowers z, g⁻¹ * x * g = x := by
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hc : Commute g⁻¹ (z ^ k) := (show Commute g z from hg).inv_left.zpow_right k
      rw [hc.eq, inv_mul_cancel_right]
    constructor
    · intro hh
      rw [key h hh]
      exact hh
    · intro hh
      have h1 := key' _ hh
      have e : g⁻¹ * (g * h * g⁻¹) * g = h := by group
      rw [e] at h1
      rw [h1]
      exact hh
  · intro hg
    have hmem : g * z * g⁻¹ ∈ Subgroup.zpowers z := (hg z).mp (Subgroup.mem_zpowers z)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk2 : z ^ k = 1 ∨ z ^ k = z := by
      rw [← zpow_mod_orderOf, hz]
      have : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
      rcases this with h | h
      · left
        rw [h, zpow_zero]
      · right
        rw [h, zpow_one]
    rcases hk2 with h | h
    · exfalso
      rw [h] at hk
      apply hz1
      have h1 : g * z * g⁻¹ = 1 := hk.symm
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    · rw [h] at hk
      calc g * z = (g * z * g⁻¹) * g := by group
        _ = z * g := by rw [← hk]

theorem charTwo_centralizer_of_isSylowTwoOf {G : Type*} [Group G]
    (hev : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G) {T : Subgroup G}
    (hT : IsSylowTwoOf T ⊤) {z : G} (hz : orderOf z = 2)
    (hTz : T ≤ Subgroup.centralizer ({z} : Set G)) :
    CharTwo (Subgroup.centralizer ({z} : Set G)) := by
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  have hloc : IsTwoLocal (Subgroup.centralizer ({z} : Set G)) :=
    ⟨Subgroup.zpowers z, fun h => hz1 (Subgroup.zpowers_eq_bot.mp h),
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one]),
      centralizer_singleton_eq_normalizer_zpowers_of_orderOf_two hz⟩
  exact charTwo_of_isTwoLocal_of_isSylowTwoOf_le hev hT hloc hTz

theorem pPrimeCore_eq_bot_of_charTwo {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (hK : CharTwo K) : CFSG.pPrimeCore 2 K = ⊥ :=
  CFSG.pPrimeCore_eq_bot_of_isCharacteristicP K 2 (EscapingLocal.isCharacteristicP_of_charTwo hK)

private theorem generalizedFitting_normal (Γ : Type*) [Group Γ] :
    (CFSG.generalizedFitting Γ).Normal := by
  rw [CFSG.generalizedFitting_eq_componentClassification]
  exact CFSG.ComponentClassification.GeneralizedFitting.normal Γ

theorem eq_bot_of_normal_isPGroup_of_normal_simple {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ}
    [Fact p.Prime] (F : Subgroup Γ) [F.Normal] [IsSimpleGroup F]
    (hnonab : ∃ x y : F, x * y ≠ y * x) (hcent : Subgroup.centralizer (F : Set Γ) = ⊥)
    (Q : Subgroup Γ) [Q.Normal] (hQ : IsPGroup p Q) : Q = ⊥ := by
  have hdisj : Q ⊓ F = ⊥ := by
    have hnorm : ((Q ⊓ F).subgroupOf F).Normal := inferInstance
    rcases hnorm.eq_bot_or_eq_top with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      have := disjoint_iff.mp h
      rwa [inf_eq_left.mpr inf_le_right] at this
    · exfalso
      rw [Subgroup.subgroupOf_eq_top] at h
      have hFQ : F ≤ Q := fun x hx => (h hx).1
      have hFp : IsPGroup p F := hQ.to_le hFQ
      have : Nontrivial (Subgroup.center F) := hFp.center_nontrivial
      have hc : (Subgroup.center F).Normal := inferInstance
      rcases hc.eq_bot_or_eq_top with h1 | h1
      · obtain ⟨x, hx⟩ := exists_ne (1 : Subgroup.center F)
        apply hx
        have : (x : F) ∈ (⊥ : Subgroup F) := h1 ▸ x.2
        exact Subtype.ext this
      · obtain ⟨a, b, hab⟩ := hnonab
        apply hab
        have ha : a ∈ Subgroup.center F := h1 ▸ Subgroup.mem_top a
        exact (Subgroup.mem_center_iff.mp ha b).symm
  rw [eq_bot_iff, ← hcent]
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 : x * q * x⁻¹ * q⁻¹ ∈ Q :=
    Q.mul_mem (Subgroup.Normal.conj_mem inferInstance q hq x) (Q.inv_mem hq)
  have h2 : x * q * x⁻¹ * q⁻¹ ∈ F := by
    have := F.mul_mem hx (Subgroup.Normal.conj_mem inferInstance x⁻¹ (F.inv_mem hx) q)
    simpa [mul_assoc] using this
  have h3 : x * q * x⁻¹ * q⁻¹ ∈ Q ⊓ F := ⟨h1, h2⟩
  rw [hdisj, Subgroup.mem_bot] at h3
  calc x * q = x * q * x⁻¹ * q⁻¹ * (q * x) := by group
    _ = q * x := by rw [h3, one_mul]

theorem eq_bot_of_normal_isPGroup_of_simple_layer {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ}
    [Fact p.Prime] [IsSimpleGroup (CFSG.generalizedFitting Γ)]
    (hnonab : ∃ x y : CFSG.generalizedFitting Γ, x * y ≠ y * x)
    (hcent : Subgroup.centralizer (CFSG.generalizedFitting Γ : Set Γ) = ⊥)
    (Q : Subgroup Γ) [Q.Normal] (hQ : IsPGroup p Q) : Q = ⊥ := by
  have := generalizedFitting_normal Γ
  exact eq_bot_of_normal_isPGroup_of_normal_simple (CFSG.generalizedFitting Γ) hnonab hcent Q hQ

theorem card_le_two_of_selfCentralizing_normal_two_subgroup {C : Type*} [Group C] [Finite C]
    (Q₀ : Subgroup C) [Q₀.Normal] (hQ₀ : IsPGroup 2 Q₀)
    (hchar : Subgroup.centralizer (Q₀ : Set C) ≤ Q₀)
    {z : C} (hzc : z ∈ Subgroup.center C) (hz : orderOf z = 2)
    (K : Subgroup C) [K.Normal] (hKz : K = Subgroup.zpowers z)
    (hΓ : ∀ Q : Subgroup (C ⧸ K), Q.Normal → IsPGroup 2 Q → Q = ⊥) : Nat.card C ≤ 2 := by
  have hmap : Q₀.map (QuotientGroup.mk' K) = ⊥ := by
    apply hΓ
    · exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective K)
    · exact hQ₀.of_surjective ((QuotientGroup.mk' K).subgroupMap Q₀)
        ((QuotientGroup.mk' K).subgroupMap_surjective Q₀)
  have hQK : Q₀ ≤ K := by
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
  have hcent : (⊤ : Subgroup C) ≤ Subgroup.centralizer (Q₀ : Set C) := by
    intro c _
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : q ∈ Subgroup.center C := (Subgroup.zpowers_le.mpr hzc) (hKz ▸ hQK hq)
    exact (Subgroup.mem_center_iff.mp hq' c).symm
  have htop : Q₀ = ⊤ := top_le_iff.mp (hcent.trans hchar)
  have hCz : (⊤ : Subgroup C) ≤ Subgroup.zpowers z := by
    rw [← htop, ← hKz]
    exact hQK
  calc Nat.card C = Nat.card (⊤ : Subgroup C) := Subgroup.card_top.symm
    _ ≤ Nat.card (Subgroup.zpowers z) := Subgroup.card_le_of_le hCz
    _ = 2 := by rw [Nat.card_zpowers, hz]

end CFSG.QuasithinUnique
