module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S14Gen
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Gen
public import CFSG.Open.FusionDefs
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Frob

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open

section Gen16

variable {Γ : Type*} [Group Γ]

theorem mem_sup_zpowers_of_normalizes {K : Subgroup Γ} {t : Γ} (ht2 : t * t = 1)
    (htN : ∀ k ∈ K, t * k * t⁻¹ ∈ K) {x : Γ} :
    x ∈ K ⊔ zpowers t ↔ x ∈ K ∨ ∃ k ∈ K, x = k * t := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  constructor
  · intro hx
    let T : Subgroup Γ :=
      { carrier := {x | x ∈ K ∨ ∃ k ∈ K, x = k * t}
        mul_mem' := by
          rintro a b (ha | ⟨k₁, hk₁, rfl⟩) (hb | ⟨k₂, hk₂, rfl⟩)
          · exact Or.inl (K.mul_mem ha hb)
          · exact Or.inr ⟨a * k₂, K.mul_mem ha hk₂, by group⟩
          · exact Or.inr ⟨k₁ * (t * b * t⁻¹), K.mul_mem hk₁ (htN b hb), by group⟩
          · refine Or.inl ?_
            have e : k₁ * t * (k₂ * t) = k₁ * (t * k₂ * t⁻¹) * (t * t) := by group
            rw [e, ht2, mul_one]
            exact K.mul_mem hk₁ (htN k₂ hk₂)
        one_mem' := Or.inl K.one_mem
        inv_mem' := by
          rintro a (ha | ⟨k, hk, rfl⟩)
          · exact Or.inl (K.inv_mem ha)
          · refine Or.inr ⟨t * k⁻¹ * t⁻¹, htN _ (K.inv_mem hk), ?_⟩
            calc (k * t)⁻¹ = t⁻¹ * k⁻¹ := mul_inv_rev k t
              _ = t * k⁻¹ := by rw [hti]
              _ = t * k⁻¹ * t⁻¹ * t := by group }
    have : K ⊔ zpowers t ≤ T :=
      sup_le (fun k hk => Or.inl hk)
        (zpowers_le.2 (Or.inr ⟨1, K.one_mem, by simp⟩))
    exact this hx
  · rintro (h | ⟨k, hk, rfl⟩)
    · exact mem_sup_left h
    · exact mul_mem (mem_sup_left hk) (mem_sup_right (mem_zpowers t))

theorem exists_odd_pow_two_power [Finite Γ] (g : Γ) :
    ∃ m : ℕ, Odd m ∧ ∃ k : ℕ, (g ^ m) ^ (2 ^ k) = 1 := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf g)
    (orderOf_pos g).ne'
  refine ⟨m, hm, k, ?_⟩
  rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]

def sylowOfMaximal {p : ℕ} [Fact p.Prime] (Γ' P : Subgroup Γ) (hPΓ : P ≤ Γ') (hP : IsPGroup p P)
    (hmax : ∀ Q : Subgroup Γ, Q ≤ Γ' → IsPGroup p Q → P ≤ Q → Q = P) : Sylow p ↥Γ' where
  toSubgroup := P.subgroupOf Γ'
  isPGroup' := hP.of_equiv (subgroupOfEquivOfLe hPΓ).symm
  is_maximal' := by
    intro Q' hQ' hle
    have hQ : IsPGroup p (Q'.map Γ'.subtype) :=
      hQ'.of_equiv (Q'.equivMapOfInjective Γ'.subtype Γ'.subtype_injective)
    have hPQ : P ≤ Q'.map Γ'.subtype := by
      intro x hx
      exact ⟨⟨x, hPΓ hx⟩, hle (mem_subgroupOf.2 hx), rfl⟩
    have h := hmax _ (map_subtype_le Q') hQ hPQ
    calc Q' = (Q'.map Γ'.subtype).subgroupOf Γ' :=
          (Subgroup.comap_map_eq_self_of_injective Γ'.subtype_injective Q').symm
      _ = P.subgroupOf Γ' := by rw [h]

theorem exists_conj_mem_St [Finite Γ] {K S : Subgroup Γ} {t : Γ}
    (hS : fusionIsSylowIn 2 S K) (hSt : ∀ s ∈ S, t * s * t⁻¹ ∈ S) (ht2 : t * t = 1)
    (htK : t ∉ K) (htN : ∀ k ∈ K, t * k * t⁻¹ ∈ K) {u : Γ} (hu2 : u * u = 1)
    (hu : ∃ k ∈ K, u = k * t) : ∃ k ∈ K, ∃ s ∈ S, k * u * k⁻¹ = s * t := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSK, hS2, hSmax⟩ := hS
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htS : t ∉ S := fun h => htK (hSK h)
  have ht1 : t ≠ 1 := fun h => htK (h ▸ K.one_mem)
  have hPmem : ∀ x, x ∈ S ⊔ zpowers t ↔ x ∈ S ∨ ∃ s ∈ S, x = s * t := fun x =>
    mem_sup_zpowers_of_normalizes ht2 hSt
  have hΓmem : ∀ x, x ∈ K ⊔ zpowers t ↔ x ∈ K ∨ ∃ k ∈ K, x = k * t := fun x =>
    mem_sup_zpowers_of_normalizes ht2 htN
  have htSN : zpowers t ≤ normalizer (S : Set Γ) := by
    rw [zpowers_le]
    refine mem_normalizer_iff.2 fun h => ⟨fun hh => hSt h hh, fun hh => ?_⟩
    have := hSt _ hh
    have e : t * (t * h * t⁻¹) * t⁻¹ = h := by
      calc t * (t * h * t⁻¹) * t⁻¹ = (t * t) * h * (t * t)⁻¹ := by group
        _ = h := by rw [ht2]; group
    rwa [e] at this
  have hbotS : S ⊓ zpowers t = ⊥ := by
    refine eq_bot_iff.2 fun a ha => ?_
    obtain ⟨haS, haT⟩ := ha
    rcases eq_one_or_of_mem_zpowers ht2 haT with h | h
    · rw [h]; exact one_mem _
    · exact absurd (h ▸ haS) htS
  have hz2 : Nat.card (zpowers t) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1]
  have hPcard : Nat.card (S ⊔ zpowers t : Subgroup Γ) = Nat.card S * 2 := by
    rw [card_sup_of_inf_eq_bot' htSN hbotS, hz2]
  obtain ⟨n, hn⟩ := hS2.exists_card_eq
  have hP2 : IsPGroup 2 (S ⊔ zpowers t : Subgroup Γ) :=
    IsPGroup.of_card (n := n + 1) (by rw [hPcard, hn, pow_succ])
  have hmaxP : ∀ Q : Subgroup Γ, Q ≤ K ⊔ zpowers t → IsPGroup 2 Q → S ⊔ zpowers t ≤ Q →
      Q = S ⊔ zpowers t := by
    intro Q hQΓ hQ2 hPQ
    have htQ : t ∈ Q := hPQ (mem_sup_right (mem_zpowers t))
    have hQK : Q ⊓ K = S :=
      hSmax (Q ⊓ K) inf_le_right (hQ2.to_le inf_le_left)
        (le_inf (le_sup_left.trans hPQ) hSK)
    refine le_antisymm (fun q hq => ?_) hPQ
    rcases (hΓmem q).1 (hQΓ hq) with h | ⟨k, hk, rfl⟩
    · exact mem_sup_left (hQK ▸ ⟨hq, h⟩)
    · have hkQ : k ∈ Q := by
        have := Q.mul_mem hq (Q.inv_mem htQ)
        rwa [show k * t * t⁻¹ = k by group] at this
      exact (hPmem _).2 (Or.inr ⟨k, hQK ▸ ⟨hkQ, hk⟩, rfl⟩)
  let P' : Sylow 2 ↥(K ⊔ zpowers t) :=
    sylowOfMaximal (K ⊔ zpowers t) (S ⊔ zpowers t) (sup_le_sup_right hSK _) hP2 hmaxP
  obtain ⟨k₀, hk₀, hu⟩ := hu
  have huΓ : u ∈ K ⊔ zpowers t := (hΓmem u).2 (Or.inr ⟨k₀, hk₀, hu⟩)
  have hu1 : u ≠ 1 := by
    intro h
    apply htK
    have : t = k₀⁻¹ * u := by rw [hu]; group
    rw [this, h, mul_one]
    exact K.inv_mem hk₀
  have hz2u : Nat.card (zpowers u) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1]
  have hU2 : IsPGroup 2 ((zpowers u).subgroupOf (K ⊔ zpowers t)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.2 huΓ)).toEquiv, hz2u]
    norm_num
  obtain ⟨Q, hQ⟩ := hU2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(K ⊔ zpowers t) Q P'
  have huQ : (⟨u, huΓ⟩ : ↥(K ⊔ zpowers t)) ∈ (Q : Subgroup ↥(K ⊔ zpowers t)) :=
    hQ (mem_subgroupOf.2 (mem_zpowers u))
  have hmem : g * ⟨u, huΓ⟩ * g⁻¹ ∈ (P' : Subgroup ↥(K ⊔ zpowers t)) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ huQ
  have hP' : (P' : Subgroup ↥(K ⊔ zpowers t)) = (S ⊔ zpowers t).subgroupOf (K ⊔ zpowers t) := rfl
  rw [hP', mem_subgroupOf] at hmem
  have hu' : (g : Γ) * u * (g : Γ)⁻¹ ∈ S ⊔ zpowers t := by simpa using hmem
  have key : ∀ (k₁ : Γ), k₁ ∈ K → ∀ v : Γ, (∃ k ∈ K, v = k * t) →
      k₁ * v * k₁⁻¹ ∈ S ⊔ zpowers t → ∃ s ∈ S, k₁ * v * k₁⁻¹ = s * t := by
    intro k₁ hk₁ v ⟨k, hk, hv⟩ hv'
    rcases (hPmem _).1 hv' with h | ⟨s, hs, hs'⟩
    · exfalso
      apply htK
      have h1 : k₁ * v * k₁⁻¹ ∈ K := hSK h
      have e : t = k⁻¹ * (k₁⁻¹ * (k₁ * v * k₁⁻¹) * k₁) := by rw [hv]; group
      rw [e]
      exact K.mul_mem (K.inv_mem hk) (K.mul_mem (K.mul_mem (K.inv_mem hk₁) h1) hk₁)
    · exact ⟨s, hs, hs'⟩
  rcases (hΓmem g).1 g.2 with hgK | ⟨k₁, hk₁, hgk⟩
  · obtain ⟨s, hs, h⟩ := key g hgK u ⟨k₀, hk₀, hu⟩ hu'
    exact ⟨g, hgK, s, hs, h⟩
  ·
    have hu₂ : ∃ k ∈ K, t * u * t⁻¹ = k * t :=
      ⟨t * k₀ * t⁻¹, htN k₀ hk₀, by rw [hu]; group⟩
    have hu'' : k₁ * (t * u * t⁻¹) * k₁⁻¹ ∈ S ⊔ zpowers t := by
      have e : (g : Γ) * u * (g : Γ)⁻¹ = k₁ * (t * u * t⁻¹) * k₁⁻¹ := by rw [hgk]; group
      rwa [e] at hu'
    obtain ⟨s, hs, h⟩ := key k₁ hk₁ _ hu₂ hu''
    refine ⟨t * k₁ * t⁻¹, htN k₁ hk₁, t * s * t⁻¹, hSt s hs, ?_⟩
    calc t * k₁ * t⁻¹ * u * (t * k₁ * t⁻¹)⁻¹
        = t * (k₁ * (t⁻¹ * u * t) * k₁⁻¹) * t⁻¹ := by group
      _ = t * (k₁ * (t * u * t⁻¹) * k₁⁻¹) * t⁻¹ := by rw [hti]
      _ = t * (s * t) * t⁻¹ := by rw [h]
      _ = t * s * t⁻¹ * t := by group

theorem exists_conj_normalizes_sylow [Finite Γ] {p : ℕ} [Fact p.Prime] {Ξ Θ : Subgroup Γ} (hΞΘ : Ξ ≤ Θ)
    (hnorm : ∀ θ ∈ Θ, ∀ ξ ∈ Ξ, θ * ξ * θ⁻¹ ∈ Ξ) {X : Subgroup Γ} (hX : fusionIsSylowIn p X Ξ)
    {θ : Γ} (hθ : θ ∈ Θ) : ∃ ξ ∈ Ξ, ξ * θ ∈ normalizer (X : Set Γ) := by
  obtain ⟨hXΞ, hXp, hXmax⟩ := hX
  have hX' : X.map (MulAut.conj θ).toMonoidHom ≤ Ξ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hnorm θ hθ x (hXΞ hx)
  have hXp' : IsPGroup p (X.map (MulAut.conj θ).toMonoidHom) :=
    hXp.of_equiv (X.equivMapOfInjective _ (MulAut.conj θ).injective)
  have hmax' : ∀ Q : Subgroup Γ, Q ≤ Ξ → IsPGroup p Q → X.map (MulAut.conj θ).toMonoidHom ≤ Q →
      Q = X.map (MulAut.conj θ).toMonoidHom := by
    intro Q hQΞ hQp hle
    have hQ' : Q.map (MulAut.conj θ⁻¹).toMonoidHom ≤ Ξ := by
      rintro _ ⟨q, hq, rfl⟩
      exact hnorm θ⁻¹ (inv_mem hθ) q (hQΞ hq)
    have hQp' : IsPGroup p (Q.map (MulAut.conj θ⁻¹).toMonoidHom) :=
      hQp.of_equiv (Q.equivMapOfInjective _ (MulAut.conj θ⁻¹).injective)
    have hXQ : X ≤ Q.map (MulAut.conj θ⁻¹).toMonoidHom := by
      intro x hx
      refine ⟨θ * x * θ⁻¹, hle ⟨x, hx, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have h := hXmax _ hQ' hQp' hXQ
    calc Q = (Q.map (MulAut.conj θ⁻¹).toMonoidHom).map (MulAut.conj θ).toMonoidHom := by
          rw [map_conj_map_conj', mul_inv_cancel, map_conj_one']
      _ = X.map (MulAut.conj θ).toMonoidHom := by rw [h]
  let P : Sylow p ↥Ξ := sylowOfMaximal Ξ X hXΞ hXp hXmax
  let P' : Sylow p ↥Ξ := sylowOfMaximal Ξ (X.map (MulAut.conj θ).toMonoidHom) hX' hXp' hmax'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Ξ P' P
  refine ⟨g, g.2, ?_⟩
  have hP : (P : Subgroup ↥Ξ) = X.subgroupOf Ξ := rfl
  have hP' : (P' : Subgroup ↥Ξ) = (X.map (MulAut.conj θ).toMonoidHom).subgroupOf Ξ := rfl
  have h1 : ((g • P' : Sylow p ↥Ξ) : Subgroup ↥Ξ) = (P : Subgroup ↥Ξ) := by rw [hg]
  rw [Sylow.coe_subgroup_smul, hP, hP'] at h1
  have hle : ∀ x ∈ X, (g : Γ) * (θ * x * θ⁻¹) * (g : Γ)⁻¹ ∈ X := by
    intro x hx
    have hmem : (⟨θ * x * θ⁻¹, hX' ⟨x, hx, rfl⟩⟩ : ↥Ξ) ∈
        (X.map (MulAut.conj θ).toMonoidHom).subgroupOf Ξ := mem_subgroupOf.2 ⟨x, hx, rfl⟩
    have := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ hmem
    rw [h1] at this
    simpa [MulAut.conj_apply, mem_subgroupOf] using this
  have hmap : X.map (MulAut.conj ((g : Γ) * θ)).toMonoidHom ≤ X := by
    rintro _ ⟨x, hx, rfl⟩
    have := hle x hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    simpa [mul_assoc] using this
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 (map_conj_eq_of_le hmap)

end Gen16

end CFSG.LocalAnalysis.EvenBN.Tits.N
