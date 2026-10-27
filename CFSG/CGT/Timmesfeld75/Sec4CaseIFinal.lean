module

public import CFSG.CGT.Timmesfeld75.Sec3TwelveCard
public import CFSG.CGT.Timmesfeld75.Sec4CaseIKernel

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Generic

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_closure {Δ : Set G} {x : G} (h : ∀ d ∈ Δ, x * d * x⁻¹ ∈ Δ) :
    x ∈ Subgroup.normalizer (Subgroup.closure Δ : Set G) := by
  refine mem_normalizer_of_conjSubgroup_eq (conjSubgroup_eq_of_le ?_)
  refine conjSubgroup_le_of_forall_mem fun z hz => ?_
  refine Subgroup.closure_induction (p := fun z _ => x * z * x⁻¹ ∈ Subgroup.closure Δ)
    ?_ ?_ ?_ ?_ hz
  · exact fun d hd => Subgroup.subset_closure (h d hd)
  · simp
  · intro u v _ _ hu hv
    have e : x * (u * v) * x⁻¹ = (x * u * x⁻¹) * (x * v * x⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hu hv
  · intro u _ hu
    have e : x * u⁻¹ * x⁻¹ = (x * u * x⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hu

omit [Finite G] in
theorem card_inf_centralizer_conj_of_mem_normalizer {T : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (T : Set G)) (d : G) :
    Nat.card ↥(T ⊓ Subgroup.centralizer ({n * d * n⁻¹} : Set G)) =
      Nat.card ↥(T ⊓ Subgroup.centralizer ({d} : Set G)) := by
  have e : T ⊓ Subgroup.centralizer ({n * d * n⁻¹} : Set G) =
      conjSubgroup n (T ⊓ Subgroup.centralizer ({d} : Set G)) := by
    ext s
    rw [mem_conjSubgroup, Subgroup.mem_inf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    have hT : s ∈ T ↔ n⁻¹ * s * n ∈ T := by
      have h1 := Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (T : Set G)).inv_mem hn) s
      simpa using h1
    refine and_congr hT ⟨fun hc => ?_, fun hc => ?_⟩
    · calc n⁻¹ * s * n * d = n⁻¹ * (s * (n * d * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * d * n⁻¹) * s) * n := by rw [hc]
        _ = d * (n⁻¹ * s * n) := by group
    · calc s * (n * d * n⁻¹) = n * ((n⁻¹ * s * n) * d) * n⁻¹ := by group
        _ = n * (d * (n⁻¹ * s * n)) * n⁻¹ := by rw [hc]
        _ = (n * d * n⁻¹) * s := by group
  rw [e, card_conjSubgroup]

theorem Sec3.card_le_sq_card_normIn {T U : Subgroup G} (hS : Sec3 T U) (hI : Sec3Iso T U) :
    Nat.card T ≤ Nat.card (normIn T U) ^ 2 := by
  obtain ⟨hN, f, hf, he⟩ := hI
  have hpair := hS.isL2Pair_quotient hf he
  have hcard := hS.card_eq_mul hf he
  have hMcard := hS.card_cfgM_eq_sq
  have hMne : cfgM T U ≠ ⊥ := fun h => hS.cfg.ne
    (eq_bot_iff.2 (h ▸ (Cfg.normIn_le_cfgM_left T U : normIn T U ≤ cfgM T U)))
  have hnorm : ∀ x ∈ T ⊔ U, ∀ n ∈ cfgM T U, x * n * x⁻¹ ∈ cfgM T U :=
    fun x hx n hn => hS.cfg.conj_mem_cfgM hx hn
  have hbig := Sec3.two_pow_le_card_of_normal hS rfl rfl (Nat.pos_of_ne_zero hf) hpair le_rfl
    hnorm hMne
  have h2f : 2 ^ f ≤ Nat.card (normIn T U) := by
    by_contra hlt
    have h1 : Nat.card (normIn T U) ^ 2 < (2 ^ f) ^ 2 :=
      Nat.pow_lt_pow_left (not_le.1 hlt) two_ne_zero
    have h2 : (2 ^ f) ^ 2 = 2 ^ (2 * f) := by rw [← pow_mul, mul_comm]
    rw [hMcard] at hbig
    omega
  calc Nat.card T = Nat.card (normIn T U) * 2 ^ f := hcard
    _ ≤ Nat.card (normIn T U) * Nat.card (normIn T U) := Nat.mul_le_mul_left _ h2f
    _ = Nat.card (normIn T U) ^ 2 := by ring

end Generic

section Embedding

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem Sec4Hyp.card_mul_le_of_acts_like_t (h : Sec4Hyp T T₁ a T₂) {V : Subgroup G}
    (hV : ∀ v ∈ V, ∃ t ∈ T, Sec4ActsTriv T T₁ T₂ (v * t))
    (hVker : ∀ v ∈ V, Sec4ActsTriv T T₁ T₂ v → v = 1) :
    Nat.card ↥V * Nat.card (normIn T T₁) ≤ Nat.card T := by
  choose! τ hτT hτ using hV
  let L' : Subgroup ↥T := (normIn T T₁).subgroupOf T
  let f : ↥V → ↥T ⧸ L' := fun v => QuotientGroup.mk ⟨τ v, hτT v v.2⟩
  have hf : Function.Injective f := by
    intro v v' hvv'
    have h1 := QuotientGroup.eq.1 hvv'
    have h2 : (τ v)⁻¹ * τ v' ∈ normIn T T₁ := Subgroup.mem_subgroupOf.1 h1
    have hTab := h.pair.wc.1
    have hcomm : τ v * (τ v')⁻¹ = (τ v')⁻¹ * τ v :=
      elemAbelian_mul_comm hTab (hτT v v.2) (T.inv_mem (hτT v' v'.2))
    have h3 : τ v * (τ v')⁻¹ ∈ sec4Ker T T₁ T₂ := by
      rw [hcomm]
      have : (τ v')⁻¹ * τ v = ((τ v)⁻¹ * τ v')⁻¹ := by group
      rw [this]
      exact (sec4Ker T T₁ T₂).inv_mem (h.sec4N_le_sec4Ker (normIn_le_sec4N_left h2))
    have hk : (v : G) * τ v ∈ sec4Ker T T₁ T₂ := hτ v v.2
    have hk' : (v' : G) * τ v' ∈ sec4Ker T T₁ T₂ := hτ v' v'.2
    have h4 : τ v * (((v : G) * τ v)⁻¹ * ((v' : G) * τ v')) * (τ v)⁻¹ ∈ sec4Ker T T₁ T₂ :=
      h.conj_mem_sec4Ker ((sec4Ker T T₁ T₂).mul_mem ((sec4Ker T T₁ T₂).inv_mem hk) hk')
        (left_le_sec4Y (hτT v v.2))
    have e : (v : G)⁻¹ * v' =
        (τ v * (((v : G) * τ v)⁻¹ * ((v' : G) * τ v')) * (τ v)⁻¹) * (τ v * (τ v')⁻¹) := by group
    have hker : (v : G)⁻¹ * v' ∈ sec4Ker T T₁ T₂ := by
      rw [e]
      exact (sec4Ker T T₁ T₂).mul_mem h4 h3
    have hone := hVker _ (V.mul_mem (V.inv_mem v.2) v'.2) hker
    exact Subtype.ext (inv_mul_eq_one.1 hone)
  have hcard : Nat.card ↥V ≤ Nat.card (↥T ⧸ L') := Nat.card_le_card_of_injective f hf
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup L'
  have hL' : Nat.card ↥L' = Nat.card (normIn T T₁) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (normIn_le T T₁)).toEquiv
  calc Nat.card ↥V * Nat.card (normIn T T₁) ≤ Nat.card (↥T ⧸ L') * Nat.card (normIn T T₁) :=
        Nat.mul_le_mul_right _ hcard
    _ = Nat.card (↥T ⧸ L') * Nat.card ↥L' := by rw [hL']
    _ = Nat.card T := hmul.symm

end Embedding

end CFSG.CGT.Timmesfeld75
