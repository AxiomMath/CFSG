module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelFacts

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

theorem inCenterOf_map_iff {K K' : Type*} [Group K] [Group K'] (e : K ≃* K') {Q : Subgroup K}
    (w : K') : InCenterOf (Q.map e.toMonoidHom) w ↔ InCenterOf Q (e.symm w) := by
  constructor
  · rintro ⟨hw, hc⟩
    refine ⟨Subgroup.mem_map_equiv.mp hw, fun q hq => ?_⟩
    simpa using (hc (e q) (Subgroup.mem_map_of_mem e.toMonoidHom hq)).map e.symm
  · rintro ⟨hw, hc⟩
    refine ⟨Subgroup.mem_map_equiv.mpr hw, fun q hq => ?_⟩
    simpa using (hc (e.symm q) (Subgroup.mem_map_equiv.mp hq)).map e

theorem inCenterOf_map_apply {K K' : Type*} [Group K] [Group K'] (e : K ≃* K')
    {Q : Subgroup K} {w : K} (hw : InCenterOf Q w) : InCenterOf (Q.map e.toMonoidHom) (e w) :=
  (inCenterOf_map_iff e (e w)).mpr (by simpa using hw)

theorem benderBorelFacts_torus_map_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K')
    {Q : Subgroup K} (h : BenderBorelFacts K Q) :
    ∃ D : Subgroup K', Odd (Nat.card D) ∧
      D ≤ Subgroup.normalizer ((Q.map e.toMonoidHom : Subgroup K') : Set K') ∧
      Q.map e.toMonoidHom ⊔ D =
        Subgroup.normalizer ((Q.map e.toMonoidHom : Subgroup K') : Set K') ∧
      (∀ w w' : K', InCenterOf (Q.map e.toMonoidHom) w → w ≠ 1 →
        InCenterOf (Q.map e.toMonoidHom) w' → w' ≠ 1 → ∃ d ∈ D, d⁻¹ * w * d = w') ∧
      (∀ β : K' → K' → ZMod 2,
        (∀ a ∈ Q.map e.toMonoidHom, ∀ b ∈ Q.map e.toMonoidHom, ∀ c ∈ Q.map e.toMonoidHom,
          β (a * b) c = β a c + β b c) →
        (∀ a ∈ Q.map e.toMonoidHom, ∀ b ∈ Q.map e.toMonoidHom, ∀ c ∈ Q.map e.toMonoidHom,
          β a (b * c) = β a b + β a c) →
        (∀ a ∈ Q.map e.toMonoidHom, β a a = 0) →
        (∀ a ∈ Q.map e.toMonoidHom, ∀ b : K', InCenterOf (Q.map e.toMonoidHom) b → β a b = 0) →
        (∀ d ∈ D, ∀ a ∈ Q.map e.toMonoidHom, ∀ b ∈ Q.map e.toMonoidHom,
          β (d⁻¹ * a * d) (d⁻¹ * b * d) = β a b) →
        ∀ a ∈ Q.map e.toMonoidHom, ∀ b ∈ Q.map e.toMonoidHom, β a b = 0) := by
  obtain ⟨D, hDodd, hDN, hsup, htrans, hform⟩ := h.torus
  have hmem : ∀ {x : K}, x ∈ Q → e x ∈ Q.map e.toMonoidHom := fun hx =>
    Subgroup.mem_map_of_mem e.toMonoidHom hx
  refine ⟨D.map e.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [Subgroup.card_map_of_injective e.injective]
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hDN
  · rw [← Subgroup.map_sup, hsup, Subgroup.map_equiv_normalizer_eq]
  · intro w w' hw hw1 hw' hw'1
    rw [inCenterOf_map_iff] at hw hw'
    obtain ⟨d, hd, hdw⟩ := htrans _ _ hw (by simpa using hw1) hw' (by simpa using hw'1)
    refine ⟨e d, Subgroup.mem_map_of_mem e.toMonoidHom hd, ?_⟩
    apply e.symm.injective
    simpa using hdw
  · intro β hβl hβr hβa hβc hβD a ha b hb
    have key := hform (fun x y => β (e x) (e y))
      (fun x hx y hy z hz => by simpa using hβl _ (hmem hx) _ (hmem hy) _ (hmem hz))
      (fun x hx y hy z hz => by simpa using hβr _ (hmem hx) _ (hmem hy) _ (hmem hz))
      (fun x hx => hβa _ (hmem hx))
      (fun x hx y hy => hβc _ (hmem hx) _ (inCenterOf_map_apply e hy))
      (fun d hd x hx y hy => by
        simpa using hβD _ (Subgroup.mem_map_of_mem e.toMonoidHom hd) _ (hmem hx) _ (hmem hy))
      _ (Subgroup.mem_map_equiv.mp ha) _ (Subgroup.mem_map_equiv.mp hb)
    simpa using key

theorem benderBorelFacts_map_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K')
    {Q : Subgroup K} (h : BenderBorelFacts K Q) :
    BenderBorelFacts K' (Q.map e.toMonoidHom) where
  commutator_central a ha b hb := by
    rw [inCenterOf_map_iff]
    simpa using h.commutator_central _ (Subgroup.mem_map_equiv.mp ha) _
      (Subgroup.mem_map_equiv.mp hb)
  sq_central a ha := by
    rw [inCenterOf_map_iff]
    simpa using h.sq_central _ (Subgroup.mem_map_equiv.mp ha)
  torus := benderBorelFacts_torus_map_mulEquiv e h
  center_card := by
    rw [Nat.card_congr (Equiv.subtypeEquiv e.symm.toEquiv (fun w => inCenterOf_map_iff e w))]
    exact h.center_card
  aut_inner σ hσ := by
    obtain ⟨r, hr, hrk⟩ := h.aut_inner ((e.trans σ).trans e.symm) (fun q hq => by
      simp [hσ (e q) (Subgroup.mem_map_of_mem e.toMonoidHom hq)])
    refine ⟨e r, Subgroup.mem_map_of_mem e.toMonoidHom hr, fun k => ?_⟩
    apply e.symm.injective
    simpa using hrk (e.symm k)

theorem benderBorelFacts_conj {K : Type*} [Group K] {Q : Subgroup K} (g : K)
    (h : BenderBorelFacts K Q) : BenderBorelFacts K (Q.map (MulAut.conj g).toMonoidHom) :=
  benderBorelFacts_map_mulEquiv (MulAut.conj g) h

theorem benderBorelFacts_sylow_smul {K : Type*} [Group K] {p : ℕ} {P : Sylow p K} (g : K)
    (h : BenderBorelFacts K P) : BenderBorelFacts K ((g • P : Sylow p K) : Subgroup K) := by
  rw [Sylow.coe_subgroup_smul]
  exact benderBorelFacts_conj g h

theorem benderBorelFacts_sylow {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    {P : Sylow p K} (h : BenderBorelFacts K P) (Q : Sylow p K) :
    BenderBorelFacts K (Q : Subgroup K) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq K P Q
  exact benderBorelFacts_sylow_smul g h

theorem benderBorelFacts_sylow_of_mulEquiv {K K' : Type*} [Group K] [Group K'] [Finite K]
    (e : K ≃* K') (h : ∃ Q : Sylow 2 K', BenderBorelFacts K' (Q : Subgroup K'))
    (P : Sylow 2 K) : BenderBorelFacts K (P : Subgroup K) := by
  obtain ⟨Q, hQ⟩ := h
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : Sylow 2 K,
      (P₀ : Subgroup K) = (Q : Subgroup K').comap e.toMonoidHom :=
    ⟨Q.comapOfInjective e.toMonoidHom e.injective (fun x _ => ⟨e.symm x, by simp⟩),
      Sylow.coe_comapOfInjective _ _ _ _⟩
  have h₀ := benderBorelFacts_map_mulEquiv e.symm hQ
  rw [← Subgroup.comap_equiv_eq_map_symm', ← hP₀] at h₀
  exact benderBorelFacts_sylow h₀ P

theorem benderBorelFactsHold_of_models (hL : PSL2BorelFacts) (hS : SuzukiBorelFacts)
    (hU : UnitaryBorelFacts) : BenderBorelFactsHold := by
  intro K _ _ hK Q
  cases hK with
  | isPSL2 n hn e => exact benderBorelFacts_sylow_of_mulEquiv e (hL n hn) Q
  | isSuzuki n hn e => exact benderBorelFacts_sylow_of_mulEquiv e (hS n hn) Q
  | isPSU3 n hn e => exact benderBorelFacts_sylow_of_mulEquiv e (hU n hn) Q

end CFSG.ProperTwoGeneratedCore.TheoremC
