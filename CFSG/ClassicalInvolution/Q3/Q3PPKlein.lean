module

public import CFSG.ClassicalInvolution.Q3.Q3PPEdge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3W
open scoped commutatorElement

section Weak

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem commutator_mem_involutionOddCore_of_pointwise (hΩ : ConjInvariant Ω) {a b : G}
    (hO : oddCoreIn (centralizingLayer Ω {b} ⊓ Subgroup.centralizer ({a} : Set G)) ≤
      oddCoreIn (centralizingLayer Ω {b}))
    {r g : G} (hr : r ∈ involutionOddCore a ⊓ Subgroup.centralizer ({b} : Set G))
    (hg : g ∈ centralizingLayer Ω {b} ⊓ Subgroup.centralizer ({a} : Set G)) :
    ⁅r, g⁆ ∈ involutionOddCore b := by
  set Y : Subgroup G := centralizingLayer Ω {b} with hY
  set R : Subgroup G := involutionOddCore a ⊓ Subgroup.centralizer ({b} : Set G) with hR
  have hYb : Y ≤ Subgroup.centralizer ({b} : Set G) := centralizingLayer_le_centralizer Ω {b}
  have hgY : g ∈ Y := hg.1
  have hga : g ∈ Subgroup.centralizer ({a} : Set G) := hg.2
  have hRconj : ∀ u ∈ Subgroup.centralizer ({a} : Set G),
      u ∈ Subgroup.centralizer ({b} : Set G) → ∀ x ∈ R, u * x * u⁻¹ ∈ R := by
    intro u hua hub x hx
    exact ⟨conj_mem_oddCoreIn hua hx.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hub hx.2) (Subgroup.inv_mem _ hub)⟩
  have hrCb : r ∈ Subgroup.centralizer ({b} : Set G) := hr.2
  have hgCb : g ∈ Subgroup.centralizer ({b} : Set G) := hYb hgY
  have hcommR : ⁅r, g⁆ ∈ R := by
    have h1 : g * r⁻¹ * g⁻¹ ∈ R := hRconj g hga hgCb r⁻¹ (R.inv_mem hr)
    have : ⁅r, g⁆ = r * (g * r⁻¹ * g⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact R.mul_mem hr h1
  have hcommY : ⁅r, g⁆ ∈ Y := by
    have : ⁅r, g⁆ = (r * g * r⁻¹) * g⁻¹ := by
      simp only [commutatorElement_def]
    rw [this]
    exact Y.mul_mem (conj_mem_centralizingLayer hΩ hrCb hgY) (Y.inv_mem hgY)
  have hRY : (R ⊓ Y) ≤ oddCoreIn (Y ⊓ Subgroup.centralizer ({a} : Set G)) := by
    refine le_oddCoreIn_of_normalizes ?_ ?_ ?_
    · intro x hx
      exact ⟨hx.2, involutionOddCore_le_centralizer a hx.1.1⟩
    · intro u hu
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hub : u ∈ Subgroup.centralizer ({b} : Set G) := hYb hu.1
      have hub' : u⁻¹ ∈ Subgroup.centralizer ({b} : Set G) := Subgroup.inv_mem _ hub
      have hua' : u⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := Subgroup.inv_mem _ hu.2
      constructor
      · rintro ⟨hyR, hyY⟩
        exact ⟨hRconj u hu.2 hub y hyR, conj_mem_centralizingLayer hΩ hub hyY⟩
      · rintro ⟨hyR, hyY⟩
        have h1 := hRconj u⁻¹ hua' hub' _ hyR
        have h2 := conj_mem_centralizingLayer hΩ hub' hyY
        simp only [mul_assoc, inv_inv, inv_mul_cancel_left] at h1 h2 ⊢
        refine ⟨?_, ?_⟩
        · simpa [mul_assoc] using h1
        · simpa [mul_assoc] using h2
    · exact (odd_card_oddCoreIn (Subgroup.centralizer ({a} : Set G))).of_dvd_nat
        (Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left))
  have h3 : ⁅r, g⁆ ∈ oddCoreIn Y := hO (hRY ⟨hcommR, hcommY⟩)
  exact oddCoreIn_centralizingLayer_le hΩ b h3

theorem fixedPointFree_of_witness (hΩ : ConjInvariant Ω) {a b z : G} {K : Subgroup G}
    (hO : oddCoreIn (centralizingLayer Ω {b} ⊓ Subgroup.centralizer ({a} : Set G)) ≤
      oddCoreIn (centralizingLayer Ω {b}))
    (hPb : involutionOddCore b = ⊥) (hKY : K ≤ centralizingLayer Ω {b})
    (hKa : K ≤ Subgroup.centralizer ({a} : Set G)) (hzK : z ∈ K)
    (hz : ∀ r ∈ involutionOddCore a, r * z = z * r → r = 1) :
    ∀ r ∈ involutionOddCore a, r * b = b * r → r = 1 := by
  intro r hr hrb
  have hc := commutator_mem_involutionOddCore_of_pointwise hΩ hO (r := r) (g := z)
    ⟨hr, Subgroup.mem_centralizer_singleton_iff.mpr hrb⟩ ⟨hKY hzK, hKa hzK⟩
  rw [hPb, Subgroup.mem_bot] at hc
  exact hz r hr (commutatorElement_eq_one_iff_mul_comm.mp hc)

end Weak

section Klein

variable {G : Type} [Group G] [Finite G]

theorem mem_klein_cases {w₀ w₁ : G} (h₀ : w₀ * w₀ = 1) (h₁ : w₁ * w₁ = 1)
    (hc : w₀ * w₁ = w₁ * w₀) {g : G} (hg : g ∈ Subgroup.closure ({w₀, w₁} : Set G)) :
    g = 1 ∨ g = w₀ ∨ g = w₁ ∨ g = w₀ * w₁ := by
  have e01 : w₀ * (w₀ * w₁) = w₁ := by rw [← mul_assoc, h₀, one_mul]
  have e10 : w₁ * (w₀ * w₁) = w₀ := by rw [← mul_assoc, ← hc, mul_assoc, h₁, mul_one]
  have e01' : (w₀ * w₁) * w₀ = w₁ := by rw [hc, mul_assoc, h₀, mul_one]
  have e10' : (w₀ * w₁) * w₁ = w₀ := by rw [mul_assoc, h₁, mul_one]
  have e22 : (w₀ * w₁) * (w₀ * w₁) = 1 := by
    calc (w₀ * w₁) * (w₀ * w₁) = w₀ * (w₁ * w₀) * w₁ := by group
      _ = w₀ * (w₀ * w₁) * w₁ := by rw [← hc]
      _ = (w₀ * w₀) * (w₁ * w₁) := by group
      _ = 1 := by rw [h₀, h₁, one_mul]
  have i0 : w₀⁻¹ = w₀ := inv_eq_of_mul_eq_one_right h₀
  have i1 : w₁⁻¹ = w₁ := inv_eq_of_mul_eq_one_right h₁
  have i2 : (w₀ * w₁)⁻¹ = w₀ * w₁ := inv_eq_of_mul_eq_one_right e22
  induction hg using Subgroup.closure_induction with
  | mem u hu =>
    rcases hu with rfl | hu
    · exact Or.inr (Or.inl rfl)
    · rw [Set.mem_singleton_iff.mp hu]
      exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul u v _ _ hu hv =>
    rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;>
      simp [h₀, h₁, e01, e10, e01', e10', e22, hc.symm]
  | inv u _ hu =>
    rcases hu with rfl | rfl | rfl | rfl <;> simp [i0, i1, i2]

theorem involutionOddCore_eq_bot_of_klein {x w₀ w₁ : G} (h₀ : w₀ * w₀ = 1) (h₁ : w₁ * w₁ = 1)
    (hc : w₀ * w₁ = w₁ * w₀) (h₀1 : w₀ ≠ 1) (h₁1 : w₁ ≠ 1) (h₀₁ : w₀ ≠ w₁)
    (hx₀ : x * w₀ = w₀ * x) (hx₁ : x * w₁ = w₁ * x)
    (f₀ : ∀ r ∈ involutionOddCore x, r * w₀ = w₀ * r → r = 1)
    (f₁ : ∀ r ∈ involutionOddCore x, r * w₁ = w₁ * r → r = 1)
    (f₂ : ∀ r ∈ involutionOddCore x, r * (w₀ * w₁) = (w₀ * w₁) * r → r = 1) :
    involutionOddCore x = ⊥ := by
  set V : Subgroup G := Subgroup.closure ({w₀, w₁} : Set G) with hV
  set P : Subgroup G := involutionOddCore x with hP
  have hVel : IsElemAbelian 2 V := by
    refine Balance.Theorem5.isElemAbelian_closure_of_commuting_involutions ?_ ?_
    · intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl <;> assumption
    · intro s hs t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
        first | rfl | assumption | exact (by assumption : _ = _).symm
  have hcard : Nat.card V = 4 := card_closure_pair_eq_four h₀ h₁ h₀1 h₁1 h₀₁ hc
  have hVC : V ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [hV, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hx₀.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hx₁.symm
  have hnorm : V ≤ Subgroup.normalizer (P : Set G) :=
    hVC.trans (normalizer_oddCoreIn (Subgroup.centralizer ({x} : Set G)))
  have hcop : Nat.Coprime 2 (Nat.card P) :=
    Nat.coprime_two_left.mpr (odd_card_oddCoreIn (Subgroup.centralizer ({x} : Set G)))
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 1
    Nat.prime_two V P hVel (by rw [hcard]; norm_num) hnorm hcop
  have key : ∀ F ∈ signalizerFunctorEk 2 1 V, P ⊓ Subgroup.centralizer (F : Set G) ≤ ⊥ := by
    rintro F ⟨hFV, hFc⟩ r ⟨hrP, hrF⟩
    have hF1 : F ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hFc
      norm_num at hFc
    obtain ⟨⟨f, hfF⟩, hf1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hF1
    have hf1' : f ≠ 1 := fun h => hf1 (Subtype.ext h)
    have hfV : f ∈ V := hFV hfF
    have hrf : f * r = r * f := Subgroup.mem_centralizer_iff.mp hrF f hfF
    rcases mem_klein_cases h₀ h₁ hc hfV with h | h | h | h
    · exact absurd h hf1'
    · rw [h] at hrf
      exact Subgroup.mem_bot.mpr (f₀ r hrP hrf.symm)
    · rw [h] at hrf
      exact Subgroup.mem_bot.mpr (f₁ r hrP hrf.symm)
    · rw [h] at hrf
      exact Subgroup.mem_bot.mpr (f₂ r hrP hrf.symm)
  exact le_bot_iff.mp (hgen.symm.le.trans (iSup₂_le key))

end Klein

section Edge

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {K₁ K₂ : Subgroup G} {z₁ z₂ : G}

namespace EdgeData

theorem swapEdge (h : EdgeData K K₁ K₂ z₁ z₂) : EdgeData K K₂ K₁ z₂ z₁ where
  mem₁ := h.mem₂
  mem₂ := h.mem₁
  cls₁ := h.cls₂
  cls₂ := h.cls₁
  ne := h.ne.symm
  comm := h.comm.symm

theorem involutionOddCore_prod_eq_bot_of_klein (hOA : OddAutLayerRigidHyp)
    (hR : RouteD3Setup K z) (hnab : ∃ a b : G, a * b ≠ b * a) (h : EdgeData K K₁ K₂ z₁ z₂)
    {M₁ M₂ : Subgroup G} {w₁ : G} (hM₁ : M₁ ∈ conjClass3 K) (hM₂ : M₂ ∈ conjClass3 K)
    (c₁ : IsClassicalMember3 M₁ w₁) (c₂ : IsClassicalMember3 M₂ (z₂ * w₁))
    (hK₁ : K₁ ≤ Subgroup.centralizer ({w₁} : Set G)) (hcomm : w₁ * z₂ = z₂ * w₁)
    (hne : w₁ ≠ z₂)
    (hO₁ : oddCoreIn (centralizingLayer (conjClass3 K) {w₁} ⊓
        Subgroup.centralizer ({z₁ * z₂} : Set G)) ≤
      oddCoreIn (centralizingLayer (conjClass3 K) {w₁}))
    (hO₂ : oddCoreIn (centralizingLayer (conjClass3 K) {z₂ * w₁} ⊓
        Subgroup.centralizer ({z₁ * z₂} : Set G)) ≤
      oddCoreIn (centralizingLayer (conjClass3 K) {z₂ * w₁})) :
    involutionOddCore (z₁ * z₂) = ⊥ := by
  have hΩ := hR.inClass.conjInvariant
  have hw₁sq : w₁ * w₁ = 1 := Q3NT.mul_self_eq_one_of_orderOf_eq_two c₁.orderOf_eq_two
  have hz₁w₁ : z₁ * w₁ = w₁ * z₁ := Subgroup.mem_centralizer_singleton_iff.mp (hK₁ h.cls₁.mem)
  have hx₀ : z₁ * z₂ * z₂ = z₂ * (z₁ * z₂) := by
    calc z₁ * z₂ * z₂ = z₁ * (z₂ * z₂) := mul_assoc _ _ _
      _ = (z₂ * z₁) * z₂ := by rw [h.sq₂, mul_one, ← h.mul_comm₁₂, mul_assoc, h.sq₂, mul_one]
      _ = z₂ * (z₁ * z₂) := by rw [mul_assoc]
  have hx₁ : z₁ * z₂ * w₁ = w₁ * (z₁ * z₂) := by
    calc z₁ * z₂ * w₁ = z₁ * (z₂ * w₁) := mul_assoc _ _ _
      _ = z₁ * (w₁ * z₂) := by rw [hcomm]
      _ = (z₁ * w₁) * z₂ := (mul_assoc _ _ _).symm
      _ = (w₁ * z₁) * z₂ := by rw [hz₁w₁]
      _ = w₁ * (z₁ * z₂) := mul_assoc _ _ _
  have f₀ : ∀ r ∈ involutionOddCore (z₁ * z₂), r * z₂ = z₂ * r → r = 1 := by
    intro r hr hrz
    have hr' : r ∈ involutionOddCore (z₂ * z₁) := by
      rw [← h.mul_comm₁₂]
      exact hr
    have hmem : r ∈ involutionOddCore (z₂ * z₁) ⊓ Subgroup.centralizer ({z₂} : Set G) :=
      ⟨hr', Subgroup.mem_centralizer_singleton_iff.mpr hrz⟩
    rw [h.swapEdge.oddCore_inf_centralizer_eq_bot hOA hR hnab] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hfz : ∀ r ∈ involutionOddCore (z₁ * z₂), r * z₁ = z₁ * r → r = 1 := by
    intro r hr hrz
    have hmem : r ∈ involutionOddCore (z₁ * z₂) ⊓ Subgroup.centralizer ({z₁} : Set G) :=
      ⟨hr, Subgroup.mem_centralizer_singleton_iff.mpr hrz⟩
    rw [h.oddCore_inf_centralizer_eq_bot hOA hR hnab] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hK₁₂ : K₁ ≤ Subgroup.centralizer ({z₂ * w₁} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have a1 : y * z₂ = z₂ * y := Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer₂ hy)
    have a2 : y * w₁ = w₁ * y := Subgroup.mem_centralizer_singleton_iff.mp (hK₁ hy)
    calc y * (z₂ * w₁) = (y * z₂) * w₁ := (mul_assoc _ _ _).symm
      _ = z₂ * (y * w₁) := by rw [a1, mul_assoc]
      _ = z₂ * (w₁ * y) := by rw [a2]
      _ = (z₂ * w₁) * y := (mul_assoc _ _ _).symm
  have f₁ : ∀ r ∈ involutionOddCore (z₁ * z₂), r * w₁ = w₁ * r → r = 1 :=
    fixedPointFree_of_witness hΩ hO₁ (Q3OF.involutionOddCore_eq_bot_of_member hR hM₁ c₁)
      (le_centralizingLayer ⟨h.mem₁, hK₁⟩) h.le_centralizer_prod₁ h.cls₁.mem hfz
  have f₂ : ∀ r ∈ involutionOddCore (z₁ * z₂), r * (z₂ * w₁) = (z₂ * w₁) * r → r = 1 :=
    fixedPointFree_of_witness hΩ hO₂ (Q3OF.involutionOddCore_eq_bot_of_member hR hM₂ c₂)
      (le_centralizingLayer ⟨h.mem₁, hK₁₂⟩) h.le_centralizer_prod₁ h.cls₁.mem hfz
  exact involutionOddCore_eq_bot_of_klein h.sq₂ hw₁sq hcomm.symm h.cls₂.ne_one c₁.ne_one hne.symm
    hx₀ hx₁ f₀ f₁ f₂

end EdgeData

@[expose] def KleinAt (K K₁ : Subgroup G) (z₂ : G) : Prop :=
  ∃ (M₁ M₂ : Subgroup G) (w₁ : G), M₁ ∈ conjClass3 K ∧ M₂ ∈ conjClass3 K ∧
    IsClassicalMember3 M₁ w₁ ∧ IsClassicalMember3 M₂ (z₂ * w₁) ∧
    K₁ ≤ Subgroup.centralizer ({w₁} : Set G) ∧ w₁ * z₂ = z₂ * w₁ ∧ w₁ ≠ z₂

end Edge

end CFSG.ClassicalInvolution.Q3.Q3PP
