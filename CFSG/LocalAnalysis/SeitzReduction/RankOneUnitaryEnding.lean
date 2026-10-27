module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingFactor
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineTwo
public import CFSG.LocalAnalysis.SeitzReduction.RankOneEndingsTransfer

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure U3EndingData (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G)
    (T R₂ U₁ : Subgroup G) (s : G) : Prop where
  start : U3Start G L f t T
  card_sylow : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2
  starPrime : StarPrimeStatement f
  r2 : U3R2 G L (szT₁ L T) R₂ t f
  c_ne_one : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹
  omega_card : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2
  canonical : ∃ E : Subgroup (Equiv.Perm (u3Omega L T R₂ t)),
    E ≤ (u3OmegaAction L T R₂ t).range ∧ (E.subgroupOf (u3OmegaAction L T R₂ t).range).Normal ∧
      (∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b) ∧
      U₁ = u3U L T R₂ t E ⊓ centralizer (R₂ : Set G)
  u1 : U3U1Data G L f t T R₂ U₁
  not_cyclic : ¬ ∃ b ∈ T, ∀ c ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * c ∈ szT₁ L T
  not_sylow : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U₁ ⊔ T
  s_mem_normalizer : s ∈ normalizer ((U₁ ⊔ T : Subgroup G) : Set G)
  s_not_mem : s ∉ U₁ ⊔ T
  s_two : ∃ P : Subgroup G, IsPGroup 2 P ∧ U₁ ⊔ T ≤ P ∧ s ∈ P
  conj_not_mem : s * t * s⁻¹ ∉ U₁ ⊔ zpowers t
  conj_mem : ∀ w ∈ T, w ^ 2 ∈ szT₁ L T → w ∉ szT₁ L T ⊔ zpowers t →
    ∃ u ∈ U₁, s * t * s⁻¹ = u * w ∨ s * t * s⁻¹ = u * t * w
  s_mem_normalizer_R₂ : s ∈ normalizer (R₂ : Set G)
  s_mem_normalizer_U₁ : s ∈ normalizer (U₁ : Set G)

@[expose] def U3EndingInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ U₁ : Subgroup G)
    (s : G), U3EndingData G L f t T R₂ U₁ s → False

@[expose] def U3EndingProductInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ U₁ : Subgroup G)
    (s v : G), U3EndingData G L f t T R₂ U₁ s → v ∈ T → v ^ 2 = 1 →
    v ∉ szT₁ L T ⊔ zpowers t → s * t * s⁻¹ = t * v → f ≠ 3 →
      ∃ Y₁ Y₂ : Subgroup G, Y₁ ⊔ Y₂ = U₁ ∧ Y₁ ⊓ Y₂ = ⊥ ∧ (∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) ∧
        (∀ a ∈ Y₁, t * a * t⁻¹ ∈ Y₂) ∧ (∀ b ∈ Y₂, t * b * t⁻¹ ∈ Y₁)

@[expose] def U3EightLieInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (T R₂ U₁ : Subgroup G)
    (s v : G), U3EndingData G L 3 t T R₂ U₁ s → v ∈ T → v ^ 2 = 1 →
    v ∉ szT₁ L T ⊔ zpowers t → s * t * s⁻¹ = t * v →
      ∃ Y₁ Y₂ : Subgroup G, Y₁ ⊔ Y₂ = U₁ ∧ Y₁ ⊓ Y₂ = ⊥ ∧ (∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) ∧
        (∀ a ∈ Y₁, t * a * t⁻¹ ∈ Y₂) ∧ (∀ b ∈ Y₂, t * b * t⁻¹ ∈ Y₁)

@[expose] def U3EndingSylowInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ U₁ : Subgroup G)
    (s v : G) (Y₁ Y₂ : Subgroup G), U3EndingData G L f t T R₂ U₁ s → v ∈ T → v ^ 2 = 1 →
    v ∉ szT₁ L T ⊔ zpowers t → s * t * s⁻¹ = t * v →
    Y₁ ⊔ Y₂ = U₁ → Y₁ ⊓ Y₂ = ⊥ → (∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) →
    (∀ a ∈ Y₁, t * a * t⁻¹ ∈ Y₂) → (∀ b ∈ Y₂, t * b * t⁻¹ ∈ Y₁) →
      ∃ S : Sylow 2 G, t ∈ S ∧ (S : Subgroup G) ≤ normalizer (U₁ : Set G) ∧
        ∀ g : G, g * t * g⁻¹ ∈ S →
          g * t * g⁻¹ ∉ normalizer ((U₁ ⊓ centralizer (Y₂ : Set G) : Subgroup G) : Set G)

namespace U3EndingData

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}
  {s : G}

theorem exists_conj_eq_t_mul (hD : U3EndingData G L f t T R₂ U₁ s) :
    ∃ s' v : G, U3EndingData G L f t T R₂ U₁ s' ∧ v ∈ T ∧ v ^ 2 = 1 ∧
      v ∉ szT₁ L T ⊔ zpowers t ∧ s' * t * s'⁻¹ = t * v := by
  have h := hD.start
  have hS2 := hD.card_sylow
  have hR := hD.r2
  have hU := hD.u1
  have htt : t * t = 1 := by rw [← sq]; exact hR.t_sq
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have htU : t ∈ normalizer (U₁ : Set G) := hU.normalizer_le (Subgroup.le_normalizer
    (show t ∈ szT₁ L T ⊔ R₂ ⊔ zpowers t from mem_sup_right (mem_zpowers t)))
  obtain ⟨v₀, hv₀T, hv₀2, hv₀S⟩ := u3SplitInput G L f t T h hS2 hD.not_cyclic
  have hv₀t : v₀ * t = t * v₀ := mem_centralizer_singleton_iff.mp (h.le hv₀T)
  obtain ⟨v, u, hvT, hv2, hvS, hu, hst⟩ : ∃ v u : G, v ∈ T ∧ v ^ 2 = 1 ∧
      v ∉ szT₁ L T ⊔ zpowers t ∧ u ∈ U₁ ∧ s * t * s⁻¹ = u * t * v := by
    obtain ⟨u, hu, h1 | h1⟩ := hD.conj_mem v₀ hv₀T (by rw [hv₀2]; exact one_mem _) hv₀S
    · refine ⟨t * v₀, u, mul_mem htT hv₀T, ?_, fun hm => hv₀S ?_, hu, ?_⟩
      · calc (t * v₀) ^ 2 = t * (v₀ * t) * v₀ := by rw [sq]; group
          _ = t * (t * v₀) * v₀ := by rw [hv₀t]
          _ = (t * t) * v₀ ^ 2 := by rw [sq]; group
          _ = 1 := by rw [htt, hv₀2, one_mul]
      · have := mul_mem (inv_mem (mem_sup_right (mem_zpowers t))) hm
        rwa [inv_mul_cancel_left] at this
      · rw [h1, show u * t * (t * v₀) = u * (t * t) * v₀ by group, htt, mul_one]
    · exact ⟨v₀, u, hv₀T, hv₀2, hv₀S, hu, h1⟩
  have hvt : v * t = t * v := mem_centralizer_singleton_iff.mp (h.le hvT)
  have hsU := hD.s_mem_normalizer_U₁
  have hu' : s⁻¹ * u⁻¹ * s ∈ U₁ := by
    have := (mem_normalizer_iff''.mp hsU (u⁻¹)).mp (inv_mem hu)
    simpa [mul_assoc] using this
  have key : s⁻¹ * u⁻¹ * s * t = s⁻¹ * (t * v) * s := by
    calc s⁻¹ * u⁻¹ * s * t = s⁻¹ * u⁻¹ * (s * t * s⁻¹) * s := by group
      _ = s⁻¹ * u⁻¹ * (u * t * v) * s := by rw [hst]
      _ = s⁻¹ * (t * v) * s := by group
  have htv2 : (t * v) * (t * v) = 1 := by
    calc t * v * (t * v) = t * (v * t) * v := by group
      _ = t * (t * v) * v := by rw [hvt]
      _ = (t * t) * v ^ 2 := by rw [sq]; group
      _ = 1 := by rw [htt, hv2, one_mul]
  have hu'2 : (s⁻¹ * u⁻¹ * s * t) ^ 2 = 1 := by
    rw [key, sq, show s⁻¹ * (t * v) * s * (s⁻¹ * (t * v) * s) =
      s⁻¹ * ((t * v) * (t * v)) * s by group, htv2, mul_one, inv_mul_cancel]
  obtain ⟨w, hw, hwt⟩ := hU.exists_conj_t_of_sq_eq_one hR hu' hu'2
  have hs't : s * w * t * (s * w)⁻¹ = t * v := by
    calc s * w * t * (s * w)⁻¹ = s * (w * t * w⁻¹) * s⁻¹ := by group
      _ = s * (s⁻¹ * u⁻¹ * s * t) * s⁻¹ := by rw [hwt]
      _ = s * (s⁻¹ * (t * v) * s) * s⁻¹ := by rw [key]
      _ = t * v := by group
  have hc : w * t * w⁻¹ * t⁻¹ ∈ U₁ := by
    have := mul_mem hw ((mem_normalizer_iff.mp htU _).mp (inv_mem hw))
    simpa [mul_assoc] using this
  have hc' : s * (w * t * w⁻¹ * t⁻¹) * s⁻¹ ∈ U₁ := (mem_normalizer_iff.mp hsU _).mp hc
  have hsplit : s * w * t * (s * w)⁻¹ =
      (s * (w * t * w⁻¹ * t⁻¹) * s⁻¹) * (s * t * s⁻¹) := by group
  have hwS : w ∈ U₁ ⊔ T := mem_sup_left hw
  refine ⟨s * w, v, { hD with
    s_mem_normalizer := mul_mem hD.s_mem_normalizer (Subgroup.le_normalizer hwS)
    s_not_mem := fun hm => hD.s_not_mem (by
      have := mul_mem hm (inv_mem hwS)
      rwa [mul_inv_cancel_right] at this)
    s_two := by
      obtain ⟨P, hP2, hPle, hsP⟩ := hD.s_two
      exact ⟨P, hP2, hPle, mul_mem hsP (hPle hwS)⟩
    conj_not_mem := by
      rw [hsplit]
      intro hm
      apply hD.conj_not_mem
      have := mul_mem (inv_mem (mem_sup_left hc' : _ ∈ U₁ ⊔ zpowers t)) hm
      rwa [inv_mul_cancel_left] at this
    conj_mem := fun w'' hw''T hw''2 hw''S => by
      obtain ⟨u₀, hu₀, h1 | h1⟩ := hD.conj_mem w'' hw''T hw''2 hw''S
      · refine ⟨s * (w * t * w⁻¹ * t⁻¹) * s⁻¹ * u₀, mul_mem hc' hu₀, Or.inl ?_⟩
        rw [hsplit, h1]
        group
      · refine ⟨s * (w * t * w⁻¹ * t⁻¹) * s⁻¹ * u₀, mul_mem hc' hu₀, Or.inr ?_⟩
        rw [hsplit, h1]
        group
    s_mem_normalizer_R₂ := mul_mem hD.s_mem_normalizer_R₂
      (centralizer_le_normalizer _ (hU.le_centralizer hw))
    s_mem_normalizer_U₁ := mul_mem hsU (Subgroup.le_normalizer hw) }, hvT, hv2, hvS, hs't⟩

theorem false_of_product_of_sylow
    (hD : U3EndingData G L f t T R₂ U₁ s) {Y₁ Y₂ : Subgroup G} (hY : Y₁ ⊔ Y₂ = U₁)
    (hinf : Y₁ ⊓ Y₂ = ⊥) (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a)
    (ht₁ : ∀ a ∈ Y₁, t * a * t⁻¹ ∈ Y₂) (ht₂ : ∀ b ∈ Y₂, t * b * t⁻¹ ∈ Y₁)
    (hS : ∃ S : Sylow 2 G, t ∈ S ∧ (S : Subgroup G) ≤ normalizer (U₁ : Set G) ∧
      ∀ g : G, g * t * g⁻¹ ∈ S →
        g * t * g⁻¹ ∉ normalizer ((U₁ ⊓ centralizer (Y₂ : Set G) : Subgroup G) : Set G)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, htS, hSU, hSt⟩ := hS
  have h := hD.start
  have hS2 := hD.card_sylow
  have hR := hD.r2
  have hU := hD.u1
  obtain ⟨hCA₁, hCA₂, hna₁, hna₂⟩ :=
    hU.product_facts_of_card_sylow h hS2 hR hY hinf hcomm ht₁ ht₂
  have htt : t * t = 1 := by rw [← sq]; exact hR.t_sq
  have htU : t ∈ normalizer (U₁ : Set G) := hU.normalizer_le (Subgroup.le_normalizer
    (show t ∈ szT₁ L T ⊔ R₂ ⊔ zpowers t from mem_sup_right (mem_zpowers t)))
  obtain ⟨hidx, htQ⟩ := relIndex_inf_normalizer_eq_two hY hinf hcomm hCA₁ hCA₂ hna₁ hna₂ htt htU
    ht₁ ht₂ hSU htS
  have hG : IsSimpleGroup G := h.setting.1
  have hnonab : ∃ a b : G, a * b ≠ b * a := h.setting.2.1
  apply Endings.not_exists_normal_index_two hnonab
  refine CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson S.isPGroup' S.not_dvd_index
    inf_le_left hidx htS htQ ?_ ?_
  · intro y _ hyQ
    rw [h.inv]
    have hy1 : y ≠ 1 := fun e => hyQ (e ▸ one_mem _)
    have hpos := orderOf_pos y
    have hne1 : orderOf y ≠ 1 := fun e => hy1 (orderOf_eq_one_iff.mp e)
    omega
  · intro g hg
    have hg' : g⁻¹ * t * g⁻¹⁻¹ ∈ (S : Subgroup G) := by
      rw [inv_inv]
      exact (mem_inf.mp hg).1
    exact hSt g⁻¹ hg' (by rw [inv_inv]; exact (mem_inf.mp hg).2)

end U3EndingData

theorem u3EndingInput_of_inputs (hprod : U3EndingProductInput)
    (height : U3EightLieInput) (hsyl : U3EndingSylowInput) : U3EndingInput := by
  intro G _ _ L f t T R₂ U₁ s₀ hD₀
  obtain ⟨s, v, hD, hvT, hv2, hvS, hsv⟩ := hD₀.exists_conj_eq_t_mul
  obtain ⟨Y₁, Y₂, hY, hinf, hcomm, ht₁, ht₂⟩ : ∃ Y₁ Y₂ : Subgroup G, Y₁ ⊔ Y₂ = U₁ ∧
      Y₁ ⊓ Y₂ = ⊥ ∧ (∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) ∧ (∀ a ∈ Y₁, t * a * t⁻¹ ∈ Y₂) ∧
        (∀ b ∈ Y₂, t * b * t⁻¹ ∈ Y₁) := by
    by_cases hf : f = 3
    · subst hf
      exact height G L t T R₂ U₁ s v hD hvT hv2 hvS hsv
    · exact hprod G L f t T R₂ U₁ s v hD hvT hv2 hvS hsv hf
  exact hD.false_of_product_of_sylow hY hinf hcomm ht₁ ht₂
    (hsyl G L f t T R₂ U₁ s v Y₁ Y₂ hD hvT hv2 hvS hsv hY hinf hcomm ht₁ ht₂)

end CFSG.SeitzReduction.RankOne
