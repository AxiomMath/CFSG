module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1Stage
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1UOne

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

theorem mem_normalizer_szR_of {G : Type*} [Group G] [Finite G] {T₁ R₂ : Subgroup G} {t d : G}
    (hdT : d ∈ normalizer (T₁ : Set G)) (hdR : d ∈ normalizer (R₂ : Set G)) (hdt : d * t = t * d) :
    d ∈ normalizer (szR T₁ R₂ t : Set G) := by
  refine mem_normalizer_of_forall_inv_mul_mul_mem fun x hx => ?_
  have hle : szR T₁ R₂ t ≤ (szR T₁ R₂ t).comap (MulAut.conj d⁻¹).toMonoidHom := by
    show T₁ ⊔ R₂ ⊔ zpowers t ≤ _
    refine sup_le (sup_le (fun y hy => ?_) (fun r hr => ?_)) (zpowers_le.mpr ?_)
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact le_szR_left _ _ _ ((mem_normalizer_iff''.mp hdT y).mp hy)
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact le_szR_mid _ _ _ ((mem_normalizer_iff''.mp hdR r).mp hr)
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
        show d⁻¹ * t * d = t by rw [mul_assoc, ← hdt, inv_mul_cancel_left]]
      exact mem_szR_right _ _ _
  have := hle hx
  rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this

namespace U3A₁Coords

variable {G : Type*} [Group G] {K : Type*} [Field K] {A₁ : Subgroup G} {d : G} {v : G → K}
  {μ : K}

theorem v_one (hc : U3A₁Coords A₁ d v μ) : v 1 = 0 := by
  have h := hc.mul 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at h
  linear_combination -h

theorem eq_one_of_conj_eq (hc : U3A₁Coords A₁ d v μ) (hμ1 : μ ≠ 1) {b : G} (hb : b ∈ A₁)
    (hbd : d⁻¹ * b * d = b) : b = 1 := by
  have h1 := hc.conj b hb
  rw [hbd] at h1
  have h2 : (μ - 1) * v b = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hμ1
  · exact hc.inj b hb 1 (one_mem _) (by rw [h3, hc.v_one])

end U3A₁Coords

theorem ne_one_of_generator {K : Type*} [Field K] [Fintype K] (hK : 2 < Fintype.card K) {μ : K}
    (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) : μ ≠ 1 := by
  classical
  intro h1
  have hall : ∀ w : K, w = 0 ∨ w = 1 := by
    intro w
    by_cases hw : w = 0
    · exact Or.inl hw
    · obtain ⟨m, hm⟩ := hμ w hw
      exact Or.inr (by rw [← hm, h1, one_pow])
  have hle : Fintype.card K ≤ 2 := by
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun w _ => by
      rcases hall w with h | h <;> simp [h]
    calc Fintype.card K = (Finset.univ : Finset K).card := rfl
      _ ≤ ({0, 1} : Finset K).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  omega

section Certificates

theorem U3C1Stage.of_data {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
    {T R₂ : Subgroup G} (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hne : ∃ r ∈ R₂, r ^ 2 ≠ 1) (hT : T ≤ szT₁ L T ⊔ zpowers t) {E : Subgroup G}
    (hEY : E ≤ normalizer (szR (szT₁ L T) R₂ t : Set G))
    (hEn : normalizer (szR (szT₁ L T) R₂ t : Set G) ≤ normalizer (E : Set G))
    (hEA : E ≤ centralizer (szA₁ (szT₁ L T) : Set G))
    (htr : ∀ r ∈ R₂, ∃ x ∈ E, x * t * x⁻¹ * (r * t)⁻¹ ∈ szA₁ (szT₁ L T)) {d : G}
    (hdodd : Odd (orderOf d)) (hdR : d ∈ normalizer (R₂ : Set G))
    (hdT : d ∈ normalizer (szT₁ L T : Set G)) (hdt : d * t = t * d) {K : Type} [Field K]
    [Fintype K] [CharP K 2] {v : G → K} {μ : K} (hK : Fintype.card K = 2 ^ f)
    (hc : U3A₁Coords (szA₁ (szT₁ L T)) d v μ) (hμ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, μ ^ m = w) :
    ∃ U₁ : Subgroup G, U3C1Stage G L f t T d R₂ (u3C1U L T R₂ t) U₁ 1 := by
  obtain ⟨hYT, hYA⟩ := h.normalizer_szR_le_normalizer_szT₁_of_inv hS2 hR hinv hne
  have hdY := mem_normalizer_szR_of hdT hdR hdt
  have hμ1 : μ ≠ 1 := ne_one_of_generator (by
    rw [hK]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le) hμ
  have hdfix : ∀ r ∈ R₂, r⁻¹ * (d⁻¹ * r * d) ∈ szA₁ (szT₁ L T) → r ∈ szA₁ (szT₁ L T) := by
    intro r hr ha
    refine hR.mem_szA₁_of_sq_eq_one_of_inv hinv hr ?_
    refine hc.eq_one_of_conj_eq hμ1 (hR.sq_mem r hr) ?_
    set a := r⁻¹ * (d⁻¹ * r * d) with hadef
    have e1 : d⁻¹ * r * d = r * a := by rw [hadef]; group
    have hra : r * a = a * r := hR.comm r hr a (hR.le ha)
    calc d⁻¹ * r ^ 2 * d = (d⁻¹ * r * d) ^ 2 := by rw [sq, sq]; group
      _ = (r * a) ^ 2 := by rw [e1]
      _ = r ^ 2 * a ^ 2 := (Commute.mul_pow hra 2)
      _ = r ^ 2 := by rw [hR.sq_A₁ a ha, mul_one]
  obtain ⟨U₁, hHU₁, hU₁U, hUU₁, htU₁, hsupU₁, hdU₁, hinf⟩ :=
    h.exists_u3C1U₁ hS2 hR hinv hne hdY hdodd hdt hdfix
  have htrU := h.exists_u3C1U_conj_of_transitive hS2 hR hinv hne hEY hEn hEA htr
  refine ⟨U₁,
    { start := h
      card_sylow := hS2
      T_le := hT
      one_le := le_rfl
      coords := ⟨K, inferInstance, inferInstance, inferInstance, v, μ, hK, hc, hμ⟩
      d_odd := hdodd
      d_norm := ⟨⟨hdR, hdT⟩, mem_centralizer_singleton_iff.mpr hdt⟩
      le_centralizer := hR.le_centralizer_T₁
      comm := hR.comm
      card := by rw [hR.card]
      omega := fun x hx h2 => hR.mem_szA₁_of_sq_eq_one_of_inv hinv hx h2
      pow := fun x hx => by
        rw [show 2 ^ (1 + 1) = 4 from rfl]
        exact hR.pow_four_eq_one_of_inv hx
      le := hR.le
      inv := hinv
      U_le := u3C1U_le_normalizer
      U_normal := le_normalizer_u3C1U hYT hYA
      isSylowOf := h.isSylowOf_u3C1U_of_transitive hS2 hR hinv hne hT htrU
      card_U := by rw [h.card_u3C1U_of_transitive hS2 hR hinv htrU]
      szR_le := h.szR_le_u3C1U hS2 hR
      conj_t_not_mem := fun u hu huR => h.conj_t_not_mem_u3C1U hS2 hR hinv hu huR
      conj_szA₁ := fun u hu b hb => U3Start.conj_szA₁_of_mem_u3C1U hu hb
      conj_T₁ := fun u hu y hy => hu.2.2.2 y hy
      conj_V₁ := fun u hu r hr => h.conj_R₂_mem_u3C1U hS2 hR hinv (hU₁U hu) hr
      inf_centralizer := h.u3C1U_inf_centralizer hS2 hR
      U₁_le := hU₁U
      U₁_normal := hUU₁
      sup_eq := hsupU₁
      t_not_mem := htU₁
      inf_eq := hinf
      d_mem_U₁ := hdU₁ }⟩

end Certificates

end CFSG.SeitzReduction.RankOne
