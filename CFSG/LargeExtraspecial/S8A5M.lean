module

public import CFSG.LargeExtraspecial.S4EightG
public import CFSG.LargeExtraspecial.S6Basic
public import CFSG.LargeExtraspecial.S8DimA
public import CFSG.LargeExtraspecial.S8Rad

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial.S2

section Abstract

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]

theorem sub_mem_of_finrank_eq_succ {V K : Submodule (ZMod 2) E} (hVK : V ≤ K)
    (hdim : finrank (ZMod 2) K = finrank (ZMod 2) V + 1) {k₁ k₂ : E} (hk₁ : k₁ ∈ K)
    (hk₂ : k₂ ∈ K) (hk₁V : k₁ ∉ V) (hk₂V : k₂ ∉ V) : k₁ - k₂ ∈ V := by
  have hk₁0 : k₁ ≠ 0 := fun h => hk₁V (h ▸ V.zero_mem)
  have hle : V ⊔ (ZMod 2) ∙ k₁ ≤ K :=
    sup_le hVK ((Submodule.span_singleton_le_iff_mem _ _).mpr hk₁)
  have hinf : V ⊓ (ZMod 2) ∙ k₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hv, hvk⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hvk
    rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
    · rw [zero_smul]; exact Submodule.zero_mem _
    · rw [one_smul] at hv; exact absurd hv hk₁V
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq V ((ZMod 2) ∙ k₁)
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hk₁0] at h1
  have heq : V ⊔ (ZMod 2) ∙ k₁ = K := Submodule.eq_of_le_of_finrank_le hle (by omega)
  rw [← heq] at hk₂
  obtain ⟨v, hv, c, hc, rfl⟩ := Submodule.mem_sup.mp hk₂
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hc
  rcases zmod2_eq_zero_or_eq_one a with rfl | rfl
  · rw [zero_smul, add_zero] at hk₂V
    exact absurd hv hk₂V
  · rw [one_smul, show k₁ - (v + k₁) = -v by abel]
    exact V.neg_mem hv

theorem finrank_sup_inf_fixSpace {V V₁ : Submodule (ZMod 2) E} {w : E ≃ₗ[ZMod 2] E}
    (hdisj : V ⊓ V₁ = ⊥) (hwV : V ≤ fixSpace w) :
    finrank (ZMod 2) ↥((V ⊔ V₁) ⊓ fixSpace w) =
      finrank (ZMod 2) V + finrank (ZMod 2) ↥(V₁ ⊓ fixSpace w) := by
  rw [sup_inf_assoc_of_le V₁ hwV]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq V (V₁ ⊓ fixSpace w)
  have h2 : V ⊓ (V₁ ⊓ fixSpace w) = ⊥ := by
    rw [eq_bot_iff, ← hdisj]
    exact inf_le_inf_left _ inf_le_left
  rw [h2, finrank_bot, add_zero] at h1
  exact h1

omit [FiniteDimensional (ZMod 2) E] in
theorem apply_sub_eq_of_commute {l w : E ≃ₗ[ZMod 2] E} (hlw : l * w = w * l) (v : E) :
    l (w v - v) = w (l v) - l v := by
  rw [map_sub, ← LinearEquiv.mul_apply, hlw, LinearEquiv.mul_apply]

theorem rank_lemma_A5 {V Y C : Submodule (ZMod 2) E} {a : E} {L : Set (E ≃ₗ[ZMod 2] E)}
    {w : E ≃ₗ[ZMod 2] E} (hVC : V ≤ C) (hCY : C ≤ Y)
    (hdimC : finrank (ZMod 2) C = finrank (ZMod 2) V + 2)
    (hLY : ∀ l ∈ L, ∀ y ∈ Y, l y - y ∈ C) (hLC : ∀ l ∈ L, ∀ c ∈ C, l c - c ∈ V)
    (hwV : ∀ v ∈ V, w v = v) (hwL : ∀ l ∈ L, l * w = w * l)
    (hfix : ∀ v : E, (∀ l ∈ L, l v = v) → v ∈ (ZMod 2) ∙ a)
    {l₁ l₂ : E ≃ₗ[ZMod 2] E} (hl₁ : l₁ ∈ L) (hl₂ : l₂ ∈ L)
    (hF₁ : ∀ y ∈ Y, l₁ y - y ∈ V → y ∈ C) (hF₂ : ∀ y ∈ Y, l₂ y - y ∈ V → y ∈ C)
    (hF₁₂ : ∀ y ∈ Y, (l₁ * l₂) y - y ∈ V → y ∈ C) :
    (∀ y ∈ Y, w y - y ∈ (ZMod 2) ∙ a) ∨
      finrank (ZMod 2) ↥(Y ⊓ fixSpace w) = finrank (ZMod 2) V + 1 := by
  by_cases hC : ∀ c ∈ C, w c = c
  · left
    intro y hy
    refine hfix _ fun l hl => ?_
    rw [apply_sub_eq_of_commute (hwL l hl)]
    have h2 := hC _ (hLY l hl y hy)
    rw [map_sub] at h2
    calc w (l y) - l y = (w (l y) - w y) + (w y - l y) := by abel
      _ = (l y - y) + (w y - l y) := by rw [h2]
      _ = w y - y := by abel
  · right
    push Not at hC
    obtain ⟨c₀, hc₀C, hc₀⟩ := hC
    set f : E →ₗ[ZMod 2] E := (w : E →ₗ[ZMod 2] E) - 1 with hf
    have hfapp : ∀ v, f v = w v - v := fun v => rfl
    have hδC : C.map f ≤ (ZMod 2) ∙ a := by
      rintro _ ⟨c, hc, rfl⟩
      refine hfix _ fun l hl => ?_
      rw [hfapp, apply_sub_eq_of_commute (hwL l hl)]
      have h2 := hwV _ (hLC l hl c hc)
      rw [map_sub] at h2
      calc w (l c) - l c = (w (l c) - w c) + (w c - l c) := by abel
        _ = (l c - c) + (w c - l c) := by rw [h2]
        _ = w c - c := by abel
    have hδC0 : C.map f ≠ ⊥ := by
      intro h
      apply hc₀
      have hmem : f c₀ ∈ C.map f := Submodule.mem_map_of_mem hc₀C
      rw [h, Submodule.mem_bot, hfapp, sub_eq_zero] at hmem
      exact hmem
    have hdimδ : finrank (ZMod 2) ↥(C.map f) = 1 := by
      have h1 := Submodule.finrank_mono hδC
      have h2 : finrank (ZMod 2) ↥((ZMod 2) ∙ a) ≤ 1 := by
        by_cases ha : a = 0
        · rw [ha, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]
          omega
        · rw [finrank_span_singleton ha]
      have h3 : finrank (ZMod 2) ↥(C.map f) ≠ 0 := fun h =>
        hδC0 (Submodule.finrank_eq_zero.mp h)
      omega
    have hK := finrank_map_add_finrank_inf_ker f C
    rw [hdimδ] at hK
    have hdimK : finrank (ZMod 2) ↥(C ⊓ fixSpace w) = finrank (ZMod 2) V + 1 := by
      change finrank (ZMod 2) ↥(C ⊓ LinearMap.ker f) = _
      omega
    have hVK : V ≤ C ⊓ fixSpace w := fun v hv => ⟨hVC hv, mem_fixSpace.mpr (hwV v hv)⟩
    have hYC : Y ⊓ fixSpace w ≤ C := by
      intro y hy'
      obtain ⟨hy, hwy⟩ := Submodule.mem_inf.mp hy'
      rw [mem_fixSpace] at hwy
      by_contra hyC
      have hk : ∀ l ∈ L, l y - y ∈ C ⊓ fixSpace w := fun l hl => by
        refine ⟨hLY l hl y hy, mem_fixSpace.mpr ?_⟩
        rw [map_sub, ← LinearEquiv.mul_apply, ← hwL l hl, LinearEquiv.mul_apply, hwy]
      have hk₁V : l₁ y - y ∉ V := fun h => hyC (hF₁ y hy h)
      have hk₂V : l₂ y - y ∉ V := fun h => hyC (hF₂ y hy h)
      have hk₃V : (l₁ * l₂) y - y ∉ V := fun h => hyC (hF₁₂ y hy h)
      have h12 := sub_mem_of_finrank_eq_succ hVK hdimK (hk l₁ hl₁) (hk l₂ hl₂) hk₁V hk₂V
      have h3 := hLC l₁ hl₁ _ (hk l₂ hl₂).1
      apply hk₃V
      have e : (l₁ * l₂) y - y = (l₁ (l₂ y - y) - (l₂ y - y)) + ((l₁ y - y) - (l₂ y - y)) +
          ((l₂ y - y) + (l₂ y - y)) := by
        rw [LinearEquiv.mul_apply, map_sub]
        abel
      rw [e, vec_add_self, add_zero]
      exact V.add_mem h3 h12
    have hYeq : Y ⊓ fixSpace w = C ⊓ fixSpace w :=
      le_antisymm (le_inf hYC inf_le_right) (inf_le_inf_right _ hCY)
    rw [hYeq, hdimK]

end Abstract

section Orth

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

theorem apply_not_mem_span_pair_of_mem_pointRadical (hq : q.polarBilin.Nondegenerate)
    {p p₁ : V} (hp0 : p ≠ 0) (hp : q p = 0) (hpp₁ : polar q p p₁ = 1)
    {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ pointRadical q p) (hx1 : x ≠ 1) :
    x p₁ ∉ Submodule.span (ZMod 2) {p, p₁} := by
  obtain ⟨u, huK, hu0, rfl⟩ := exists_eichler_of_mem_pointRadical hq hp0 hp hpp₁ hx hx1
  obtain ⟨-, hpu, hp₁u⟩ := mem_perp_sup_span_pair.mp huK
  intro hmem
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hmem
  rw [eichler_apply_zmod2 hp hpu, polar_comm q p₁ p, hpp₁, hp₁u, one_smul, zero_add,
    mul_one] at hab
  set c := q u with hc
  have hu : u = (a + c) • p + (b + 1) • p₁ := by
    have e : u = a • p + b • p₁ - p₁ - c • p := by rw [hab]; abel
    rw [e, sub_eq_add_neg, sub_eq_add_neg, vec_neg, vec_neg, add_smul, add_smul, one_smul]
    abel
  have h1 : polar q p u = b + 1 := by
    rw [hu, polar_add_right, polar_smul_right, polar_smul_right, polar_self_eq_zero, hpp₁,
      smul_eq_mul, smul_eq_mul]
    ring
  have h2 : polar q p₁ u = a + c := by
    rw [hu, polar_add_right, polar_smul_right, polar_smul_right, polar_self_eq_zero,
      polar_comm q p₁ p, hpp₁, smul_eq_mul, smul_eq_mul]
    ring
  rw [hpu] at h1
  rw [hp₁u] at h2
  apply hu0
  rw [hu, ← h1, ← h2, zero_smul, zero_smul, add_zero]

variable {hq : q.polarBilin.Nondegenerate}
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
  (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M))

theorem timmesfeld_2_1_b0_of_invariant {m : ℕ} (hm : 2 ≤ m)
    (hdim : finrank (ZMod 2) V = 2 * m) {p p₁ : V} (hp0 : p ≠ 0) (hp : q p = 0)
    (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1) (hD : RadDecomp ρ ⊥ ⊤ p p₁)
    {N' : Submodule (ZMod 2) M} (hN' : ∀ e : omegaGroup q hq, ∀ v ∈ N', ρ e v ∈ N')
    (x : omegaGroup q hq) (hx : (x : V ≃ₗ[ZMod 2] V) ∈ radFix q ⊥ p)
    (hx1 : (x : V ≃ₗ[ZMod 2] V) ≠ 1) (hxa : ¬ IsTypeA q x 2) :
    N' ⊓ fixSpace (ρ x) = N' ⊓ fixOf ρ (radFix q ⊥ p : Set (V ≃ₗ[ZMod 2] V)) ∧
      N'.map ((ρ x : M →ₗ[ZMod 2] M) - 1) =
        N' ⊓ fixOf ρ (radFix q ⊥ p : Set (V ≃ₗ[ZMod 2] V)) := by
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  have hpp₁' : polar q p₁ p = 1 := by rw [polar_comm]; exact hpp₁
  have hF : (⊥ : Submodule (ZMod 2) V) ⊓ perp q ⊥ = ⊥ := bot_inf_eq _
  have hdimV : finrank (ZMod 2) (perp q (⊥ : Submodule (ZMod 2) V)) = 2 * m := by
    rw [perp_bot, finrank_top]; exact hdim
  have h3 : 3 ≤ finrank (ZMod 2) (perp q (⊥ : Submodule (ZMod 2) V)) := by omega
  have hmem : ∀ v : V, v ∈ perp q (⊥ : Submodule (ZMod 2) V) := fun v => by
    rw [perp_bot]; exact Submodule.mem_top
  have htop : OmegaInvariant ρ ⊥ (⊤ : Submodule (ZMod 2) M) := fun _ _ _ _ => Submodule.mem_top
  obtain ⟨c, -, -, hcR, hc1, hca⟩ := exists_mem_radFix_not_isTypeA hq hF h3 (hmem p) (hmem p₁)
    hp0 hp hpp₁
  obtain ⟨c₁, -, -, hc₁R, hc₁1, hc₁a⟩ := exists_mem_radFix_not_isTypeA hq hF h3 (hmem p₁)
    (hmem p) hp₁0 hp₁ hpp₁'
  have hN'inv : OmegaInvariant ρ ⊥ N' := fun e _ v hv => hN' e v hv
  have hD' : RadDecomp ρ ⊥ N' p p₁ :=
    radDecomp_mono ρ hF hm hdimV htop (hmem _) (hmem _) hp0 hp hp₁ hpp₁ hD le_rfl le_top
      (x := ⟨_, (radFix_le_omegaFix hq hp₁0 hp₁ hc₁R).1⟩)
      (y := ⟨_, (radFix_le_omegaFix hq hp0 hp hcR).1⟩) hc₁R hc₁1 hc₁a hcR hc1 hca
      (fun v hv => hN' _ v hv) (fun v hv => hN' _ v hv)
  exact timmesfeld_2_1_b0 ρ hF hm hdimV hN'inv (hmem p₁) (hmem p) hp₁0 hp₁ hp hpp₁' hD'.symm x
    hx hx1 hxa

end Orth

end CFSG.LargeExtraspecial.S8
