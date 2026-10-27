module

public import CFSG.LargeExtraspecial.S8Rad

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Module QuadraticMap CFSG.LargeExtraspecial.S2 CFSG.LargeExtraspecial.OrthoF2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

omit [FiniteDimensional (ZMod 2) V] in
theorem polar_self_zmod2 (x : V) : polar q x x = 0 := by
  rw [polar_self, two_smul, zmod2_add_self]

structure HypBasis (q : QuadraticForm (ZMod 2) V) (p p₁ e₁ f₁ e₂ f₂ : V) : Prop where
  he₁ : e₁ ∈ perp q (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁})
  hf₁ : f₁ ∈ perp q (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁})
  he₂ : e₂ ∈ perp q ((⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) ⊔ Submodule.span (ZMod 2) {e₁, f₁})
  hf₂ : f₂ ∈ perp q ((⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) ⊔ Submodule.span (ZMod 2) {e₁, f₁})
  qe₁ : q e₁ = 0
  qf₁ : q f₁ = 0
  qe₂ : q e₂ = 0
  qf₂ : q f₂ = 0
  e₁f₁ : polar q e₁ f₁ = 1
  e₂f₂ : polar q e₂ f₂ = 1
  bot : perp q (((⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) ⊔ Submodule.span (ZMod 2) {e₁, f₁}) ⊔
    Submodule.span (ZMod 2) {e₂, f₂}) = ⊥

theorem exists_hypBasis (hq : q.polarBilin.Nondegenerate) (hV : finrank (ZMod 2) V = 6)
    {p p₁ : V} (hp : q p = 0) (hpp₁ : polar q p p₁ = 1) {T : Submodule (ZMod 2) V}
    (hT : ∀ x ∈ T, q x = 0) (hT3 : 3 ≤ finrank (ZMod 2) T) :
    ∃ e₁ f₁ e₂ f₂ : V, HypBasis q p p₁ e₁ f₁ e₂ f₂ := by
  have hmem0 : ∀ v : V, v ∈ perp q (⊥ : Submodule (ZMod 2) V) := fun v => by
    rw [perp_bot]; exact Submodule.mem_top
  have hF0 : (⊥ : Submodule (ZMod 2) V) ⊓ perp q ⊥ = ⊥ := bot_inf_eq _
  set F₁ := (⊥ : Submodule (ZMod 2) V) ⊔ Submodule.span (ZMod 2) {p, p₁} with hF₁def
  have hF₁ : F₁ ⊓ perp q F₁ = ⊥ := sup_span_pair_inf_perp_eq_bot hF0 (hmem0 p) (hmem0 p₁) hpp₁
  have hd₁ : finrank (ZMod 2) (perp q F₁) = 4 := by
    have : finrank (ZMod 2) (perp q F₁) + 2 =
        finrank (ZMod 2) (perp q (⊥ : Submodule (ZMod 2) V)) :=
      finrank_perp_sup_span_pair hq hF0 (hmem0 p) (hmem0 p₁) hpp₁
    rw [perp_bot, finrank_top, hV] at this
    omega
  obtain ⟨e₁, he₁F, he₁0, he₁⟩ := exists_singular_mem_perp (q := q) (F := F₁)
    (by rw [hd₁]; norm_num)
  obtain ⟨f₁, hf₁F, hf₁, he₁f₁⟩ := exists_hyperbolic_partner hq hF₁ he₁F he₁0 he₁
  set F₂ := F₁ ⊔ Submodule.span (ZMod 2) {e₁, f₁} with hF₂def
  have hF₂ : F₂ ⊓ perp q F₂ = ⊥ := sup_span_pair_inf_perp_eq_bot hF₁ he₁F hf₁F he₁f₁
  have hd₂ : finrank (ZMod 2) (perp q F₂) = 2 := by
    have : finrank (ZMod 2) (perp q F₂) + 2 = finrank (ZMod 2) (perp q F₁) :=
      finrank_perp_sup_span_pair hq hF₁ he₁F hf₁F he₁f₁
    rw [hd₁] at this
    omega
  obtain ⟨e₂, he₂F, he₂0, he₂⟩ : ∃ e₂ ∈ perp q F₂, e₂ ≠ 0 ∧ q e₂ = 0 := by
    by_contra hcon
    push Not at hcon
    have hE : perp q F₂ ⊓ perp q (perp q F₂) = ⊥ := by
      rw [S8.perp_perp hq, inf_comm]; exact hF₂
    have hmin := S8.isMinusType_of_aniso hq hE hd₂
      (fun x hx hqx => by by_contra h; exact hcon x hx h hqx) (m := 2) (by rw [hV]) hT hT3
    have hpe₁ : polar q p e₁ = 0 :=
      (mem_perp.mp he₁F) p (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
    have hp0 : p ≠ 0 := by
      rintro rfl
      rw [polar_zero_left] at hpp₁
      exact zero_ne_one hpp₁
    have hpe : p ≠ e₁ := by
      rintro rfl
      have := (mem_perp.mp he₁F) p₁ (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
      rw [polar_comm] at this
      rw [this] at hpp₁
      exact zero_ne_one hpp₁
    have hli : LinearIndependent (ZMod 2) ![p, e₁] :=
      linearIndependent_pair_iff.mpr ⟨hp0, he₁0, hpe⟩
    have hle : Submodule.span (ZMod 2) {p, e₁} ≤ perp q (perp q F₂) := by
      rw [S8.perp_perp hq, Submodule.span_le]
      rintro x (rfl | rfl)
      · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
      · exact Submodule.mem_sup_right (Submodule.subset_span (by simp))
    have h2 := hmin _ hle fun x hx => map_eq_zero_of_mem_span_pair hp he₁ hpe₁ hx
    rw [finrank_span_pair hli] at h2
    exact lt_irrefl _ h2
  obtain ⟨f₂, hf₂F, hf₂, he₂f₂⟩ := exists_hyperbolic_partner hq hF₂ he₂F he₂0 he₂
  refine ⟨e₁, f₁, e₂, f₂, he₁F, hf₁F, he₂F, hf₂F, he₁, hf₁, he₂, hf₂, he₁f₁, he₂f₂, ?_⟩
  have : finrank (ZMod 2) (perp q (F₂ ⊔ Submodule.span (ZMod 2) {e₂, f₂})) + 2 =
      finrank (ZMod 2) (perp q F₂) := finrank_perp_sup_span_pair hq hF₂ he₂F hf₂F he₂f₂
  rw [hd₂] at this
  have h0 : finrank (ZMod 2) (perp q (F₂ ⊔ Submodule.span (ZMod 2) {e₂, f₂})) = 0 := by omega
  exact Submodule.finrank_eq_zero.mp h0

namespace HypBasis

variable {p p₁ e₁ f₁ e₂ f₂ : V} (B : HypBasis q p p₁ e₁ f₁ e₂ f₂)
include B

omit [FiniteDimensional (ZMod 2) V]

theorem he₂' : e₂ ∈ perp q (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) := perp_sup_span_pair_le B.he₂

theorem hf₂' : f₂ ∈ perp q (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) := perp_sup_span_pair_le B.hf₂

theorem e₁e₂ : polar q e₁ e₂ = 0 := (mem_perp_sup_span_pair.mp B.he₂).2.1
theorem f₁e₂ : polar q f₁ e₂ = 0 := (mem_perp_sup_span_pair.mp B.he₂).2.2
theorem e₁f₂ : polar q e₁ f₂ = 0 := (mem_perp_sup_span_pair.mp B.hf₂).2.1
theorem f₁f₂ : polar q f₁ f₂ = 0 := (mem_perp_sup_span_pair.mp B.hf₂).2.2

theorem f₁e₁ : polar q f₁ e₁ = 1 := by rw [polar_comm]; exact B.e₁f₁
theorem f₂e₂ : polar q f₂ e₂ = 1 := by rw [polar_comm]; exact B.e₂f₂
theorem e₂e₁ : polar q e₂ e₁ = 0 := by rw [polar_comm]; exact B.e₁e₂
theorem e₂f₁ : polar q e₂ f₁ = 0 := by rw [polar_comm]; exact B.f₁e₂
theorem f₂e₁ : polar q f₂ e₁ = 0 := by rw [polar_comm]; exact B.e₁f₂
theorem f₂f₁ : polar q f₂ f₁ = 0 := by rw [polar_comm]; exact B.f₁f₂

theorem eq_sum {u : V} (hu : u ∈ perp q (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁})) :
    u = polar q u f₁ • e₁ + polar q u e₁ • f₁ + polar q u f₂ • e₂ + polar q u e₂ • f₂ := by
  set r := u - (polar q u f₁ • e₁ + polar q u e₁ • f₁ + polar q u f₂ • e₂ + polar q u e₂ • f₂)
    with hr
  have hrF : r ∈ perp q (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) :=
    sub_mem hu (add_mem (add_mem (add_mem (Submodule.smul_mem _ _ B.he₁)
      (Submodule.smul_mem _ _ B.hf₁)) (Submodule.smul_mem _ _ B.he₂'))
      (Submodule.smul_mem _ _ B.hf₂'))
  have key : ∀ v : V, polar q v r = polar q v u - (polar q u f₁ * polar q v e₁ +
      polar q u e₁ * polar q v f₁ + polar q u f₂ * polar q v e₂ + polar q u e₂ * polar q v f₂) :=
    fun v => by simp only [hr, polar_sub_right, polar_add_right, polar_smul_right, smul_eq_mul]
  have h1 : polar q e₁ r = 0 := by
    rw [key, polar_self_zmod2, B.e₁f₁, B.e₁e₂, B.e₁f₂, polar_comm q e₁ u]; ring
  have h2 : polar q f₁ r = 0 := by
    rw [key, polar_self_zmod2, B.f₁e₁, B.f₁e₂, B.f₁f₂, polar_comm q f₁ u]; ring
  have h3 : polar q e₂ r = 0 := by
    rw [key, polar_self_zmod2, B.e₂e₁, B.e₂f₁, B.e₂f₂, polar_comm q e₂ u]; ring
  have h4 : polar q f₂ r = 0 := by
    rw [key, polar_self_zmod2, B.f₂e₁, B.f₂f₁, B.f₂e₂, polar_comm q f₂ u]; ring
  have hr0 : r ∈ perp q (((⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) ⊔
      Submodule.span (ZMod 2) {e₁, f₁}) ⊔ Submodule.span (ZMod 2) {e₂, f₂}) :=
    mem_perp_sup_span_pair.mpr ⟨mem_perp_sup_span_pair.mpr ⟨hrF, h1, h2⟩, h3, h4⟩
  rw [B.bot, Submodule.mem_bot, sub_eq_zero] at hr0
  exact hr0

end HypBasis

end CFSG.LargeExtraspecial.S14
