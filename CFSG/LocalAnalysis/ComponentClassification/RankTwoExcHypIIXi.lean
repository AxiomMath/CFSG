module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIClassicalConfig

public section

namespace CFSG.ComponentClassification.RankTwoExcHypII

open Subgroup CFSG.Open CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.RankTwoHypIIY
open CFSG.ComponentClassification.RankTwoHypIIClassical (HypIIConfig)
open CFSG.ComponentClassification.OuterAutomorphisms (inner_normal)

variable {C : Type*} [Group C]

@[expose] def SecondGraphWitness (ξ : MulAut C) : Prop :=
  ∀ E₀ : Subgroup (MulAut C), IsElemAbelian 2 E₀ → E₀ ≠ ⊥ → E₀ ≤ OuterAutomorphisms.inner C →
    E₀ ≤ centralizer {ξ} →
    OuterAutomorphisms.inner C ⊓ centralizer {ξ} ≤ normalizer (E₀ : Set (MulAut C)) →
    (∀ x ∈ E₀, x ≠ 1 → ∀ w ∈ OuterAutomorphisms.inner C ⊓ centralizer {x},
      w * ξ * w⁻¹ * ξ⁻¹ ∈ E₀) → False

theorem exists_config_secondGraph [Finite C] {ξ : MulAut C} {G' : Type*} [Group G']
    (hrig : ∀ α : MulAut C, α ∉ OuterAutomorphisms.inner C → α ^ 2 = 1 →
      RigidInvolution (OuterAutomorphisms.inner C) α ∨ ∃ φ : MulAut C, φ * α * φ⁻¹ = ξ)
    (Θ : MulAut C →* G') (hcomm : ∀ a b : G', a * b = b * a)
    (hker : ∀ α ∈ Θ.ker, α ^ 2 = 1 → α ∈ OuterAutomorphisms.inner C)
    (hodd : ∀ x : MulAut C, x ^ 2 = 1 → x ≠ 1 →
      CFSG.oddCore ↥(OuterAutomorphisms.inner C ⊓ centralizer ({x} : Set (MulAut C))) = ⊥)
    {E M : Subgroup (MulAut C)} (h : HypIIConfig (OuterAutomorphisms.inner C) E M) :
    ∃ E' M' : Subgroup (MulAut C), HypIIConfig (OuterAutomorphisms.inner C) E' M' ∧ ξ ∈ E' ∧
      E' ⊓ OuterAutomorphisms.inner C ≠ ⊥ ∧
      ∀ x ∈ E', x ≠ 1 → OuterAutomorphisms.inner C ⊓ centralizer ({x} : Set (MulAut C)) ≤
        normalizer (E' : Set (MulAut C)) := by
  have : Finite (MulAut C) := MulEquiv.finite_left
  have hX := inner_normal C
  have hconj : ∀ {E M : Subgroup (MulAut C)}, HypIIConfig (OuterAutomorphisms.inner C) E M →
      ∀ t ∈ E, t ∉ OuterAutomorphisms.inner C → ∃ φ : MulAut C, φ * t * φ⁻¹ = ξ := by
    intro E M h t htE htX
    have ht1 : t ≠ 1 := fun h1 => htX (h1 ▸ one_mem _)
    exact (hrig t htX (h.elemAbelian.2 t htE)).resolve_left (h.not_rigidInvolution htE ht1)
  obtain ⟨t₀, ht₀E, ht₀X⟩ := IsConcreteLE.not_le_iff_exists.mp h.not_le
  obtain ⟨φ, hφ⟩ := hconj h t₀ ht₀E ht₀X
  set E' := E.map (MulAut.conj φ).toMonoidHom
  set M' := M.map (MulAut.conj φ).toMonoidHom
  have h' : HypIIConfig (OuterAutomorphisms.inner C) E' M' := h.conj hX φ
  have hξE : ξ ∈ E' := ⟨t₀, ht₀E, by rw [← hφ]; rfl⟩
  have hξ2 : ξ ^ 2 = 1 := h'.elemAbelian.2 ξ hξE
  refine ⟨E', M', h', hξE, fun hbot => ?_, fun x hxE hx1 =>
    h'.centralizer_le_normalizer hX hxE hx1 (hodd x (h'.elemAbelian.2 x hxE) hx1)⟩
  have hΘ : ∀ e ∈ E', e ≠ 1 → Θ e = Θ ξ := by
    intro e heE he1
    have heX : e ∉ OuterAutomorphisms.inner C := fun heX => he1 (by
      have : e ∈ E' ⊓ OuterAutomorphisms.inner C := ⟨heE, heX⟩
      rwa [hbot, mem_bot] at this)
    obtain ⟨ψ, hψ⟩ := hconj h' e heE heX
    rw [← hψ, map_mul, map_mul, hcomm (Θ ψ) (Θ e), mul_assoc, ← map_mul, mul_inv_cancel,
      map_one, mul_one]
  have hle : E' ≤ zpowers ξ := by
    intro e heE
    by_cases he1 : e = 1
    · rw [he1]
      exact one_mem _
    have heξE : e * ξ ∈ E' := mul_mem heE hξE
    have hker' : e * ξ ∈ Θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, hΘ e heE he1, ← map_mul, ← sq, hξ2, map_one]
    have heξX := hker _ hker' (h'.elemAbelian.2 _ heξE)
    have heξ : e * ξ ∈ E' ⊓ OuterAutomorphisms.inner C := ⟨heξE, heξX⟩
    rw [hbot, mem_bot] at heξ
    have : e = ξ⁻¹ := eq_inv_of_mul_eq_one_left heξ
    rw [this]
    exact inv_mem (mem_zpowers ξ)
  have hcard := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers] at hcard
  have := orderOf_le_of_pow_eq_one two_pos hξ2
  have := h'.four_le_card
  omega

theorem not_config_secondGraph [Finite C] {ξ : MulAut C} {G' : Type*} [Group G']
    (hrig : ∀ α : MulAut C, α ∉ OuterAutomorphisms.inner C → α ^ 2 = 1 →
      RigidInvolution (OuterAutomorphisms.inner C) α ∨ ∃ φ : MulAut C, φ * α * φ⁻¹ = ξ)
    (Θ : MulAut C →* G') (hcomm : ∀ a b : G', a * b = b * a)
    (hker : ∀ α ∈ Θ.ker, α ^ 2 = 1 → α ∈ OuterAutomorphisms.inner C)
    (hodd : ∀ x : MulAut C, x ^ 2 = 1 → x ≠ 1 →
      CFSG.oddCore ↥(OuterAutomorphisms.inner C ⊓ centralizer ({x} : Set (MulAut C))) = ⊥)
    (hwit : SecondGraphWitness ξ) (E M : Subgroup (MulAut C)) :
    ¬ HypIIConfig (OuterAutomorphisms.inner C) E M := by
  intro h
  obtain ⟨E', M', h', hξE, hbot, hN⟩ := exists_config_secondGraph hrig Θ hcomm hker hodd h
  set E₀ := E' ⊓ OuterAutomorphisms.inner C with hE₀
  have hX := inner_normal C
  have hE₀ab : IsElemAbelian 2 E₀ :=
    ⟨⟨⟨fun a b => Subtype.ext (h'.commute a.2.1 b.2.1)⟩⟩, fun x hx => h'.elemAbelian.2 x hx.1⟩
  have hE₀ξ : E₀ ≤ centralizer {ξ} := fun x hx =>
    mem_centralizer_singleton_iff.mpr (h'.commute hx.1 hξE)
  have hξ1 : ξ ≠ 1 := fun h1 => by
    obtain ⟨t, htE, htX⟩ := IsConcreteLE.not_le_iff_exists.mp h'.not_le
    obtain ⟨ψ, hψ⟩ := ((hrig t htX (h'.elemAbelian.2 t htE)).resolve_left
      (h'.not_rigidInvolution htE fun ht1 => htX (ht1 ▸ one_mem _)))
    rw [h1, show ψ * t * ψ⁻¹ = 1 ↔ t = 1 by
      constructor
      · intro e
        have := congrArg (fun y => ψ⁻¹ * y * ψ) e
        simpa [mul_assoc] using this
      · intro e
        rw [e, mul_one, mul_inv_cancel]] at hψ
    exact htX (hψ ▸ one_mem _)
  have hnorm : ∀ c ∈ normalizer (E' : Set (MulAut C)), c ∈ normalizer (E₀ : Set (MulAut C)) := by
    intro c hc
    rw [mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyE, hyX⟩
      exact ⟨(mem_normalizer_iff.mp hc y).mp hyE, hX.conj_mem y hyX c⟩
    · rintro ⟨hyE, hyX⟩
      refine ⟨(mem_normalizer_iff.mp hc y).mpr hyE, ?_⟩
      have := hX.conj_mem _ hyX c⁻¹
      simpa [mul_assoc] using this
  have hE₀n : OuterAutomorphisms.inner C ⊓ centralizer {ξ} ≤ normalizer (E₀ : Set (MulAut C)) :=
    fun c hc => hnorm c (hN ξ hξE hξ1 hc)
  refine hwit E₀ hE₀ab hbot inf_le_right hE₀ξ hE₀n fun x hx hx1 w hw => ?_
  have hwN := hN x hx.1 hx1 hw
  have hwξ : w * ξ * w⁻¹ ∈ E' := (mem_normalizer_iff.mp hwN ξ).mp hξE
  refine ⟨mul_mem hwξ (E'.inv_mem hξE), ?_⟩
  have h1 := hX.conj_mem _ ((OuterAutomorphisms.inner C).inv_mem hw.1) ξ
  have h2 := mul_mem hw.1 h1
  simpa [mul_assoc] using h2

theorem hypII_of_secondGraph [Finite C] (hZ : center C = ⊥) {ξ : MulAut C} {G' : Type*}
    [Group G']
    (hrig : ∀ α : MulAut C, α ∉ OuterAutomorphisms.inner C → α ^ 2 = 1 →
      RigidInvolution (OuterAutomorphisms.inner C) α ∨ ∃ φ : MulAut C, φ * α * φ⁻¹ = ξ)
    (Θ : MulAut C →* G') (hcomm : ∀ a b : G', a * b = b * a)
    (hker : ∀ α ∈ Θ.ker, α ^ 2 = 1 → α ∈ OuterAutomorphisms.inner C)
    (hodd : ∀ x : MulAut C, x ^ 2 = 1 → x ≠ 1 →
      CFSG.oddCore ↥(OuterAutomorphisms.inner C ⊓ centralizer ({x} : Set (MulAut C))) = ⊥)
    (hwit : SecondGraphWitness ξ) {A : Type*} [Group A] (hA : commutator A = ⊤)
    (hoddA : Odd (Nat.card (center A))) (e : A ⧸ center A ≃* C) : HypII A := by
  have : Finite (MulAut C) := MulEquiv.finite_left
  exact RankTwoHypIIClassical.hypII_of_forall_not_config (autModel_mulAut hZ)
    (not_config_secondGraph hrig Θ hcomm hker hodd hwit) hA hoddA e

end CFSG.ComponentClassification.RankTwoExcHypII
