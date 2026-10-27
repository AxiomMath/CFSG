module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR8
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR6

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.Obs
open scoped commutatorElement

@[expose] def B_p72c_P79 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x y : G) (K T S : Subgroup G),
    Th2Std x y K T S → ¬ IsTerminalPair 2 x K → ∀ ρ : Th2Row,
      (ρ = .r1b ∨ ρ = .r3b ∨ ρ = .r3c) → ρ.holds x y K T S →
        ∀ (B : Subgroup G) (t : G) (J : Subgroup G), Th2Pick ρ x y K T S B t J →
          ∃ (W V : Subgroup G) (b : G) (X₀ X₁ : Subgroup G),
            W ≤ V ∧ V ≤ B ∧ Nat.card B = 2 * Nat.card V ∧ Nat.card B = 4 * Nat.card W ∧ b ∈ B ∧
            Odd (Nat.card X₀) ∧ Odd (Nat.card X₁) ∧
            X₀ ≤ pPrimeCoreOf 2 (centralizer ({t} : Set G)) ∧ X₁ ≤ centralizer ({t} : Set G) ∧
            (∀ w ∈ W, ∀ z ∈ X₀, w * z = z * w) ∧ (∀ v ∈ V, ∀ z ∈ X₁, v * z = z * v) ∧
            (∀ g ∈ B, ∀ z ∈ X₀, g * z * g⁻¹ ∈ X₀) ∧ (∀ z ∈ X₁, ∀ z' ∈ X₀, z * z' * z⁻¹ ∈ X₀) ∧
            (∀ z ∈ X₁, b * z * b⁻¹ = z⁻¹) ∧ ⁅⁅X₀, X₁⁆, X₁⁆ ≠ ⊥ ∧
            ((∀ v ∈ V, ∀ z ∈ X₀, v * z = z * v) ∨
              (∀ v ∈ V, v ∉ W → ∃ z ∈ ⁅⁅X₀, X₁⁆, X₁⁆, v * z ≠ z * v))

theorem u2_of_p79 (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) (hKG : B_ivk_oddcent)
    (h79 : B_p72c_P79) : B_thm2_p72c_U2 := by
  intro G _ _ hG x y K T S h hnt ρ hρ hρh hbal B t J hpick
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hθ
  have hlevel : ρ.level = Th2Level.fiveHalves := by rcases hρ with rfl | rfl | rfl <;> rfl
  have hθ' : thetaHalf 2 B = ⊥ := by
    have h1 : ρ.level.theta B = ⊥ := hθ
    rw [hlevel] at h1
    exact h1
  have hbalB : IsKBal 3 B ∧ IsWeakKBal 2 B := by
    have h1 := hbal B hpick.mem
    rw [hlevel] at h1
    exact h1
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hpick.elem
  obtain ⟨W, V, b, X₀, X₁, hWV, hVB, hVcard, hWcard, hbB, hX₀odd, hX₁odd, hX₀t, hX₁t, hWX₀, hVX₁,
    hBX₀, hX₁X₀, hbinv, hZne, hα⟩ := h79 G hG x y K T S h hnt ρ hρ hρh B t J hpick
  have htB : t ∈ B := hpick.t_mem.1
  have ht2 : orderOf t = 2 := hpick.t_two
  set Z : Subgroup G := ⁅⁅X₀, X₁⁆, X₁⁆ with hZ
  have hZX₀ : Z ≤ X₀ := by
    have h1 : ⁅X₀, X₁⁆ ≤ X₀ := by
      rw [Subgroup.commutator_le]
      intro z hz y hy
      have : ⁅z, y⁆ = z * (y * z⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      exact X₀.mul_mem hz (hX₁X₀ y hy z⁻¹ (X₀.inv_mem hz))
    rw [hZ, Subgroup.commutator_le]
    intro m hm y hy
    have : ⁅m, y⁆ = m * (y * m⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact X₀.mul_mem (h1 hm) (hX₁X₀ y hy m⁻¹ (X₀.inv_mem (h1 hm)))
  have key : ∀ u ∈ B, u ≠ 1 → (∀ z ∈ X₀, u * z = z * u) → (∀ z ∈ X₁, u * z = z * u) →
      ¬ Z ≤ pPrimeCoreOf 2 (centralizer ({u} : Set G)) → False := by
    intro u huB hu1 hu₀ hu₁ hZnot
    have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq u huB) hu1
    have hut : u * t = t * u := hBc u huB t htB
    have hZt : Z ≤ pPrimeCoreOf 2 (centralizer ({t} : Set G)) := hZX₀.trans hX₀t
    have hZu : Z ≤ centralizer ({u} : Set G) := fun z hz =>
      mem_centralizer_singleton_iff.2 (hu₀ z (hZX₀ hz)).symm
    obtain ⟨L, hL, htN, hZN, htnot, hZnot'⟩ := exists_pComponent_of_Z ht2 hut hZt hZu hZnot
    have htu : t ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.2 hut.symm
    have hunb : IsUnbalancingTriple u t L :=
      ⟨⟨hu2, hL⟩, ht2, htu, htN, fun hle => hZnot' (fun z hz => hle ⟨hZt hz, hZu hz⟩)⟩
    have hu := kBar_u2_of_unbal hG hL34 h102 hunb
    have hLN := centralizer_le_normalizer_of_u2 hG.pRank_eq_four.le hu2 hL hu
    have hXu : X₁ ≤ centralizer ({u} : Set G) := fun z hz =>
      mem_centralizer_singleton_iff.2 (hu₁ z hz).symm
    have hbu : b ∈ centralizer ({u} : Set G) :=
      mem_centralizer_singleton_iff.2 (hBc b hbB u huB)
    have hEG := endgame_comm_le_cSec hKG ht2 hut hL hLN hu hXu hX₁t hX₁odd hbu hbinv
    have hX₀A : X₀ ≤ pPrimeCoreOf 2 (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) :=
      le_inf hX₀t (fun z hz => mem_centralizer_singleton_iff.2 (hu₀ z hz).symm)
    have hZle : Z ≤ ⁅⁅pPrimeCoreOf 2 (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G), X₁⁆,
        X₁⁆ :=
      Subgroup.commutator_mono (Subgroup.commutator_mono hX₀A le_rfl) le_rfl
    exact hZnot' (hZle.trans hEG)
  obtain ⟨u, huV, hu1, huX₀, huX₁, hZnot⟩ :=
    exists_defect_centralizing_actors_of_thetaHalf hpick.elem hpick.rank hbalB.1 hθ'
      hWV hVB hVcard hWcard hZne hWX₀ hVX₁ hα
  exact key u (hVB huV) hu1 huX₀ huX₁ hZnot

end CFSG.GH74.GLS
