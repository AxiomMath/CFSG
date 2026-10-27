module

public import CFSG.ClassicalInvolution.Phan.PhanQ55Plane
public import CFSG.ClassicalInvolution.Phan.PhanQ54Combined

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan

section RatSetup

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem conj_zero' : conj D (0 : V8 K) = 0 := by
  ext i
  simp [conj]

theorem rat_her_zero {r w : V8 K} (hrc : conj D r = r) (hrw : B8 r w = 0) :
    her D r w = 0 ∧ her D w r = 0 := by
  have h1 := B8_conj D r w
  rw [hrc, hrw, map_zero] at h1
  have h2 : her D r w = 0 := h1
  exact ⟨h2, by rw [her_conj_symm D r w, h2, map_zero]⟩

theorem decomp_rat {W : Submodule K (V8 K)} (hW : PhanSolid D W) {r : V8 K}
    (hrc : conj D r = r) : ∃ r₁ ∈ W, r = r₁ + conj D r₁ := by
  obtain ⟨w₁, hw₁, w₂, hw₂, hr⟩ := hW.sup r
  have hconj : conj D r = conj D w₁ + w₂ := by rw [hr, conj_add, conj_conj]
  have h1 : w₁ + conj D w₂ = conj D w₁ + w₂ := by rw [← hr, ← hconj, hrc]
  have hd : w₂ - w₁ ∈ W := W.sub_mem hw₂ hw₁
  have hcd : conj D (w₂ - w₁) = w₂ - w₁ := by
    rw [conj_sub', sub_eq_sub_iff_add_eq_add, add_comm (conj D w₂) w₁, add_comm w₂ (conj D w₁)]
    exact h1
  have h0 : w₂ - w₁ = 0 := hW.inf _ hd (by rw [hcd]; exact hd)
  have hw : w₂ = w₁ := sub_eq_zero.1 h0
  exact ⟨w₁, hw₁, by rw [hr, hw]⟩

theorem B8_rat_eq {W : Submodule K (V8 K)} (hW : PhanSolid D W) {r r₁ x : V8 K}
    (hr : r = r₁ + conj D r₁) (hr₁ : r₁ ∈ W) (hx : x ∈ W) : B8 r x = her D x r₁ := by
  have h1 : B8 r₁ x = 0 := hW.ts _ hr₁ _ hx
  rw [hr, B8_add_left, h1, zero_add, B8_comm]
  rfl

theorem her_r1_self {W : Submodule K (V8 K)} (hW : PhanSolid D W) (h2 : (2 : K) ≠ 0)
    {r r₁ : V8 K} (hr : r = r₁ + conj D r₁) (hr₁ : r₁ ∈ W) (hQ : Q8 r = 0) :
    her D r₁ r₁ = 0 := by
  have h1 : Q8 r₁ = 0 := hW.Q_eq_zero D h2 hr₁
  have h3 := Q8_add_B8 r₁ (conj D r₁)
  rw [← hr, hQ, h1, Q8_conj, h1, map_zero] at h3
  have h4 : B8 r₁ (conj D r₁) = 0 := by linear_combination -h3
  exact h4

theorem ColK.indep_rad {x y r₁ : V8 K} (h : ColK D x y) (hr0 : r₁ ≠ 0)
    (hxr : her D r₁ x = 0) (hyr : her D r₁ y = 0) {s t δ : K}
    (hst : s • x + t • y + δ • r₁ = 0) : s = 0 ∧ t = 0 ∧ δ = 0 := by
  have h1 : s * her D x x + t * her D y x = 0 := by
    have := congrArg (fun w => her D w x) hst
    simpa only [her_add_left, her_smul_left, her_zero_left, hxr, mul_zero, add_zero] using this
  have h2 : s * her D x y + t * her D y y = 0 := by
    have := congrArg (fun w => her D w y) hst
    simpa only [her_add_left, her_smul_left, her_zero_left, hyr, mul_zero, add_zero] using this
  obtain ⟨hs, ht⟩ := h.coeff_zero D h1 h2
  rw [hs, ht, zero_smul, zero_smul, zero_add, zero_add] at hst
  exact ⟨hs, ht, (smul_eq_zero.1 hst).resolve_right hr0⟩

theorem norm_sub_ne {A β f : K} (hβ : β ≠ 0) (hf : D.τ f = f) (hf0 : f ≠ 0)
    (hfz : f ≠ (A * D.τ β + β * D.τ A) / (β * D.τ β)) :
    (A - β * f) * D.τ (A - β * f) ≠ A * D.τ A := by
  intro h
  have hn : β * D.τ β ≠ 0 := norm_ne_zero D hβ
  apply hfz
  rw [eq_div_iff hn]
  simp only [map_sub, map_mul, hf] at h
  have h' : f * (f * (β * D.τ β) - (A * D.τ β + β * D.τ A)) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h' with h1 | h1
  · exact absurd h1 hf0
  · linear_combination h1

end RatSetup

section Choice

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem exists_alg_not_mem [Finite F] {S : Finset K} (hS : S.card < Nat.card F) :
    ∃ f : F, algebraMap F K f ∉ S := by
  by_contra h
  have h' : ∀ f : F, algebraMap F K f ∈ S := fun f => Classical.byContradiction fun hf => h ⟨f, hf⟩
  have hle : Nat.card F ≤ Nat.card S :=
    Nat.card_le_card_of_injective (fun f : F => (⟨algebraMap F K f, h' f⟩ : S))
      (fun f g hfg => (algebraMap F K).injective (congrArg Subtype.val hfg))
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe] at hle
  omega

end Choice

end CFSG.ClassicalInvolution.PhanQ
