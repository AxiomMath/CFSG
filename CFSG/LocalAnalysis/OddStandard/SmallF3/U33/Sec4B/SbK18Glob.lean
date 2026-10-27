module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Syl

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G]

private lemma cj_centralizer_singleton_eq {t u h : G} (hh : h * t * h⁻¹ = u) :
    cj h (centralizer ({t} : Set G)) = centralizer ({u} : Set G) := by
  ext x
  rw [mem_cj, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    have e1 : u * x = h * (t * (h⁻¹ * x * h)) * h⁻¹ := by rw [← hh]; group
    have e2 : x * u = h * ((h⁻¹ * x * h) * t) * h⁻¹ := by rw [← hh]; group
    rw [e1, e2, hx]
  · intro hx
    have e1 : t * (h⁻¹ * x * h) = h⁻¹ * (u * x) * h := by rw [← hh]; group
    have e2 : (h⁻¹ * x * h) * t = h⁻¹ * (x * u) * h := by rw [← hh]; group
    rw [e2, e1, hx]

theorem k18_glob_A {S D W V : Subgroup G} {t u : G}
    (hS : IsSylowIn 2 S (centralizer ({t} : Set G))) (hScard : Nat.card S = 2 ^ 7)
    (hfus : ∃ h : G, h * t * h⁻¹ = u)
    (hD2 : IsPGroup 2 D) (hDu : D ≤ centralizer ({u} : Set G)) (hDcard : 2 ^ 7 ≤ Nat.card D)
    (hWD : W ≤ D) (hWn : ∀ d ∈ D, ∀ w ∈ W, d * w * d⁻¹ ∈ W)
    (hWe : CFSG.Open.IsElemAbelian 2 W) (hW4 : Nat.card W = 4)
    (hWt : ∀ g : G, ∀ w ∈ W, g * t * g⁻¹ ≠ w)
    (hL45 : ∀ W' : Subgroup G, NormalIn W' S → CFSG.Open.IsElemAbelian 2 W' →
      Nat.card W' = 4 → (∀ g : G, ∀ w ∈ W', g * t * g⁻¹ ≠ w) → W' = V) :
    ∃ g : G, cj g W = V := by
  obtain ⟨h, hh⟩ := hfus
  have hS' : IsSylowIn 2 (cj h S) (centralizer ({u} : Set G)) := by
    have hs := isSylowIn_cj hS h
    rwa [cj_centralizer_singleton_eq hh] at hs
  have hcardS' : Nat.card (cj h S) = 2 ^ 7 := by rw [card_cj, hScard]
  obtain ⟨c, hcC, hcS'⟩ :=
    exists_cj_of_card_le hS' hDu hD2 (by rw [hcardS']; exact hDcard)
  have hD' : cj (c * h) S = D := (cj_cj c h S).symm.trans hcS'
  refine ⟨(c * h)⁻¹, ?_⟩
  have hW'le : cj (c * h)⁻¹ W ≤ S := by
    calc cj (c * h)⁻¹ W ≤ cj (c * h)⁻¹ D := cj_mono hWD
      _ = cj (c * h)⁻¹ (cj (c * h) S) := by rw [hD']
      _ = cj ((c * h)⁻¹ * (c * h)) S := by rw [cj_cj (c * h)⁻¹ (c * h) S]
      _ = cj 1 S := by rw [inv_mul_cancel (c * h)]
      _ = S := by rw [cj_one S]
  have hW'normal : NormalIn (cj (c * h)⁻¹ W) S := by
    refine ⟨hW'le, ?_⟩
    intro s hs k hk
    rw [mem_cj] at hk ⊢
    have hd : (c * h) * s * (c * h)⁻¹ ∈ D := by
      rw [← hD']; exact conj_mem_cj hs
    have heq : ((c * h)⁻¹)⁻¹ * (s * k * s⁻¹) * (c * h)⁻¹
        = ((c * h) * s * (c * h)⁻¹) *
          (((c * h)⁻¹)⁻¹ * k * (c * h)⁻¹) * ((c * h) * s * (c * h)⁻¹)⁻¹ := by
      group
    rw [heq]
    exact hWn _ hd _ hk
  have hW't : ∀ g : G, ∀ w ∈ cj (c * h)⁻¹ W, g * t * g⁻¹ ≠ w := by
    intro g w hw hconj
    have hw' : (c * h) * w * (c * h)⁻¹ ∈ W := by
      rw [mem_cj] at hw
      simpa using hw
    have heq : (c * h * g) * t * (c * h * g)⁻¹ = (c * h) * w * (c * h)⁻¹ := by
      rw [← hconj]; group
    exact hWt (c * h * g) ((c * h) * w * (c * h)⁻¹) hw' heq
  exact hL45 (cj (c * h)⁻¹ W) hW'normal (isElemAbelian_cj hWe)
    (by rw [card_cj, hW4]) hW't

theorem k18_glob_C {OK E₀ B₀ Y N : Subgroup G} {g₂ : G}
    (hE : cj g₂ E₀ ≤ OK) (hB₀ : B₀ ≤ ⁅E₀, E₀⁆) (hOKN : ⁅OK, OK⁆ ≤ N)
    (hB₀card : Nat.card B₀ = 2 ^ 6) (hNcard : Nat.card N = 2 ^ 7)
    (hZ : B₀ ⊓ centralizer (B₀ : Set G) = Y) (hYe : CFSG.Open.IsElemAbelian 2 Y)
    (hY16 : Nat.card Y = 16)
    (h415 : ∀ B : Subgroup G, B ⋖ N → CFSG.Open.IsElemAbelian 2 (B ⊓ centralizer (B : Set G)) →
      Nat.card (B ⊓ centralizer (B : Set G) : Subgroup G) = 16 →
      B ⊓ centralizer (B : Set G) = Y) :
    cj g₂ Y = Y := by
  have hBN : cj g₂ B₀ ≤ N := by
    calc cj g₂ B₀ ≤ cj g₂ ⁅E₀, E₀⁆ := cj_mono hB₀
      _ = ⁅cj g₂ E₀, cj g₂ E₀⁆ := cj_commutator g₂ E₀ E₀
      _ ≤ ⁅OK, OK⁆ := Subgroup.commutator_mono hE hE
      _ ≤ N := hOKN
  have hBcard : Nat.card (cj g₂ B₀) = 2 ^ 6 := by rw [card_cj, hB₀card]
  have hcov : cj g₂ B₀ ⋖ N :=
    covBy_of_card_eq_two_mul hBN (by rw [hNcard, hBcard]; norm_num)
  have hBcent : cj g₂ B₀ ⊓ centralizer ((cj g₂ B₀ : Subgroup G) : Set G) = cj g₂ Y := by
    rw [← cj_centralizer g₂ B₀, ← cj_inf g₂ B₀ (centralizer (B₀ : Set G)), hZ]
  have hBea : CFSG.Open.IsElemAbelian 2
      (cj g₂ B₀ ⊓ centralizer ((cj g₂ B₀ : Subgroup G) : Set G)) := by
    rw [hBcent]; exact isElemAbelian_cj hYe
  have hB16 : Nat.card
      (cj g₂ B₀ ⊓ centralizer ((cj g₂ B₀ : Subgroup G) : Set G) : Subgroup G) = 16 := by
    rw [hBcent, card_cj, hY16]
  have hres := h415 (cj g₂ B₀) hcov hBea hB16
  rw [← hBcent]
  exact hres

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
