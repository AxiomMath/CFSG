module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FFrameLem
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121Fin

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

namespace S7FFrame

variable {t : G} {B E H : Subgroup G} {φ : (Fin 5 → ZMod 2) → G}

theorem kap_inv_mul (F : S7FFrame t B E H φ) {x y : G} (hx : x ∈ E) (hy : y ∈ E) :
    s7fKap t (x⁻¹ * y) = (s7fKap t x)⁻¹ * s7fKap t y := by
  rw [F.kap_mul (E.inv_mem hx) hy, F.kap_inv hx]

theorem conj_A_mem (F : S7FFrame t B E H φ) {h d : G} (hh : h ∈ H) (hd : d ∈ E)
    (hκ : s7fKap t d = 1) : d⁻¹ * (h * d * h⁻¹) ∈ B := by
  rcases F.kap_ker d hd hκ with hdB | htdB
  · exact B.mul_mem (B.inv_mem hdB) (F.H_B hh hdB)
  · have hd' : d = t * (t * d) := by rw [← mul_assoc, F.t_sq, one_mul]
    set b := t * d with hb
    have hht : h * t * h⁻¹ = t * (t⁻¹ * (h * t * h⁻¹)) := by group
    have hc := F.H_t h hh
    have hhb := F.H_B hh htdB
    rw [hd']
    have e : (t * b)⁻¹ * (h * (t * b) * h⁻¹) =
        b⁻¹ * (t⁻¹ * (h * t * h⁻¹)) * (h * b * h⁻¹) := by group
    rw [e]
    exact B.mul_mem (B.mul_mem (B.inv_mem htdB) hc) hhb

theorem kap_conj_perm (F : S7FFrame t B E H φ) {h x : G} (hh : h ∈ H) (hx : x ∈ E)
    {σ : Equiv.Perm (Fin 5)} (hσ : s7fActs φ h σ) {v : Fin 5 → ZMod 2} (hv : IsEvenVec v)
    (hκ : s7fKap t x = φ v) : s7fKap t (h * x * h⁻¹) = φ (permVec σ v) := by
  rw [F.kap_conj hh hx, hκ, hσ v hv]

theorem cube_lift (F : S7FFrame t B E H φ) {e₀ h : G} (he₀ : e₀ ∈ E) (hh : h ∈ H)
    {τ : Equiv.Perm (Fin 5)} (hτ : s7fActs φ h τ) (hτ3 : τ ^ 3 = 1)
    (hκ : s7fKap t (h * e₀ * h⁻¹) = s7fKap t e₀) : e₀⁻¹ * (h * e₀ * h⁻¹) ∈ B := by
  have he₁ : h * e₀ * h⁻¹ ∈ E := F.H_E h hh e₀ he₀
  set d := e₀⁻¹ * (h * e₀ * h⁻¹) with hd
  have hdE : d ∈ E := E.mul_mem (E.inv_mem he₀) he₁
  have hκd : s7fKap t d = 1 := by
    rw [hd, F.kap_inv_mul he₀ he₁, hκ, inv_mul_cancel]
  rcases F.kap_ker d hdE hκd with hdB | htdB
  · exact hdB
  · exfalso
    have hτ3' : s7fActs φ (h * h * h) 1 := by
      have h1 := s7fActs_mul (s7fActs_mul hτ hτ) hτ
      rwa [show τ * τ * τ = τ ^ 3 from (pow_three' τ).symm, hτ3] at h1
    have hh3 : h * h * h ∈ H := H.mul_mem (H.mul_mem hh hh) hh
    have htriv := F.triv_of_acts_one hh3 hτ3' e₀ he₀
    have htB : ∀ x, t * x ∈ B → t * (h * x * h⁻¹) ∈ B := by
      intro x hx
      have hx' : x = t * (t * x) := by rw [← mul_assoc, F.t_sq, one_mul]
      have e : t * (h * x * h⁻¹) = t * (h * t * h⁻¹) * (h * (t * x) * h⁻¹) := by
        conv_lhs => rw [hx']
        group
      rw [e]
      have h1 : t * (h * t * h⁻¹) ∈ B := by
        have h2 := F.H_t h hh
        rwa [F.t_inv] at h2
      exact B.mul_mem h1 (F.H_B hh hx)
    have hd1 : t * (h * d * h⁻¹) ∈ B := htB d htdB
    have hd2 : t * (h * (h * d * h⁻¹) * h⁻¹) ∈ B := htB _ hd1
    have htele : e₀⁻¹ * ((h * h * h) * e₀ * (h * h * h)⁻¹) =
        d * (h * d * h⁻¹) * (h * (h * d * h⁻¹) * h⁻¹) := by
      rw [hd]
      group
    rw [htele] at htriv
    have key : ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, t * ((t * a) * (t * b) * (t * c)) ∈ B := by
      intro a ha b hb c hc
      have e : t * ((t * a) * (t * b) * (t * c)) = (t * t) * a * (t * b * t) * c := by group
      rw [e, F.t_sq, F.t_comm hb, mul_assoc b t t, F.t_sq, mul_one, one_mul]
      exact B.mul_mem (B.mul_mem ha hb) hc
    have hx : ∀ x : G, x = t * (t * x) := fun x => by rw [← mul_assoc, F.t_sq, one_mul]
    have hprod : t * (d * (h * d * h⁻¹) * (h * (h * d * h⁻¹) * h⁻¹)) ∈ B := by
      have h1 := key _ htdB _ hd1 _ hd2
      rwa [← hx d, ← hx (h * d * h⁻¹), ← hx (h * (h * d * h⁻¹) * h⁻¹)] at h1
    apply F.t_not_mem
    have e : t = (t * (d * (h * d * h⁻¹) * (h * (h * d * h⁻¹) * h⁻¹))) *
        (d * (h * d * h⁻¹) * (h * (h * d * h⁻¹) * h⁻¹))⁻¹ := by group
    rw [e]
    exact B.mul_mem hprod (B.inv_mem htriv)

theorem fixed_lift (F : S7FFrame t B E H φ) {i : Fin 5} {e₀ h : G} (he₀ : e₀ ∈ E)
    (hκ₀ : s7fKap t e₀ = φ (wvec i)) (hh : h ∈ H) {σ : Equiv.Perm (Fin 5)}
    (hσ : s7fActs φ h σ) (hσA : σ ∈ alternatingGroup (Fin 5)) (hσi : σ i = i) :
    e₀⁻¹ * (h * e₀ * h⁻¹) ∈ B := by
  obtain ⟨ρ₁, -, ρ₂, -, hρ₁i, hρ₂i, hρ₁c, hρ₂c, hσeq⟩ := alt_stab_decomp i hσA hσi
  obtain ⟨h₁, hh₁, hρ₁⟩ := F.realize ρ₁
  obtain ⟨h₂, hh₂, hρ₂⟩ := F.realize ρ₂
  have hfix : ∀ {y : G} {ρ : Equiv.Perm (Fin 5)}, y ∈ H → s7fActs φ y ρ → ρ ^ 3 = 1 →
      ρ i = i → e₀⁻¹ * (y * e₀ * y⁻¹) ∈ B := by
    intro y ρ hy hρ hρc hρi
    refine F.cube_lift he₀ hy hρ hρc ?_
    rw [F.kap_conj_perm hy he₀ hρ (wvec_even i) hκ₀, permVec_wvec, hρi, hκ₀]
  have hc₁ := hfix hh₁ hρ₁ hρ₁c hρ₁i
  have hc₂ := hfix hh₂ hρ₂ hρ₂c hρ₂i
  set k := (h₁ * h₂)⁻¹ * h with hk
  have hkH : k ∈ H := H.mul_mem (H.inv_mem (H.mul_mem hh₁ hh₂)) hh
  have hk1 : s7fActs φ k 1 := by
    have h1 := s7fActs_mul (s7fActs_inv (s7fActs_mul hρ₁ hρ₂)) hσ
    rwa [← hσeq, inv_mul_cancel] at h1
  have hc₃ := F.triv_of_acts_one hkH hk1 e₀ he₀
  have hheq : h = h₁ * h₂ * k := by rw [hk]; group
  set c₁ := e₀⁻¹ * (h₁ * e₀ * h₁⁻¹)
  set c₂ := e₀⁻¹ * (h₂ * e₀ * h₂⁻¹)
  set c₃ := e₀⁻¹ * (k * e₀ * k⁻¹)
  have e : e₀⁻¹ * (h * e₀ * h⁻¹) = c₁ * (h₁ * c₂ * h₁⁻¹) * (h₁ * h₂ * c₃ * (h₁ * h₂)⁻¹) := by
    rw [hheq]
    simp only [c₁, c₂, c₃]
    group
  rw [e]
  exact B.mul_mem (B.mul_mem hc₁ (F.H_B hh₁ hc₂)) (F.H_B (H.mul_mem hh₁ hh₂) hc₃)

end S7FFrame

end CFSG.OddStandard.SmallF3.Omega
