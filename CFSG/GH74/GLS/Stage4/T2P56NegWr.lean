module

public import CFSG.GH74.GLS.Stage4.T2P56WrLoc
public import CFSG.GH74.GLS.Stage4.T2P56NegSyl

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup

theorem hasWreathedSylow_neg {G : Type} [Group G] [Finite G] {C₁ : Subgroup G} {q : ℕ} {z u : G}
    {K₁ K₂ H : Subgroup G} {w₁ w₂ : G} (hr : CFSG.pRank 2 G = 3)
    (cfg : Ch6NegCfg C₁ q z u K₁ K₂ H w₁ w₂) (hq : q % 4 = 3)
    (hC₁ : ∀ g : G, g * z = z * g → TwoElt g → g ∈ C₁)
    {y : G} (hyH : y ∈ H) (hy1 : y ≠ 1) (hyodd : Odd (orderOf y)) {a w h₀ : G}
    (haN : a ∈ normalizer (H : Set G)) (ha3 : a ^ 3 ∈ H) (haz : a⁻¹ * z * a = u)
    (hau : a⁻¹ * u * a = z * u) (hay : a * y = y * a) (hwy : w * y = y * w)
    (hwN : w ∈ normalizer (H : Set G)) (hw2 : w * w = z) (hwu : w * u * w⁻¹ = u * z)
    (hh₀ : h₀ ∈ H) (hwa : w * a * w⁻¹ = a⁻¹ * h₀) :
    HasWreathedSylow ↥(centralizer ({y} : Set G)) := by
  have hHc := cfg.H_comm
  have hy2 : y * y ≠ 1 := by
    intro h
    have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h3 | h3
    · exact hy1 (orderOf_eq_one_iff.1 h3)
    · rw [h3] at hyodd
      exact absurd hyodd (by decide)
  have hz2 : z * z = 1 := cfg.zz
  have hz1 : z ≠ 1 := cfg.z_ne
  have hu2 : u * u = 1 := cfg.uu
  have hu1 : u ≠ 1 := cfg.u_ne
  have hzu : z * u = u * z := cfg.zu_comm
  have hΩ : ∀ x ∈ H, x * x = 1 → x ∈ t2U z u := fun x hx hx2 =>
    (t2U_mem hz2 hu2 hzu).2 (cfg.toT2Four1.omega1 hr x hx hx2)
  have hzT : z ∈ twoPart H hHc := mem_twoPart.2 ⟨cfg.z_mem_H, TwoElt.of_sq_eq_one hz2⟩
  have huT : u ∈ twoPart H hHc := mem_twoPart.2 ⟨cfg.u_mem_H, TwoElt.of_sq_eq_one hu2⟩
  have hTH : ∀ x ∈ twoPart H hHc, x ∈ H := fun x hx => (mem_twoPart.1 hx).1
  have hT2 : ∀ x ∈ twoPart H hHc, TwoElt x := fun x hx => (mem_twoPart.1 hx).2
  have hcomm : ∀ x ∈ H, x * y = y * x := fun x hx => hHc x hx y hyH
  have hmemX : ∀ x : G, x * y = y * x → x ∈ centralizer ({y} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 hx
  have hd₁ : 4 ∣ Nat.card ↥(H ⊓ K₁) := by rw [cfg.H₁_card]; omega
  obtain ⟨-, c₁, hc₁H, hc₁⟩ := cyc_invol (H ⊓ K₁) cfg.H₁_cyc hd₁
    ⟨cfg.z_mem_H, cfg.z_mem_K₁⟩ hz2 hz1
  have hT4 : ∃ x ∈ twoPart H hHc, x * x ≠ 1 := by
    refine ⟨c₁, mem_twoPart.2 ⟨hc₁H.1, ⟨2, ?_⟩⟩, ?_⟩
    · calc c₁ ^ 2 ^ 2 = (c₁ * c₁) * (c₁ * c₁) := by
            rw [show (2 : ℕ) ^ 2 = 2 * 2 from rfl, pow_mul, pow_two, pow_two]
        _ = 1 := by rw [hc₁]; exact hz2
    · rw [hc₁]; exact hz1
  exact hasWreathedSylow_sub (centralizer ({y} : Set G)) (T := twoPart H hHc)
    (z := z) (u := u) (a := a) (w := w) (h := h₀)
    (fun x hx => hmemX x (hcomm x (hTH x hx))) (hmemX _ (hcomm _ cfg.z_mem_H))
    (hmemX _ (hcomm _ cfg.u_mem_H)) (hmemX _ hay) (hmemX _ hwy) (hmemX _ (hcomm _ hh₀))
    (fun x hx y' hy' => hHc x (hTH x hx) y' (hTH y' hy')) hT2 hz2 hu2 hzu hz1 hu1 cfg.zu_ne
    hzT huT (fun x hx hx2 => hΩ x (hTH x hx) hx2)
    (fun g hg hgz hgu hg2 => mem_twoPart.2 ⟨twoElt_cent_mem_H_neg cfg.toT2Four1 hC₁ hyH hy2
      (Subgroup.mem_centralizer_singleton_iff.1 hg) hgz hgu hg2, hg2⟩) hT4
    (fun x hx => mem_twoPart.2
      ⟨(Subgroup.mem_normalizer_iff.1 haN x).1 (hTH x hx), (hT2 x hx).conj a⟩)
    (fun x hx => mem_twoPart.2 ⟨(Subgroup.mem_normalizer_iff.1 haN (a⁻¹ * x * a)).2
        (by rw [show a * (a⁻¹ * x * a) * a⁻¹ = x by group]; exact hTH x hx),
      by simpa using (hT2 x hx).conj a⁻¹⟩)
    (fun x hx => hHc _ ha3 x (hTH x hx)) haz hau hw2
    (fun x hx => mem_twoPart.2
      ⟨(Subgroup.mem_normalizer_iff.1 hwN x).1 (hTH x hx), (hT2 x hx).conj w⟩) hwu
    (fun x hx => hHc _ hh₀ x (hTH x hx)) hwa

end CFSG.GH74.GLS.Stage4.Rest
