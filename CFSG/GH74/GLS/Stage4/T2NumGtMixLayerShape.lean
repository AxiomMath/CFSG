module

public import CFSG.GH74.GLS.Stage4.T2NumGtMixLocDefs
public import CFSG.GH74.GLS.Stage4.T2P56NegSyl
public import CFSG.GH74.GLS.Stage4.T2P56WrLoc

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup

theorem hasSDSylow_mix {G : Type} [Group G] [Finite G] {C₁ : Subgroup G} {q₁ q₂ : ℕ} {z u : G}
    {K₁ K₂ H : Subgroup G} {w₁ w₂ : G} (cfg : Ch6MixCfg C₁ q₁ q₂ z u K₁ K₂ H w₁ w₂) (hq₁ : q₁ % 4 = 1) (hq₂ : q₂ % 4 = 3)
    (hC₁ : ∀ g : G, g * z = z * g → TwoElt g → g ∈ C₁)
    {y : G} (hyH : y ∈ H) (hy1 : y ≠ 1) (hyodd : Odd (orderOf y)) {Kj : Subgroup G}
    (hKj : ∀ x ∈ Kj, x * y = y * x) {F : Type} [Field F] [Finite F] (hFodd : Odd (Nat.card F))
    (e : ↥Kj ≃* CFSG.GH74.GLS.Stage4.Hex.SL2 F) :
    HasSDSylow ↥(centralizer ({y} : Set G)) := by
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
  have hHc := cfg.H_comm
  have hzu : z * u = u * z := hHc _ cfg.z_mem_H u cfg.u_mem_H
  have h2part : ∀ x ∈ H, TwoElt x → x ∈ t2U z u := by
    intro x hx hx2
    refine twoElt_mem_U hHc inf_le_left inf_le_left cfg.H₁_cyc cfg.H₂_cyc
      (k₁ := (q₁ + 1) / 2) (k₂ := (q₂ - 1) / 2) (Nat.odd_iff.2 (by omega))
      (Nat.odd_iff.2 (by omega)) (by rw [cfg.H₁_card]; omega) (by rw [cfg.H₂_card]; omega)
      cfg.H_idx ⟨cfg.z_mem_H, cfg.z_mem_K₁⟩ ⟨cfg.z_mem_H, cfg.z_mem_K₂⟩ hz2 hz1
      cfg.u_mem_H hu2 hu1 cfg.zu_ne.symm hx hx2
  set X : Subgroup G := centralizer ({y} : Set G) with hXdef
  have hyz' : y * z = z * y := hHc y hyH _ cfg.z_mem_H
  have hyu : y * u = u * y := hHc y hyH u cfg.u_mem_H
  have hzX : z ∈ X := Subgroup.mem_centralizer_singleton_iff.mpr hyz'.symm
  have huX : u ∈ X := Subgroup.mem_centralizer_singleton_iff.mpr hyu.symm
  have hUX : t2U z u ≤ X := by
    unfold t2U
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hzX
    · simpa using huX
  have hzU : z ∈ t2U z u := Subgroup.subset_closure (by simp)
  have huU : u ∈ t2U z u := Subgroup.subset_closure (by simp)
  have hUH : t2U z u ≤ H := t2U_le_of_mem hz2 hu2 hzu cfg.z_mem_H cfg.u_mem_H
  let U' : Subgroup ↥X := (t2U z u).subgroupOf X
  have hUab : ∀ a ∈ U', ∀ b ∈ U', a * b = b * a := by
    intro a ha b hb
    apply Subtype.ext
    exact hHc (a : G) (hUH (Subgroup.mem_subgroupOf.mp ha)) (b : G)
      (hUH (Subgroup.mem_subgroupOf.mp hb))
  have hUexp : ∀ a ∈ U', a ^ 2 = 1 := by
    intro a ha
    apply Subtype.ext
    have h := t2S_closure_sq hz2 hu2 hzu.symm (a : G) (Subgroup.mem_subgroupOf.mp ha)
    simpa [pow_two] using h
  have hUcard : Nat.card ↥U' = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUX).toEquiv]
    exact t2U_card hz2 hu2 hzu hz1 hu1 cfg.zu_ne
  have hcent : ∀ g : ↥X, (∀ a ∈ U', g * a = a * g) → (∃ k : ℕ, g ^ (2 ^ k) = 1) → g ∈ U' := by
    intro g hg hk2
    obtain ⟨k, hk⟩ := hk2
    have hgz : (g : G) * z = z * (g : G) :=
      congrArg Subtype.val (hg ⟨z, hzX⟩ (Subgroup.mem_subgroupOf.mpr hzU))
    have hgu : (g : G) * u = u * (g : G) :=
      congrArg Subtype.val (hg ⟨u, huX⟩ (Subgroup.mem_subgroupOf.mpr huU))
    have hgy : (g : G) * y = y * (g : G) := Subgroup.mem_centralizer_singleton_iff.mp g.2
    have hg2 : TwoElt (g : G) := ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hgH : (g : G) ∈ H :=
      twoElt_cent_mem_H_neg cfg.toT2Four1 hC₁ hyH hy2 hgy hgz hgu hg2
    exact Subgroup.mem_subgroupOf.mpr (h2part _ hgH hg2)
  have hU'p : IsPGroup 2 ↥U' := IsPGroup.of_card (n := 2) (by rw [hUcard]; norm_num)
  obtain ⟨S, hUS⟩ := hU'p.exists_le_sylow
  have hKjX : Kj ≤ X := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hKj x hx)
  rcases t2P56_sylow_shape U' hUab hUexp hUcard hcent S hUS with ⟨m, hm, ⟨φ⟩⟩ | ⟨m, hm, ⟨φ⟩⟩
  · exfalso
    exact t2P56_not_dihedral hFodd (Kj.subgroupOf X) ((Subgroup.subgroupOfEquivOfLe hKjX).trans e) S
      ⟨φ⟩
  · exact ⟨S, m, hm, ⟨φ⟩⟩

theorem hasWreathedSylow_mix {G : Type} [Group G] [Finite G] {C₁ : Subgroup G} {q₁ q₂ : ℕ} {z u : G}
    {K₁ K₂ H : Subgroup G} {w₁ w₂ : G} (hr : CFSG.pRank 2 G = 3)
    (cfg : Ch6MixCfg C₁ q₁ q₂ z u K₁ K₂ H w₁ w₂) (hq₁ : q₁ % 4 = 3)
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
