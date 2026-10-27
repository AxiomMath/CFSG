module

public import CFSG.GH74.GLS.Stage4.T2P56Syl
public import CFSG.GH74.GLS.Stage4.T2NegFour

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup

theorem twoElt_cent_mem_H_neg {G : Type} [Group G] {C₁ : Subgroup G} {z u : G}
    {K₁ K₂ H : Subgroup G} {w₁ w₂ : G} (cfg : T2Four1 C₁ z u K₁ K₂ H w₁ w₂)
    (hC₁ : ∀ g : G, g * z = z * g → TwoElt g → g ∈ C₁)
    {y : G} (hyH : y ∈ H) (hy2 : y * y ≠ 1) {g : G} (hgy : g * y = y * g) (hgz : g * z = z * g)
    (hgu : g * u = u * g) (hg2 : TwoElt g) : g ∈ H := by
  rcases cfg.Y1 g (hC₁ g hgz hg2) hgu with hgH | ⟨x, hxH, hgx⟩
  · exact hgH
  · exfalso
    have hw : (w₁ * w₂) * y * (w₁ * w₂)⁻¹ = y⁻¹ := cfg.w₀_inv y hyH
    have hxc : x * y⁻¹ = y⁻¹ * x := cfg.H_comm x hxH y⁻¹ (H.inv_mem hyH)
    have h1 : g * y * g⁻¹ = y⁻¹ := by
      rw [hgx]
      calc x * (w₁ * w₂) * y * (x * (w₁ * w₂))⁻¹
          = x * ((w₁ * w₂) * y * (w₁ * w₂)⁻¹) * x⁻¹ := by group
        _ = x * y⁻¹ * x⁻¹ := by rw [hw]
        _ = y⁻¹ := by rw [hxc]; group
    have h2 : g * y * g⁻¹ = y := by rw [hgy]; group
    have h3 : y = y⁻¹ := h2.symm.trans h1
    apply hy2
    calc y * y = y * y⁻¹ := by rw [← h3]
      _ = 1 := mul_inv_cancel y

theorem hasSDSylow_neg {G : Type} [Group G] [Finite G] {C₁ : Subgroup G} {q : ℕ} {z u : G}
    {K₁ K₂ H : Subgroup G} {w₁ w₂ : G} (cfg : Ch6NegCfg C₁ q z u K₁ K₂ H w₁ w₂) (hq : q % 4 = 1)
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
      (k₁ := (q + 1) / 2) (k₂ := (q + 1) / 2) (Nat.odd_iff.2 (by omega))
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

end CFSG.GH74.GLS.Stage4.Rest
