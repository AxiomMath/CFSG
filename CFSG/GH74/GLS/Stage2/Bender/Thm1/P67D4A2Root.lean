module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Core

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Solutions

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem A2Core.a2Fix_sigma_cube (h : A2Core σ d q) (c : K) :
    σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c :=
  sigma_three_of_card h.card h.frob c

theorem A2Core.a2Fix_char_fixed (h : A2Core σ d q) (β : Fin d4.rank → ℤ) :
    σ (a2Char d β) = a2Char d β := by
  have h1 : Units.map σ.toRingHom.toMonoidHom (d ^ β (nd 2)) = d ^ β (nd 2) := by
    rw [map_zpow, h.fixed]
  exact congrArg (fun u : Kˣ => (u : K)) h1

theorem A2Core.a2Fix_zpow_ne_one (h : A2Core σ d q) {m : ℤ} (hm : ¬ (3 : ℤ) ∣ m) : d ^ m ≠ 1 := by
  intro h1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf d = 3 := orderOf_eq_prime h.cube h.ne_one
  have h2 := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [hord] at h2
  exact hm (by exact_mod_cast h2)

theorem A2Core.a2Fix_exists_solution (h : A2Core σ d q) (m : ℤ) :
    ∃ u : Kˣ, ((d ^ m : Kˣ) : K) * σ (u : K) = (u : K) := by
  obtain ⟨t, ht⟩ : 3 ∣ q ^ 2 + q + 1 := by
    obtain ⟨s, hs⟩ : ∃ s, q = 3 * s + 1 := ⟨q / 3, by have := h.mod3; omega⟩
    exact ⟨3 * s ^ 2 + 3 * s + 1, by subst hs; ring⟩
  have hx : (d ^ (-m)) ^ (q ^ 2 + q + 1) = 1 := by
    rw [ht, ← zpow_natCast, ← zpow_mul]
    have : -m * ((3 * t : ℕ) : ℤ) = 3 * (-m * t) := by push_cast; ring
    rw [this, zpow_mul]
    have h3 : d ^ (3 : ℤ) = 1 := by
      have := h.cube
      exact_mod_cast this
    rw [h3, one_zpow]
  obtain ⟨b, hb⟩ := exists_unit_pow_sub_one_eq h.two_le h.card (d ^ (-m)) hx
  refine ⟨b, ?_⟩
  have e1 : σ (b : K) = (b : K) * ((d ^ (-m) : Kˣ) : K) := by
    rw [h.frob, ← hb, Units.val_pow_eq_pow_val, ← pow_succ',
      Nat.sub_add_cancel (by have := h.two_le; omega)]
  have e2 : ((d ^ m : Kˣ) : K) * ((d ^ (-m) : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]
  rw [e1]
  calc ((d ^ m : Kˣ) : K) * ((b : K) * ((d ^ (-m) : Kˣ) : K))
      = (((d ^ m : Kˣ) : K) * ((d ^ (-m) : Kˣ) : K)) * (b : K) := by ring
    _ = (b : K) := by rw [e2, one_mul]

theorem A2Core.a2Fix_card_solutions (h : A2Core σ d q) (m : ℤ) :
    Nat.card {c : K // ((d ^ m : Kˣ) : K) * σ c = c} = q := by
  obtain ⟨u, hu⟩ := a2Fix_exists_solution h m
  rw [← card_fixedField_of_cube σ.toRingHom h.two_le h.card h.frob]
  have hσu : σ (u : K) ≠ 0 := by simp
  refine (Nat.card_congr (Equiv.ofBijective
    (fun f : fixedField σ.toRingHom =>
      (⟨(u : K) * f, ?_⟩ : {c : K // ((d ^ m : Kˣ) : K) * σ c = c}))
    ⟨?_, ?_⟩)).symm
  · have hf : σ (f : K) = f := f.2
    rw [map_mul, hf]
    linear_combination (f : K) * hu
  · intro f g hfg
    have := congrArg Subtype.val hfg
    exact Subtype.ext (mul_left_cancel₀ (Units.ne_zero u) this)
  · rintro ⟨c, hc⟩
    refine ⟨⟨(u : K)⁻¹ * c, ?_⟩, ?_⟩
    · change σ ((u : K)⁻¹ * c) = (u : K)⁻¹ * c
      rw [map_mul, map_inv₀]
      field_simp
      linear_combination (σ (u : K)) * hc - (σ c) * hu
    · apply Subtype.ext
      simp [Units.ne_zero]

end Solutions

theorem a2Fix_lift_two_of_long {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) (hl : d43Long γ) :
    d43Lift γ (nd 2) = 1 ∨ d43Lift γ (nd 2) = -1 ∨ d43Lift γ (nd 2) = 2 ∨
      d43Lift γ (nd 2) = -2 := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hγ
  have hk' : k < 12 := hk
  rw [d43Lift_root hk']
  revert hl
  interval_cases k <;> intro hl <;> first
    | exact absurd hl (by decide)
    | decide

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem A2Core.a2_root_stable (h : A2Core σ d q) {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ)
    {g : adjointGroup d4 K} (hg : g ∈ twistedRootSubgroupD4 σ.toRingHom γ) :
    ∃ g' ∈ twistedRootSubgroupD4 σ.toRingHom γ,
      (g' : ModGL TwistTag.D4.tag K) = a2Conj σ d (g : ModGL TwistTag.D4.tag K) := by
  have hσ := a2Fix_sigma_cube h
  have hα := isRoot_d43Lift hγ
  have hp := proj_d43Lift hγ
  by_cases hl : d43Long γ
  · have hρ := rho_d43Lift_of_long hγ hl
    obtain ⟨c, hc, rfl⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ hα hp hρ g).1 hg
    refine ⟨xPar (rootOperatorFamily d4) (d43Lift γ) (a2Char d (d43Lift γ) * c), ?_, ?_⟩
    · refine (mem_twistedRootSubgroupD4_iff_of_fixed hσ hα hp hρ _).2 ⟨_, ?_, rfl⟩
      change σ (a2Char d (d43Lift γ) * c) = a2Char d (d43Lift γ) * c
      rw [map_mul, a2Fix_char_fixed h]
      exact congrArg _ hc
    · rw [a2Conj_xPar h hα]
      have hc' : σ c = c := hc
      rw [hc']
  · have hne := rho_d43Lift_ne hγ hl
    obtain ⟨c, rfl⟩ := (mem_twistedRootSubgroupD4_iff_of_orbit hσ hα hp hne g).1 hg
    exact ⟨xOrbit σ.toRingHom (d43Lift γ) (a2Char d (d43Lift γ) * σ c),
      (mem_twistedRootSubgroupD4_iff_of_orbit hσ hα hp hne _).2 ⟨_, rfl⟩,
      (a2Conj_xOrbit h hα hne c).symm⟩

theorem A2Core.a2_long_fix (h : A2Core σ d q) {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ)
    (hl : d43Long γ) {g : adjointGroup d4 K} (hg : g ∈ twistedRootSubgroupD4 σ.toRingHom γ)
    (hfix : a2Conj σ d (g : ModGL TwistTag.D4.tag K) = (g : ModGL TwistTag.D4.tag K)) :
    g = 1 := by
  have hσ := a2Fix_sigma_cube h
  have hα := isRoot_d43Lift hγ
  have hp := proj_d43Lift hγ
  have hρ := rho_d43Lift_of_long hγ hl
  obtain ⟨c, hc, rfl⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ hα hp hρ g).1 hg
  have hc' : σ c = c := hc
  rw [a2Conj_xPar h hα, hc'] at hfix
  have h1 := xPar_injective hα (Subtype.ext hfix)
  have hχ : a2Char d (d43Lift γ) ≠ 1 := by
    intro h2
    refine a2Fix_zpow_ne_one h (m := d43Lift γ (nd 2)) ?_ (Units.val_eq_one.1 h2)
    rcases a2Fix_lift_two_of_long hγ hl with e | e | e | e <;> rw [e] <;> omega
  have hc0 : c = 0 := by
    by_contra hc0
    exact hχ (mul_right_cancel₀ hc0 (by rw [one_mul]; exact h1))
  rw [hc0, xPar_zero]

theorem A2Core.a2_short_fix (h : A2Core σ d q) {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ)
    (hs : ¬ d43Long γ) :
    ∃ g ∈ twistedRootSubgroupD4 σ.toRingHom γ, g ≠ 1 ∧
      a2Conj σ d (g : ModGL TwistTag.D4.tag K) = (g : ModGL TwistTag.D4.tag K) := by
  have hσ := a2Fix_sigma_cube h
  have hα := isRoot_d43Lift hγ
  have hp := proj_d43Lift hγ
  have hne := rho_d43Lift_ne hγ hs
  obtain ⟨u, hu⟩ := a2Fix_exists_solution h (d43Lift γ (nd 2))
  refine ⟨xOrbit σ.toRingHom (d43Lift γ) u,
    (mem_twistedRootSubgroupD4_iff_of_orbit hσ hα hp hne _).2 ⟨u, rfl⟩, fun h1 => ?_, ?_⟩
  · exact Units.ne_zero u
      (xOrbit_injective σ.toRingHom hα hne (h1.trans (xOrbit_zero σ.toRingHom (d43Lift γ)).symm))
  · rw [a2Conj_xOrbit h hα hne, show a2Char d (d43Lift γ) * σ (u : K) = u from hu]

theorem A2Core.a2_short_fix_card (h : A2Core σ d q) {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ)
    (hs : ¬ d43Long γ) :
    Nat.card {g : twistedRootSubgroupD4 σ.toRingHom γ //
      a2Conj σ d ((g : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
        ((g : adjointGroup d4 K) : ModGL TwistTag.D4.tag K)} = q := by
  have hσ := a2Fix_sigma_cube h
  have hα := isRoot_d43Lift hγ
  have hp := proj_d43Lift hγ
  have hne := rho_d43Lift_ne hγ hs
  have hfixiff : ∀ c : K, a2Conj σ d ((xOrbit σ.toRingHom (d43Lift γ) c : adjointGroup d4 K) :
      ModGL TwistTag.D4.tag K) = ((xOrbit σ.toRingHom (d43Lift γ) c : adjointGroup d4 K) :
        ModGL TwistTag.D4.tag K) ↔ a2Char d (d43Lift γ) * σ c = c := fun c => by
    rw [a2Conj_xOrbit h hα hne]
    exact ⟨fun h1 => xOrbit_injective σ.toRingHom hα hne (Subtype.ext h1), fun h1 => by rw [h1]⟩
  rw [← a2Fix_card_solutions h (d43Lift γ (nd 2))]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun c : {c : K // ((d ^ (d43Lift γ (nd 2)) : Kˣ) : K) * σ c = c} =>
      (⟨⟨xOrbit σ.toRingHom (d43Lift γ) c,
        (mem_twistedRootSubgroupD4_iff_of_orbit hσ hα hp hne _).2 ⟨c, rfl⟩⟩,
          (hfixiff c).2 c.2⟩ :
        {g : twistedRootSubgroupD4 σ.toRingHom γ //
          a2Conj σ d ((g : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
            ((g : adjointGroup d4 K) : ModGL TwistTag.D4.tag K)}))
    ⟨fun c c' hcc' =>
      Subtype.ext (xOrbit_injective σ.toRingHom hα hne (congrArg (fun g => g.1.1) hcc')),
      ?_⟩)).symm
  rintro ⟨⟨g, hg⟩, hgfix⟩
  obtain ⟨c, rfl⟩ := (mem_twistedRootSubgroupD4_iff_of_orbit hσ hα hp hne g).1 hg
  exact ⟨⟨c, (hfixiff c).1 hgfix⟩, rfl⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm1
