module

public import CFSG.GH74.GLS.Stage4.HexModelD4
public import CFSG.LieType.Steinberg.CentralExt.TrialityTorus
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ZRoot
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4HexLong

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.BNPair

section Pure

variable {K : Type} [Field K] {σ : K →+* K}

theorem d4z_chi {ω : Kˣ} (hωσ : σ (ω : K) = ω) (hω3 : ω ^ 3 = 1) (α : Fin d4.rank → ℤ) :
    chi σ 1 (ω ^ 2) α = ω ^ (α 0 + α 1 + α 3) := by
  have hω : Units.map σ.toMonoidHom ω = ω := Units.ext hωσ
  have h3 : ω ^ (3 : ℤ) = 1 := by exact_mod_cast hω3
  obtain ⟨h0, h1, -, h3'⟩ := pr_eq α
  have e1 : Units.map σ.toMonoidHom (ω ^ 2) = ω ^ 2 := by rw [map_pow, hω]
  have e2 : ω ^ 2 = ω ^ (2 : ℤ) := (zpow_ofNat ω 2).symm
  simp only [chi, e1, one_zpow, one_mul, h0, h1, h3']
  rw [e2]
  simp only [← zpow_mul, ← zpow_add]
  have e3 : (2 : ℤ) * (2 * α (nd 0) - α (nd 2)) + 2 * (2 * α (nd 1) - α (nd 2)) +
      2 * (2 * α (nd 3) - α (nd 2)) =
      (α 0 + α 1 + α 3) + 3 * ((α 0 + α 1 + α 3) - 2 * α (nd 2)) := by
    change (2 : ℤ) * (2 * α 0 - α (nd 2)) + 2 * (2 * α 1 - α (nd 2)) +
      2 * (2 * α 3 - α (nd 2)) = _
    ring
  rw [e3, zpow_add, zpow_mul, h3, one_zpow, mul_one]

theorem d4z_zpow_ne_one {ω : Kˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {m : ℤ} (hm : m % 3 ≠ 0) :
    ω ^ m ≠ 1 := by
  intro h1
  have hord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
  have h2 : ((orderOf ω : ℕ) : ℤ) ∣ m := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [hord] at h2
  exact hm (Int.emod_eq_zero_of_dvd (by exact_mod_cast h2))

theorem d4z_long_hexPos_iff {k : ℤ} (hk : CFSG.GH74.BNPair.IsRoot 6 k) :
    d43Long (hexPos k) ↔ k % 2 = 0 := by
  obtain ⟨h0, h6⟩ := hk
  have h6' : -6 ≤ k ∧ k ≤ 6 := by omega
  obtain ⟨hl, hu⟩ := h6'
  have e : d43Long (hexPos k) ↔ (3 : ℤ) ∣ hexPos k (1 : Fin 2) := Iff.rfl
  rw [e]
  interval_cases k <;> first | exact absurd rfl h0 | simp [hexPos]

theorem d4z_fixed_pr_two (β : Fin d4.rank → ℤ)
    (hβ : IsRoot d4 β) (hρ : rho β = β) : pr (nd 2) β % 3 ≠ 0 := by
  rw [(pr_eq β).2.2.1]
  obtain ⟨k, hk, rfl⟩ := CFSG.ClassicalInvolution.Balance.isRoot_d4_iff.1 hβ
  clear hβ
  revert hρ hk
  revert k
  decide +kernel

end Pure

section Tori

variable {K : Type} [Field K] {σ : K →+* K}

theorem d4_hHat_le_torus :
    ∀ h ∈ (⨆ i, hHat σ i), ((h : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) ∈
      torusGroup TwistTag.D4.tag K := by
  let φ : twistedGroup σ →* ModGL TwistTag.D4.tag K :=
    (adjointGroup d4 K).subtype.comp (twistedGroup σ).subtype
  have hle : (⨆ i, hHat σ i) ≤ (torusGroup TwistTag.D4.tag K).comap φ := by
    refine iSup_le fun i => ?_
    intro x hx
    have hx' : (x : adjointGroup d4 K) ∈ hHatE σ i := hx
    show φ x ∈ torusGroup TwistTag.D4.tag K
    fin_cases i
    · obtain ⟨s, hs⟩ := (show (x : adjointGroup d4 K) ∈ (hLongHom σ).range from hx')
      have : φ x = torusElt d4 K (nd 2) (s : Kˣ) := by
        show ((x : adjointGroup d4 K) : ModGL d4 K) = _
        rw [← hs]
        rfl
      rw [this]
      exact torusElt_mem_torusGroup _ _
    · obtain ⟨s, hs⟩ := (show (x : adjointGroup d4 K) ∈ (hShortHom σ).range from hx')
      have : φ x = torusElt d4 K (nd 0) s *
          torusElt d4 K (nd 1) (Units.map σ.toMonoidHom s) *
          torusElt d4 K (nd 3) (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom s)) := by
        show ((x : adjointGroup d4 K) : ModGL d4 K) = _
        rw [← hs]
        rfl
      rw [this]
      exact mul_mem (mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _))
        (torusElt_mem_torusGroup _ _)
  intro h hh
  exact hle hh

theorem d4z_coe_torE {ω : Kˣ} (hωσ : σ (ω : K) = ω) (hω3 : ω ^ 3 = 1) :
    ((torE σ 1 (ω ^ 2) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
      rootDiagUnit TwistTag.D4.tag ![ω, ω, 1, ω] := by
  have hω : Units.map σ.toMonoidHom ω = ω := Units.ext hωσ
  have e1 : Units.map σ.toMonoidHom (ω ^ 2) = ω ^ 2 := by rw [map_pow, hω]
  have h : ∀ (i : Fin d4.rank) (t : Kˣ),
      ((torusElement d4 K i t : adjointGroup d4 K) : ModGL d4 K) = torusElt d4 K i t :=
    fun _ _ => rfl
  have c00 : d4.cartan (nd 0) (nd 0) = 2 := by decide
  have c01 : d4.cartan (nd 0) (nd 1) = 0 := by decide
  have c02 : d4.cartan (nd 0) (nd 2) = -1 := by decide
  have c03 : d4.cartan (nd 0) (nd 3) = 0 := by decide
  have c10 : d4.cartan (nd 1) (nd 0) = 0 := by decide
  have c11 : d4.cartan (nd 1) (nd 1) = 2 := by decide
  have c12 : d4.cartan (nd 1) (nd 2) = -1 := by decide
  have c13 : d4.cartan (nd 1) (nd 3) = 0 := by decide
  have c30 : d4.cartan (nd 3) (nd 0) = 0 := by decide
  have c31 : d4.cartan (nd 3) (nd 1) = 0 := by decide
  have c32 : d4.cartan (nd 3) (nd 2) = -1 := by decide
  have c33 : d4.cartan (nd 3) (nd 3) = 2 := by decide
  have h4 : (ω ^ 2) ^ (2 : ℤ) = ω := by
    rw [zpow_ofNat, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, hω3, one_mul, pow_one]
  have h6 : (ω ^ 2)⁻¹ * (ω ^ 2)⁻¹ * (ω ^ 2)⁻¹ = 1 := by
    rw [← mul_inv, ← mul_inv, ← pow_add, ← pow_add, show 2 + 2 + 2 = 3 * 2 from rfl, pow_mul, hω3,
      one_pow, inv_one]
  unfold torE
  rw [hShortHom_apply]
  simp only [Subgroup.coe_mul, h, e1, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
  congr 1
  funext j
  fin_cases j
  · show (1 : Kˣ) ^ d4.cartan (nd 2) (nd 0) * ((ω ^ 2) ^ d4.cartan (nd 0) (nd 0) *
      (ω ^ 2) ^ d4.cartan (nd 1) (nd 0) * (ω ^ 2) ^ d4.cartan (nd 3) (nd 0)) = ω
    rw [c00, c10, c30]
    simp only [one_zpow, zpow_zero, one_mul, mul_one]
    exact h4
  · show (1 : Kˣ) ^ d4.cartan (nd 2) (nd 1) * ((ω ^ 2) ^ d4.cartan (nd 0) (nd 1) *
      (ω ^ 2) ^ d4.cartan (nd 1) (nd 1) * (ω ^ 2) ^ d4.cartan (nd 3) (nd 1)) = ω
    rw [c01, c11, c31]
    simp only [one_zpow, zpow_zero, one_mul, mul_one]
    exact h4
  · show (1 : Kˣ) ^ d4.cartan (nd 2) (nd 2) * ((ω ^ 2) ^ d4.cartan (nd 0) (nd 2) *
      (ω ^ 2) ^ d4.cartan (nd 1) (nd 2) * (ω ^ 2) ^ d4.cartan (nd 3) (nd 2)) = 1
    rw [c02, c12, c32, one_zpow, one_mul, zpow_neg_one, h6]
  · show (1 : Kˣ) ^ d4.cartan (nd 2) (nd 3) * ((ω ^ 2) ^ d4.cartan (nd 0) (nd 3) *
      (ω ^ 2) ^ d4.cartan (nd 1) (nd 3) * (ω ^ 2) ^ d4.cartan (nd 3) (nd 3)) = ω
    rw [c03, c13, c33]
    simp only [one_zpow, zpow_zero, one_mul, mul_one]
    exact h4

theorem d4z_torE_one_left (t : Kˣ) : torE σ 1 t = hShortHom σ t := by
  unfold torE
  have h : torusElement d4 K (nd 2) (1 : Kˣ) = 1 := (torusHom (τ := d4) K (nd 2)).map_one
  rw [h, one_mul]

theorem d4z_tor_one_mem_hHat (hσ : ∀ c, σ (σ (σ c)) = c) (t : Kˣ) :
    tor hσ 1 t ∈ hHat σ (ng 1) := by
  rw [hHat, Subgroup.mem_subgroupOf]
  show (tor hσ 1 t : adjointGroup d4 K) ∈ (hShortHom σ).range
  refine ⟨t, ?_⟩
  rw [tor_val]
  exact (d4z_torE_one_left t).symm

theorem d4z_tor_fixed_mem_hHat (hσ : ∀ c, σ (σ (σ c)) = c) (s : fixedUnits σ) :
    tor hσ s 1 ∈ hHat σ (ng 0) := by
  rw [hHat, Subgroup.mem_subgroupOf]
  show (tor hσ s 1 : adjointGroup d4 K) ∈ (hLongHom σ).range
  refine ⟨s, ?_⟩
  rw [tor_val]
  unfold torE
  have h : hShortHom σ (1 : Kˣ) = 1 := map_one _
  rw [h, mul_one]
  rfl

end Tori

section Fix

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

theorem d4z_tor_conj_long (s : fixedUnits σ) (t : Kˣ) {γ : Fin (Tag.rank .G2) → ℤ}
    (hγ : IsRoot .G2 γ) (hl : d43Long γ) (hχ : chi σ s t (d43Lift γ) = 1) {x : twistedGroup σ}
    (hx : x ∈ twistedRootGroup σ γ) : tor hσ s t * x * (tor hσ s t)⁻¹ = x := by
  have hα := isRoot_d43Lift hγ
  have hp := proj_d43Lift hγ
  have hfix := rho_d43Lift_of_long hγ hl
  obtain ⟨c, rfl⟩ := (mem_iff_xL hσ hα hfix hp x).1 hx
  rw [tor_conj_xL hσ hα hfix s t c]
  have h1 : chiF hσ hfix s t = 1 := Subtype.ext (by rw [chiF_val, hχ]; rfl)
  rw [h1, one_mul]

theorem d4z_tor_fix_long (s : fixedUnits σ) (t : Kˣ) {γ : Fin (Tag.rank .G2) → ℤ}
    (hγ : IsRoot .G2 γ) (hl : d43Long γ) (hχ : chi σ s t (d43Lift γ) ≠ 1) {x : twistedGroup σ}
    (hx : x ∈ twistedRootGroup σ γ) (hfix : tor hσ s t * x * (tor hσ s t)⁻¹ = x) : x = 1 := by
  have hα := isRoot_d43Lift hγ
  have hp := proj_d43Lift hγ
  have hρ := rho_d43Lift_of_long hγ hl
  obtain ⟨c, rfl⟩ := (mem_iff_xL hσ hα hρ hp x).1 hx
  rw [tor_conj_xL hσ hα hρ s t c] at hfix
  have h1 : (chi σ s t (d43Lift γ) : K) * (c : K) = c := by
    have := xPar_injective hα (congrArg Subtype.val hfix)
    rwa [Subfield.coe_mul] at this
  have hc0 : c = 0 := by
    by_contra hc0
    have hc0' : (c : K) ≠ 0 := fun h => hc0 (Subtype.ext h)
    exact hχ (Units.val_eq_one.1 (mul_right_cancel₀ hc0' (by rw [one_mul]; exact h1)))
  rw [hc0]
  exact Subtype.ext (by rw [xL_val]; exact xPar_zero _)

theorem d4z_tor_fix_short (s : fixedUnits σ) (t : Kˣ) {γ : Fin (Tag.rank .G2) → ℤ}
    (hγ : IsRoot .G2 γ) (hs : ¬ d43Long γ) (hχ : chi σ s t (d43Lift γ) ≠ 1) {x : twistedGroup σ}
    (hx : x ∈ twistedRootGroup σ γ) (hfix : tor hσ s t * x * (tor hσ s t)⁻¹ = x) : x = 1 := by
  have hα := isRoot_d43Lift hγ
  have hp := proj_d43Lift hγ
  have hne := rho_d43Lift_ne hγ hs
  obtain ⟨c, rfl⟩ := (mem_iff_xS hσ hα hne hp x).1 hx
  rw [tor_conj_xS hσ hα hne s t c] at hfix
  have h1 : (chi σ s t (d43Lift γ) : K) * c = c :=
    xOrbit_injective σ hα hne (congrArg Subtype.val hfix)
  have hc0 : c = 0 := by
    by_contra hc0
    exact hχ (Units.val_eq_one.1 (mul_right_cancel₀ hc0 (by rw [one_mul]; exact h1)))
  rw [hc0]
  exact Subtype.ext (xOrbit_zero σ _)

end Fix

section ZT

variable {K : Type} [Field K] {σ : K →+* K}

theorem d4_z_facts (hσ : ∀ c, σ (σ (σ c)) = c) (ω : Kˣ) (hωσ : σ (ω : K) = ω)
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ∃ zX : twistedGroup σ,
      ((zX : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
        rootDiagUnit TwistTag.D4.tag ![ω, ω, 1, ω] ∧
      zX ∈ ⨆ i, hHat σ i ∧
      (∀ k, CFSG.GH74.BNPair.IsRoot 6 k → k % 2 = 0 → ∀ x ∈ hexGroup (twistedX σ) k,
        zX * x * zX⁻¹ = x) ∧
      (∀ k, CFSG.GH74.BNPair.IsRoot 6 k → k % 2 ≠ 0 → ∀ x ∈ hexGroup (twistedX σ) k,
        zX * x * zX⁻¹ = x → x = 1) := by
  refine ⟨tor hσ 1 (ω ^ 2), ?_, ?_, ?_, ?_⟩
  · rw [tor_val]
    exact d4z_coe_torE hωσ hω3
  · exact Subgroup.mem_iSup_of_mem (ng 1) (d4z_tor_one_mem_hHat hσ _)
  · intro k hk hk2 x hx
    have hγ := isRoot_hexPos hk.1 hk.2
    have hl := (d4z_long_hexPos_iff hk).2 hk2
    refine d4z_tor_conj_long hσ 1 (ω ^ 2) hγ hl ?_ hx
    have e : chi σ ((1 : fixedUnits σ) : Kˣ) (ω ^ 2) (d43Lift (hexPos k)) =
        ω ^ (d43Lift (hexPos k) 0 + d43Lift (hexPos k) 1 + d43Lift (hexPos k) 3) :=
      d4z_chi hωσ hω3 _
    rw [e, ← rootChar_z ω]
    exact rootChar_z_fixed ω hω3 (isRoot_d43Lift hγ) (rho_d43Lift_of_long hγ hl)
  · intro k hk hk2 x hx hfix
    have hγ := isRoot_hexPos hk.1 hk.2
    have hs : ¬ d43Long (hexPos k) := fun h => hk2 ((d4z_long_hexPos_iff hk).1 h)
    refine d4z_tor_fix_short hσ 1 (ω ^ 2) hγ hs ?_ hx hfix
    have e : chi σ ((1 : fixedUnits σ) : Kˣ) (ω ^ 2) (d43Lift (hexPos k)) =
        ω ^ (d43Lift (hexPos k) 0 + d43Lift (hexPos k) 1 + d43Lift (hexPos k) 3) :=
      d4z_chi hωσ hω3 _
    rw [e, ← rootChar_z ω]
    exact rootChar_z_ne_one ω hω3 hω1 (isRoot_d43Lift hγ) (rho_d43Lift_ne hγ hs)

theorem d4z_hHat_zero_le_longSub (hσ : ∀ c, σ (σ (σ c)) = c) :
    hHat σ (ng 0) ≤ longSub 6 (hexGroup (twistedX σ)) := by
  refine (hHat_le_rankOne hσ (ng 0)).trans (sup_le ?_ ?_)
  · have h := root_le_longSub (n := 6) (root := hexGroup (twistedX σ)) (k := 6)
      ⟨by norm_num, by norm_num⟩ (by norm_num)
    change twistedRootGroup σ (hexPos 6) ≤ _ at h
    rwa [hexPos_six_eq_single] at h
  · have h := root_le_longSub (n := 6) (root := hexGroup (twistedX σ)) (k := -6)
      ⟨by norm_num, by norm_num⟩ (by norm_num)
    change twistedRootGroup σ (hexPos (-6)) ≤ _ at h
    rwa [hexPos_neg_six_eq_single] at h

theorem d4_t0_facts (hσ : ∀ c, σ (σ (σ c)) = c) (ω : Kˣ) (hωσ : σ (ω : K) = ω)
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ∃ t : twistedGroup σ, t ∈ ⨆ i, hHat σ i ∧ t ∈ longSub 6 (hexGroup (twistedX σ)) ∧
      ∀ k, CFSG.GH74.BNPair.IsRoot 6 k → 0 < k → k % 2 = 0 → ∀ x ∈ hexGroup (twistedX σ) k,
        t * x * t⁻¹ = x → x = 1 := by
  set s : fixedUnits σ := ⟨ω, (mem_fixedUnits σ).2 hωσ⟩ with hs
  refine ⟨tor hσ s 1, Subgroup.mem_iSup_of_mem (ng 0) (d4z_tor_fixed_mem_hHat hσ s),
    d4z_hHat_zero_le_longSub hσ (d4z_tor_fixed_mem_hHat hσ s), ?_⟩
  intro k hk _ hk2 x hx hfix
  have hγ := isRoot_hexPos hk.1 hk.2
  have hl := (d4z_long_hexPos_iff hk).2 hk2
  refine d4z_tor_fix_long hσ s 1 hγ hl ?_ hx hfix
  have hα := isRoot_d43Lift hγ
  have hρ := rho_d43Lift_of_long hγ hl
  have e : chi σ (s : Kˣ) 1 (d43Lift (hexPos k)) = ω ^ pr (nd 2) (d43Lift (hexPos k)) := by
    simp [chi, hs]
  rw [e]
  exact d4z_zpow_ne_one hω3 hω1 (d4z_fixed_pr_two _ hα hρ)

end ZT

end CFSG.GH74.GLS.Stage2.Bender.Thm1
