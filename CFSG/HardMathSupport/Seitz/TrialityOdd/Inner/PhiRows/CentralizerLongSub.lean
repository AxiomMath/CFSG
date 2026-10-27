module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.ThreeQ1Long
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2TorusCoord

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.CentL

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint CFSG.Timmesfeld.RankTwo
  CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex
  CFSG.ClassicalInvolution.G2D4Models
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg.CentralExt.TrialityClosed
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
open scoped MatrixGroups commutatorElement


variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

@[expose] def CentralizerLongSubInN (σ : K →+* K) (hσ : ∀ c, σ (σ (σ c)) = c) : Prop :=
  Subgroup.centralizer (longSub 6 (hexGroup (twistedX σ)) : Set (twistedGroup σ)) ≤
    (d4RGD2 σ hσ).N

include hσ in
theorem d4X_zero_eq_one (i : Fin 6) (c : d43Par σ i) (hc : c = 0) :
    d4X hσ i c = 1 := by
  subst hc
  have h := d4X_add hσ i (0 : d43Par σ i) (0 : d43Par σ i)
  have h' : d4X hσ i (0 : d43Par σ i) =
      d4X hσ i (0 : d43Par σ i) * d4X hσ i (0 : d43Par σ i) := by
    simpa using h
  have h2 := congrArg (fun x => (d4X hσ i (0 : d43Par σ i))⁻¹ * x) h'
  simpa [mul_assoc] using h2.symm

include hσ in
theorem chi_lift_four (s : fixedUnits σ) (t : Kˣ) :
    chi σ (s : Kˣ) t (d43Lift (hexPos 4)) = (s : Kˣ) := by
  have e0 : pr (nd 0) (d43Lift (hexPos 4)) = 0 := by decide +kernel
  have e1 : pr (nd 1) (d43Lift (hexPos 4)) = 0 := by decide +kernel
  have e2 : pr (nd 2) (d43Lift (hexPos 4)) = 1 := by decide +kernel
  have e3 : pr (nd 3) (d43Lift (hexPos 4)) = 0 := by decide +kernel
  rw [chi, e0, e1, e2, e3]
  simp

include hσ in
theorem chi_lift_two (s : fixedUnits σ) (t : Kˣ) :
    chi σ (s : Kˣ) t (d43Lift (hexPos 2)) = (s : Kˣ)⁻¹ * normU σ t := by
  have e0 : pr (nd 0) (d43Lift (hexPos 2)) = 1 := by decide +kernel
  have e1 : pr (nd 1) (d43Lift (hexPos 2)) = 1 := by decide +kernel
  have e2 : pr (nd 2) (d43Lift (hexPos 2)) = -1 := by decide +kernel
  have e3 : pr (nd 3) (d43Lift (hexPos 2)) = 1 := by decide +kernel
  rw [chi, e0, e1, e2, e3, normU]
  simp

include hσ in
theorem exists_tor_of_mem_iSup_hHat {c : twistedGroup σ} (hc : c ∈ ⨆ i, hHat σ i) :
    ∃ s : fixedUnits σ, ∃ t : Kˣ, c = tor hσ s t := by
  have hEq : (⨆ i, hHat σ i) = hHat σ (ng 0) ⊔ hHat σ (ng 1) := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun i => ?_
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup (fun i => hHat σ i) (ng 0))
        (le_iSup (fun i => hHat σ i) (ng 1))
  rw [hEq] at hc
  have hnorm : hHat σ (ng 0) ≤
      Subgroup.normalizer (hHat σ (ng 1) : Set (twistedGroup σ)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have e : x * y * x⁻¹ = y := by
        rw [(hHat_commute σ hx hy).eq]
        group
      rwa [e]
    · intro hy
      have hz : x * y * x⁻¹ ∈ hHat σ (ng 1) := hy
      have e : x⁻¹ * (x * y * x⁻¹) * x = x * y * x⁻¹ := by
        rw [(hHat_commute σ (Subgroup.inv_mem _ hx) hz).eq]
        group
      have hyy : y = x⁻¹ * (x * y * x⁻¹) * x := by group
      rw [hyy, e]
      exact hz
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right
    (hHat σ (ng 0)) (hHat σ (ng 1)) hnorm
  change c ∈ (↑(hHat σ (ng 0) ⊔ hHat σ (ng 1)) : Set (twistedGroup σ)) at hc
  rw [hcoe, Set.mem_mul] at hc
  obtain ⟨a, ha, b, hb, hab⟩ := hc
  have hs0 : (a : adjointGroup d4 K) ∈ (hLongHom σ).range := by
    have h := Subgroup.mem_subgroupOf.1 ha
    change (a : adjointGroup d4 K) ∈ hHatE σ (ng 0) at h
    change (a : adjointGroup d4 K) ∈ (hLongHom σ).range at h
    exact h
  obtain ⟨s, hs⟩ := hs0
  have ha' : a = tor hσ s 1 := Subtype.ext (by
    rw [tor_val]
    show (a : adjointGroup d4 K) = torE σ (s : Kˣ) 1
    rw [show torE σ (s : Kˣ) 1 = torusElement d4 K (nd 2) (s : Kˣ) from by
      unfold torE
      rw [map_one, mul_one]]
    rw [← hs]
    rfl)
  have ht0 : (b : adjointGroup d4 K) ∈ (hShortHom σ).range := by
    have h := Subgroup.mem_subgroupOf.1 hb
    change (b : adjointGroup d4 K) ∈ hHatE σ (ng 1) at h
    change (b : adjointGroup d4 K) ∈ (hShortHom σ).range at h
    exact h
  obtain ⟨t, ht⟩ := ht0
  have hb' : b = tor hσ 1 t := Subtype.ext (by
    rw [tor_val]
    show (b : adjointGroup d4 K) = torE σ ((1 : fixedUnits σ) : Kˣ) t
    rw [← ht]
    exact (d4z_torE_one_left t).symm)
  refine ⟨s, t, ?_⟩
  rw [← hab, ha', hb']
  apply Subtype.ext
  rw [Subgroup.coe_mul, tor_val, tor_val, tor_val]
  unfold torE
  have h1 : ((1 : fixedUnits σ) : Kˣ) = 1 := rfl
  rw [h1, show torusElement d4 K (nd 2) (1 : Kˣ) = 1 from
      (torusHom (τ := d4) K (nd 2)).map_one,
    show (hShortHom σ) (1 : Kˣ) = 1 from (hShortHom σ).map_one]
  group

include hσ in
theorem eq_slShort_of_mem_iSup_hHat_centralizer {c : twistedGroup σ}
    (hcH : c ∈ ⨆ i, hHat σ i)
    (hcL : ∀ l ∈ longSub 6 (hexGroup (twistedX σ)), c * l = l * c) :
    ∃ t : Kˣ, (t : K) * σ t * σ (σ t) = 1 ∧ c = slShort σ hσ (HSL t) := by
  obtain ⟨s, t, rfl⟩ := exists_tor_of_mem_iSup_hHat hσ hcH
  have hmem4 : d4X hσ 3 (1 : fixedField σ) ∈ longSub 6 (hexGroup (twistedX σ)) :=
    root_le_longSub (n := 6) (root := hexGroup (twistedX σ)) (k := 4)
      ⟨by norm_num, by norm_num⟩ (by norm_num)
      (d4X_mem_hexGroup' hσ 3 (1 : fixedField σ) (by norm_num))
  have hfix4 : tor hσ s t * d4X hσ 3 (1 : fixedField σ) * (tor hσ s t)⁻¹ =
      d4X hσ 3 (1 : fixedField σ) := by
    have hcomm := hcL _ hmem4
    rw [hcomm]
    group
  have hx4 : d4X hσ 3 (1 : fixedField σ) ≠ 1 := by
    have hzero : d4X hσ 3 (0 : fixedField σ) = 1 := d4X_zero_eq_one hσ 3 0 rfl
    intro h
    have h' : (1 : fixedField σ) = 0 := d4X_injective hσ 3 (h.trans hzero.symm)
    exact one_ne_zero h'
  have hmem4' : d4X hσ 3 (1 : fixedField σ) ∈ twistedRootGroup σ (hexPos 4) :=
    d4X_mem_hexGroup' hσ 3 (1 : fixedField σ) (by norm_num)
  have hchi4 : chi σ (s : Kˣ) t (d43Lift (hexPos 4)) = 1 := by
    by_contra hne
    exact hx4 (d4z_tor_fix_long hσ s t
      (isRoot_hexPos (by norm_num) (by norm_num))
      (by unfold CFSG.Timmesfeld.RankTwo.d43Long; decide) hne hmem4' hfix4)
  have hs1 : (s : Kˣ) = 1 := by
    rw [chi_lift_four hσ] at hchi4
    exact hchi4
  have hmem2 : d4X hσ 1 (1 : fixedField σ) ∈ longSub 6 (hexGroup (twistedX σ)) :=
    root_le_longSub (n := 6) (root := hexGroup (twistedX σ)) (k := 2)
      ⟨by norm_num, by norm_num⟩ (by norm_num)
      (d4X_mem_hexGroup' hσ 1 (1 : fixedField σ) (by norm_num))
  have hfix2 : tor hσ s t * d4X hσ 1 (1 : fixedField σ) * (tor hσ s t)⁻¹ =
      d4X hσ 1 (1 : fixedField σ) := by
    have hcomm := hcL _ hmem2
    rw [hcomm]
    group
  have hx2 : d4X hσ 1 (1 : fixedField σ) ≠ 1 := by
    have hzero : d4X hσ 1 (0 : fixedField σ) = 1 := d4X_zero_eq_one hσ 1 0 rfl
    intro h
    have h' : (1 : fixedField σ) = 0 := d4X_injective hσ 1 (h.trans hzero.symm)
    exact one_ne_zero h'
  have hmem2' : d4X hσ 1 (1 : fixedField σ) ∈ twistedRootGroup σ (hexPos 2) :=
    d4X_mem_hexGroup' hσ 1 (1 : fixedField σ) (by norm_num)
  have hchi2 : chi σ (s : Kˣ) t (d43Lift (hexPos 2)) = 1 := by
    by_contra hne
    exact hx2 (d4z_tor_fix_long hσ s t
      (isRoot_hexPos (by norm_num) (by norm_num))
      (by unfold CFSG.Timmesfeld.RankTwo.d43Long; decide) hne hmem2' hfix2)
  have hnorm : normU σ t = 1 := by
    rw [chi_lift_two hσ, hs1, inv_one, one_mul] at hchi2
    exact hchi2
  have hNval : (t : K) * σ t * σ (σ t) = 1 := by
    have h := congrArg (fun u : Kˣ => (u : K)) hnorm
    simpa [normU, Units.coe_map] using h
  have hs1' : s = 1 := Subtype.ext hs1
  refine ⟨t, hNval, ?_⟩
  have htor : tor hσ 1 t = slShort σ hσ (HSL t) := by
    apply Subtype.ext
    rw [tor_val]
    show torE σ ((1 : fixedUnits σ) : Kˣ) t =
      ((slShort σ hσ (HSL t) : twistedGroup σ) : adjointGroup d4 K)
    rw [slShort_HSL]
    exact d4z_torE_one_left t
  rw [hs1']
  exact htor

include hσ in
theorem chi_tor_one (s : fixedUnits σ) (α : Fin d4.rank → ℤ) :
    chi σ (s : Kˣ) 1 α = (s : Kˣ) ^ (pr (nd 2) α) := by
  rw [chi]
  simp


include hσ in
theorem tor_fix_root_ne_three (s : fixedUnits σ) (hs1 : ((s : Kˣ) : K) ≠ 1)
    (hs2 : (((s : Kˣ) : K)) ^ 2 ≠ 1) {k : ℤ} (hk1 : 1 ≤ k) (hk6 : k ≤ 6) (hk3 : k ≠ 3)
    {x : twistedGroup σ} (hx : x ∈ hexGroup (twistedX σ) k)
    (hfix : tor hσ s 1 * x * (tor hσ s 1)⁻¹ = x) : x = 1 := by
  have hs1u : (s : Kˣ) ≠ 1 := fun h => hs1 (by rw [h]; rfl)
  have hs2u : (s : Kˣ) ^ 2 ≠ 1 := fun h => hs2 (by
    have := congrArg (fun u : Kˣ => (u : K)) h
    simpa using this)
  have hk : k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · have hχ : chi σ (s : Kˣ) 1 (d43Lift (hexPos 1)) ≠ 1 := by
      rw [chi_tor_one hσ]
      have e : pr (nd 2) (d43Lift (hexPos 1)) = -1 := by decide +kernel
      rw [e, zpow_neg_one]
      exact inv_ne_one.2 hs1u
    refine d4z_tor_fix_short hσ s 1 (isRoot_hexPos (by norm_num) (by norm_num))
      (by unfold CFSG.Timmesfeld.RankTwo.d43Long; decide) hχ ?_ hfix
    exact hx
  · have hχ : chi σ (s : Kˣ) 1 (d43Lift (hexPos 2)) ≠ 1 := by
      rw [chi_tor_one hσ]
      have e : pr (nd 2) (d43Lift (hexPos 2)) = -1 := by decide +kernel
      rw [e, zpow_neg_one]
      exact inv_ne_one.2 hs1u
    refine d4z_tor_fix_long hσ s 1 (isRoot_hexPos (by norm_num) (by norm_num))
      (by unfold CFSG.Timmesfeld.RankTwo.d43Long; decide) hχ ?_ hfix
    exact hx
  · have hχ : chi σ (s : Kˣ) 1 (d43Lift (hexPos 4)) ≠ 1 := by
      rw [chi_tor_one hσ]
      have e : pr (nd 2) (d43Lift (hexPos 4)) = 1 := by decide +kernel
      rw [e, zpow_one]
      exact hs1u
    refine d4z_tor_fix_long hσ s 1 (isRoot_hexPos (by norm_num) (by norm_num))
      (by unfold CFSG.Timmesfeld.RankTwo.d43Long; decide) hχ ?_ hfix
    exact hx
  · have hχ : chi σ (s : Kˣ) 1 (d43Lift (hexPos 5)) ≠ 1 := by
      rw [chi_tor_one hσ]
      have e : pr (nd 2) (d43Lift (hexPos 5)) = 1 := by decide +kernel
      rw [e, zpow_one]
      exact hs1u
    refine d4z_tor_fix_short hσ s 1 (isRoot_hexPos (by norm_num) (by norm_num))
      (by unfold CFSG.Timmesfeld.RankTwo.d43Long; decide) hχ ?_ hfix
    exact hx
  · have hχ : chi σ (s : Kˣ) 1 (d43Lift (hexPos 6)) ≠ 1 := by
      rw [chi_tor_one hσ]
      have e : pr (nd 2) (d43Lift (hexPos 6)) = 2 := by decide +kernel
      rw [e, zpow_ofNat]
      exact hs2u
    refine d4z_tor_fix_long hσ s 1 (isRoot_hexPos (by norm_num) (by norm_num))
      (by unfold CFSG.Timmesfeld.RankTwo.d43Long; decide) hχ ?_ hfix
    exact hx


include hσ in
theorem fixed_U_le_root_three (s : fixedUnits σ) (hs1 : ((s : Kˣ) : K) ≠ 1)
    (hs2 : (((s : Kˣ) : K)) ^ 2 ≠ 1) {w : twistedGroup σ}
    (hwU : w ∈ posUnipotent (g2Shape (twistedX σ)))
    (hfix : tor hσ s 1 * w * (tor hσ s 1)⁻¹ = w) :
    w ∈ hexGroup (twistedX σ) 3 := by
  let R := d4RGD2 σ hσ
  have hh1H : tor hσ s 1 ∈ ⨆ i, hHat σ i :=
    Subgroup.mem_iSup_of_mem (ng 0) (d4z_tor_fixed_mem_hHat hσ s)
  have hwU' : w ∈ chainProd (hexGroup (twistedX σ)) (intList 1 ((6 : ℕ) : ℤ)) := by
    rw [← R.carrier_eq]
    exact hwU
  obtain ⟨f, hf, hfw⟩ :=
    (chain_mem_chainProd_iff (hexGroup (twistedX σ)) _ (chain_intList_nodup 1 6) w).1 hwU'
  let g : ℤ → twistedGroup σ := fun k => tor hσ s 1 * f k * (tor hσ s 1)⁻¹
  have hf' : ∀ k ∈ intList 1 (6 : ℤ), f k ∈ hexGroup (twistedX σ) k := hf
  have hg : ∀ k ∈ intList 1 (6 : ℤ), g k ∈ hexGroup (twistedX σ) k := by
    intro k hk
    have hk' := mem_intList_iff.1 hk
    exact R.invariant k (isRoot_of_pos_le hk'.1 hk'.2) (tor hσ s 1) hh1H (f k) (hf k hk)
  have hprod : (List.map g (intList 1 (6 : ℤ))).prod =
      (List.map f (intList 1 (6 : ℤ))).prod := by
    have h1 : List.map g (intList 1 (6 : ℤ)) =
        List.map (MulAut.conj (tor hσ s 1)) (List.map f (intList 1 (6 : ℤ))) := by
      rw [List.map_map]
      rfl
    rw [h1, List.prod_hom (List.map f (intList 1 (6 : ℤ))) (MulAut.conj (tor hσ s 1)), hfw]
    simpa [MulAut.conj_apply] using hfix
  have hfg := R.unique g f hg hf' hprod
  have hshort : ∀ k : ℤ, 1 ≤ k → k ≤ 6 → k ≠ 3 → f k = 1 := by
    intro k hk1 hk6 hk3
    have hk : k ∈ intList 1 ((6 : ℕ) : ℤ) := mem_intList_iff.2 ⟨hk1, by simpa using hk6⟩
    have hfixk : tor hσ s 1 * f k * (tor hσ s 1)⁻¹ = f k := hfg k hk
    exact tor_fix_root_ne_three hσ s hs1 hs2 hk1 hk6 hk3 (hf k hk) hfixk
  have hmem3 : 3 ∈ intList 1 ((6 : ℕ) : ℤ) := mem_intList_iff.2 ⟨by norm_num, by norm_num⟩
  have hw : w = f 3 := by
    rw [← hfw]
    rw [show intList 1 (6 : ℤ) = [1, 2, 3, 4, 5, 6] by decide]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    rw [hshort 1 (by norm_num) (by norm_num) (by norm_num),
      hshort 2 (by norm_num) (by norm_num) (by norm_num),
      hshort 4 (by norm_num) (by norm_num) (by norm_num),
      hshort 5 (by norm_num) (by norm_num) (by norm_num),
      hshort 6 (by norm_num) (by norm_num) (by norm_num)]
    simp
  rw [hw]
  exact hf 3 hmem3


include hσ in
theorem tor_one_eq_slShort (t : Kˣ) :
    tor hσ 1 t = slShort σ hσ (HSL t) := by
  apply Subtype.ext
  rw [tor_val]
  show torE σ ((1 : fixedUnits σ) : Kˣ) t =
    ((slShort σ hσ (HSL t) : twistedGroup σ) : adjointGroup d4 K)
  rw [slShort_HSL]
  exact d4z_torE_one_left t

include hσ in
theorem chi_one_lift_three (t : fixedUnits σ) :
    chi σ 1 (t : Kˣ) (d43Lift (hexPos 3)) = (t : Kˣ) := by
  have e0 : pr (nd 0) (d43Lift (hexPos 3)) = -1 := by decide +kernel
  have e1 : pr (nd 1) (d43Lift (hexPos 3)) = 1 := by decide +kernel
  have e2 : pr (nd 2) (d43Lift (hexPos 3)) = 0 := by decide +kernel
  have e3 : pr (nd 3) (d43Lift (hexPos 3)) = 1 := by decide +kernel
  have ht : Units.map σ.toMonoidHom (t : Kˣ) = (t : Kˣ) := Units.ext ((mem_fixedUnits σ).1 t.2)
  rw [chi, e0, e1, e2, e3]
  rw [ht, ht]
  simp

include hσ in
theorem tor_one_fix_root_three (t : fixedUnits σ) (ht : ((t : Kˣ) : K) ≠ 1)
    {x : twistedGroup σ} (hx : x ∈ hexGroup (twistedX σ) 3)
    (hfix : tor hσ 1 t * x * (tor hσ 1 t)⁻¹ = x) : x = 1 := by
  have hχ : chi σ 1 (t : Kˣ) (d43Lift (hexPos 3)) ≠ 1 := by
    rw [chi_one_lift_three hσ]
    exact fun h => ht (by simpa using congrArg (fun u : Kˣ => (u : K)) h)
  refine d4z_tor_fix_short hσ 1 t (isRoot_hexPos (by norm_num) (by norm_num))
    (by unfold CFSG.Timmesfeld.RankTwo.d43Long; decide) hχ ?_ hfix
  exact hx


include hσ in
theorem root_three_commute_root_two {a b : twistedGroup σ}
    (ha : a ∈ hexGroup (twistedX σ) 3) (hb : b ∈ hexGroup (twistedX σ) 2) :
    a * b = b * a := by
  obtain ⟨c, rfl⟩ := (mem_hexGroup_iff' hσ 2 (by norm_num)).1 ha
  obtain ⟨d, rfl⟩ := (mem_hexGroup_iff' hσ 1 (by norm_num)).1 hb
  exact ((d4Rel_model hσ).c12 d c).symm.eq

include hσ in
theorem root_three_commute_root_six {a b : twistedGroup σ}
    (ha : a ∈ hexGroup (twistedX σ) 3) (hb : b ∈ hexGroup (twistedX σ) 6) :
    a * b = b * a := by
  obtain ⟨c, rfl⟩ := (mem_hexGroup_iff' hσ 2 (by norm_num)).1 ha
  obtain ⟨d, rfl⟩ := (mem_hexGroup_iff' hσ 5 (by norm_num)).1 hb
  exact ((d4Rel_model hσ).c25 c d).eq


include hσ in
theorem commute_of_mem_iSup_hHat {g h : twistedGroup σ}
    (hg : g ∈ ⨆ i, hHat σ i) (hh : h ∈ ⨆ i, hHat σ i) : Commute g h := by
  refine Subgroup.iSup_induction _ (C := fun g => Commute g h) hg (fun i x hx => ?_)
    (Commute.one_left h) (fun x y hx hy => hx.mul_left hy)
  exact Subgroup.iSup_induction _ (C := fun h => Commute x h) hh
    (fun j y hy => hHat_commute σ hx hy) (Commute.one_right x)
    (fun y y' hy hy' => hy.mul_right hy')


section FiniteField

variable [Finite K]

theorem conj_eq_of_conj_split {G : Type*} [Group G] {v n u c x : G}
    (hcvu : c = v * n * u) (hv : v * x * v⁻¹ = x) (hu : u * x * u⁻¹ = x)
    (hc : c * x * c⁻¹ = x) : n * x * n⁻¹ = x := by
  have hnv : v * (n * x * n⁻¹) * v⁻¹ = x := by
    calc v * (n * x * n⁻¹) * v⁻¹
        = v * n * (u * x * u⁻¹) * n⁻¹ * v⁻¹ := by
            rw [hu]; group
      _ = v * n * u * x * u⁻¹ * n⁻¹ * v⁻¹ := by group
      _ = c * x * c⁻¹ := by rw [hcvu]; group
      _ = x := hc
  have h1 : v⁻¹ * (v * (n * x * n⁻¹) * v⁻¹) * v = n * x * n⁻¹ := by group
  have h2 : v⁻¹ * x * v = x := by
    have := congrArg (fun y => v⁻¹ * y * v) hv
    simpa [mul_assoc] using this.symm
  calc n * x * n⁻¹ = v⁻¹ * (v * (n * x * n⁻¹) * v⁻¹) * v := by rw [h1]
    _ = v⁻¹ * x * v := by rw [hnv]
    _ = x := h2

include hσ in
theorem centralizerLongSub_cell {q : ℕ} (hq : 5 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q)
    (s : fixedUnits σ) (hs1 : ((s : Kˣ) : K) ≠ 1)
    (hs2 : (((s : Kˣ) : K)) ^ 2 ≠ 1) {c : twistedGroup σ}
    (hc : c ∈ Subgroup.centralizer
      (longSub 6 (hexGroup (twistedX σ)) : Set (twistedGroup σ))) :
    ∃ v n u : twistedGroup σ,
      v ∈ hexGroup (twistedX σ) 3 ∧ u ∈ hexGroup (twistedX σ) 3 ∧
        n ∈ ⨆ i, hHat σ i ∧ c = v * n * u := by
  classical
  let R := d4RGD2 σ hσ
  have hcen : Subgroup.center (twistedGroup σ) = ⊥ :=
    twistedGroup_center_eq_bot_of_card (q := q) (by omega) hK hσq
  have hgen : ((⨆ i, hHat σ i) ⊔ posUnipotent (g2Shape (twistedX σ))) ⊔ R.N = ⊤ :=
    d4RGD2_gen hσ
  have hZ := RGD2.hZ_of_center_bot R hgen hcen
  have hh1H : tor hσ s 1 ∈ ⨆ i, hHat σ i :=
    Subgroup.mem_iSup_of_mem (ng 0) (d4z_tor_fixed_mem_hHat hσ s)
  have hh1L : tor hσ s 1 ∈ longSub 6 (hexGroup (twistedX σ)) :=
    d4z_hHat_zero_le_longSub hσ (d4z_tor_fixed_mem_hHat hσ s)
  have hc1 : tor hσ s 1 * c * (tor hσ s 1)⁻¹ = c := by
    have h := Subgroup.mem_centralizer_iff.1 hc _ hh1L
    calc tor hσ s 1 * c * (tor hσ s 1)⁻¹ =
        c * tor hσ s 1 * (tor hσ s 1)⁻¹ := by rw [h]
      _ = c := by group
  have hS : FoldStab R (MulAut.conj (tor hσ s 1)) :=
    FoldStab.conj_of_mem_H (R := R) hh1H
  obtain ⟨v, hv, n, hn, u, hu, hcvu⟩ := hS.cell hgen hZ hc1
  have hv3 : v ∈ hexGroup (twistedX σ) 3 :=
    fixed_U_le_root_three hσ s hs1 hs2 hv.1 (mem_foldFix_conj_iff.1 hv.2)
  have hu3 : u ∈ hexGroup (twistedX σ) 3 :=
    fixed_U_le_root_three hσ s hs1 hs2 hu.1 (mem_foldFix_conj_iff.1 hu.2)
  obtain ⟨⟨x2, hx2⟩, hx2ne⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).1 (R.ne_bot 2 ⟨by norm_num, by norm_num⟩)
  have hx21 : x2 ≠ 1 := fun h => hx2ne (Subtype.ext h)
  obtain ⟨⟨x6, hx6⟩, hx6ne⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).1 (R.ne_bot 6 ⟨by norm_num, by norm_num⟩)
  have hx61 : x6 ≠ 1 := fun h => hx6ne (Subtype.ext h)
  have hx2L : x2 ∈ longSub 6 (hexGroup (twistedX σ)) :=
    root_le_longSub (⟨by norm_num, by norm_num⟩ : CFSG.GH74.BNPair.IsRoot 6 2)
      (by norm_num) hx2
  have hx6L : x6 ∈ longSub 6 (hexGroup (twistedX σ)) :=
    root_le_longSub (⟨by norm_num, by norm_num⟩ : CFSG.GH74.BNPair.IsRoot 6 6)
      (by norm_num) hx6
  have hc_x2 : c * x2 * c⁻¹ = x2 := by
    have h := (Subgroup.mem_centralizer_iff.1 hc x2 hx2L).symm
    calc c * x2 * c⁻¹ = x2 * c * c⁻¹ := by rw [h]
      _ = x2 := by group
  have hc_x6 : c * x6 * c⁻¹ = x6 := by
    have h := (Subgroup.mem_centralizer_iff.1 hc x6 hx6L).symm
    calc c * x6 * c⁻¹ = x6 * c * c⁻¹ := by rw [h]
      _ = x6 := by group
  have hv_x2 : v * x2 * v⁻¹ = x2 := by
    rw [root_three_commute_root_two hσ hv3 hx2]
    group
  have hu_x2 : u * x2 * u⁻¹ = x2 := by
    rw [root_three_commute_root_two hσ hu3 hx2]
    group
  have hv_x6 : v * x6 * v⁻¹ = x6 := by
    rw [root_three_commute_root_six hσ hv3 hx6]
    group
  have hu_x6 : u * x6 * u⁻¹ = x6 := by
    rw [root_three_commute_root_six hσ hu3 hx6]
    group
  have hn_x2 : n * x2 * n⁻¹ = x2 :=
    conj_eq_of_conj_split hcvu hv_x2 hu_x2 hc_x2
  have hn_x6 : n * x6 * n⁻¹ = x6 :=
    conj_eq_of_conj_split hcvu hv_x6 hu_x6 hc_x6
  have hnH : n ∈ ⨆ i, hHat σ i :=
    RGD2.mem_H_of_fixes_two R hn.1 hx2 hx21 hx6 hx61 hn_x2 hn_x6
  exact ⟨v, n, u, hv3, hu3, hnH, hcvu⟩

include hσ in
theorem centralizerLongSub_eq_H (t0 : (fixedField σ)ˣ) (ht0 : (t0 : fixedField σ) ≠ 1)
    {c v n u : twistedGroup σ}
    (hc : c ∈ Subgroup.centralizer
      (longSub 6 (hexGroup (twistedX σ)) : Set (twistedGroup σ)))
    (hv3 : v ∈ hexGroup (twistedX σ) 3) (hu3 : u ∈ hexGroup (twistedX σ) 3)
    (hnH : n ∈ ⨆ i, hHat σ i) (hcvu : c = v * n * u) :
    c ∈ ⨆ i, hHat σ i := by
  classical
  let t0K : fixedUnits σ :=
    ⟨Units.map (fixedField σ).subtype.toMonoidHom t0, by
      refine (mem_fixedUnits σ).2 ?_
      change σ (↑t0 : K) = (↑t0 : K)
      exact (t0 : fixedField σ).2⟩
  have ht0K : ((t0K : Kˣ) : K) ≠ 1 := by
    intro h
    apply ht0
    apply Subtype.ext
    show (t0 : K) = 1
    simpa [t0K, Units.coe_map] using h
  have h2H : tor hσ 1 t0K ∈ ⨆ i, hHat σ i :=
    Subgroup.mem_iSup_of_mem (ng 1) (d4z_tor_one_mem_hHat hσ t0K)
  have h2L : tor hσ 1 t0K ∈ longSub 6 (hexGroup (twistedX σ)) := by
    rw [tor_one_eq_slShort hσ (t0K : Kˣ)]
    simpa [t0K] using slShort_HSL_fixed_mem_longSub hσ t0
  have hc_h2 : tor hσ 1 t0K * c * (tor hσ 1 t0K)⁻¹ = c := by
    have h := Subgroup.mem_centralizer_iff.1 hc _ h2L
    calc tor hσ 1 t0K * c * (tor hσ 1 t0K)⁻¹ =
        c * tor hσ 1 t0K * (tor hσ 1 t0K)⁻¹ := by rw [h]
      _ = c := by group
  have h2n : tor hσ 1 t0K * n * (tor hσ 1 t0K)⁻¹ = n := by
    have h := (commute_of_mem_iSup_hHat hσ h2H hnH).eq
    rw [h]
    group
  set w3 := v * (n * u * n⁻¹) with hw3
  have hnu3 : n * u * n⁻¹ ∈ hexGroup (twistedX σ) 3 :=
    (d4RGD2 σ hσ).invariant 3 (isRoot_of_pos_le (by norm_num) (by norm_num))
      n hnH u hu3
  have hw3root3 : w3 ∈ hexGroup (twistedX σ) 3 :=
    (hexGroup (twistedX σ) 3).mul_mem hv3 hnu3
  have hc_eq : c = w3 * n := by
    rw [hcvu, hw3]
    group
  have hw3fix : tor hσ 1 t0K * w3 * (tor hσ 1 t0K)⁻¹ = w3 := by
    calc tor hσ 1 t0K * w3 * (tor hσ 1 t0K)⁻¹ =
        tor hσ 1 t0K * (c * n⁻¹) * (tor hσ 1 t0K)⁻¹ := by rw [hc_eq]; group
      _ = (tor hσ 1 t0K * c * (tor hσ 1 t0K)⁻¹) *
          (tor hσ 1 t0K * n * (tor hσ 1 t0K)⁻¹)⁻¹ := by group
      _ = c * n⁻¹ := by rw [hc_h2, h2n]
      _ = w3 := by rw [hc_eq]; group
  have hw3eq1 : w3 = 1 :=
    tor_one_fix_root_three hσ t0K ht0K hw3root3 hw3fix
  rw [hc_eq, hw3eq1, one_mul]
  exact hnH

include hσ in
theorem centralizerLongSubInN_holds_aux {q : ℕ} (hq : 5 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q)
    (s : fixedUnits σ) (hs1 : ((s : Kˣ) : K) ≠ 1)
    (hs2 : (((s : Kˣ) : K)) ^ 2 ≠ 1)
    (t0 : (fixedField σ)ˣ) (ht0 : (t0 : fixedField σ) ≠ 1) :
    CentralizerLongSubInN σ hσ := by
  intro c hc
  obtain ⟨v, n, u, hv3, hu3, hnH, hcvu⟩ :=
    centralizerLongSub_cell hσ hq hK hσq s hs1 hs2 hc
  have hcH := centralizerLongSub_eq_H hσ t0 ht0 hc hv3 hu3 hnH hcvu
  exact RGD2.H_le_N (d4RGD2 σ hσ) hcH

include hσ in
theorem exists_fixedUnits_regular {q : ℕ} (hq : 5 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) :
    ∃ s : fixedUnits σ, ((s : Kˣ) : K) ≠ 1 ∧ (((s : Kˣ) : K)) ^ 2 ≠ 1 := by
  have hF : Nat.card (fixedField σ) = q := card_fixedField_of_cube σ (by omega) hK hσq
  have hcard : Nat.card (fixedUnits σ) = q - 1 := a2tc_card_fixedUnits hF
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := fixedUnits σ)
  have hgcard : orderOf g = q - 1 := by rw [hg, hcard]
  refine ⟨g, ?_, ?_⟩
  · intro h
    have h1 : g = 1 := Subtype.ext (Units.ext h)
    rw [h1, orderOf_one] at hgcard
    omega
  · intro h
    have h2 : g ^ 2 = 1 := Subtype.ext (Units.ext (by simpa using h))
    have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [hgcard] at hdvd
    have hle : q - 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega

include hσ in
theorem exists_fixedField_unit_ne_one {q : ℕ} (hq : 5 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) :
    ∃ t0 : (fixedField σ)ˣ, (t0 : fixedField σ) ≠ 1 := by
  have hF : Nat.card (fixedField σ) = q := card_fixedField_of_cube σ (by omega) hK hσq
  have hcardU : Nat.card (fixedField σ)ˣ = q - 1 := by
    rw [Nat.card_units, hF]
  obtain ⟨t0, ht0⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (fixedField σ)ˣ)
  have ht0card : orderOf t0 = q - 1 := by rw [ht0, hcardU]
  refine ⟨t0, ?_⟩
  intro h
  have h1 : t0 = 1 := Units.ext h
  rw [h1, orderOf_one] at ht0card
  omega

include hσ in
theorem centralizerLongSubInN_holds {q : ℕ} (hq : 5 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) :
    CentralizerLongSubInN σ hσ := by
  obtain ⟨s, hs1, hs2⟩ := exists_fixedUnits_regular hσ hq hK hσq
  obtain ⟨t0, ht0⟩ := exists_fixedField_unit_ne_one hσ hq hK hσq
  exact centralizerLongSubInN_holds_aux hσ hq hK hσq s hs1 hs2 t0 ht0

include hσ in
theorem centralizer_longSub_le_H {q : ℕ} (hq : 5 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) :
    Subgroup.centralizer (longSub 6 (hexGroup (twistedX σ)) : Set (twistedGroup σ)) ≤
      ⨆ i, hHat σ i := by
  have hN := centralizerLongSubInN_holds hσ hq hK hσq
  intro c hc
  have hcN : c ∈ (d4RGD2 σ hσ).N := hN hc
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ hexGroup (twistedX σ) 2, x ≠ 1 := by
    have hne : hexGroup (twistedX σ) 2 ≠ ⊥ :=
      (d4RGD2 σ hσ).ne_bot 2 ⟨by norm_num, by norm_num⟩
    obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    exact ⟨y, hy, fun h => hy1 (Subtype.ext h)⟩
  obtain ⟨x', hx', hx'1⟩ : ∃ x' ∈ hexGroup (twistedX σ) 6, x' ≠ 1 := by
    have hne : hexGroup (twistedX σ) 6 ≠ ⊥ :=
      (d4RGD2 σ hσ).ne_bot 6 ⟨by norm_num, by norm_num⟩
    obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    exact ⟨y, hy, fun h => hy1 (Subtype.ext h)⟩
  have hxL : x ∈ longSub 6 (hexGroup (twistedX σ)) :=
    root_le_longSub (⟨by norm_num, by norm_num⟩ : CFSG.GH74.BNPair.IsRoot 6 2)
      (by norm_num) hx
  have hx'L : x' ∈ longSub 6 (hexGroup (twistedX σ)) :=
    root_le_longSub (⟨by norm_num, by norm_num⟩ : CFSG.GH74.BNPair.IsRoot 6 6)
      (by norm_num) hx'
  have hcx : c * x * c⁻¹ = x := by
    have h := (Subgroup.mem_centralizer_iff.1 hc x hxL).symm
    calc c * x * c⁻¹ = x * c * c⁻¹ := by rw [h]
      _ = x := by group
  have hcx' : c * x' * c⁻¹ = x' := by
    have h := (Subgroup.mem_centralizer_iff.1 hc x' hx'L).symm
    calc c * x' * c⁻¹ = x' * c * c⁻¹ := by rw [h]
      _ = x' := by group
  exact RGD2.mem_H_of_fixes_two (d4RGD2 σ hσ) hcN hx hx1 hx' hx'1 hcx hcx'

include hσ in
theorem centralizer_longSub {q : ℕ} (hq : 5 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) :
    ∀ z ∈ Subgroup.centralizer (longSub 6 (hexGroup (twistedX σ)) : Set (twistedGroup σ)),
      ∃ t : Kˣ, (t : K) * σ t * σ (σ t) = 1 ∧ z = slShort σ hσ (HSL t) := by
  intro z hz
  have hzH := centralizer_longSub_le_H hσ hq hK hσq hz
  have hzL : ∀ l ∈ longSub 6 (hexGroup (twistedX σ)), z * l = l * z := by
    intro l hl
    exact (Subgroup.mem_centralizer_iff.1 hz l hl).symm
  exact eq_slShort_of_mem_iSup_hHat_centralizer hσ hzH hzL

include hσ in
theorem centralizer_longSub_le_range {q : ℕ} (hq : 5 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσq : ∀ c, σ c = c ^ q) :
    Subgroup.centralizer (longSub 6 (hexGroup (twistedX σ)) : Set (twistedGroup σ)) ≤
      (slShort σ hσ).range := by
  intro z hz
  obtain ⟨t, -, rfl⟩ := centralizer_longSub hσ hq hK hσq z hz
  exact ⟨HSL t, rfl⟩


end FiniteField

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.CentL
