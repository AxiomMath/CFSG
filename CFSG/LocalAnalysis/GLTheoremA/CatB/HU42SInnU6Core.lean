module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SInnU6Glk
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SInnU6Count
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SRankSU

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.InnU6

open CFSG.LocalAnalysis.GLTheoremA.CatB Module Matrix CFSG.Open

theorem card_units_end (V : Type) [AddCommGroup V] [Module K4 V] [FiniteDimensional K4 V] :
    Nat.card (LinearMap.GeneralLinearGroup K4 V) =
      ∏ i : Fin (Module.finrank K4 V), (4 ^ Module.finrank K4 V - 4 ^ (i : ℕ)) := by
  classical
  letI : Fintype K4 := Fintype.ofFinite K4
  have h4 : Fintype.card K4 = 4 := by
    rw [Fintype.card_eq_nat_card]
    exact K4_card
  rw [← Nat.card_congr (Matrix.GeneralLinearGroup.toLin' (Module.finBasis K4 V)).toEquiv,
    Matrix.card_GL_field, h4]

theorem rhoG_fixSub_normal {H : Subgroup ↥(StatedSU 6 (2 ^ 1) K4)} {p : ↥(StatedSU 6 (2 ^ 1) K4)}
    (hp : ∀ t ∈ H, p⁻¹ * t * p ∈ H) {c : Fin 6 → K4} (hc : c ∈ fixSub H) :
    rhoG p c ∈ fixSub H := by
  rw [mem_fixSub] at hc ⊢
  intro t ht
  have h1 : rhoG (p⁻¹ * t * p) c = c := hc _ (hp t ht)
  have h2 : t * p = p * (p⁻¹ * t * p) := by group
  calc rhoG t (rhoG p c) = rhoG (t * p) c := by rw [map_mul, Module.End.mul_apply]
    _ = rhoG (p * (p⁻¹ * t * p)) c := by rw [h2]
    _ = rhoG p (rhoG (p⁻¹ * t * p) c) := by rw [map_mul, Module.End.mul_apply]
    _ = rhoG p c := by rw [h1]

theorem rhoG_perp_fixSub_mem {H : Subgroup ↥(StatedSU 6 (2 ^ 1) K4)}
    {g : ↥(StatedSU 6 (2 ^ 1) K4)} (hg : g ∈ H) {y : Fin 6 → K4} (hy : y ∈ perp (fixSub H)) :
    rhoG g y ∈ perp (fixSub H) := by
  rw [mem_perp] at hy ⊢
  intro c hc
  have hgc : rhoG g c = c := (mem_fixSub.1 hc) g hg
  calc hermF c (rhoG g y) = hermF (rhoG g c) (rhoG g y) := by rw [hgc]
    _ = hermF c y := rhoG_herm g c y
    _ = 0 := hy c hc

theorem rhoG_perp_fixSub_normal {H : Subgroup ↥(StatedSU 6 (2 ^ 1) K4)}
    {p : ↥(StatedSU 6 (2 ^ 1) K4)} (hN : ∀ t ∈ H, p * t * p⁻¹ ∈ H) {y : Fin 6 → K4}
    (hy : y ∈ perp (fixSub H)) : rhoG p y ∈ perp (fixSub H) := by
  rw [mem_perp] at hy ⊢
  intro c hc
  have hc' : rhoG p⁻¹ c ∈ fixSub H := by
    apply rhoG_fixSub_normal (p := p⁻¹) _ hc
    intro t ht
    rw [inv_inv]
    exact hN t ht
  have hcc : rhoG p (rhoG p⁻¹ c) = c := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  calc hermF c (rhoG p y) = hermF (rhoG p (rhoG p⁻¹ c)) (rhoG p y) := by rw [hcc]
    _ = hermF (rhoG p⁻¹ c) y := rhoG_herm p (rhoG p⁻¹ c) y
    _ = 0 := hy _ hc'

@[expose] noncomputable def stabHom (P : Subgroup ↥(StatedSU 6 (2 ^ 1) K4))
    (R : Submodule K4 (Fin 6 → K4)) (hR : ∀ p ∈ P, ∀ r ∈ R, rhoG p r ∈ R) :
    P →* LinearMap.GeneralLinearGroup K4 R where
  toFun p :=
    { val := (rhoG p.1).restrict (hR p.1 p.2)
      inv := (rhoG p.1⁻¹).restrict (hR p.1⁻¹ (P.inv_mem p.2))
      val_inv := by
        apply LinearMap.ext
        intro r
        apply Subtype.ext
        simp only [Module.End.mul_apply, LinearMap.restrict_apply, Module.End.one_apply]
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      inv_val := by
        apply LinearMap.ext
        intro r
        apply Subtype.ext
        simp only [Module.End.mul_apply, LinearMap.restrict_apply, Module.End.one_apply]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  map_one' := by
    apply Units.ext
    apply LinearMap.ext
    intro r
    apply Subtype.ext
    simp
  map_mul' p q := by
    apply Units.ext
    apply LinearMap.ext
    intro r
    apply Subtype.ext
    simp [map_mul, Module.End.mul_apply]

theorem stabHom_apply_val (P : Subgroup ↥(StatedSU 6 (2 ^ 1) K4)) (R : Submodule K4 (Fin 6 → K4))
    (hR : ∀ p ∈ P, ∀ r ∈ R, rhoG p r ∈ R) (p : P) (r : R) :
    (((stabHom P R hR p : LinearMap.GeneralLinearGroup K4 R) : Module.End K4 R) r : Fin 6 → K4) =
      rhoG p.1 r.1 := rfl

theorem exists_fixed_of_two_group {H : Subgroup ↥(StatedSU 6 (2 ^ 1) K4)} (hH : IsPGroup 2 H)
    (W : Submodule K4 (Fin 6 → K4)) (hW : ∀ h ∈ H, ∀ w ∈ W, rhoG h w ∈ W) (hne : W ≠ ⊥) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ h ∈ H, rhoG h w = w := by
  let τ : H →* Module.End (ZMod 2) (Fin 6 → K4) :=
    { toFun := fun h => (rhoG h.1).restrictScalars (ZMod 2)
      map_one' := by
        apply LinearMap.ext
        intro v
        simp
      map_mul' := fun a b => by
        apply LinearMap.ext
        intro v
        simp [map_mul, Module.End.mul_apply] }
  have hW2 : ∀ h : H, ∀ w ∈ W.restrictScalars (ZMod 2),
      τ h w ∈ W.restrictScalars (ZMod 2) := by
    intro h w hw
    rw [Submodule.restrictScalars_mem] at hw ⊢
    exact hW h.1 h.2 w hw
  have hne2 : W.restrictScalars (ZMod 2) ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro w hw
    have : w ∈ W.restrictScalars (ZMod 2) := (Submodule.restrictScalars_mem _ _ _).2 hw
    rw [h] at this
    exact (Submodule.mem_bot _).1 this
  obtain ⟨w, hw, hw0, hfix⟩ :=
    Rank3.exists_fixed_vector hH τ (W.restrictScalars (ZMod 2)) hW2 hne2
  refine ⟨w, (Submodule.restrictScalars_mem _ _ _).1 hw, hw0, fun h hh => ?_⟩
  exact hfix ⟨h, hh⟩

theorem core_false (P T₀ Z : Subgroup ↥(StatedSU 6 (2 ^ 1) K4))
    (hPcard : Nat.card P = 243)
    (hZ : ∀ z ∈ Z, ∃ c : K4, (∀ v, rhoG z v = c • v) ∧ (c = 1 → z = 1))
    (hcube : ∀ x ∈ P, x ^ 3 ∈ Z)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Z)
    (hT₀ : IsPGroup 2 T₀) (hT₀ne : T₀ ≠ ⊥)
    (hN : ∀ p ∈ P, ∀ t ∈ T₀, p * t * p⁻¹ ∈ T₀) : False := by
  classical
  haveI : Finite ↥(StatedSU 6 (2 ^ 1) K4) := HU42S.finite_SU K4
  set C : Submodule K4 (Fin 6 → K4) := fixSub T₀ with hCdef
  set R : Submodule K4 (Fin 6 → K4) := C ⊓ perp C with hRdef
  have hRne : R ≠ ⊥ := by
    intro hR0
    have hdim := finrank_perp_add C
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq C (perp C)
    rw [← hRdef, hR0, finrank_bot, add_zero] at hsum
    have hfull : C ⊔ perp C = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]
      omega
    have hD0 : perp C = ⊥ := by
      by_contra hD
      obtain ⟨w, hwD, hw0, hwfix⟩ := exists_fixed_of_two_group hT₀ (perp C)
        (fun h hh w hw => rhoG_perp_fixSub_mem hh hw) hD
      have hwC : w ∈ C := mem_fixSub.2 hwfix
      have hwR : w ∈ R := Submodule.mem_inf.2 ⟨hwC, hwD⟩
      rw [hR0, Submodule.mem_bot] at hwR
      exact hw0 hwR
    have hCtop : C = ⊤ := by
      rw [hD0, sup_bot_eq] at hfull
      exact hfull
    apply hT₀ne
    rw [eq_bot_iff]
    intro t _
    rw [Subgroup.mem_bot]
    apply rhoG_injective
    rw [map_one]
    apply LinearMap.ext
    intro v
    rw [Module.End.one_apply]
    have hv : v ∈ C := by
      rw [hCtop]
      exact Submodule.mem_top
    exact (mem_fixSub.1 hv) t ‹t ∈ T₀›
  have hRinv : ∀ p ∈ P, ∀ r ∈ R, rhoG p r ∈ R := by
    intro p hp r hr
    have hp' : ∀ t ∈ T₀, p⁻¹ * t * p ∈ T₀ := fun t ht => by
      simpa using hN p⁻¹ (P.inv_mem hp) t ht
    exact Submodule.mem_inf.2 ⟨rhoG_fixSub_normal hp' (Submodule.mem_inf.1 hr).1,
      rhoG_perp_fixSub_normal (hN p hp) (Submodule.mem_inf.1 hr).2⟩
  set ψ := stabHom P R hRinv with hψdef
  have hψfix : ∀ q : P, ψ q = 1 → ∀ r ∈ R, rhoG q.1 r = r := by
    intro q hq r hr
    have h := congrArg (fun u : LinearMap.GeneralLinearGroup K4 R =>
      ((u : Module.End K4 R) ⟨r, hr⟩ : Fin 6 → K4)) hq
    simp only [hψdef, stabHom_apply_val, Units.val_one, Module.End.one_apply] at h
    exact h
  have hψrev : ∀ q : P, (∀ r ∈ R, rhoG q.1 r = r) → ψ q = 1 := by
    intro q hq
    apply Units.ext
    apply LinearMap.ext
    intro r
    apply Subtype.ext
    simp only [hψdef, Units.val_one, Module.End.one_apply]
    rw [stabHom_apply_val]
    exact hq r.1 r.2
  have hZS : ∀ x : P, (x : ↥(StatedSU 6 (2 ^ 1) K4)) ∈ Z → ψ x = 1 → x = 1 := by
    intro x hxZ hx1
    obtain ⟨c, hcsc, hc1⟩ := hZ x.1 hxZ
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hRne
    have h2 : c • r = r := by
      rw [← hcsc r]
      exact hψfix x hx1 r hr
    have h1 : (c - 1) • r = 0 := by
      rw [sub_smul, one_smul, h2, sub_self]
    have hc : c = 1 := by
      rcases smul_eq_zero.1 h1 with h | h
      · exact sub_eq_zero.1 h
      · exact absurd h hr0
    exact Subtype.ext (by simpa using hc1 hc)
  have hcommS : ∀ q q' : ψ.ker, q * q' = q' * q := by
    intro q q'
    have hq : ψ q.1 = 1 := MonoidHom.mem_ker.1 q.2
    have hq' : ψ q'.1 = 1 := MonoidHom.mem_ker.1 q'.2
    have hcZ : ((q.1 * q'.1 * q.1⁻¹ * q'.1⁻¹ : P) : ↥(StatedSU 6 (2 ^ 1) K4)) ∈ Z := by
      have := hcomm q.1.1 q.1.2 q'.1.1 q'.1.2
      simpa using this
    have hc1 : ψ (q.1 * q'.1 * q.1⁻¹ * q'.1⁻¹) = 1 := by
      simp [hq, hq']
    have hc := hZS _ hcZ hc1
    have hcomm' : q.1 * q'.1 = q'.1 * q.1 := by
      have h0 : q.1 * q'.1 * q.1⁻¹ * q'.1⁻¹ = 1 := hc
      calc q.1 * q'.1 = (q.1 * q'.1 * q.1⁻¹ * q'.1⁻¹) * (q'.1 * q.1) := by group
        _ = q'.1 * q.1 := by rw [h0, one_mul]
    exact Subtype.ext hcomm'
  have hpowS : ∀ q : ψ.ker, q.1 ^ 3 = 1 := by
    intro q
    have hq3 : ψ (q.1 ^ 3) = 1 := by
      rw [map_pow, MonoidHom.mem_ker.1 q.2, one_pow]
    apply hZS (q.1 ^ 3) _ hq3
    have := hcube q.1.1 q.1.2
    simpa using this
  have hcard : Nat.card ψ.ker ≤ 3 ^ (5 - 2 * Module.finrank K4 R) := by
    apply card_le_of_fixes_isotropic (Q := ψ.ker) (fun q => rhoG q.1.1)
    · intro q q' h
      exact Subtype.ext (Subtype.ext (rhoG_injective h))
    · intro q q'
      show rhoG q.1.1 * rhoG q'.1.1 = rhoG q'.1.1 * rhoG q.1.1
      have h := congrArg (fun x : ψ.ker => ((x.1 : P) : ↥(StatedSU 6 (2 ^ 1) K4)))
        (hcommS q q')
      simp only [Subgroup.coe_mul] at h
      rw [← map_mul, ← map_mul, h]
    · intro q
      have h : q.1.1 ^ 3 = 1 := by
        have h' := congrArg Subtype.val (hpowS q)
        simpa using h'
      rw [← map_pow, h, map_one]
    · intro q x y
      exact rhoG_herm _ x y
    · intro q
      exact rhoG_det _
    · intro q r hr
      exact hψfix q.1 (MonoidHom.mem_ker.1 q.2) r hr
    · intro r hr r' hr'
      exact (mem_perp.1 (Submodule.mem_inf.1 hr').2) r (Submodule.mem_inf.1 hr).1
  have hd1 : 1 ≤ Module.finrank K4 R :=
    Nat.pos_of_ne_zero (fun h => hRne (Submodule.finrank_eq_zero.1 h))
  have hd3 : Module.finrank K4 R ≤ 3 := by
    have hle : R ≤ perp R := fun r hr => mem_perp.2 fun w hw =>
      (mem_perp.1 (Submodule.mem_inf.1 hr).2) w (Submodule.mem_inf.1 hw).1
    have h1 := Submodule.finrank_mono hle
    have h2 := finrank_perp_add R
    omega
  have hsplit := Subgroup.card_ker_mul_card_range ψ
  have hdvd : Nat.card ψ.range ∣ Nat.card (LinearMap.GeneralLinearGroup K4 R) :=
    Subgroup.card_subgroup_dvd_card _
  rw [card_units_end R] at hdvd
  rw [hPcard] at hsplit
  generalize hdef : Module.finrank K4 R = d at hcard hdvd hd1 hd3
  generalize hs : Nat.card ψ.ker = s at hcard hsplit
  generalize hr : Nat.card ψ.range = r at hdvd hsplit
  have hrdvd : r ∣ 243 := Dvd.intro_left s hsplit
  interval_cases d
  · norm_num [Fin.prod_univ_one] at hdvd hcard
    have hr3 : r ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    have : s * r ≤ 27 * 3 := Nat.mul_le_mul hcard hr3
    linarith
  · norm_num [Fin.prod_univ_two] at hdvd hcard
    have hg := Nat.dvd_gcd hdvd hrdvd
    norm_num at hg
    have hr9 : r ≤ 9 := Nat.le_of_dvd (by norm_num) hg
    have : s * r ≤ 3 * 9 := Nat.mul_le_mul hcard hr9
    linarith
  · norm_num [Fin.prod_univ_three] at hdvd hcard
    have hg := Nat.dvd_gcd hdvd hrdvd
    norm_num at hg
    have hr81 : r ≤ 81 := Nat.le_of_dvd (by norm_num) hg
    have : s * r ≤ 1 * 81 := Nat.mul_le_mul hcard hr81
    linarith

end CFSG.LocalAnalysis.GLTheoremA.CatB.InnU6

end
