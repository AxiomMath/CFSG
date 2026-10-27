module

public import CFSG.LargeExtraspecial.S2OrthB1
public import CFSG.LargeExtraspecial.S2Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81.PointIrr

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
open CFSG.LargeExtraspecial.OrthoF2 CFSG.LargeExtraspecial.S2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_mem_orthogonalGroup)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

theorem mem_of_singular_le (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ perp q F = ⊥) (h3 : 3 ≤ finrank (ZMod 2) (perp q F)) {W : Submodule (ZMod 2) V}
    (hW : ∀ s ∈ perp q F, q s = 0 → s ∈ W) {x : V} (hx : x ∈ perp q F) : x ∈ W := by
  obtain ⟨p₀, hp₀F, hp₀0, hp₀⟩ := exists_singular_mem_perp (q := q) (F := F) h3
  obtain ⟨p₁, hp₁F, hp₁, hpp₁⟩ := exists_hyperbolic_partner hq hF hp₀F hp₀0 hp₀
  have hx₀ := sub_mem_perp_sup_span_pair hp₀F hp₁F hpp₁ hx
  set x₀ := x - polar q x p₁ • p₀ - polar q x p₀ • p₁ with hx₀def
  obtain ⟨hx₀F, hp₀x₀, hp₁x₀⟩ := mem_perp_sup_span_pair.mp hx₀
  have hx' : x = x₀ + polar q x p₁ • p₀ + polar q x p₀ • p₁ := by
    rw [hx₀def]
    abel
  have hx₀W : x₀ ∈ W := by
    rcases zmod2_eq_zero_or_eq_one (q x₀) with h | h
    · exact hW x₀ hx₀F h
    · have hs : q (x₀ + p₀ + p₁) = 0 := by
        rw [map_add_eq, map_add_eq, h, hp₀, hp₁, polar_add_left, polar_comm, hp₀x₀,
          polar_comm q x₀ p₁, hp₁x₀, hpp₁]
        decide
      have h1 := hW _ (Submodule.add_mem _ (Submodule.add_mem _ hx₀F hp₀F) hp₁F) hs
      have h2 := Submodule.sub_mem _ (Submodule.sub_mem _ h1 (hW p₀ hp₀F hp₀)) (hW p₁ hp₁F hp₁)
      have e : x₀ + p₀ + p₁ - p₀ - p₁ = x₀ := by abel
      rwa [e] at h2
  rw [hx']
  exact Submodule.add_mem _ (Submodule.add_mem _ hx₀W (Submodule.smul_mem _ _ (hW p₀ hp₀F hp₀)))
    (Submodule.smul_mem _ _ (hW p₁ hp₁F hp₁))

theorem eq_perp_of_invariant (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ perp q F = ⊥) (h6 : 6 ≤ finrank (ZMod 2) (perp q F)) {W : Submodule (ZMod 2) V}
    (hWF : W ≤ perp q F) (hW : W ≠ ⊥) (hinv : ∀ g ∈ omegaFix q hq F, ∀ w ∈ W, g w ∈ W) :
    W = perp q F := by
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hwF : w ∈ perp q F := hWF hwW
  have hsing : ∃ s ∈ W, s ≠ 0 ∧ q s = 0 := by
    rcases zmod2_eq_zero_or_eq_one (q w) with hqw | hqw
    · exact ⟨w, hwW, hw0, hqw⟩
    obtain ⟨p, hpF, hp, hwp⟩ : ∃ p ∈ perp q F, q p = 0 ∧ polar q w p = 1 := by
      by_contra hcon
      push Not at hcon
      have hall : ∀ x ∈ perp q F, polar q w x = 0 := by
        intro x hx
        have h1 := mem_of_singular_le hq hF (by omega)
          (W := LinearMap.ker ((polarBilin q) w)) (fun s hs hqs => by
            rcases zmod2_eq_zero_or_eq_one (polar q w s) with h | h
            · exact h
            · exact absurd h (hcon s hs hqs)) hx
        exact h1
      apply hw0
      have hwFF : w ∈ F ⊓ perp q F := by
        refine ⟨?_, hwF⟩
        have h1 : w ∈ perp q (perp q F) := mem_perp.mpr fun x hx => by
          rw [polar_comm]
          exact hall x hx
        have h2 : w ∈ LinearMap.BilinForm.orthogonal (polarBilin q)
            (LinearMap.BilinForm.orthogonal (polarBilin q) F) := h1
        rwa [LinearMap.BilinForm.orthogonal_orthogonal hq (isRefl_polarBilin q)] at h2
      rw [hF] at hwFF
      exact hwFF
    have hwp' : polar q p w = 1 := by rw [polar_comm]; exact hwp
    have hdim := finrank_perp_sup_span_pair hq hF hpF hwF hwp'
    obtain ⟨u, huF, hu0, hu⟩ := exists_singular_mem_perp (q := q)
      (F := F ⊔ Submodule.span (ZMod 2) {p, w}) (by omega)
    obtain ⟨huF', hpu, hwu⟩ := mem_perp_sup_span_pair.mp huF
    have hp0 : p ≠ 0 := by
      rintro rfl
      rw [polar_zero_right] at hwp
      exact zero_ne_one hwp
    have ht : eichler q p u ∈ omegaFix q hq F :=
      radFix_le_omegaFix hq hp0 hp ((mem_radFix_iff hq hp0 hp hpF).mpr ⟨u, huF', hpu, rfl⟩)
    have h1 := hinv _ ht w hwW
    rw [eichler_apply_zmod2 hp hpu, hwp, one_smul, hwu, zero_add, mul_one, hu, zero_smul,
      add_zero] at h1
    refine ⟨u, ?_, hu0, hu⟩
    have h2 := Submodule.sub_mem _ h1 hwW
    rwa [add_sub_cancel_left] at h2
  obtain ⟨s₀, hs₀W, hs₀0, hs₀⟩ := hsing
  have hall : ∀ s ∈ perp q F, q s = 0 → s ∈ W := by
    intro s hsF hs
    by_cases hs0 : s = 0
    · rw [hs0]
      exact W.zero_mem
    obtain ⟨g, hg, hgs⟩ :=
      exists_mem_radGen_apply_eq hq hF (by omega) (hWF hs₀W) hsF hs₀0 hs0 hs₀ hs
    rw [← hgs]
    exact hinv g (radGen_le_omegaFix hq F hg) s₀ hs₀W
  exact le_antisymm hWF fun x hx => mem_of_singular_le hq hF (by omega) hall hx

theorem le_pointRadical_of_isPGroup (hq : q.polarBilin.Nondegenerate)
    (h8 : 8 ≤ finrank (ZMod 2) V) {a b : V} (hab : polar q a b = 1)
    {P : Subgroup (V ≃ₗ[ZMod 2] V)} (hP2 : IsPGroup 2 P)
    (hPO : P ≤ orthogonalGroup q) (hPa : ∀ g ∈ P, g a = a)
    (hPn : ∀ y ∈ omegaFix q hq (Submodule.span (ZMod 2) {a, b}), ∀ g ∈ P, y * g * y⁻¹ ∈ P) :
    P ≤ pointRadical q a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := Submodule.span (ZMod 2) {a, b} with hFdef
  have hF : F ⊓ perp q F = ⊥ := by
    have h := sup_span_pair_inf_perp_eq_bot (q := q) (F := ⊥) (bot_inf_eq _)
      (by rw [perp_bot]; exact Submodule.mem_top) (by rw [perp_bot]; exact Submodule.mem_top) hab
    rwa [bot_sup_eq] at h
  have hdim : 6 ≤ finrank (ZMod 2) (perp q F) := by
    have h := finrank_perp_sup_span_pair hq (F := ⊥) (bot_inf_eq _)
      (by rw [perp_bot]; exact Submodule.mem_top) (by rw [perp_bot]; exact Submodule.mem_top) hab
    rw [bot_sup_eq, perp_bot, finrank_top, ← hFdef] at h
    omega
  have hmemF : ∀ v ∈ perp q F, polar q a v = 0 ∧ polar q b v = 0 := fun v hv =>
    ⟨(mem_perp.mp hv) a (Submodule.subset_span (by simp)),
      (mem_perp.mp hv) b (Submodule.subset_span (by simp))⟩
  have hproj : ∀ w, polar q a w = 0 → w - polar q w b • a ∈ perp q F := by
    intro w hw
    refine mem_perp.mpr fun y hy => ?_
    obtain ⟨c, d, rfl⟩ : ∃ c d : ZMod 2, c • a + d • b = y := by
      rcases Submodule.mem_span_pair.mp hy with ⟨c, d, h⟩
      exact ⟨c, d, h⟩
    rw [polar_add_left, polar_smul_left, polar_smul_left, polar_sub_right, polar_sub_right,
      polar_smul_right, polar_smul_right, hw, polar_self_eq_zero, polar_comm q b w,
      polar_comm q b a, hab]
    simp
  have hga : ∀ g ∈ P, ∀ v, polar q a v = 0 → polar q a (g v) = 0 := by
    intro g hg v hv
    rw [← hPa g hg, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hPO hg), hv]
  let act : ↥P → ↥(perp q F) → ↥(perp q F) := fun g v =>
    ⟨(g : V ≃ₗ[ZMod 2] V) v - polar q ((g : V ≃ₗ[ZMod 2] V) v) b • a,
      hproj _ (hga g g.2 v (hmemF v v.2).1)⟩
  have hact_one : ∀ v, act 1 v = v := fun v => by
    apply Subtype.ext
    show (v : V) - polar q (v : V) b • a = v
    rw [polar_comm, (hmemF v v.2).2, zero_smul, sub_zero]
  have hact_mul : ∀ g h v, act (g * h) v = act g (act h v) := by
    intro g h v
    apply Subtype.ext
    show ((g : V ≃ₗ[ZMod 2] V) * h) v - polar q (((g : V ≃ₗ[ZMod 2] V) * h) v) b • a =
      (g : V ≃ₗ[ZMod 2] V) ((h : V ≃ₗ[ZMod 2] V) v - polar q ((h : V ≃ₗ[ZMod 2] V) v) b • a) -
        polar q ((g : V ≃ₗ[ZMod 2] V) ((h : V ≃ₗ[ZMod 2] V) v -
          polar q ((h : V ≃ₗ[ZMod 2] V) v) b • a)) b • a
    rw [map_sub, map_smul, hPa g g.2, LinearEquiv.mul_apply, polar_sub_left, polar_smul_left,
      hab]
    simp only [smul_eq_mul, mul_one, sub_smul]
    abel
  have : Finite V := Module.finite_of_finite (ZMod 2)
  let _ : MulAction ↥P ↥(perp q F) :=
    { smul := act
      one_smul := hact_one
      mul_smul := hact_mul }
  have hmod := hP2.card_modEq_card_fixedPoints ↥(perp q F)
  have hcardF : 2 ∣ Nat.card ↥(perp q F) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact dvd_pow_self 2 (by omega)
  have h0fix : (0 : ↥(perp q F)) ∈ MulAction.fixedPoints ↥P ↥(perp q F) := fun g => by
    apply Subtype.ext
    show (g : V ≃ₗ[ZMod 2] V) 0 - polar q ((g : V ≃ₗ[ZMod 2] V) 0) b • a = 0
    simp
  obtain ⟨v₀, hv₀fix, hv₀0⟩ : ∃ v₀ ∈ MulAction.fixedPoints ↥P ↥(perp q F), v₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hsub : MulAction.fixedPoints ↥P ↥(perp q F) = {0} := by
      ext v
      exact ⟨fun hv => hcon v hv, fun hv => by rw [Set.mem_singleton_iff.mp hv]; exact h0fix⟩
    have h1 : Nat.card (MulAction.fixedPoints ↥P ↥(perp q F)) = 1 := by
      rw [hsub, Nat.card_unique]
    rw [h1] at hmod
    have hpos : 1 ≤ Nat.card ↥(perp q F) := Nat.card_pos
    have h2 := (Nat.modEq_iff_dvd' hpos).mp hmod.symm
    have h3 := Nat.dvd_sub hcardF h2
    rw [Nat.sub_sub_self hpos] at h3
    norm_num at h3
  set W : Submodule (ZMod 2) V :=
    { carrier := {v | v ∈ perp q F ∧ ∀ g ∈ P, (g : V ≃ₗ[ZMod 2] V) v - v ∈ (ZMod 2) ∙ a}
      add_mem' := by
        rintro v w ⟨hv, hv'⟩ ⟨hw, hw'⟩
        refine ⟨Submodule.add_mem _ hv hw, fun g hg => ?_⟩
        have e : g (v + w) - (v + w) = (g v - v) + (g w - w) := by rw [map_add]; abel
        rw [e]
        exact Submodule.add_mem _ (hv' g hg) (hw' g hg)
      zero_mem' := ⟨Submodule.zero_mem _, fun g _ => by simp⟩
      smul_mem' := by
        rintro c v ⟨hv, hv'⟩
        refine ⟨Submodule.smul_mem _ _ hv, fun g hg => ?_⟩
        rw [map_smul, ← smul_sub]
        exact Submodule.smul_mem _ _ (hv' g hg) } with hWdef
  have hfixW : ∀ v : ↥(perp q F), v ∈ MulAction.fixedPoints ↥P ↥(perp q F) → (v : V) ∈ W := by
    intro v hv
    refine ⟨v.2, fun g hg => ?_⟩
    have h1 := congrArg Subtype.val (hv ⟨g, hg⟩)
    change (g : V ≃ₗ[ZMod 2] V) v - polar q ((g : V ≃ₗ[ZMod 2] V) v) b • a = v at h1
    have h2 : (g : V ≃ₗ[ZMod 2] V) v - v = polar q ((g : V ≃ₗ[ZMod 2] V) v) b • a := by
      calc (g : V ≃ₗ[ZMod 2] V) v - v = (g : V ≃ₗ[ZMod 2] V) v -
            ((g : V ≃ₗ[ZMod 2] V) v - polar q ((g : V ≃ₗ[ZMod 2] V) v) b • a) := by rw [h1]
        _ = polar q ((g : V ≃ₗ[ZMod 2] V) v) b • a := by abel
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
  have hWne : W ≠ ⊥ := by
    intro h
    have h1 := hfixW v₀ hv₀fix
    rw [h, Submodule.mem_bot] at h1
    exact hv₀0 (Subtype.ext h1)
  have hWinv : ∀ y ∈ omegaFix q hq F, ∀ w ∈ W, y w ∈ W := by
    intro y hy w ⟨hw, hw'⟩
    have hyO := mem_orthogonalGroup_of_mem_omegaFix hy
    have hya : y a = a := hy.2 a (Submodule.subset_span (by simp))
    refine ⟨apply_mem_perp hyO hy.2 hw, fun g hg => ?_⟩
    have hg' : y⁻¹ * g * y ∈ P := by
      have h1 := hPn y⁻¹ (inv_mem hy) g hg
      rwa [inv_inv] at h1
    have h1 := hw' _ hg'
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
    refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
    have hyy : ∀ x, y (y⁻¹ x) = x := fun x => by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    have e : g (y w) - y w = y ((y⁻¹ * g * y) w - w) := by
      rw [map_sub, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hyy]
    rw [e, ← hc, map_smul, hya]
  have hWF : W = perp q F := eq_perp_of_invariant hq hF hdim (fun w hw => hw.1) hWne hWinv
  intro g hg
  refine ⟨hPO hg, hPa g hg, fun x hx => ?_, fun v => ?_⟩
  · have hxF := hproj x hx
    have h1 : x - polar q x b • a ∈ W := by rw [hWF]; exact hxF
    have h2 := h1.2 g hg
    have e : g x - x = (g (x - polar q x b • a) - (x - polar q x b • a)) := by
      rw [map_sub, map_smul, hPa g hg]
      abel
    rw [e]
    exact h2
  · rw [polar_sub_right, ← hPa g hg,
      TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hPO hg), hPa g hg, sub_self]

end CFSG.ComponentClassification.AS81.PointIrr
