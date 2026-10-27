module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBInterfaces
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.StrWts

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6


section SL2

variable {F : Type*} [Field F]

theorem map_id_SL2 (g : SL2 F) : Matrix.SpecialLinearGroup.map (RingHom.id F) g = g :=
  Subtype.ext (by ext i j; rfl)

theorem HSL_conj_uSL (z : Fˣ) (c : F) : (HSL z : SL2 F) * uSL c * (HSL z)⁻¹ = uSL ((z : F) ^ 2 * c) := by
  have := slAut_uSL (RingEquiv.refl F) z c
  simpa [slAut, map_id_SL2] using this

theorem HSL_conj_vSL (z : Fˣ) (c : F) :
    (HSL z : SL2 F) * vSL c * (HSL z)⁻¹ = vSL (((z⁻¹ : Fˣ) : F) ^ 2 * c) := by
  have := slAut_vSL (RingEquiv.refl F) z c
  simpa [slAut, map_id_SL2] using this

end SL2

section Torus

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem conj_list_prod {M α : Type*} [Group M] (T : M) (l : List α) (g : α → M) :
    T * (l.map g).prod * T⁻¹ = (l.map fun a => T * g a * T⁻¹).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [← ih]
    group

theorem list_prod_zpow_neg {ι : Type*} (l : List ι) (x : ι → K) (n : ι → ℤ) :
    (l.map fun k => (x k) ^ (-n k)).prod = ((l.map fun k => (x k) ^ (n k)).prod)⁻¹ := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, mul_inv, zpow_neg]

theorem conj_prod_hm {ι : Type*} (l : List ι) (jf : ι → Fin TwistTag.E6.tag.rank) (tf : ι → Kˣ)
    (γ : Fin TwistTag.E6.tag.rank → ℤ) (ex : ι → ℤ)
    (h : ∀ k (c : K), e6Data_valid.hm K (jf k) (tf k) * e6Data_valid.xm K γ c *
        (e6Data_valid.hm K (jf k) (tf k))⁻¹ =
      e6Data_valid.xm K γ ((((tf k) ^ (ex k) : Kˣ) : K) * c)) (c : K) :
    (l.map fun k => e6Data_valid.hm K (jf k) (tf k)).prod * e6Data_valid.xm K γ c *
        ((l.map fun k => e6Data_valid.hm K (jf k) (tf k)).prod)⁻¹ =
      e6Data_valid.xm K γ (((l.map fun k => (((tf k) ^ (ex k) : Kˣ) : K)).prod) * c) := by
  induction l with
  | nil => simp
  | cons k l ih =>
    simp only [List.map_cons, List.prod_cons] at ih ⊢
    set P := (l.map fun k => e6Data_valid.hm K (jf k) (tf k)).prod
    have e : (e6Data_valid.hm K (jf k) (tf k) * P) * e6Data_valid.xm K γ c *
        (e6Data_valid.hm K (jf k) (tf k) * P)⁻¹ = e6Data_valid.hm K (jf k) (tf k) *
        (P * e6Data_valid.xm K γ c * P⁻¹) * (e6Data_valid.hm K (jf k) (tf k))⁻¹ := by group
    rw [e, ih, h, mul_assoc]

variable (σ : K →+* K)

@[expose] def Fv (b : TwN) (w : K) (i : Fin TwistTag.E6.tag.rank) : K :=
  ((List.range (TwistTag.E6.orbit b).card).map fun k =>
    ((σ ^ k) w) ^ (Tag.cartan Tag.E6 ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin b)) i)).prod

theorem Fv_one {b : TwN} (h : (TwistTag.E6.orbit b).card = 1) (w : K)
    (i : Fin TwistTag.E6.tag.rank) :
    Fv σ b w i = w ^ (Tag.cartan Tag.E6 (TwistTag.E6.orbitMin b) i) := by
  simp [Fv, h]

theorem Fv_two {b : TwN} (h : (TwistTag.E6.orbit b).card = 2) (w : K)
    (i : Fin TwistTag.E6.tag.rank) :
    Fv σ b w i = w ^ (Tag.cartan Tag.E6 (TwistTag.E6.orbitMin b) i) *
      (σ w) ^ (Tag.cartan Tag.E6 (TwistTag.E6.perm (TwistTag.E6.orbitMin b)) i) := by
  have hr : List.range 2 = [0, 1] := rfl
  simp [Fv, h, hr]

theorem rhatH_conj_xm (b : TwN) (w : (orbitField TwistTag.E6 K σ b)ˣ)
    (i : Fin TwistTag.E6.tag.rank) (c : K) :
    minOrbitHom σ b (HSL w) * e6Data_valid.xm K (Pi.single i 1) c *
        (minOrbitHom σ b (HSL w))⁻¹ =
      e6Data_valid.xm K (Pi.single i 1) (Fv σ b (w : K) i * c) := by
  rw [minOrbitHom_HSL]
  rw [conj_prod_hm _ _ _ _ (fun k => Tag.cartan Tag.E6 ((TwistTag.E6.perm ^ k)
    (TwistTag.E6.orbitMin b)) i) (fun k c => hm_conj_xr _ _ _ _) c]
  have hF : ((List.range (TwistTag.E6.orbit b).card).map fun k =>
      ((((Units.map ((σ ^ k).comp (orbitField TwistTag.E6 K σ b).subtype).toMonoidHom w) ^
        Tag.cartan Tag.E6 ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin b)) i : Kˣ)) : K)).prod =
      Fv σ b (w : K) i := by
    unfold Fv
    refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
    rw [Units.val_zpow_eq_zpow_val]
    rfl
  rw [hF]

theorem rhatH_conj_ym (b : TwN) (w : (orbitField TwistTag.E6 K σ b)ˣ)
    (i : Fin TwistTag.E6.tag.rank) (c : K) :
    minOrbitHom σ b (HSL w) * e6Data_valid.xm K (-Pi.single i 1) c *
        (minOrbitHom σ b (HSL w))⁻¹ =
      e6Data_valid.xm K (-Pi.single i 1) ((Fv σ b (w : K) i)⁻¹ * c) := by
  rw [minOrbitHom_HSL]
  rw [conj_prod_hm (List.range (TwistTag.E6.orbit b).card)
    (fun k => (TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin b))
    (fun k => Units.map ((σ ^ k).comp (orbitField TwistTag.E6 K σ b).subtype).toMonoidHom w)
    (-Pi.single i 1) (fun k => -Tag.cartan Tag.E6 ((TwistTag.E6.perm ^ k)
    (TwistTag.E6.orbitMin b)) i) (fun k c => hm_conj_yr _ _ _ _) c]
  have hF : ((List.range (TwistTag.E6.orbit b).card).map fun k =>
      ((((Units.map ((σ ^ k).comp (orbitField TwistTag.E6 K σ b).subtype).toMonoidHom w) ^
        (-Tag.cartan Tag.E6 ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin b)) i) : Kˣ)) :
          K)).prod = (Fv σ b (w : K) i)⁻¹ := by
    unfold Fv
    rw [← list_prod_zpow_neg]
    refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
    rw [Units.val_zpow_eq_zpow_val]
    rfl
  rw [hF]

theorem rhat_conj_u (b s : TwN) (w : (orbitField TwistTag.E6 K σ b)ˣ)
    (c : orbitField TwistTag.E6 K σ s) :
    minOrbitHom σ b (HSL w) * minOrbitHom σ s (uSL c) * (minOrbitHom σ b (HSL w))⁻¹ =
      ((List.range (TwistTag.E6.orbit s).card).map fun l =>
        e6Data_valid.xm K (Pi.single ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin s)) 1)
          (Fv σ b (w : K) ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin s)) *
            (σ ^ l) (c : K))).prod := by
  rw [minOrbitHom_uSL, conj_list_prod]
  exact congrArg List.prod (List.map_congr_left fun l _ => rhatH_conj_xm σ b w _ _)

theorem rhat_conj_v (b s : TwN) (w : (orbitField TwistTag.E6 K σ b)ˣ)
    (c : orbitField TwistTag.E6 K σ s) :
    minOrbitHom σ b (HSL w) * minOrbitHom σ s (vSL c) * (minOrbitHom σ b (HSL w))⁻¹ =
      ((List.range (TwistTag.E6.orbit s).card).map fun l =>
        e6Data_valid.xm K (-Pi.single ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin s)) 1)
          ((Fv σ b (w : K) ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin s)))⁻¹ *
            (σ ^ l) (c : K))).prod := by
  rw [minOrbitHom_vSL, conj_list_prod]
  exact congrArg List.prod (List.map_congr_left fun l _ => rhatH_conj_ym σ b w _ _)

end Torus

section Key

abbrev nd (n : ℕ) (h : n < 4 := by decide) : TwN := ⟨n, h⟩

abbrev ei (n : ℕ) (h : n < 6 := by decide) : Fin TwistTag.E6.tag.rank := ⟨n, h⟩

theorem cartan_E6_val (i j : Fin TwistTag.E6.tag.rank) :
    Tag.cartan Tag.E6 i j = if i.val = j.val then 2 else
      if (i.val, j.val) ∈ ([(0, 2), (2, 0), (1, 3), (3, 1), (2, 3), (3, 2), (3, 4), (4, 3), (4, 5),
        (5, 4)] : List (ℕ × ℕ)) then -1 else 0 := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  have hi' : i < 6 := hi
  have hj' : j < 6 := hj
  interval_cases i <;> interval_cases j <;> decide +revert

theorem card_nd0 : (TwistTag.E6.orbit (nd 0)).card = 2 := by decide
theorem card_nd1 : (TwistTag.E6.orbit (nd 1)).card = 2 := by decide
theorem card_nd2 : (TwistTag.E6.orbit (nd 2)).card = 1 := by decide
theorem card_nd3 : (TwistTag.E6.orbit (nd 3)).card = 1 := by decide
theorem min_nd0 : TwistTag.E6.orbitMin (nd 0) = ei 0 := by decide
theorem min_nd1 : TwistTag.E6.orbitMin (nd 1) = ei 2 := by decide
theorem min_nd2 : TwistTag.E6.orbitMin (nd 2) = ei 3 := by decide
theorem min_nd3 : TwistTag.E6.orbitMin (nd 3) = ei 1 := by decide
theorem perm_ei0 : TwistTag.E6.perm (ei 0) = ei 5 := by decide
theorem perm_ei2 : TwistTag.E6.perm (ei 2) = ei 4 := by decide

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K →+* K)

theorem Fv_nd0 (w : K) (i : Fin TwistTag.E6.tag.rank) : Fv σ (nd 0) w i =
    w ^ Tag.cartan Tag.E6 (ei 0) i * (σ w) ^ Tag.cartan Tag.E6 (ei 5) i := by
  rw [Fv_two σ card_nd0, min_nd0, perm_ei0]

theorem Fv_nd1 (w : K) (i : Fin TwistTag.E6.tag.rank) : Fv σ (nd 1) w i =
    w ^ Tag.cartan Tag.E6 (ei 2) i * (σ w) ^ Tag.cartan Tag.E6 (ei 4) i := by
  rw [Fv_two σ card_nd1, min_nd1, perm_ei2]

theorem Fv_nd2 (w : K) (i : Fin TwistTag.E6.tag.rank) : Fv σ (nd 2) w i =
    w ^ Tag.cartan Tag.E6 (ei 3) i := by
  rw [Fv_one σ card_nd2, min_nd2]

theorem Fv_nd3 (w : K) (i : Fin TwistTag.E6.tag.rank) : Fv σ (nd 3) w i =
    w ^ Tag.cartan Tag.E6 (ei 1) i := by
  rw [Fv_one σ card_nd3, min_nd3]

theorem unit_coe_ne_zero {b : TwN} (w : (orbitField TwistTag.E6 K σ b)ˣ) : (w : K) ≠ 0 :=
  fun h => w.ne_zero (Subtype.ext h)

theorem w_fix {b : TwN} (w : (orbitField TwistTag.E6 K σ b)ˣ) :
    (σ ^ (TwistTag.E6.orbit b).card) (w : K) = w :=
  mem_orbitField.1 (w : orbitField TwistTag.E6 K σ b).2

theorem key_of_u {b s : TwN} (w : (orbitField TwistTag.E6 K σ b)ˣ) (u : K) (hu0 : u ≠ 0)
    (hu : (σ ^ (TwistTag.E6.orbit s).card) u = u) (hA : u = (w : K) ^ (twA f b s))
    (hF : ∀ l < (TwistTag.E6.orbit s).card,
      Fv σ b (w : K) ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin s)) = (σ ^ l) u) :
    ∃ z : (orbitField TwistTag.E6 K σ s)ˣ, (z : K) ^ 2 = (w : K) ^ (twA f b s) ∧
      ∀ l < (TwistTag.E6.orbit s).card,
        Fv σ b (w : K) ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin s)) =
          (σ ^ l) ((z : K) ^ 2) := by
  obtain ⟨z, hz⟩ := exists_sq_unit (K := orbitField TwistTag.E6 K σ s)
    (Units.mk0 ⟨u, mem_orbitField.2 hu⟩ (fun h => hu0 (congrArg Subtype.val h)))
  have hz' : (z : K) ^ 2 = u := by
    have := congrArg (fun x : (orbitField TwistTag.E6 K σ s)ˣ => ((x : orbitField TwistTag.E6 K σ s) : K)) hz
    simpa using this
  exact ⟨z, hz'.trans hA, fun l hl => by rw [hz']; exact hF l hl⟩

theorem key_01 (hσσ : ∀ c : K, σ (σ c) = c) (hσ : ∀ c : K, σ c = c ^ (2 ^ f))
    (w : (orbitField TwistTag.E6 K σ (nd 0))ˣ) :
    ∃ z : (orbitField TwistTag.E6 K σ (nd 1))ˣ, (z : K) ^ 2 = (w : K) ^ (twA f (nd 0) (nd 1)) ∧
      ∀ l < (TwistTag.E6.orbit (nd 1)).card,
        Fv σ (nd 0) (w : K) ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin (nd 1))) =
          (σ ^ l) ((z : K) ^ 2) := by
  have hw0 := unit_coe_ne_zero σ w
  have hw := w_fix σ w
  rw [card_nd0, pow_two] at hw
  refine key_of_u σ w ((w : K) ^ (-1 : ℤ)) (zpow_ne_zero _ hw0) ?_ ?_ ?_
  · rw [card_nd1, pow_two]
    show σ (σ _) = _
    rw [map_zpow₀, map_zpow₀]
    show _ ^ _ = _
    rw [show σ (σ (w : K)) = w from hw]
  · rfl
  · intro l hl
    rw [card_nd1] at hl
    interval_cases l
    · simp [Fv_nd0, cartan_E6_val, min_nd1]
    · simp [Fv_nd0, cartan_E6_val, min_nd1, perm_ei2]

theorem key_00 (hσσ : ∀ c : K, σ (σ c) = c)
    (hσ : ∀ c : K, σ c = c ^ (2 ^ f)) (w : (orbitField TwistTag.E6 K σ (nd 0))ˣ) :
    ∃ z : (orbitField TwistTag.E6 K σ (nd 0))ˣ,
      (z : K) ^ 2 = (w : K) ^ (twA f (nd 0) (nd 0)) ∧
      ∀ l < (TwistTag.E6.orbit (nd 0)).card,
        Fv σ (nd 0) (w : K) ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin (nd 0))) =
          (σ ^ l) ((z : K) ^ 2) := by
  have hw0 := unit_coe_ne_zero σ w
  have hw := w_fix σ w
  rw [card_nd0, pow_two] at hw
  have hw' : σ (σ (w : K)) = w := hw
  refine key_of_u σ w ((w : K) ^ (2 : ℤ)) (zpow_ne_zero _ hw0)
    (by rw [card_nd0, pow_two]; show σ (σ _) = _; rw [map_zpow₀, map_zpow₀, hw']) (by rfl) ?_
  intro l hl
  rw [card_nd0] at hl
  interval_cases l <;> simp [Fv_nd0, Fv_nd1, Fv_nd2, Fv_nd3, cartan_E6_val, min_nd0, min_nd1, min_nd2, min_nd3, perm_ei0, perm_ei2, map_zpow₀, hw']

theorem key_02 (hσσ : ∀ c : K, σ (σ c) = c)
    (hσ : ∀ c : K, σ c = c ^ (2 ^ f)) (w : (orbitField TwistTag.E6 K σ (nd 0))ˣ) :
    ∃ z : (orbitField TwistTag.E6 K σ (nd 2))ˣ,
      (z : K) ^ 2 = (w : K) ^ (twA f (nd 0) (nd 2)) ∧
      ∀ l < (TwistTag.E6.orbit (nd 2)).card,
        Fv σ (nd 0) (w : K) ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin (nd 2))) =
          (σ ^ l) ((z : K) ^ 2) := by
  have hw0 := unit_coe_ne_zero σ w
  have hw := w_fix σ w
  rw [card_nd0, pow_two] at hw
  have hw' : σ (σ (w : K)) = w := hw
  refine key_of_u σ w 1 one_ne_zero (by simp) (by show (1 : K) = (w : K) ^ (0 : ℤ); simp) ?_
  intro l hl
  rw [card_nd2] at hl
  interval_cases l <;> simp [Fv_nd0, Fv_nd1, Fv_nd2, Fv_nd3, cartan_E6_val, min_nd0, min_nd1, min_nd2, min_nd3, perm_ei0, perm_ei2]

theorem key_03 (hσσ : ∀ c : K, σ (σ c) = c)
    (hσ : ∀ c : K, σ c = c ^ (2 ^ f)) (w : (orbitField TwistTag.E6 K σ (nd 0))ˣ) :
    ∃ z : (orbitField TwistTag.E6 K σ (nd 3))ˣ,
      (z : K) ^ 2 = (w : K) ^ (twA f (nd 0) (nd 3)) ∧
      ∀ l < (TwistTag.E6.orbit (nd 3)).card,
        Fv σ (nd 0) (w : K) ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin (nd 3))) =
          (σ ^ l) ((z : K) ^ 2) := by
  have hw0 := unit_coe_ne_zero σ w
  have hw := w_fix σ w
  rw [card_nd0, pow_two] at hw
  have hw' : σ (σ (w : K)) = w := hw
  refine key_of_u σ w 1 one_ne_zero (by simp) (by show (1 : K) = (w : K) ^ (0 : ℤ); simp) ?_
  intro l hl
  rw [card_nd3] at hl
  interval_cases l <;> simp [Fv_nd0, Fv_nd1, Fv_nd2, Fv_nd3, cartan_E6_val, min_nd0, min_nd1, min_nd2, min_nd3, perm_ei0, perm_ei2]

theorem key_10 (hσσ : ∀ c : K, σ (σ c) = c)
    (hσ : ∀ c : K, σ c = c ^ (2 ^ f)) (w : (orbitField TwistTag.E6 K σ (nd 1))ˣ) :
    ∃ z : (orbitField TwistTag.E6 K σ (nd 0))ˣ,
      (z : K) ^ 2 = (w : K) ^ (twA f (nd 1) (nd 0)) ∧
      ∀ l < (TwistTag.E6.orbit (nd 0)).card,
        Fv σ (nd 1) (w : K) ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin (nd 0))) =
          (σ ^ l) ((z : K) ^ 2) := by
  have hw0 := unit_coe_ne_zero σ w
  have hw := w_fix σ w
  rw [card_nd1, pow_two] at hw
  have hw' : σ (σ (w : K)) = w := hw
  refine key_of_u σ w ((w : K) ^ (-1 : ℤ)) (zpow_ne_zero _ hw0)
    (by rw [card_nd0, pow_two]; show σ (σ _) = _; rw [map_zpow₀, map_zpow₀]; show _ ^ _ = _; rw [hw']) (by rfl) ?_
  intro l hl
  rw [card_nd0] at hl
  interval_cases l <;> simp [Fv_nd0, Fv_nd1, Fv_nd2, Fv_nd3, cartan_E6_val, min_nd0, min_nd1, min_nd2, min_nd3, perm_ei0, perm_ei2, map_zpow₀, hw']

theorem key_11 (hσσ : ∀ c : K, σ (σ c) = c)
    (hσ : ∀ c : K, σ c = c ^ (2 ^ f)) (w : (orbitField TwistTag.E6 K σ (nd 1))ˣ) :
    ∃ z : (orbitField TwistTag.E6 K σ (nd 1))ˣ,
      (z : K) ^ 2 = (w : K) ^ (twA f (nd 1) (nd 1)) ∧
      ∀ l < (TwistTag.E6.orbit (nd 1)).card,
        Fv σ (nd 1) (w : K) ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin (nd 1))) =
          (σ ^ l) ((z : K) ^ 2) := by
  have hw0 := unit_coe_ne_zero σ w
  have hw := w_fix σ w
  rw [card_nd1, pow_two] at hw
  have hw' : σ (σ (w : K)) = w := hw
  refine key_of_u σ w ((w : K) ^ (2 : ℤ)) (zpow_ne_zero _ hw0)
    (by rw [card_nd1, pow_two]; show σ (σ _) = _; rw [map_zpow₀, map_zpow₀, hw']) (by rfl) ?_
  intro l hl
  rw [card_nd1] at hl
  interval_cases l <;> simp [Fv_nd0, Fv_nd1, Fv_nd2, Fv_nd3, cartan_E6_val, min_nd0, min_nd1, min_nd2, min_nd3, perm_ei0, perm_ei2, map_zpow₀, hw']

theorem key_12 (hσσ : ∀ c : K, σ (σ c) = c)
    (hσ : ∀ c : K, σ c = c ^ (2 ^ f)) (w : (orbitField TwistTag.E6 K σ (nd 1))ˣ) :
    ∃ z : (orbitField TwistTag.E6 K σ (nd 2))ˣ,
      (z : K) ^ 2 = (w : K) ^ (twA f (nd 1) (nd 2)) ∧
      ∀ l < (TwistTag.E6.orbit (nd 2)).card,
        Fv σ (nd 1) (w : K) ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin (nd 2))) =
          (σ ^ l) ((z : K) ^ 2) := by
  have hw0 := unit_coe_ne_zero σ w
  have hw := w_fix σ w
  rw [card_nd1, pow_two] at hw
  have hw' : σ (σ (w : K)) = w := hw
  have hσw0 : σ (w : K) ≠ 0 := fun h => hw0 (by rw [← hσσ (w : K), h, map_zero])
  refine key_of_u σ w ((w : K) ^ (-1 : ℤ) * (σ (w : K)) ^ (-1 : ℤ))
    (mul_ne_zero (zpow_ne_zero _ hw0) (zpow_ne_zero _ hσw0))
    (by rw [card_nd2, pow_one]; show σ _ = _; rw [map_mul, map_zpow₀, map_zpow₀, hw', mul_comm]) ?_ ?_
  · have h2 : (w : K) ^ ((2 : ℤ) ^ f) = (w : K) ^ (2 ^ f) := by
      rw [← zpow_natCast]; norm_num
    show (w : K) ^ (-1 : ℤ) * (σ (w : K)) ^ (-1 : ℤ) = (w : K) ^ (-(1 + (2 : ℤ) ^ f))
    rw [hσ (w : K), neg_add, zpow_add₀ hw0, zpow_neg ((w : K)) ((2 : ℤ) ^ f), h2, zpow_neg_one,
      zpow_neg_one]
  · intro l hl
    rw [card_nd2] at hl
    interval_cases l <;> simp [Fv_nd0, Fv_nd1, Fv_nd2, Fv_nd3, cartan_E6_val, min_nd0, min_nd1, min_nd2, min_nd3, perm_ei0, perm_ei2]

theorem key_13 (hσσ : ∀ c : K, σ (σ c) = c)
    (hσ : ∀ c : K, σ c = c ^ (2 ^ f)) (w : (orbitField TwistTag.E6 K σ (nd 1))ˣ) :
    ∃ z : (orbitField TwistTag.E6 K σ (nd 3))ˣ,
      (z : K) ^ 2 = (w : K) ^ (twA f (nd 1) (nd 3)) ∧
      ∀ l < (TwistTag.E6.orbit (nd 3)).card,
        Fv σ (nd 1) (w : K) ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin (nd 3))) =
          (σ ^ l) ((z : K) ^ 2) := by
  have hw0 := unit_coe_ne_zero σ w
  have hw := w_fix σ w
  rw [card_nd1, pow_two] at hw
  have hw' : σ (σ (w : K)) = w := hw
  refine key_of_u σ w 1 one_ne_zero (by simp) (by show (1 : K) = (w : K) ^ (0 : ℤ); simp) ?_
  intro l hl
  rw [card_nd3] at hl
  interval_cases l <;> simp [Fv_nd0, Fv_nd1, Fv_nd2, Fv_nd3, cartan_E6_val, min_nd0, min_nd1, min_nd2, min_nd3, perm_ei0, perm_ei2]

theorem key_20 (hσσ : ∀ c : K, σ (σ c) = c)
    (hσ : ∀ c : K, σ c = c ^ (2 ^ f)) (w : (orbitField TwistTag.E6 K σ (nd 2))ˣ) :
    ∃ z : (orbitField TwistTag.E6 K σ (nd 0))ˣ,
      (z : K) ^ 2 = (w : K) ^ (twA f (nd 2) (nd 0)) ∧
      ∀ l < (TwistTag.E6.orbit (nd 0)).card,
        Fv σ (nd 2) (w : K) ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin (nd 0))) =
          (σ ^ l) ((z : K) ^ 2) := by
  have hw0 := unit_coe_ne_zero σ w
  have hw := w_fix σ w
  rw [card_nd2, pow_one] at hw
  have hw' : σ (w : K) = w := hw
  refine key_of_u σ w 1 one_ne_zero (by simp) (by show (1 : K) = (w : K) ^ (0 : ℤ); simp) ?_
  intro l hl
  rw [card_nd0] at hl
  interval_cases l <;> simp [Fv_nd0, Fv_nd1, Fv_nd2, Fv_nd3, cartan_E6_val, min_nd0, min_nd1, min_nd2, min_nd3, perm_ei0, perm_ei2]

theorem key_21 (hσσ : ∀ c : K, σ (σ c) = c)
    (hσ : ∀ c : K, σ c = c ^ (2 ^ f)) (w : (orbitField TwistTag.E6 K σ (nd 2))ˣ) :
    ∃ z : (orbitField TwistTag.E6 K σ (nd 1))ˣ,
      (z : K) ^ 2 = (w : K) ^ (twA f (nd 2) (nd 1)) ∧
      ∀ l < (TwistTag.E6.orbit (nd 1)).card,
        Fv σ (nd 2) (w : K) ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin (nd 1))) =
          (σ ^ l) ((z : K) ^ 2) := by
  have hw0 := unit_coe_ne_zero σ w
  have hw := w_fix σ w
  rw [card_nd2, pow_one] at hw
  have hw' : σ (w : K) = w := hw
  refine key_of_u σ w ((w : K) ^ (-1 : ℤ)) (zpow_ne_zero _ hw0)
    (by rw [card_nd1, pow_two]; show σ (σ _) = _; rw [map_zpow₀, map_zpow₀, hw', hw']) (by rfl) ?_
  intro l hl
  rw [card_nd1] at hl
  interval_cases l <;> simp [Fv_nd0, Fv_nd1, Fv_nd2, Fv_nd3, cartan_E6_val, min_nd0, min_nd1, min_nd2, min_nd3, perm_ei0, perm_ei2, map_zpow₀, hw']

theorem key_22 (hσσ : ∀ c : K, σ (σ c) = c)
    (hσ : ∀ c : K, σ c = c ^ (2 ^ f)) (w : (orbitField TwistTag.E6 K σ (nd 2))ˣ) :
    ∃ z : (orbitField TwistTag.E6 K σ (nd 2))ˣ,
      (z : K) ^ 2 = (w : K) ^ (twA f (nd 2) (nd 2)) ∧
      ∀ l < (TwistTag.E6.orbit (nd 2)).card,
        Fv σ (nd 2) (w : K) ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin (nd 2))) =
          (σ ^ l) ((z : K) ^ 2) := by
  have hw0 := unit_coe_ne_zero σ w
  have hw := w_fix σ w
  rw [card_nd2, pow_one] at hw
  have hw' : σ (w : K) = w := hw
  refine key_of_u σ w ((w : K) ^ (2 : ℤ)) (zpow_ne_zero _ hw0)
    (by rw [card_nd2, pow_one]; show σ _ = _; rw [map_zpow₀, hw']) (by rfl) ?_
  intro l hl
  rw [card_nd2] at hl
  interval_cases l <;> simp [Fv_nd0, Fv_nd1, Fv_nd2, Fv_nd3, cartan_E6_val, min_nd0, min_nd1, min_nd2, min_nd3, perm_ei0, perm_ei2, map_zpow₀, hw']

theorem key_23 (hσσ : ∀ c : K, σ (σ c) = c)
    (hσ : ∀ c : K, σ c = c ^ (2 ^ f)) (w : (orbitField TwistTag.E6 K σ (nd 2))ˣ) :
    ∃ z : (orbitField TwistTag.E6 K σ (nd 3))ˣ,
      (z : K) ^ 2 = (w : K) ^ (twA f (nd 2) (nd 3)) ∧
      ∀ l < (TwistTag.E6.orbit (nd 3)).card,
        Fv σ (nd 2) (w : K) ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin (nd 3))) =
          (σ ^ l) ((z : K) ^ 2) := by
  have hw0 := unit_coe_ne_zero σ w
  have hw := w_fix σ w
  rw [card_nd2, pow_one] at hw
  have hw' : σ (w : K) = w := hw
  refine key_of_u σ w ((w : K) ^ (-1 : ℤ)) (zpow_ne_zero _ hw0)
    (by rw [card_nd3, pow_one]; show σ _ = _; rw [map_zpow₀, hw']) (by rfl) ?_
  intro l hl
  rw [card_nd3] at hl
  interval_cases l <;> simp [Fv_nd0, Fv_nd1, Fv_nd2, Fv_nd3, cartan_E6_val, min_nd0, min_nd1, min_nd2, min_nd3, perm_ei0, perm_ei2, map_zpow₀, hw']

theorem key_30 (hσσ : ∀ c : K, σ (σ c) = c)
    (hσ : ∀ c : K, σ c = c ^ (2 ^ f)) (w : (orbitField TwistTag.E6 K σ (nd 3))ˣ) :
    ∃ z : (orbitField TwistTag.E6 K σ (nd 0))ˣ,
      (z : K) ^ 2 = (w : K) ^ (twA f (nd 3) (nd 0)) ∧
      ∀ l < (TwistTag.E6.orbit (nd 0)).card,
        Fv σ (nd 3) (w : K) ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin (nd 0))) =
          (σ ^ l) ((z : K) ^ 2) := by
  have hw0 := unit_coe_ne_zero σ w
  have hw := w_fix σ w
  rw [card_nd3, pow_one] at hw
  have hw' : σ (w : K) = w := hw
  refine key_of_u σ w 1 one_ne_zero (by simp) (by show (1 : K) = (w : K) ^ (0 : ℤ); simp) ?_
  intro l hl
  rw [card_nd0] at hl
  interval_cases l <;> simp [Fv_nd0, Fv_nd1, Fv_nd2, Fv_nd3, cartan_E6_val, min_nd0, min_nd1, min_nd2, min_nd3, perm_ei0, perm_ei2]

theorem key_31 (hσσ : ∀ c : K, σ (σ c) = c)
    (hσ : ∀ c : K, σ c = c ^ (2 ^ f)) (w : (orbitField TwistTag.E6 K σ (nd 3))ˣ) :
    ∃ z : (orbitField TwistTag.E6 K σ (nd 1))ˣ,
      (z : K) ^ 2 = (w : K) ^ (twA f (nd 3) (nd 1)) ∧
      ∀ l < (TwistTag.E6.orbit (nd 1)).card,
        Fv σ (nd 3) (w : K) ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin (nd 1))) =
          (σ ^ l) ((z : K) ^ 2) := by
  have hw0 := unit_coe_ne_zero σ w
  have hw := w_fix σ w
  rw [card_nd3, pow_one] at hw
  have hw' : σ (w : K) = w := hw
  refine key_of_u σ w 1 one_ne_zero (by simp) (by show (1 : K) = (w : K) ^ (0 : ℤ); simp) ?_
  intro l hl
  rw [card_nd1] at hl
  interval_cases l <;> simp [Fv_nd0, Fv_nd1, Fv_nd2, Fv_nd3, cartan_E6_val, min_nd0, min_nd1, min_nd2, min_nd3, perm_ei0, perm_ei2]

theorem key_32 (hσσ : ∀ c : K, σ (σ c) = c)
    (hσ : ∀ c : K, σ c = c ^ (2 ^ f)) (w : (orbitField TwistTag.E6 K σ (nd 3))ˣ) :
    ∃ z : (orbitField TwistTag.E6 K σ (nd 2))ˣ,
      (z : K) ^ 2 = (w : K) ^ (twA f (nd 3) (nd 2)) ∧
      ∀ l < (TwistTag.E6.orbit (nd 2)).card,
        Fv σ (nd 3) (w : K) ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin (nd 2))) =
          (σ ^ l) ((z : K) ^ 2) := by
  have hw0 := unit_coe_ne_zero σ w
  have hw := w_fix σ w
  rw [card_nd3, pow_one] at hw
  have hw' : σ (w : K) = w := hw
  refine key_of_u σ w ((w : K) ^ (-1 : ℤ)) (zpow_ne_zero _ hw0)
    (by rw [card_nd2, pow_one]; show σ _ = _; rw [map_zpow₀, hw']) (by rfl) ?_
  intro l hl
  rw [card_nd2] at hl
  interval_cases l <;> simp [Fv_nd0, Fv_nd1, Fv_nd2, Fv_nd3, cartan_E6_val, min_nd0, min_nd1, min_nd2, min_nd3, perm_ei0, perm_ei2, map_zpow₀, hw']

theorem key_33 (hσσ : ∀ c : K, σ (σ c) = c)
    (hσ : ∀ c : K, σ c = c ^ (2 ^ f)) (w : (orbitField TwistTag.E6 K σ (nd 3))ˣ) :
    ∃ z : (orbitField TwistTag.E6 K σ (nd 3))ˣ,
      (z : K) ^ 2 = (w : K) ^ (twA f (nd 3) (nd 3)) ∧
      ∀ l < (TwistTag.E6.orbit (nd 3)).card,
        Fv σ (nd 3) (w : K) ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin (nd 3))) =
          (σ ^ l) ((z : K) ^ 2) := by
  have hw0 := unit_coe_ne_zero σ w
  have hw := w_fix σ w
  rw [card_nd3, pow_one] at hw
  have hw' : σ (w : K) = w := hw
  refine key_of_u σ w ((w : K) ^ (2 : ℤ)) (zpow_ne_zero _ hw0)
    (by rw [card_nd3, pow_one]; show σ _ = _; rw [map_zpow₀, hw']) (by rfl) ?_
  intro l hl
  rw [card_nd3] at hl
  interval_cases l <;> simp [Fv_nd0, Fv_nd1, Fv_nd2, Fv_nd3, cartan_E6_val, min_nd0, min_nd1, min_nd2, min_nd3, perm_ei0, perm_ei2, map_zpow₀, hw']

theorem key_all (hσσ : ∀ c : K, σ (σ c) = c) (hσ : ∀ c : K, σ c = c ^ (2 ^ f))
    (b s : TwN) (w : (orbitField TwistTag.E6 K σ b)ˣ) :
    ∃ z : (orbitField TwistTag.E6 K σ s)ˣ, (z : K) ^ 2 = (w : K) ^ (twA f b s) ∧
      ∀ l < (TwistTag.E6.orbit s).card,
        Fv σ b (w : K) ((TwistTag.E6.perm ^ l) (TwistTag.E6.orbitMin s)) =
          (σ ^ l) ((z : K) ^ 2) := by
  obtain ⟨bv, hbv⟩ := b
  obtain ⟨sv, hsv⟩ := s
  have hb4 : bv < 4 := hbv
  have hs4 : sv < 4 := hsv
  interval_cases bv <;> interval_cases sv
  · exact key_00 σ hσσ hσ w
  · exact key_01 σ hσσ hσ w
  · exact key_02 σ hσσ hσ w
  · exact key_03 σ hσσ hσ w
  · exact key_10 σ hσσ hσ w
  · exact key_11 σ hσσ hσ w
  · exact key_12 σ hσσ hσ w
  · exact key_13 σ hσσ hσ w
  · exact key_20 σ hσσ hσ w
  · exact key_21 σ hσσ hσ w
  · exact key_22 σ hσσ hσ w
  · exact key_23 σ hσσ hσ w
  · exact key_30 σ hσσ hσ w
  · exact key_31 σ hσσ hσ w
  · exact key_32 σ hσσ hσ w
  · exact key_33 σ hσσ hσ w

theorem conj_rhat_eq (hσσ : ∀ c : K, σ (σ c) = c) (hσ : ∀ c : K, σ c = c ^ (2 ^ f))
    (b s : TwN) (w : (orbitField TwistTag.E6 K σ b)ˣ) :
    ∃ z : (orbitField TwistTag.E6 K σ s)ˣ, (z : K) ^ 2 = (w : K) ^ (twA f b s) ∧
      ∀ g : SL2 (orbitField TwistTag.E6 K σ s),
        minOrbitHom σ b (HSL w) * minOrbitHom σ s g * (minOrbitHom σ b (HSL w))⁻¹ =
          minOrbitHom σ s (HSL z * g * (HSL z)⁻¹) := by
  obtain ⟨z, hz, hF⟩ := key_all σ hσσ hσ b s w
  refine ⟨z, hz, fun g => ?_⟩
  have hmem : ∀ l ∈ List.range (TwistTag.E6.orbit s).card, l < (TwistTag.E6.orbit s).card :=
    fun l hl => List.mem_range.1 hl
  have := hom_ext_SL2
    (f₁ := (MulAut.conj (minOrbitHom σ b (HSL w))).toMonoidHom.comp (minOrbitHom σ s))
    (f₂ := (minOrbitHom σ s).comp (MulAut.conj (HSL z)).toMonoidHom) (fun c => ?_) (fun c => ?_)
  · exact DFunLike.congr_fun this g
  · show minOrbitHom σ b (HSL w) * minOrbitHom σ s (uSL c) * (minOrbitHom σ b (HSL w))⁻¹ =
      minOrbitHom σ s (HSL z * uSL c * (HSL z)⁻¹)
    rw [rhat_conj_u, HSL_conj_uSL, minOrbitHom_uSL]
    refine congrArg List.prod (List.map_congr_left fun l hl => ?_)
    rw [hF l (hmem l hl)]
    congr 1
    show _ = (σ ^ l) (((z : K)) ^ 2 * (c : K))
    simp only [map_mul, map_pow]
  · show minOrbitHom σ b (HSL w) * minOrbitHom σ s (vSL c) * (minOrbitHom σ b (HSL w))⁻¹ =
      minOrbitHom σ s (HSL z * vSL c * (HSL z)⁻¹)
    rw [rhat_conj_v, HSL_conj_vSL, minOrbitHom_vSL]
    refine congrArg List.prod (List.map_congr_left fun l hl => ?_)
    rw [hF l (hmem l hl)]
    congr 1
    have hinv : ((((z⁻¹ : (orbitField TwistTag.E6 K σ s)ˣ) : orbitField TwistTag.E6 K σ s)) : K) =
        ((z : K))⁻¹ := by simp
    show _ = (σ ^ l) ((((z⁻¹ : (orbitField TwistTag.E6 K σ s)ˣ) : orbitField TwistTag.E6 K σ s)
      : K) ^ 2 * (c : K))
    rw [hinv]
    simp only [map_mul, map_pow, map_inv₀, inv_pow]

end Key

section Main

variable {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

include hf hK hσ in
theorem hatH_inv (a : TwN) (u : (orbitField TwistTag.E6 K σ a)ˣ) :
    (hatH hf hK σ hσ a u)⁻¹ = hatH hf hK σ hσ a u⁻¹ := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  show minOrbitHom σ a (HSL u) * minOrbitHom σ a (HSL u⁻¹) = 1
  rw [← map_mul, ← HSL_mul, mul_inv_cancel, HSL_one, map_one]

include hf hK hσ in
theorem twWeightShift_holds : TwWeightShift hf K hK σ hσ := by
  intro k _ _ _ V _ _ ρ s E y hy m e he hes b w
  have hσσ := sigma_sigma_eq hK σ hσ
  obtain ⟨z, hz, hconj⟩ := conj_rhat_eq σ hσσ hσ b s w
  have hG : ∀ g : SL2 (orbitField TwistTag.E6 K σ s),
      hatH hf hK σ hσ b w * Rhat hf hK σ hσ s g * (hatH hf hK σ hσ b w)⁻¹ =
        hatH hf hK σ hσ s z * Rhat hf hK σ hσ s g * (hatH hf hK σ hσ s z)⁻¹ := fun g =>
    Subtype.ext (by
      show minOrbitHom σ b (HSL w) * minOrbitHom σ s g * (minOrbitHom σ b (HSL w))⁻¹ =
        minOrbitHom σ s (HSL z) * minOrbitHom σ s g * (minOrbitHom σ s (HSL z))⁻¹
      rw [hconj g, map_mul, map_mul, map_inv])
  set ω : k := algebraMap K k ((w : orbitField TwistTag.E6 K σ b) : K) with hω
  set ζ : k := algebraMap K k ((z : orbitField TwistTag.E6 K σ s) : K) with hζ
  have hω0 : ω ≠ 0 := by
    rw [hω]; exact (map_ne_zero _).2 (unit_coe_ne_zero σ w)
  have hζ0 : ζ ≠ 0 := by
    rw [hζ]; exact (map_ne_zero _).2 (unit_coe_ne_zero σ z)
  have hζω : ζ ^ 2 = ω ^ (twA f b s) := by
    have := congrArg (algebraMap K k) hz
    rwa [map_pow, map_zpow₀] at this
  have hinvζ : algebraMap K k ((((z⁻¹ : (orbitField TwistTag.E6 K σ s)ˣ) :
      orbitField TwistTag.E6 K σ s)) : K) = ζ⁻¹ := by
    rw [hζ, ← map_inv₀]; congr 1; simp
  have hclaim : ∀ e' ∈ orbitSpan (ρ.comp (Rhat hf hK σ hσ s)) y,
      ρ (hatH hf hK σ hσ b w) e' = (ω ^ (E b) * (ζ⁻¹) ^ (E s)) •
        ρ (hatH hf hK σ hσ s z) e' := by
    intro e' he'
    induction he' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      show ρ (hatH hf hK σ hσ b w) (ρ (Rhat hf hK σ hσ s g) y) = _ •
        ρ (hatH hf hK σ hσ s z) (ρ (Rhat hf hK σ hσ s g) y)
      have h1 : hatH hf hK σ hσ b w * Rhat hf hK σ hσ s g =
          (hatH hf hK σ hσ s z * Rhat hf hK σ hσ s g * (hatH hf hK σ hσ s z)⁻¹) *
            hatH hf hK σ hσ b w := by
        rw [← hG g]; group
      have hyb : ρ (hatH hf hK σ hσ b w) y = ω ^ (E b) • y := hy b w
      have hys : ρ (hatH hf hK σ hσ s z⁻¹) y = (ζ⁻¹) ^ (E s) • y := by
        have := hy s z⁻¹
        rwa [hinvζ] at this
      rw [act_mul, h1, ← act_mul, ← act_mul, ← act_mul, hyb, map_smul, hatH_inv hf K hK σ hσ, hys,
        map_smul, map_smul, map_smul, map_smul, smul_smul, mul_comm]
    | zero => simp
    | add x y _ _ hx hy' => rw [map_add, map_add, hx, hy', smul_add]
    | smul c x _ hx => rw [map_smul, map_smul, hx, smul_comm]
  have hes' : ρ (hatH hf hK σ hσ s z) e = ζ ^ (E s - 2 * (m : ℤ)) • e := hes z
  show ρ (hatH hf hK σ hσ b w) e = ω ^ (E b - (m : ℤ) * twA f b s) • e
  rw [hclaim e he, hes', smul_smul]
  congr 1
  have h1 : (ζ⁻¹) ^ (E s) * ζ ^ (E s - 2 * (m : ℤ)) = (ζ ^ 2) ^ (-(m : ℤ)) := by
    rw [inv_zpow', ← zpow_natCast ζ 2, ← zpow_mul, ← zpow_add₀ hζ0]
    congr 1
    push_cast
    ring
  rw [mul_assoc, h1, hζω, ← zpow_mul, ← zpow_add₀ hω0]
  congr 1
  ring

end Main

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
