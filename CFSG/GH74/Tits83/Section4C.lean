module

public import CFSG.GH74.Tits83.Section4B

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

namespace OctFrame

variable {G : Type u} [Group G] {T : TitsSystem G 8} (F : OctFrame T)

theorem val_ne_one {x : F.K} (hx : x ≠ 0) : x.val ≠ 1 := by
  intro h
  exact hx (F.val_eq_one_iff.mp h)

private theorem alpha_def (x : F.K) : F.alpha x = T.mu 1 x.val * F.a := rfl

private theorem inv_ne_zero {x : F.K} (hx : x ≠ 0) : x⁻¹ ≠ 0 := by
  intro h
  have h' : x = 0 := by
    rw [← inv_inv x, h, inv_zero]
  exact hx h'

theorem exists_sigma (x : F.K) : ∃ s : F.K, (x = 0 → s = 0) ∧
    (x ≠ 0 → F.xo 3 s.val = F.alpha x * F.xo 3 F.e1 * (F.alpha x)⁻¹) := by
  by_cases hx : x = 0
  · exact ⟨0, fun _ => rfl, fun h => (h hx).elim⟩
  · have hx' : x.val ≠ 1 := F.val_ne_one hx
    have hmoves : T.Moves (F.alpha x) (fun j => j) := F.moves_alpha hx'
    have hmem : F.alpha x * F.xo 3 F.e1 * (F.alpha x)⁻¹ ∈ T.U 3 := by
      exact TitsSystem.Moves.conj_mem T hmoves (j := 3) (F.xo_mem (j := 3) (by decide) F.e1_mem)
    obtain ⟨s, hs_mem, hs⟩ := (F.xo_bijOn (j := 3) (by decide)).surjOn hmem
    refine ⟨⟨s, hs_mem⟩, fun h => (hx h).elim, fun _ => ?_⟩
    exact hs

noncomputable def sigmaFun (x : F.K) : F.K := Classical.choose (F.exists_sigma x)

theorem xo_three_sigmaFun {x : F.K} (hx : x ≠ 0) :
    F.xo 3 (F.sigmaFun x).val = F.alpha x * F.xo 3 F.e1 * (F.alpha x)⁻¹ :=
  (Classical.choose_spec (F.exists_sigma x)).2 hx

theorem sigmaFun_ne_zero {x : F.K} (hx : x ≠ 0) : F.sigmaFun x ≠ 0 := by
  intro hs
  have hsval : (F.sigmaFun x).val = 1 := by
    rw [hs, F.val_zero]
  have h1 : F.xo 3 (F.sigmaFun x).val = 1 := by
    rw [hsval, F.xo_one_eq]
  have h2 : F.alpha x * F.xo 3 F.e1 * (F.alpha x)⁻¹ = 1 := by
    rw [← F.xo_three_sigmaFun hx, h1]
  have he3 : F.xo 3 F.e1 = 1 := by
    calc F.xo 3 F.e1 = (F.alpha x)⁻¹ * (F.alpha x * F.xo 3 F.e1 *
        (F.alpha x)⁻¹) * F.alpha x := by group
      _ = 1 := by rw [h2]; group
  have hxval : F.e1 = 1 := by
    have hinj := (F.xo_bijOn (j := 3) (by decide)).injOn F.e1_mem
      (T.U 1).one_mem (by simpa [F.xo_one_eq] using he3)
    exact hinj
  exact F.e1_ne hxval

theorem a_conj_alpha {x : F.K} (hx : x ≠ 0) : F.a * F.alpha x * F.a⁻¹ = (F.alpha x)⁻¹ := by
  have hx' : x.val ≠ 1 := F.val_ne_one hx
  have hm : T.mu 1 x.val * T.mu 1 x.val = 1 :=
    T.lemma35_ii F.hT (by decide : Odd (1 : ℤ)) x.mem hx'
  have ha : F.a * F.a = 1 := F.a_mul_self
  have hainv : F.a⁻¹ = F.a := inv_eq_of_mul_eq_one_right ha
  have hminv : (T.mu 1 x.val)⁻¹ = T.mu 1 x.val := inv_eq_of_mul_eq_one_right hm
  calc
    F.a * F.alpha x * F.a⁻¹ = F.a * (T.mu 1 x.val * F.a) * F.a := by
      rw [F.alpha_def, hainv]
    _ = F.a * T.mu 1 x.val := by
      rw [mul_assoc, mul_assoc, ha, mul_one]
    _ = (T.mu 1 x.val * F.a)⁻¹ := by
      rw [mul_inv_rev, hminv, hainv]
    _ = (F.alpha x)⁻¹ := by rw [F.alpha_def]

private theorem alpha_mul_a {x : F.K} (hx : x ≠ 0) :
    F.alpha x * F.a = F.a * (F.alpha x)⁻¹ := by
  have h := F.a_conj_alpha hx
  have hαeq : F.alpha x = F.a * (F.alpha x)⁻¹ * F.a := by
    calc F.alpha x = (F.a * F.a) * F.alpha x * (F.a⁻¹ * F.a) := by
          rw [F.a_mul_self, inv_mul_cancel, one_mul, mul_one]
      _ = F.a * (F.a * F.alpha x * F.a⁻¹) * F.a := by group
      _ = F.a * (F.alpha x)⁻¹ * F.a := by rw [h]
  calc
    F.alpha x * F.a = (F.a * (F.alpha x)⁻¹ * F.a) * F.a := by
      conv_lhs => rw [hαeq]
    _ = F.a * (F.alpha x)⁻¹ := by
      rw [mul_assoc, mul_assoc, F.a_mul_self, mul_one]

theorem alpha_mul_conj {x y : F.K} (hx : x ≠ 0) (hy : y ≠ 0) {j : ℤ} (hj : Odd j) {w : G}
    (hw : w ∈ T.U j) :
    F.alpha (x * y) * w * (F.alpha (x * y))⁻¹ =
      F.alpha x * F.alpha y * w * (F.alpha x * F.alpha y)⁻¹ := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have hx' : x.val ≠ 1 := F.val_ne_one hx
  have hy' : y.val ≠ 1 := F.val_ne_one hy
  have hg : (F.alpha (F.mulK x y))⁻¹ * (F.alpha x * F.alpha y) ∈ T.Ctriv :=
    F.alpha_mulK_mem hx' hy'
  have hg' : (F.alpha (x * y))⁻¹ * (F.alpha x * F.alpha y) ∈ T.Ctriv := by
    simpa [F.mul_def] using hg
  set g : G := (F.alpha (x * y))⁻¹ * (F.alpha x * F.alpha y) with hgdef
  have hgcomm : g * w = w * g := T.Ctriv_comm_odd hg' hj hw
  have hα : F.alpha (x * y) = F.alpha x * F.alpha y * g⁻¹ := by
    rw [hgdef]
    group
  have hgconj : g⁻¹ * w * g = w := by
    have h := congrArg (fun t => g⁻¹ * t) hgcomm
    simpa [mul_assoc] using h.symm
  have hαinv : (F.alpha (x * y))⁻¹ = g * (F.alpha y)⁻¹ * (F.alpha x)⁻¹ := by
    rw [hα]
    group
  have hmain : F.alpha (x * y) * w * (F.alpha (x * y))⁻¹ =
      F.alpha x * F.alpha y * w * (F.alpha x * F.alpha y)⁻¹ := by
    calc
      F.alpha (x * y) * w * (F.alpha (x * y))⁻¹
          = (F.alpha x * F.alpha y * g⁻¹) * w *
              (g * (F.alpha y)⁻¹ * (F.alpha x)⁻¹) := by rw [hαinv, hα]
      _ = F.alpha x * F.alpha y * (g⁻¹ * w * g) *
            (F.alpha x * F.alpha y)⁻¹ := by group
      _ = F.alpha x * F.alpha y * w * (F.alpha x * F.alpha y)⁻¹ := by rw [hgconj]
  exact hmain

theorem alpha_xo_five {x : F.K} (hx : x ≠ 0) (y : F.K) :
    F.alpha x * F.xo 5 y.val * (F.alpha x)⁻¹ = F.xo 5 y.val := by
  have hx' : x.val ≠ 1 := F.val_ne_one hx
  have hy : F.xo 5 y.val ∈ T.U 5 := F.xo_mem (j := 5) (by decide) y.mem
  have h := F.alpha_comm_five hx' hy
  rw [h]
  group

theorem alpha_xp_four' {x : F.K} (hx : x ≠ 0) (y : F.K) :
    F.alpha x * F.xp 4 y.val * (F.alpha x)⁻¹ = F.xp 4 (x * y).val := by
  have hx' : x.val ≠ 1 := F.val_ne_one hx
  simpa [F.mul_def] using F.alpha_xp_four hx' y

theorem alpha_xp_six {x : F.K} (hx : x ≠ 0) (y : F.K) :
    F.alpha x * F.xp 6 y.val * (F.alpha x)⁻¹ = F.xp 6 (x⁻¹ * y).val := by
  have hxinv : x⁻¹ ≠ 0 := F.inv_ne_zero hx
  have h6 : F.a * F.xp 4 y.val * F.a⁻¹ = F.xp 6 y.val := by
    simpa using F.a_conj_xp (j := 4) (by decide : Even (4 : ℤ)) y.mem
  have h4 : F.alpha x * F.xp 4 (x⁻¹ * y).val * (F.alpha x)⁻¹ = F.xp 4 y.val := by
    have h := F.alpha_xp_four' hx (x⁻¹ * y)
    have hval : x * (x⁻¹ * y) = y := by
      calc x * (x⁻¹ * y) = (x * x⁻¹) * y := by rw [mul_assoc]
        _ = y := by rw [mul_inv_cancel₀ hx, one_mul]
    rwa [hval] at h
  have hinv : (F.alpha x)⁻¹ * F.xp 4 y.val * F.alpha x = F.xp 4 (x⁻¹ * y).val := by
    rw [← h4]
    group
  have hconj : F.a⁻¹ * (F.alpha x)⁻¹ = F.alpha x * F.a⁻¹ := by
    calc F.a⁻¹ * (F.alpha x)⁻¹ = (F.alpha x * F.a)⁻¹ := by rw [mul_inv_rev]
      _ = (F.a * (F.alpha x)⁻¹)⁻¹ := by rw [F.alpha_mul_a hx]
      _ = F.alpha x * F.a⁻¹ := by rw [mul_inv_rev, inv_inv]
  calc
    F.alpha x * F.xp 6 y.val * (F.alpha x)⁻¹
        = F.alpha x * (F.a * F.xp 4 y.val * F.a⁻¹) * (F.alpha x)⁻¹ := by rw [h6]
    _ = (F.alpha x * F.a) * F.xp 4 y.val * (F.a⁻¹ * (F.alpha x)⁻¹) := by group
    _ = (F.a * (F.alpha x)⁻¹) * F.xp 4 y.val * (F.a⁻¹ * (F.alpha x)⁻¹) := by
      rw [F.alpha_mul_a hx]
    _ = F.a * ((F.alpha x)⁻¹ * F.xp 4 y.val * F.alpha x) * F.a⁻¹ := by
      rw [hconj]
      group
    _ = F.a * F.xp 4 (x⁻¹ * y).val * F.a⁻¹ := by rw [hinv]
    _ = F.xp 6 (x⁻¹ * y).val := by
      simpa using F.a_conj_xp (j := 4) (by decide : Even (4 : ℤ)) (x⁻¹ * y).mem
private theorem alpha_conj_mem {x : F.K} (hx : x ≠ 0) {j : ℤ} {y : G} (hy : y ∈ T.U j) :
    F.alpha x * y * (F.alpha x)⁻¹ ∈ T.U j := by
  have hmoves : T.Moves (F.alpha x) (fun j => j) := F.moves_alpha (F.val_ne_one hx)
  exact TitsSystem.Moves.conj_mem T hmoves hy

private theorem alpha_conj_mem_Uprime {x : F.K} (hx : x ≠ 0) {j : ℤ} {y : G}
    (hy : y ∈ T.Uprime j) : F.alpha x * y * (F.alpha x)⁻¹ ∈ T.Uprime j := by
  have hmoves : T.Moves (F.alpha x) (fun j => 1 * j + 0) := by
    simpa using F.moves_alpha (F.val_ne_one hx)
  have h := TitsSystem.Moves.conj_mem_Uprime T (Or.inl rfl) hmoves hy
  simpa using h

private theorem alpha_xo_image {x : F.K} (hx : x ≠ 0) {j : ℤ} (hj : Odd j) (y : F.K) :
    ∃ t : F.K, F.alpha x * F.xo j y.val * (F.alpha x)⁻¹ = F.xo j t.val := by
  obtain ⟨z, hzmem, hz⟩ := (F.xo_bijOn hj).surjOn (F.alpha_conj_mem hx (F.xo_mem hj y.mem))
  exact ⟨⟨z, hzmem⟩, hz.symm⟩

private theorem alpha_xp_image {x : F.K} (hx : x ≠ 0) {j : ℤ} (hj : Even j) (y : F.K) :
    ∃ t : F.K, F.alpha x * F.xp j y.val * (F.alpha x)⁻¹ = F.xp j t.val := by
  obtain ⟨z, hzmem, hz⟩ := (F.xp_bijOn hj).surjOn
    (F.alpha_conj_mem_Uprime hx (F.xp_mem hj y.mem))
  exact ⟨⟨z, hzmem⟩, hz.symm⟩

theorem alpha_xp_eight {x : F.K} (hx : x ≠ 0) (y : F.K) :
    F.alpha x * F.xp 8 y.val * (F.alpha x)⁻¹ =
      F.xp 8 ((F.sigmaFun x * x)⁻¹ * y).val := by
  have hs : F.sigmaFun x ≠ 0 := F.sigmaFun_ne_zero hx
  have hrel : ⁅F.xo 3 F.e1, F.xp 8 y.val⁆ = F.xp 6 y.val := by
    have h := F.comm_xo_xp (j := 6) (by decide) (1 : F.K) y
    simpa [F.val_one, mul_one] using h
  obtain ⟨t, ht⟩ := F.alpha_xp_image hx (j := 8) (by decide) y
  have hconj : ⁅F.xo 3 (F.sigmaFun x).val, F.xp 8 t.val⁆ =
      F.xp 6 (x⁻¹ * y).val := by
    have h := congrArg (fun g => F.alpha x * g * (F.alpha x)⁻¹) hrel
    rw [conjugate_commutatorElement, F.alpha_xp_six hx y] at h
    rw [← F.xo_three_sigmaFun hx, ht] at h
    exact h
  have hcomm : ⁅F.xo 3 (F.sigmaFun x).val, F.xp 8 t.val⁆ =
      F.xp 6 (F.sigmaFun x * t).val := by
    simpa using F.comm_xo_xp (j := 6) (by decide) (F.sigmaFun x) t
  have heq : F.xp 6 (F.sigmaFun x * t).val = F.xp 6 (x⁻¹ * y).val := by
    rw [← hcomm]
    exact hconj
  have hprod : F.sigmaFun x * t = x⁻¹ * y :=
    K.ext ((F.xp_bijOn (j := 6) (by decide)).injOn
      (F.sigmaFun x * t).mem (x⁻¹ * y).mem heq)
  have htval : t = (F.sigmaFun x * x)⁻¹ * y := by
    calc t = (F.sigmaFun x)⁻¹ * (F.sigmaFun x * t) := by
          rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
      _ = (F.sigmaFun x)⁻¹ * (x⁻¹ * y) := by rw [hprod]
      _ = (F.sigmaFun x * x)⁻¹ * y := by field_simp [hs, hx]
  rw [ht, htval]

theorem alpha_xo_three {x : F.K} (hx : x ≠ 0) (y : F.K) :
    F.alpha x * F.xo 3 y.val * (F.alpha x)⁻¹ = F.xo 3 (F.sigmaFun x * y).val := by
  have hs : F.sigmaFun x ≠ 0 := F.sigmaFun_ne_zero hx
  have hrel : ⁅F.xo 3 y.val, F.xp 8 F.e1⁆ = F.xp 6 y.val := by
    have h := F.comm_xo_xp (j := 6) (by decide) y (1 : F.K)
    simpa [F.val_one, mul_one] using h
  obtain ⟨w, hw⟩ := F.alpha_xo_image hx (j := 3) (by decide) y
  have h8 : F.alpha x * F.xp 8 F.e1 * (F.alpha x)⁻¹ =
      F.xp 8 ((F.sigmaFun x * x)⁻¹).val := by
    have h := F.alpha_xp_eight hx (1 : F.K)
    simpa [F.val_one, mul_one] using h
  have hconj : ⁅F.xo 3 w.val, F.xp 8 ((F.sigmaFun x * x)⁻¹).val⁆ =
      F.xp 6 (x⁻¹ * y).val := by
    have h := congrArg (fun g => F.alpha x * g * (F.alpha x)⁻¹) hrel
    rw [conjugate_commutatorElement, F.alpha_xp_six hx y] at h
    rw [hw, h8] at h
    exact h
  have hcomm : ⁅F.xo 3 w.val, F.xp 8 ((F.sigmaFun x * x)⁻¹).val⁆ =
      F.xp 6 (w * (F.sigmaFun x * x)⁻¹).val := by
    simpa using F.comm_xo_xp (j := 6) (by decide) w ((F.sigmaFun x * x)⁻¹)
  rw [hcomm] at hconj
  have hprod : w * (F.sigmaFun x * x)⁻¹ = x⁻¹ * y :=
    K.ext ((F.xp_bijOn (j := 6) (by decide)).injOn
      (w * (F.sigmaFun x * x)⁻¹).mem (x⁻¹ * y).mem hconj)
  have hwval : w = F.sigmaFun x * y := by
    have ht : (F.sigmaFun x * x)⁻¹ ≠ 0 := F.inv_ne_zero (mul_ne_zero hs hx)
    calc w = (w * (F.sigmaFun x * x)⁻¹) * (F.sigmaFun x * x) := by
          field_simp [ht]
      _ = (x⁻¹ * y) * (F.sigmaFun x * x) := by rw [hprod]
      _ = F.sigmaFun x * y := by field_simp [hs, hx]
  rw [hw, hwval]

theorem alpha_xo_nine {x : F.K} (hx : x ≠ 0) (y : F.K) :
    F.alpha x * F.xo 9 y.val * (F.alpha x)⁻¹ = F.xo 9 ((x ^ 2)⁻¹ * y).val := by
  have hrel : ⁅F.xo 9 y.val, F.xp 4 F.e1⁆ = F.xp 6 y.val := by
    have h := F.comm_xo_xp' (j := 6) (by decide) y (1 : F.K)
    simpa [F.val_one, mul_one] using h
  obtain ⟨w, hw⟩ := F.alpha_xo_image hx (j := 9) (by decide) y
  have h4 : F.alpha x * F.xp 4 F.e1 * (F.alpha x)⁻¹ = F.xp 4 x.val := by
    have h := F.alpha_xp_four' hx (1 : F.K)
    simpa [F.val_one, mul_one] using h
  have hconj : ⁅F.xo 9 w.val, F.xp 4 x.val⁆ = F.xp 6 (x⁻¹ * y).val := by
    have h := congrArg (fun g => F.alpha x * g * (F.alpha x)⁻¹) hrel
    rw [conjugate_commutatorElement, F.alpha_xp_six hx y] at h
    rw [hw, h4] at h
    exact h
  have hcomm : ⁅F.xo 9 w.val, F.xp 4 x.val⁆ = F.xp 6 (w * x).val := by
    simpa using F.comm_xo_xp' (j := 6) (by decide) w x
  rw [hcomm] at hconj
  have hprod : w * x = x⁻¹ * y :=
    K.ext ((F.xp_bijOn (j := 6) (by decide)).injOn
      (w * x).mem (x⁻¹ * y).mem hconj)
  have hwval : w = (x ^ 2)⁻¹ * y := by
    calc w = (w * x) * x⁻¹ := by
          field_simp [hx]
      _ = (x⁻¹ * y) * x⁻¹ := by rw [hprod]
      _ = (x ^ 2)⁻¹ * y := by field_simp [hx]
  rw [hw, hwval]

private theorem alpha_conj_refl_xo {x : F.K} (hx : x ≠ 0) {j : ℤ} (hj : Odd j)
    (t : F.K) (ht : t ≠ 0)
    (h : ∀ y : F.K, F.alpha x * F.xo j y.val * (F.alpha x)⁻¹ = F.xo j (t * y).val)
    (y : F.K) :
    F.alpha x * F.xo (10 - j) y.val * (F.alpha x)⁻¹ =
      F.xo (10 - j) (t⁻¹ * y).val := by
  have hz : F.alpha x * F.xo j (t⁻¹ * y).val * (F.alpha x)⁻¹ = F.xo j y.val := by
    have h' := h (t⁻¹ * y)
    rw [show t * (t⁻¹ * y) = y by field_simp [ht]] at h'
    simpa [mul_assoc] using h'
  have hinv : (F.alpha x)⁻¹ * F.xo j y.val * F.alpha x = F.xo j (t⁻¹ * y).val := by
    rw [← hz]
    group
  have haα : F.a * (F.alpha x)⁻¹ * F.a⁻¹ = F.alpha x := by
    have h := congrArg Inv.inv (F.a_conj_alpha hx)
    simpa [mul_assoc] using h
  calc
    F.alpha x * F.xo (10 - j) y.val * (F.alpha x)⁻¹
        = (F.a * (F.alpha x)⁻¹ * F.a⁻¹) * (F.a * F.xo j y.val * F.a⁻¹) *
            (F.a * F.alpha x * F.a⁻¹) := by
          rw [haα, F.a_conj_xo (j := j) hj y.mem, F.a_conj_alpha hx]
    _ = F.a * ((F.alpha x)⁻¹ * F.xo j y.val * F.alpha x) * F.a⁻¹ := by group
    _ = F.a * F.xo j (t⁻¹ * y).val * F.a⁻¹ := by rw [hinv]
    _ = F.xo (10 - j) (t⁻¹ * y).val := F.a_conj_xo (j := j) hj (t⁻¹ * y).mem

private theorem alpha_conj_refl_xp {x : F.K} (hx : x ≠ 0) {j : ℤ} (hj : Even j)
    (t : F.K) (ht : t ≠ 0)
    (h : ∀ y : F.K, F.alpha x * F.xp j y.val * (F.alpha x)⁻¹ = F.xp j (t * y).val)
    (y : F.K) :
    F.alpha x * F.xp (10 - j) y.val * (F.alpha x)⁻¹ =
      F.xp (10 - j) (t⁻¹ * y).val := by
  have hz : F.alpha x * F.xp j (t⁻¹ * y).val * (F.alpha x)⁻¹ = F.xp j y.val := by
    have h' := h (t⁻¹ * y)
    rw [show t * (t⁻¹ * y) = y by field_simp [ht]] at h'
    simpa [mul_assoc] using h'
  have hinv : (F.alpha x)⁻¹ * F.xp j y.val * F.alpha x = F.xp j (t⁻¹ * y).val := by
    rw [← hz]
    group
  have haα : F.a * (F.alpha x)⁻¹ * F.a⁻¹ = F.alpha x := by
    have h := congrArg Inv.inv (F.a_conj_alpha hx)
    simpa [mul_assoc] using h
  calc
    F.alpha x * F.xp (10 - j) y.val * (F.alpha x)⁻¹
        = (F.a * (F.alpha x)⁻¹ * F.a⁻¹) * (F.a * F.xp j y.val * F.a⁻¹) *
            (F.a * F.alpha x * F.a⁻¹) := by
          rw [haα, F.a_conj_xp (j := j) hj y.mem, F.a_conj_alpha hx]
    _ = F.a * ((F.alpha x)⁻¹ * F.xp j y.val * F.alpha x) * F.a⁻¹ := by group
    _ = F.a * F.xp j (t⁻¹ * y).val * F.a⁻¹ := by rw [hinv]
    _ = F.xp (10 - j) (t⁻¹ * y).val := F.a_conj_xp (j := j) hj (t⁻¹ * y).mem

theorem alpha_xo_one {x : F.K} (hx : x ≠ 0) (y : F.K) :
    F.alpha x * F.xo 1 y.val * (F.alpha x)⁻¹ = F.xo 1 (x ^ 2 * y).val := by
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have h := F.alpha_conj_refl_xo hx (j := 9) (by decide) ((x ^ 2)⁻¹) (F.inv_ne_zero hx2)
    (F.alpha_xo_nine hx) y
  simpa using h

theorem alpha_xp_two {x : F.K} (hx : x ≠ 0) (y : F.K) :
    F.alpha x * F.xp 2 y.val * (F.alpha x)⁻¹ = F.xp 2 (F.sigmaFun x * x * y).val := by
  have hs : F.sigmaFun x ≠ 0 := F.sigmaFun_ne_zero hx
  have h := F.alpha_conj_refl_xp hx (j := 8) (by decide) ((F.sigmaFun x * x)⁻¹)
    (F.inv_ne_zero (mul_ne_zero hs hx)) (F.alpha_xp_eight hx) y
  simpa [mul_assoc] using h

theorem alpha_xo_seven {x : F.K} (hx : x ≠ 0) (y : F.K) :
    F.alpha x * F.xo 7 y.val * (F.alpha x)⁻¹ =
      F.xo 7 ((F.sigmaFun x)⁻¹ * y).val := by
  have hs : F.sigmaFun x ≠ 0 := F.sigmaFun_ne_zero hx
  have h := F.alpha_conj_refl_xo hx (j := 3) (by decide) (F.sigmaFun x) hs
    (F.alpha_xo_three hx) y
  simpa using h

theorem alpha_comm_refl {x : F.K} (hx : x ≠ 0) :
    F.alpha x * (F.rho ^ (-4 : ℤ) * F.a) = F.rho ^ (-4 : ℤ) * F.a * F.alpha x := by
  let r : G := F.rho ^ (-4 : ℤ) * F.a
  change F.alpha x * r = r * F.alpha x
  have hmoves : T.Moves r (fun j => -1 * j + 2) := by
    have h := F.moves_rho_zpow_a (-4 : ℤ)
    intro j
    have h' := h j
    change (T.U j).map (MulAut.conj (F.rho ^ (-4 : ℤ) * F.a)).toMonoidHom =
      T.U (10 + 2 * (-4 : ℤ) - j) at h'
    rw [show 10 + 2 * (-4 : ℤ) - j = -1 * j + 2 by ring] at h'
    simpa [r] using h'
  have hx' : x.val ≠ 1 := F.val_ne_one hx
  have hrm : r * T.mu 1 x.val * r⁻¹ = T.mu 1 x.val := by
    have h := (T.mu_conj (by norm_num : 3 ≤ 8) (Or.inr rfl) hmoves x.mem hx').1
    have hxcomm : r * x.val * r⁻¹ = x.val := by
      have hc := F.refl_comm x.mem
      change r * x.val = x.val * r at hc
      rw [hc]
      change x.val * r * r⁻¹ = x.val
      group
    rw [hxcomm] at h
    have h' : T.mu 1 x.val = r * T.mu 1 x.val * r⁻¹ := by simpa using h
    exact h'.symm
  have hm : r * T.mu 1 x.val = T.mu 1 x.val * r := by
    calc r * T.mu 1 x.val = (r * T.mu 1 x.val * r⁻¹) * r := by group
      _ = T.mu 1 x.val * r := by rw [hrm]
  have h4 : F.rho ^ (4 : ℤ) = F.rho ^ (-4 : ℤ) := by
    have h8 : F.rho ^ (8 : ℤ) = 1 := by simpa using F.rho_pow_eight
    calc F.rho ^ (4 : ℤ) = F.rho ^ (8 : ℤ) * F.rho ^ (-4 : ℤ) := by
          rw [← zpow_add]
          norm_num
      _ = 1 * F.rho ^ (-4 : ℤ) := by rw [h8]
      _ = F.rho ^ (-4 : ℤ) := by rw [one_mul]
  have haρ : F.a * F.rho ^ (-4 : ℤ) = F.rho ^ (-4 : ℤ) * F.a := by
    calc F.a * F.rho ^ (-4 : ℤ) = F.rho ^ (4 : ℤ) * F.a := F.a_mul_rho_zpow (-4)
      _ = F.rho ^ (-4 : ℤ) * F.a := by rw [h4]
  have ha : r * F.a = F.a * r := by
    change (F.rho ^ (-4 : ℤ) * F.a) * F.a = F.a * (F.rho ^ (-4 : ℤ) * F.a)
    calc
      (F.rho ^ (-4 : ℤ) * F.a) * F.a = F.rho ^ (-4 : ℤ) := by
        rw [mul_assoc, F.a_mul_self, mul_one]
      _ = F.a * (F.rho ^ (-4 : ℤ) * F.a) := by
        symm
        calc F.a * (F.rho ^ (-4 : ℤ) * F.a) =
            (F.a * F.rho ^ (-4 : ℤ)) * F.a := by group
          _ = (F.rho ^ (-4 : ℤ) * F.a) * F.a := by rw [haρ]
          _ = F.rho ^ (-4 : ℤ) := by rw [mul_assoc, F.a_mul_self, mul_one]
  calc
    F.alpha x * r = (T.mu 1 x.val * F.a) * r := by rw [F.alpha_def]
    _ = T.mu 1 x.val * (F.a * r) := by group
    _ = T.mu 1 x.val * (r * F.a) := by rw [← ha]
    _ = (T.mu 1 x.val * r) * F.a := by group
    _ = (r * T.mu 1 x.val) * F.a := by rw [← hm]
    _ = r * (T.mu 1 x.val * F.a) := by group
    _ = r * F.alpha x := by rw [F.alpha_def]

theorem sigmaFun_zero : F.sigmaFun 0 = 0 :=
  (Classical.choose_spec (F.exists_sigma 0)).1 rfl

theorem sigmaFun_one : F.sigmaFun 1 = 1 := by
  have hα : F.alpha (1 : F.K) = 1 := by
    rw [F.alpha_def, F.val_one]
    rw [show T.mu 1 F.e1 = F.a from rfl, F.a_mul_self]
  have hspec : F.xo 3 (F.sigmaFun 1).val = F.xo 3 F.e1 := by
    have h := F.xo_three_sigmaFun (x := (1 : F.K)) one_ne_zero
    simpa [hα] using h
  have hval : (F.sigmaFun 1).val = F.e1 :=
    (F.xo_bijOn (j := 3) (by decide)).injOn (F.sigmaFun 1).mem F.e1_mem hspec
  exact K.ext (by simpa [F.val_one] using hval)

theorem xo_ne_one {j : ℤ} (hj : Odd j) {x : F.K} (hx : x ≠ 0) :
    F.xo j x.val ≠ 1 := by
  intro h
  have h0 : F.xo j x.val = F.xo j (0 : F.K).val := by
    simpa [F.val_zero, F.xo_one_eq] using h
  have hval : x.val = (0 : F.K).val :=
    (F.xo_bijOn hj).injOn x.mem (0 : F.K).mem h0
  exact hx (F.val_eq_one_iff.mp (by simpa [F.val_zero] using hval))

theorem mu_conj_xo_seven {x : F.K} (hx : x ≠ 0) (y : F.K) :
    T.mu 1 x.val * F.xo 7 y.val * (T.mu 1 x.val)⁻¹ =
      F.xo 3 (F.sigmaFun x * y).val := by
  have hm : T.mu 1 x.val = F.alpha x * F.a := by
    calc T.mu 1 x.val = T.mu 1 x.val * (F.a * F.a) := by rw [F.a_mul_self, mul_one]
      _ = (T.mu 1 x.val * F.a) * F.a := by group
      _ = F.alpha x * F.a := by rw [F.alpha_def]
  calc
    T.mu 1 x.val * F.xo 7 y.val * (T.mu 1 x.val)⁻¹
        = (F.alpha x * F.a) * F.xo 7 y.val * (F.alpha x * F.a)⁻¹ := by rw [hm]
    _ = F.alpha x * (F.a * F.xo 7 y.val * F.a⁻¹) * (F.alpha x)⁻¹ := by group
    _ = F.alpha x * F.xo 3 y.val * (F.alpha x)⁻¹ := by
      have h := F.a_conj_xo (j := 7) (by decide) y.mem
      simpa only [show (10 : ℤ) - 7 = 3 by norm_num] using
        congrArg (fun z => F.alpha x * z * (F.alpha x)⁻¹) h
    _ = F.xo 3 (F.sigmaFun x * y).val := F.alpha_xo_three hx y

private theorem mu_seven_eq {y : F.K} (hy : y ≠ 0) :
    T.mu 7 (F.xo 7 y.val) = F.b * T.mu 1 y.val * F.b⁻¹ := by
  have hyval : y.val ≠ 1 := F.val_ne_one hy
  have hmovesb : T.Moves F.b (fun j => -1 * j + 24) := by
    simpa [sub_eq_add_neg, neg_one_mul, add_comm] using F.moves_b
  have hby : F.b * y.val * F.b⁻¹ = F.xo 7 y.val := by
    have h := F.b_conj_xo (j := 1) (by decide) y.mem
    rw [F.xo_one] at h
    rwa [show (24 : ℤ) - 1 = 7 + 16 by norm_num, F.xo_add_sixteen] at h
  have h := (T.mu_conj (by norm_num : 3 ≤ 8) (Or.inr rfl) hmovesb y.mem hyval).1
  change T.mu 23 (F.b * y.val * F.b⁻¹) = F.b * T.mu 1 y.val * F.b⁻¹ at h
  rw [hby] at h
  have h23 : T.mu 23 (F.xo 7 y.val) = T.mu 7 (F.xo 7 y.val) := by
    have h := T.mu_add_two_mul (by norm_num : 3 ≤ 8) 7 1 (F.xo 7 y.val)
    simpa [show 7 + 2 * (8 : ℤ) * 1 = 23 by norm_num] using h
  rw [← h23]
  exact h

private theorem b_inv_conj_one {x : F.K} :
    F.b⁻¹ * x.val * F.b = F.xo 7 x.val := by
  have hbinv : F.b⁻¹ = F.b := inv_eq_of_mul_eq_one_right F.b_mul_self
  have h := F.b_conj_xo (j := 1) (by decide) x.mem
  rw [F.xo_one] at h
  rw [show (24 : ℤ) - 1 = 7 + 16 by norm_num, F.xo_add_sixteen] at h
  simpa [hbinv] using h

private theorem b_conj_three {z : F.K} :
    F.b * F.xo 3 z.val * F.b⁻¹ = F.xo 5 z.val := by
  have h := F.b_conj_xo (j := 3) (by decide) z.mem
  rwa [show (24 : ℤ) - 3 = 5 + 16 by norm_num, F.xo_add_sixteen] at h

private theorem mu_seven_conj_one {y x : F.K} (hy : y ≠ 0) :
    T.mu 7 (F.xo 7 y.val) * x.val * (T.mu 7 (F.xo 7 y.val))⁻¹ =
      F.xo 5 (x * F.sigmaFun y).val := by
  rw [mu_seven_eq F hy]
  calc
    (F.b * T.mu 1 y.val * F.b⁻¹) * x.val * (F.b * T.mu 1 y.val * F.b⁻¹)⁻¹
        = F.b * (T.mu 1 y.val * (F.b⁻¹ * x.val * F.b) * (T.mu 1 y.val)⁻¹) *
            F.b⁻¹ := by group
    _ = F.b * (T.mu 1 y.val * F.xo 7 x.val * (T.mu 1 y.val)⁻¹) * F.b⁻¹ := by
      rw [b_inv_conj_one]
    _ = F.b * F.xo 3 (F.sigmaFun y * x).val * F.b⁻¹ := by
      rw [F.mu_conj_xo_seven hy x]
    _ = F.xo 5 (F.sigmaFun y * x).val := b_conj_three F
    _ = F.xo 5 (x * F.sigmaFun y).val := by rw [mul_comm (F.sigmaFun y) x]

theorem comm_xo_one_xo_seven (x y : F.K) :
    ⁅F.xo 1 x.val, F.xo 7 y.val⁆ =
      F.xo 3 (F.sigmaFun x * y).val * F.xo 5 (x * F.sigmaFun y).val := by
  by_cases hx : x = 0
  · subst hx
    simp [F.sigmaFun_zero, F.val_zero, F.xo_one_eq]
  by_cases hy : y = 0
  · subst hy
    simp [F.sigmaFun_zero, F.val_zero, F.xo_one_eq]
  have hxval : x.val ≠ 1 := F.val_ne_one hx
  have hy7 : F.xo 7 y.val ∈ T.U 7 := F.xo_mem (j := 7) (by decide) y.mem
  have hy7ne : F.xo 7 y.val ≠ 1 := F.xo_ne_one (j := 7) (by decide) hy
  have h35 := T.lemma35_iii F.hT x.mem hxval hy7 hy7ne
  rw [F.mu_conj_xo_seven hx y, F.mu_seven_conj_one (x := x) hy] at h35
  simpa [F.xo_one] using h35

private theorem comm_e_one_seven (y : F.K) :
    ⁅F.e1, F.xo 7 y.val⁆ = F.xo 3 y.val * F.xo 5 (F.sigmaFun y).val := by
  have h := F.comm_xo_one_xo_seven (1 : F.K) y
  simpa [F.val_one, F.sigmaFun_one, F.xo_one] using h

private theorem comm_expand (x y : F.K) :
    (F.xo 3 x.val * F.xo 5 (F.sigmaFun x).val) * F.xo 7 x.val *
        (F.xo 3 y.val * F.xo 5 (F.sigmaFun y).val) * (F.xo 7 x.val)⁻¹ =
      F.xo 3 (x.val * y.val) * F.xo 5 ((F.sigmaFun x).val * (F.sigmaFun y).val) := by
  have hs5 : F.xo 7 x.val * F.xo 5 (F.sigmaFun x).val =
      F.xo 5 (F.sigmaFun x).val * F.xo 7 x.val :=
    (T.comm_odd_add_two F.hT (j := 5) (by decide)
      (F.xo_mem (j := 5) (by decide) (F.sigmaFun x).mem)
      (F.xo_mem (j := 7) (by decide) x.mem)).symm
  have hs1 : F.xo 7 x.val * F.xo 3 y.val =
      F.xo 3 y.val * F.xo 7 x.val :=
    (T.comm_odd_add_four F.hT (j := 3) (by decide)
      (F.xo_mem (j := 3) (by decide) y.mem)
      (F.xo_mem (j := 7) (by decide) x.mem)).symm
  have hs5y : F.xo 7 x.val * F.xo 5 (F.sigmaFun y).val =
      F.xo 5 (F.sigmaFun y).val * F.xo 7 x.val :=
    (T.comm_odd_add_two F.hT (j := 5) (by decide)
      (F.xo_mem (j := 5) (by decide) (F.sigmaFun y).mem)
      (F.xo_mem (j := 7) (by decide) x.mem)).symm
  have h51 : F.xo 5 (F.sigmaFun x).val * F.xo 3 y.val =
      F.xo 3 y.val * F.xo 5 (F.sigmaFun x).val :=
    (T.comm_odd_add_two F.hT (j := 3) (by decide)
      (F.xo_mem (j := 3) (by decide) y.mem)
      (F.xo_mem (j := 5) (by decide) (F.sigmaFun x).mem)).symm
  calc
    (F.xo 3 x.val * F.xo 5 (F.sigmaFun x).val) * F.xo 7 x.val *
        (F.xo 3 y.val * F.xo 5 (F.sigmaFun y).val) * (F.xo 7 x.val)⁻¹
        = F.xo 3 x.val * (F.xo 5 (F.sigmaFun x).val * F.xo 7 x.val) *
            (F.xo 3 y.val * F.xo 5 (F.sigmaFun y).val) *
              (F.xo 7 x.val)⁻¹ := by group
    _ = F.xo 3 x.val * (F.xo 7 x.val * F.xo 5 (F.sigmaFun x).val) *
            (F.xo 3 y.val * F.xo 5 (F.sigmaFun y).val) *
              (F.xo 7 x.val)⁻¹ := by rw [hs5.symm]
    _ = F.xo 3 x.val * F.xo 7 x.val * F.xo 5 (F.sigmaFun x).val *
          (F.xo 3 y.val * F.xo 5 (F.sigmaFun y).val) *
            (F.xo 7 x.val)⁻¹ := by group
    _ = F.xo 3 x.val * F.xo 7 x.val *
          (F.xo 5 (F.sigmaFun x).val * F.xo 3 y.val) *
            F.xo 5 (F.sigmaFun y).val * (F.xo 7 x.val)⁻¹ := by group
    _ = F.xo 3 x.val * F.xo 7 x.val *
          (F.xo 3 y.val * F.xo 5 (F.sigmaFun x).val) *
            F.xo 5 (F.sigmaFun y).val * (F.xo 7 x.val)⁻¹ := by rw [h51]
    _ = F.xo 3 x.val * (F.xo 7 x.val * F.xo 3 y.val) *
          F.xo 5 (F.sigmaFun x).val * F.xo 5 (F.sigmaFun y).val *
            (F.xo 7 x.val)⁻¹ := by group
    _ = F.xo 3 x.val * (F.xo 3 y.val * F.xo 7 x.val) *
          F.xo 5 (F.sigmaFun x).val * F.xo 5 (F.sigmaFun y).val *
            (F.xo 7 x.val)⁻¹ := by rw [hs1]
    _ = (F.xo 3 x.val * F.xo 3 y.val) * F.xo 7 x.val *
          F.xo 5 (F.sigmaFun x).val * F.xo 5 (F.sigmaFun y).val *
            (F.xo 7 x.val)⁻¹ := by group
    _ = (F.xo 3 x.val * F.xo 3 y.val) *
          (F.xo 7 x.val * F.xo 5 (F.sigmaFun x).val) *
            F.xo 5 (F.sigmaFun y).val * (F.xo 7 x.val)⁻¹ := by group
    _ = (F.xo 3 x.val * F.xo 3 y.val) *
          (F.xo 5 (F.sigmaFun x).val * F.xo 7 x.val) *
            F.xo 5 (F.sigmaFun y).val * (F.xo 7 x.val)⁻¹ := by rw [hs5]
    _ = (F.xo 3 x.val * F.xo 3 y.val) * F.xo 5 (F.sigmaFun x).val *
          F.xo 7 x.val * F.xo 5 (F.sigmaFun y).val *
            (F.xo 7 x.val)⁻¹ := by group
    _ = (F.xo 3 x.val * F.xo 3 y.val) * F.xo 5 (F.sigmaFun x).val *
          (F.xo 7 x.val * F.xo 5 (F.sigmaFun y).val) *
            (F.xo 7 x.val)⁻¹ := by group
    _ = (F.xo 3 x.val * F.xo 3 y.val) * F.xo 5 (F.sigmaFun x).val *
          (F.xo 5 (F.sigmaFun y).val * F.xo 7 x.val) *
            (F.xo 7 x.val)⁻¹ := by rw [hs5y]
    _ = (F.xo 3 x.val * F.xo 3 y.val) *
          (F.xo 5 (F.sigmaFun x).val * F.xo 5 (F.sigmaFun y).val) *
            (F.xo 7 x.val * (F.xo 7 x.val)⁻¹) := by group
    _ = (F.xo 3 x.val * F.xo 3 y.val) *
          (F.xo 5 (F.sigmaFun x).val * F.xo 5 (F.sigmaFun y).val) := by group
    _ = F.xo 3 (x.val * y.val) *
          F.xo 5 ((F.sigmaFun x).val * (F.sigmaFun y).val) := by
          rw [← F.xo_mul, ← F.xo_mul]

theorem sigmaFun_add (x y : F.K) : F.sigmaFun (x + y) = F.sigmaFun x + F.sigmaFun y := by
  have hx := F.comm_e_one_seven x
  have hy := F.comm_e_one_seven y
  have hsum : F.xo 7 (x + y).val = F.xo 7 x.val * F.xo 7 y.val := by
    rw [F.val_add, F.xo_mul]
  have hcomp : ⁅F.e1, F.xo 7 x.val * F.xo 7 y.val⁆ =
      F.xo 3 (x.val * y.val) * F.xo 5 ((F.sigmaFun x).val * (F.sigmaFun y).val) := by
    have hexp : ⁅F.e1, F.xo 7 x.val * F.xo 7 y.val⁆ =
        (F.xo 3 x.val * F.xo 5 (F.sigmaFun x).val) * F.xo 7 x.val *
          (F.xo 3 y.val * F.xo 5 (F.sigmaFun y).val) * (F.xo 7 x.val)⁻¹ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hx, hy]
    rw [hexp, F.comm_expand]
  have h1 : ⁅F.e1, F.xo 7 x.val * F.xo 7 y.val⁆ =
      F.xo 3 (x.val * y.val) * F.xo 5 (F.sigmaFun (x + y)).val := by
    have h := F.comm_e_one_seven (x + y)
    rw [hsum] at h
    simpa [F.val_add] using h
  have hleft : F.xo 3 (x.val * y.val) * F.xo 5 (F.sigmaFun (x + y)).val =
      F.xo 3 (x.val * y.val) * F.xo 5 ((F.sigmaFun x).val * (F.sigmaFun y).val) := by
    rw [← h1, hcomp]
  have h5 : F.xo 5 (F.sigmaFun (x + y)).val =
      F.xo 5 ((F.sigmaFun x).val * (F.sigmaFun y).val) := mul_left_cancel hleft
  have h5' : F.xo 5 (F.sigmaFun (x + y)).val =
      F.xo 5 (F.sigmaFun x + F.sigmaFun y).val := by
    simpa [F.val_add] using h5
  have hval : (F.sigmaFun (x + y)).val = (F.sigmaFun x + F.sigmaFun y).val := by
    have h := (F.xo_bijOn (j := 5) (by decide)).injOn (F.sigmaFun (x + y)).mem
      (F.sigmaFun x + F.sigmaFun y).mem h5'
    simpa [F.val_add] using h
  exact K.ext hval

theorem sigmaFun_mul (x y : F.K) : F.sigmaFun (x * y) = F.sigmaFun x * F.sigmaFun y := by
  by_cases hx : x = 0
  · subst hx
    simp [F.sigmaFun_zero]
  by_cases hy : y = 0
  · subst hy
    simp [F.sigmaFun_zero]
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have h1 := F.xo_three_sigmaFun (x := x * y) hxy
  have hm := F.alpha_mul_conj hx hy (j := 3) (by decide)
    (F.xo_mem (j := 3) (by decide) F.e1_mem)
  have hα : F.alpha x * F.alpha y * F.xo 3 F.e1 * (F.alpha x * F.alpha y)⁻¹ =
      F.xo 3 (F.sigmaFun x * F.sigmaFun y).val := by
    calc
      (F.alpha x * F.alpha y) * F.xo 3 F.e1 * (F.alpha x * F.alpha y)⁻¹
          = F.alpha x * (F.alpha y * F.xo 3 F.e1 * (F.alpha y)⁻¹) *
              (F.alpha x)⁻¹ := by group
      _ = F.alpha x * F.xo 3 (F.sigmaFun y).val * (F.alpha x)⁻¹ := by
        simpa [F.val_one] using F.alpha_xo_three hy (1 : F.K)
      _ = F.xo 3 (F.sigmaFun x * F.sigmaFun y).val :=
        F.alpha_xo_three hx (F.sigmaFun y)
  have hval : (F.sigmaFun (x * y)).val = (F.sigmaFun x * F.sigmaFun y).val := by
    have heq : F.xo 3 (F.sigmaFun (x * y)).val =
        F.xo 3 (F.sigmaFun x * F.sigmaFun y).val := by
      rw [h1, hm, hα]
    exact (F.xo_bijOn (j := 3) (by decide)).injOn (F.sigmaFun (x * y)).mem
      (F.sigmaFun x * F.sigmaFun y).mem heq
  exact K.ext hval

private theorem mu_eq_alpha_mul_a {x : F.K} (hx : x ≠ 0) :
    T.mu 1 x.val = F.alpha x * F.a := by
  calc T.mu 1 x.val = T.mu 1 x.val * (F.a * F.a) := by rw [F.a_mul_self, mul_one]
    _ = (T.mu 1 x.val * F.a) * F.a := by group
    _ = F.alpha x * F.a := by rw [F.alpha_def]

private theorem mu_x_conj_e7 {x : F.K} (hx : x ≠ 0)
    (s : F.K) (hs : F.xo 3 s.val = F.alpha x * F.xo 3 F.e1 * (F.alpha x)⁻¹) :
    T.mu 1 x.val * T.mu 7 (F.xo 7 F.e1) * (T.mu 1 x.val)⁻¹ =
      T.mu 3 (F.xo 3 s.val) := by
  have hxval : x.val ≠ 1 := F.val_ne_one hx
  have hs3 : F.xo 3 s.val = T.mu 1 x.val * F.xo 7 F.e1 * (T.mu 1 x.val)⁻¹ := by
    calc F.xo 3 s.val = F.alpha x * F.xo 3 F.e1 * (F.alpha x)⁻¹ := hs
      _ = (T.mu 1 x.val * F.a) * F.xo 3 F.e1 * (T.mu 1 x.val * F.a)⁻¹ := by
        rw [F.alpha_def]
      _ = T.mu 1 x.val * (F.a * F.xo 3 F.e1 * F.a⁻¹) * (T.mu 1 x.val)⁻¹ := by group
      _ = T.mu 1 x.val * F.xo 7 F.e1 * (T.mu 1 x.val)⁻¹ := by
        have h := F.a_conj_xo (j := 3) (by decide) F.e1_mem
        simpa only [show (10 : ℤ) - 3 = 7 by norm_num] using
          congrArg (fun z => T.mu 1 x.val * z * (T.mu 1 x.val)⁻¹) h
  have hmovesx : T.Moves (T.mu 1 x.val) (fun j => -1 * j + 10) := by
    have h := T.moves_mu x.mem hxval
    intro j
    have h' := h j
    change (T.U j).map (MulAut.conj (T.mu 1 x.val)).toMonoidHom =
      T.U (2 * (1 : ℤ) + (8 : ℕ) - j) at h'
    rw [show 2 * (1 : ℤ) + (8 : ℕ) - j = -1 * j + 10 by ring] at h'
    exact h'
  have he7ne : F.xo 7 F.e1 ≠ 1 := by
    have h := F.xo_ne_one (j := 7) (by decide) (x := (1 : F.K)) one_ne_zero
    simpa [F.val_one] using h
  have h := (T.mu_conj (by norm_num : 3 ≤ 8) (Or.inr rfl) hmovesx
    (F.xo_mem (j := 7) (by decide) F.e1_mem) he7ne).1
  change T.mu 3 (T.mu 1 x.val * F.xo 7 F.e1 * (T.mu 1 x.val)⁻¹) =
    T.mu 1 x.val * T.mu 7 (F.xo 7 F.e1) * (T.mu 1 x.val)⁻¹ at h
  rw [← hs3] at h
  exact h.symm

private theorem mu_seven_e7 :
    T.mu 7 (F.xo 7 F.e1) = F.rho ^ (6 : ℤ) * F.a := by
  have hmovesrho : T.Moves (F.rho ^ (3 : ℤ)) (fun j => 1 * j + 6) := by
    simpa using F.moves_rho_zpow (3 : ℤ)
  have h := (T.mu_conj (by norm_num : 3 ≤ 8) (Or.inl rfl) hmovesrho
    F.e1_mem F.e1_ne).1
  have hconj : F.rho ^ (3 : ℤ) * F.e1 * (F.rho ^ (3 : ℤ))⁻¹ = F.xo 7 F.e1 := by
    have h := F.rho_zpow_conj_xo (3 : ℤ) (1 : ℤ) F.e1
    rw [F.xo_one] at h
    rwa [show (1 : ℤ) + 2 * 3 = 7 by norm_num] at h
  change T.mu (1 + 6) (F.rho ^ (3 : ℤ) * F.e1 * (F.rho ^ (3 : ℤ))⁻¹) =
    F.rho ^ (3 : ℤ) * F.a * (F.rho ^ (3 : ℤ))⁻¹ at h
  rw [hconj] at h
  have hrho : F.rho ^ (3 : ℤ) * F.a * (F.rho ^ (3 : ℤ))⁻¹ =
      F.rho ^ (6 : ℤ) * F.a := by
    have ha : F.a * F.rho ^ (-3 : ℤ) = F.rho ^ (3 : ℤ) * F.a := F.a_mul_rho_zpow (-3)
    calc F.rho ^ (3 : ℤ) * F.a * (F.rho ^ (3 : ℤ))⁻¹
        = F.rho ^ (3 : ℤ) * (F.a * F.rho ^ (-3 : ℤ)) := by group
      _ = F.rho ^ (3 : ℤ) * (F.rho ^ (3 : ℤ) * F.a) := by rw [ha]
      _ = F.rho ^ (6 : ℤ) * F.a := by
        rw [← mul_assoc, ← zpow_add]
        norm_num
  rw [hrho] at h
  exact h

private theorem mu_seven_conj_em3 :
    T.mu 7 (F.xo 7 F.e1) * F.xo (-3) F.e1 * (T.mu 7 (F.xo 7 F.e1))⁻¹ =
      F.xo 9 F.e1 := by
  rw [mu_seven_e7 F]
  have h := F.rho_zpow_a_conj_xo (6 : ℤ) (j := -3) (by decide) F.e1_mem
  rw [show (10 : ℤ) + 2 * 6 - (-3) = 9 + 16 by norm_num, F.xo_add_sixteen] at h
  exact h

private theorem mu_x_conj_e9 {x : F.K} (hx : x ≠ 0) (s : F.K)
    (hs : F.xo 3 s.val = F.alpha x * F.xo 3 F.e1 * (F.alpha x)⁻¹) :
    T.mu 1 x.val * F.xo 9 F.e1 * (T.mu 1 x.val)⁻¹ =
      T.mu 3 (F.xo 3 s.val) * F.xo (-3) F.e1 *
        (T.mu 3 (F.xo 3 s.val))⁻¹ := by
  have hstep1 := mu_x_conj_e7 F hx s hs
  have hxcomm' : (T.mu 1 x.val)⁻¹ * F.xo (-3) F.e1 * T.mu 1 x.val =
      F.xo (-3) F.e1 := by
    have h := T.mu_one_comm' F.hT x.mem (F.val_ne_one hx)
      (F.xo_mem (j := -3) (by decide) F.e1_mem)
    calc
      (T.mu 1 x.val)⁻¹ * F.xo (-3) F.e1 * T.mu 1 x.val
          = (T.mu 1 x.val)⁻¹ * (F.xo (-3) F.e1 * T.mu 1 x.val) := by group
      _ = (T.mu 1 x.val)⁻¹ * (T.mu 1 x.val * F.xo (-3) F.e1) := by rw [← h]
      _ = F.xo (-3) F.e1 := by group
  have hconj := mu_seven_conj_em3 F
  have hconv : (T.mu 1 x.val * T.mu 7 (F.xo 7 F.e1) * (T.mu 1 x.val)⁻¹) *
        F.xo (-3) F.e1 *
          (T.mu 1 x.val * T.mu 7 (F.xo 7 F.e1) * (T.mu 1 x.val)⁻¹)⁻¹ =
      T.mu 1 x.val * (T.mu 7 (F.xo 7 F.e1) * F.xo (-3) F.e1 *
        (T.mu 7 (F.xo 7 F.e1))⁻¹) * (T.mu 1 x.val)⁻¹ := by
    calc
      (T.mu 1 x.val * T.mu 7 (F.xo 7 F.e1) * (T.mu 1 x.val)⁻¹) *
          F.xo (-3) F.e1 *
            (T.mu 1 x.val * T.mu 7 (F.xo 7 F.e1) * (T.mu 1 x.val)⁻¹)⁻¹
          = T.mu 1 x.val * (T.mu 7 (F.xo 7 F.e1) *
              ((T.mu 1 x.val)⁻¹ * F.xo (-3) F.e1 * T.mu 1 x.val) *
                (T.mu 7 (F.xo 7 F.e1))⁻¹) * (T.mu 1 x.val)⁻¹ := by group
      _ = T.mu 1 x.val * (T.mu 7 (F.xo 7 F.e1) * F.xo (-3) F.e1 *
            (T.mu 7 (F.xo 7 F.e1))⁻¹) * (T.mu 1 x.val)⁻¹ := by rw [hxcomm']
  calc
    T.mu 1 x.val * F.xo 9 F.e1 * (T.mu 1 x.val)⁻¹
        = T.mu 1 x.val * (T.mu 7 (F.xo 7 F.e1) * F.xo (-3) F.e1 *
            (T.mu 7 (F.xo 7 F.e1))⁻¹) * (T.mu 1 x.val)⁻¹ := by rw [← hconj]
    _ = (T.mu 1 x.val * T.mu 7 (F.xo 7 F.e1) * (T.mu 1 x.val)⁻¹) *
          F.xo (-3) F.e1 *
            (T.mu 1 x.val * T.mu 7 (F.xo 7 F.e1) * (T.mu 1 x.val)⁻¹)⁻¹ := hconv.symm
    _ = T.mu 3 (F.xo 3 s.val) * F.xo (-3) F.e1 *
          (T.mu 3 (F.xo 3 s.val))⁻¹ := by rw [hstep1]
private theorem mu_x_conj_e9_eq {x : F.K} (hx : x ≠ 0) :
    T.mu 1 x.val * F.xo 9 F.e1 * (T.mu 1 x.val)⁻¹ = F.xo 1 (x ^ 2).val := by
  rw [mu_eq_alpha_mul_a F hx]
  calc
    (F.alpha x * F.a) * F.xo 9 F.e1 * (F.alpha x * F.a)⁻¹
        = F.alpha x * (F.a * F.xo 9 F.e1 * F.a⁻¹) * (F.alpha x)⁻¹ := by group
    _ = F.alpha x * F.xo 1 F.e1 * (F.alpha x)⁻¹ := by
      have h := F.a_conj_xo (j := 9) (by decide) F.e1_mem
      simpa only [show (10 : ℤ) - 9 = 1 by norm_num] using
        congrArg (fun z => F.alpha x * z * (F.alpha x)⁻¹) h
    _ = F.alpha x * F.xo 1 (1 : F.K).val * (F.alpha x)⁻¹ := by rw [F.val_one]
    _ = F.xo 1 (x ^ 2 * 1).val := F.alpha_xo_one hx (1 : F.K)
    _ = F.xo 1 (x ^ 2).val := by rw [mul_one]

private theorem g_mul_self :
    (F.rho ^ (-3 : ℤ) * F.a) * (F.rho ^ (-3 : ℤ) * F.a) = 1 := by
  have ha : F.a * F.rho ^ (-3 : ℤ) = F.rho ^ (3 : ℤ) * F.a := F.a_mul_rho_zpow (-3)
  calc
    (F.rho ^ (-3 : ℤ) * F.a) * (F.rho ^ (-3 : ℤ) * F.a)
        = F.rho ^ (-3 : ℤ) * (F.a * F.rho ^ (-3 : ℤ)) * F.a := by group
    _ = F.rho ^ (-3 : ℤ) * (F.rho ^ (3 : ℤ) * F.a) * F.a := by rw [ha]
    _ = (F.rho ^ (-3 : ℤ) * F.rho ^ (3 : ℤ)) * (F.a * F.a) := by group
    _ = 1 := by
      rw [← zpow_add, F.a_mul_self]
      norm_num

private theorem g_inv :
    (F.rho ^ (-3 : ℤ) * F.a)⁻¹ = F.rho ^ (-3 : ℤ) * F.a :=
  inv_eq_of_mul_eq_one_right (g_mul_self F)

private theorem g_conj_xo {j : ℤ} (hj : Odd j) {x : G} (hx : x ∈ T.U 1) :
    (F.rho ^ (-3 : ℤ) * F.a) * F.xo j x * (F.rho ^ (-3 : ℤ) * F.a)⁻¹ =
      F.xo (4 - j) x := by
  have h := F.rho_zpow_a_conj_xo (-3 : ℤ) hj hx
  simpa only [show (10 : ℤ) + 2 * (-3) - j = 4 - j by ring] using h

private theorem mu_s3_conj_em3 {x : F.K} (hx : x ≠ 0) :
    T.mu 3 (F.xo 3 (F.sigmaFun x).val) * F.xo (-3) F.e1 *
      (T.mu 3 (F.xo 3 (F.sigmaFun x).val))⁻¹ =
      F.xo 1 (F.sigmaFun (F.sigmaFun x)).val := by
  let g : G := F.rho ^ (-3 : ℤ) * F.a
  have hs : F.sigmaFun x ≠ 0 := F.sigmaFun_ne_zero hx
  have hsval : (F.sigmaFun x).val ≠ 1 := F.val_ne_one hs
  have hmovesg : T.Moves g (fun j => -1 * j + 4) := by
    have h := F.moves_rho_zpow_a (-3 : ℤ)
    intro j
    have h' := h j
    change (T.U j).map (MulAut.conj (F.rho ^ (-3 : ℤ) * F.a)).toMonoidHom =
      T.U (10 + 2 * (-3 : ℤ) - j) at h'
    rw [show 10 + 2 * (-3 : ℤ) - j = -1 * j + 4 by ring] at h'
    simpa [g] using h'
  have hg_s : g * (F.sigmaFun x).val * g⁻¹ = F.xo 3 (F.sigmaFun x).val := by
    simpa [g, F.xo_one] using g_conj_xo F (j := 1) (by decide) (F.sigmaFun x).mem
  have hms3 : T.mu 3 (F.xo 3 (F.sigmaFun x).val) =
      g * T.mu 1 (F.sigmaFun x).val * g⁻¹ := by
    have h := (T.mu_conj (by norm_num : 3 ≤ 8) (Or.inr rfl) hmovesg
      (F.sigmaFun x).mem hsval).1
    change T.mu 3 (g * (F.sigmaFun x).val * g⁻¹) =
      g * T.mu 1 (F.sigmaFun x).val * g⁻¹ at h
    rw [hg_s] at h
    exact h
  have hg_em3 : g * F.xo (-3) F.e1 * g⁻¹ = F.xo 7 F.e1 := by
    simpa [g] using g_conj_xo F (j := -3) (by decide) F.e1_mem
  have hg_inv : g⁻¹ = g := by
    simpa [g] using g_inv F
  have hg_em3' : g⁻¹ * F.xo (-3) F.e1 * g = F.xo 7 F.e1 := by
    simpa [hg_inv] using hg_em3
  have hg_xo3 : g * F.xo 3 (F.sigmaFun (F.sigmaFun x)).val * g⁻¹ =
      F.xo 1 (F.sigmaFun (F.sigmaFun x)).val := by
    simpa [g] using g_conj_xo F (j := 3) (by decide) (F.sigmaFun (F.sigmaFun x)).mem
  rw [hms3]
  calc
    (g * T.mu 1 (F.sigmaFun x).val * g⁻¹) * F.xo (-3) F.e1 *
        (g * T.mu 1 (F.sigmaFun x).val * g⁻¹)⁻¹
        = g * (T.mu 1 (F.sigmaFun x).val * (g⁻¹ * F.xo (-3) F.e1 * g) *
            (T.mu 1 (F.sigmaFun x).val)⁻¹) * g⁻¹ := by group
    _ = g * (T.mu 1 (F.sigmaFun x).val * F.xo 7 F.e1 *
          (T.mu 1 (F.sigmaFun x).val)⁻¹) * g⁻¹ := by rw [hg_em3']
    _ = g * F.xo 3 (F.sigmaFun (F.sigmaFun x)).val * g⁻¹ := by
      rw [show T.mu 1 (F.sigmaFun x).val * F.xo 7 F.e1 *
            (T.mu 1 (F.sigmaFun x).val)⁻¹ =
          F.xo 3 (F.sigmaFun (F.sigmaFun x)).val by
        simpa [F.val_one, mul_one] using F.mu_conj_xo_seven hs (1 : F.K)]
    _ = F.xo 1 (F.sigmaFun (F.sigmaFun x)).val := hg_xo3

theorem sigmaFun_sigmaFun (x : F.K) : F.sigmaFun (F.sigmaFun x) = x ^ 2 := by
  by_cases hx : x = 0
  · subst hx
    simp [F.sigmaFun_zero]
  have hstep := mu_x_conj_e9 F hx (F.sigmaFun x) (F.xo_three_sigmaFun hx)
  have hleft := mu_x_conj_e9_eq F hx
  have hright := mu_s3_conj_em3 F hx
  have heq : F.xo 1 (x ^ 2).val = F.xo 1 (F.sigmaFun (F.sigmaFun x)).val := by
    rw [← hleft, hstep, hright]
  have hval : (x ^ 2).val = (F.sigmaFun (F.sigmaFun x)).val :=
    (F.xo_bijOn (j := 1) (by decide)).injOn (x ^ 2).mem
      (F.sigmaFun (F.sigmaFun x)).mem heq
  exact K.ext hval.symm

@[expose] noncomputable def sigma : F.K →+* F.K where
  toFun := F.sigmaFun
  map_one' := F.sigmaFun_one
  map_mul' := F.sigmaFun_mul
  map_zero' := F.sigmaFun_zero
  map_add' := F.sigmaFun_add

theorem sigma_apply (x : F.K) : F.sigma x = F.sigmaFun x := rfl

theorem sigma_sigma (x : F.K) : F.sigma (F.sigma x) = x ^ 2 :=
  F.sigmaFun_sigmaFun x
