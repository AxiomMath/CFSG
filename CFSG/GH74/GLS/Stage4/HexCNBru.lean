module

public import CFSG.GH74.GLS.Stage4.HexCNWin

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Steinberg
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G}

theorem Vsub_norm_one (R : RGD2 6 H r₁ r₂ U root) {j : ℤ} (hj : j ≤ 6) {a : G} (ha : a ∈ root 1)
    {v : G} (hv : v ∈ Vsub root 2 j) : a * v * a⁻¹ ∈ Vsub root 2 j :=
  Vsub_norm_left R (i := 2) (j := j) (by norm_num) hj (by simpa using ha) hv

theorem r1_mem_Vsub (R : RGD2 6 H r₁ r₂ U root) {k j : ℤ} (hk : 2 ≤ k) (hj : j ≤ 6) {v : G}
    (hv : v ∈ Vsub root k j) : r₁ * v * r₁⁻¹ ∈ Vsub root (8 - j) (8 - k) := by
  refine conj_mem_of_forall_mem (P := {m | m ∈ intList k j}) (X := root)
    (M := Vsub root (8 - j) (8 - k)) (fun m hm y hy => ?_) hv
  have hm' := mem_intList_iff.1 hm
  have := (RGD2.mem_iff_r₁ R (i := m) (by omega) (by omega) y).1 hy
  exact root_le_Vsub (by omega) (by omega) this

theorem r1_inv_mem_Vsub (R : RGD2 6 H r₁ r₂ U root) {k j : ℤ} (hk : 2 ≤ k) (hj : j ≤ 6) {v : G}
    (hv : v ∈ Vsub root k j) : r₁⁻¹ * v * r₁ ∈ Vsub root (8 - j) (8 - k) := by
  have gen : ∀ m ∈ {m : ℤ | m ∈ intList k j}, ∀ y ∈ root m,
      r₁⁻¹ * y * r₁⁻¹⁻¹ ∈ Vsub root (8 - j) (8 - k) := by
    intro m hm y hy
    have hm' := mem_intList_iff.1 hm
    have h6 : 8 - (8 - m) = m := by omega
    have h2 := (RGD2.mem_iff_r₁ R (i := 8 - m) (by omega) (by omega) (r₁⁻¹ * y * r₁)).2
    rw [h6] at h2
    have h3 : r₁ * (r₁⁻¹ * y * r₁) * r₁⁻¹ = y := by group
    rw [h3] at h2
    have hmem : r₁⁻¹ * y * r₁⁻¹⁻¹ ∈ root (8 - m) := by simpa using h2 hy
    exact root_le_Vsub (i := 8 - j) (j := 8 - k) (k := 8 - m) (by omega) (by omega) hmem
  simpa using conj_mem_of_forall_mem (P := {m | m ∈ intList k j}) (X := root) gen hv

theorem exists_conj_r1_of_mem_neg (R : RGD2 6 H r₁ r₂ U root) {b : G} (hb : b ∈ root (-1)) :
    ∃ a ∈ root 1, b = r₁⁻¹ * a * r₁ := by
  have h := (mem_iff_conj_of_conjBy (m := r₁) (A := root (-1)) (B := root 1)
    (by simpa using R.act₁.2.1) b).1 hb
  exact ⟨r₁ * b * r₁⁻¹, h, by group⟩

theorem Vsub_norm_negOne (R : RGD2 6 H r₁ r₂ U root) {k : ℤ} (hk2 : 2 ≤ k) (hk6 : k ≤ 6) {b : G}
    (hb : b ∈ root (-1)) {v : G} (hv : v ∈ Vsub root k 6) : b * v * b⁻¹ ∈ Vsub root k 6 := by
  obtain ⟨a, ha, rfl⟩ := exists_conj_r1_of_mem_neg R hb
  have h1 := r1_mem_Vsub R hk2 le_rfl hv
  have h2 := Vsub_norm_one R (j := 8 - k) (by omega) ha h1
  have h3 := r1_inv_mem_Vsub R (k := 2) (j := 8 - k) le_rfl (by omega) h2
  have e : 8 - (8 - k) = k := by omega
  have e' : 8 - (2 : ℤ) = 6 := by norm_num
  rw [e, e'] at h3
  have e2 : r₁⁻¹ * a * r₁ * v * (r₁⁻¹ * a * r₁)⁻¹ =
      r₁⁻¹ * (a * (r₁ * v * r₁⁻¹) * a⁻¹) * r₁ := by group
  rw [e2]
  exact h3



theorem sl2Wc_eq_mul {F : Type*} [Field F] (t : Fˣ) : sl2Wc (t : F) = sl2D t * sl2W F := by
  apply sl2_ext
  rw [coe_sl2Wc t.ne_zero, Matrix.SpecialLinearGroup.coe_mul, coe_sl2D, coe_sl2W]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem actsPos_weylOne (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 1)
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a) :
    ActsPos 6 root (E.φ (sl2W E.F)) (fun q => 6 - q) := by
  classical
  set n := E.φ (sl2W E.F) with hn_def
  have hn : n ∈ R.N := E.hW
  obtain ⟨f, g, hf, hg, hactf, hactg⟩ := R.goodAct_of_mem_N hn
  have hn1 : n ∈ root 1 ⊔ root (-1) := by
    rw [hn_def, sl2W_eq_sl2Wc]
    simp only [sl2Wc, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (sl2Pos_U_mem E _))
      (Subgroup.mem_sup_right (sl2Pos_L_mem E _))) (Subgroup.mem_sup_left (sl2Pos_U_mem E _))
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ root 4, x ≠ 1 := by
    have h := R.ne_bot 4 (isRoot_of_pos_le (by norm_num) (by norm_num))
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h
    exact ⟨x, hx, fun h' => hx1 (Subtype.ext h')⟩
  have hxfix : n * x * n⁻¹ = x := by
    have := hO n hn1 x (Subgroup.mem_sup_left hx)
    rw [mul_inv_eq_iff_eq_mul]; exact this
  have hy : E.φ (sl2U (1 : E.F)) ∈ root 1 := sl2Pos_U_mem E 1
  have hyn : n * E.φ (sl2U (1 : E.F)) * n⁻¹ = E.φ (sl2L (-1)) := by
    rw [mul_inv_eq_iff_eq_mul, hn_def, ← map_mul, ← map_mul, sl2W_mul_sl2U]
  have hyn' : n * E.φ (sl2U (1 : E.F)) * n⁻¹ ∈ root (-1) := hyn ▸ sl2Pos_L_mem E (-1)
  have hRt0 : Rt 6 0 = 1 := (Rt6_eq_pos (q := 0) (by norm_num) (by norm_num)).2 (by norm_num)
  have hRt3 : Rt 6 3 = 4 := (Rt6_eq_pos (q := 3) (by norm_num) (by norm_num)).2 (by norm_num)
  have hx' : x ∈ root (Rt 6 3) := by rw [hRt3]; exact hx
  have hxn : n * x * n⁻¹ ∈ root 4 := by rw [hxfix]; exact hx
  have hy' : E.φ (sl2U (1 : E.F)) ∈ root (Rt 6 0) := by rw [hRt0]; exact hy
  have h3 := actsPos_eq_of_conj R hactf (q := 3) (b := 4) ⟨by norm_num, by norm_num⟩
    hx' hx1 hxn
  have h0 := actsPos_eq_of_conj R hactf (q := 0) (b := -1) ⟨by norm_num, by norm_num⟩ hy'
    (sl2Pos_U_ne_one E) hyn'
  rw [Rt6_eq_pos (by norm_num) (by norm_num)] at h3
  rw [Rt6_eq_neg (by norm_num) (by norm_num)] at h0
  rcases hf with ⟨c, hc⟩ | ⟨c, hc⟩
  · exfalso
    rw [hc] at h0 h3
    omega
  · have hq : ∀ q, Rt 6 (f q) = Rt 6 (6 - q) := fun q => by
      apply Rt_congr
      rw [hc q]
      rw [hc 0] at h0
      simp only [Nat.cast_ofNat]
      omega
    intro q z hz
    have := hactf q z hz
    rwa [hq q] at this


theorem weylOne_conj (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 1)
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a) {i : ℤ} (hi2 : 2 ≤ i)
    (hi6 : i ≤ 6) {x : G} (hx : x ∈ root i) :
    E.φ (sl2W E.F) * x * (E.φ (sl2W E.F))⁻¹ ∈ root (8 - i) := by
  have hx' : x ∈ root (Rt 6 (i - 1)) := by
    rw [Rt_of_lt (by omega) (by omega)]
    simpa using hx
  have := actsPos_weylOne R E hO (i - 1) x hx'
  simp only at this
  rwa [Rt_of_lt (by omega) (by omega), show 6 - (i - 1) + 1 = 8 - i by ring] at this

theorem weylOne_mul_self (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 1) :
    E.φ (sl2W E.F) * E.φ (sl2W E.F) ∈ H := by
  rw [← map_mul, sl2W_mul_self]
  exact E.hD (-1)

theorem weylOne_conj_inv (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 1)
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a) {i : ℤ} (hi2 : 2 ≤ i)
    (hi6 : i ≤ 6) {x : G} (hx : x ∈ root i) :
    (E.φ (sl2W E.F))⁻¹ * x * E.φ (sl2W E.F) ∈ root (8 - i) := by
  set n := E.φ (sl2W E.F) with hn
  have hh : (n * n)⁻¹ ∈ H := H.inv_mem (weylOne_mul_self R E)
  have hx1 : (n * n)⁻¹ * x * ((n * n)⁻¹)⁻¹ ∈ root i :=
    R.invariant i (isRoot_of_pos_le (by omega) hi6) _ hh x hx
  have h2 := weylOne_conj R E hO hi2 hi6 hx1
  have e : n * ((n * n)⁻¹ * x * ((n * n)⁻¹)⁻¹) * n⁻¹ = n⁻¹ * x * n := by group
  rwa [e] at h2

theorem exists_bruhat_root1 {N : Subgroup G} (E : SL2Pos H N root 1) {a : G} (ha : a ∈ root 1)
    (ha1 : a ≠ 1) :
    ∃ b ∈ root (-1), ∃ h ∈ H, a * b * a = h * E.φ (sl2W E.F) := by
  obtain ⟨s, hs⟩ := (E.hU a).1 ha
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply ha1
    rw [← hs, sl2U_zero, map_one]
  refine ⟨E.φ (sl2L (-s⁻¹)), sl2Pos_L_mem E _, E.φ (sl2D (Units.mk0 s hs0)), E.hD _, ?_⟩
  have hW : sl2U s * sl2L (-s⁻¹) * sl2U s = sl2D (Units.mk0 s hs0) * sl2W E.F := by
    have := sl2Wc_eq_mul (F := E.F) (Units.mk0 s hs0)
    simpa [sl2Wc] using this
  calc a * E.φ (sl2L (-s⁻¹)) * a = E.φ (sl2U s * sl2L (-s⁻¹) * sl2U s) := by
        rw [← hs]; simp only [map_mul]
    _ = E.φ (sl2D (Units.mk0 s hs0)) * E.φ (sl2W E.F) := by rw [hW, map_mul]

theorem bruhat_conj {a b h n : G} (hbru : a * b * a = h * n) (g : G) :
    (a * b * a) * g * (a * b * a)⁻¹ = h * (n * g * n⁻¹) * h⁻¹ := by
  rw [hbru]; group

theorem ne_one_conj {h n x : G} (hx1 : x ≠ 1) : h * (n * x * n⁻¹) * h⁻¹ ≠ 1 := by
  intro h1
  apply hx1
  have h2 : n * x * n⁻¹ = 1 := by
    have := congrArg (fun y => h⁻¹ * y * h) h1
    simpa [mul_assoc] using this
  simpa [mul_inv_eq_one] using h2

theorem bru_comm16_not_mem_V35 (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 1)
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a)
    {a x : G} (ha : a ∈ root 1) (ha1 : a ≠ 1) (hx : x ∈ root 6) (hx1 : x ≠ 1) :
    ⁅a, x⁆ ∉ Vsub root 3 5 := by
  intro hv
  obtain ⟨b, hb, h, hh, hbru⟩ := exists_bruhat_root1 E ha ha1
  set n := E.φ (sl2W E.F) with hn
  have hx2 : n * x * n⁻¹ ∈ root 2 := by
    have := weylOne_conj R E hO (i := 6) (by norm_num) le_rfl hx
    simpa using this
  set x₂ := h * (n * x * n⁻¹) * h⁻¹ with hx₂def
  have hx₂ : x₂ ∈ root 2 := R.invariant 2 (isRoot_of_pos_le (by norm_num) (by norm_num)) h hh _ hx2
  have hx₂1 : x₂ ≠ 1 := ne_one_conj hx1
  have hw : a * x * a⁻¹ ∈ Vsub root 3 6 := by
    have e : a * x * a⁻¹ = ⁅a, x⁆ * x := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact Subgroup.mul_mem _ (Vsub_mono (by norm_num) (by norm_num) hv)
      (root_le_Vsub (by norm_num) le_rfl hx)
  have hw' := Vsub_norm_negOne R (k := 3) (by norm_num) (by norm_num) hb hw
  have e1 : (a * b * a) * x * (a * b * a)⁻¹ = x₂ := bruhat_conj hbru x
  have e2 : a * (b * (a * x * a⁻¹) * b⁻¹) * a⁻¹ = x₂ := by rw [← e1]; group
  have hc : a * x₂ = x₂ * a :=
    rgd2_comm_adj R (a := 1) (by norm_num) (by norm_num) ha (by simpa using hx₂)
  have h2 : a⁻¹ * x₂ * a = x₂ := by
    calc a⁻¹ * x₂ * a = a⁻¹ * (x₂ * a) := by group
      _ = a⁻¹ * (a * x₂) := by rw [hc]
      _ = x₂ := by group
  have e3 : b * (a * x * a⁻¹) * b⁻¹ = x₂ := by
    calc b * (a * x * a⁻¹) * b⁻¹ = a⁻¹ * (a * (b * (a * x * a⁻¹) * b⁻¹) * a⁻¹) * a := by group
      _ = a⁻¹ * x₂ * a := by rw [e2]
      _ = x₂ := h2
  rw [e3] at hw'
  exact hx₂1 (eq_one_of_mem_root2_Vsub36 R hx₂ hw')

theorem bru_comm15_ne_one (R : RGD2 6 H r₁ r₂ U root) (E : SL2Pos H R.N root 1)
    (hO : ∀ a ∈ root 1 ⊔ root (-1), ∀ b ∈ root 4 ⊔ root (-4), a * b = b * a)
    {a y : G} (ha : a ∈ root 1) (ha1 : a ≠ 1) (hy : y ∈ root 5) (hy1 : y ≠ 1) :
    ⁅a, y⁆ ≠ 1 := by
  intro hcomm
  have hay : a * y = y * a := commutatorElement_eq_one_iff_mul_comm.1 hcomm
  obtain ⟨b, hb, h, hh, hbru⟩ := exists_bruhat_root1 E ha ha1
  set n := E.φ (sl2W E.F) with hn
  have hy3 : n * y * n⁻¹ ∈ root 3 := by
    have := weylOne_conj R E hO (i := 5) (by norm_num) (by norm_num) hy
    simpa using this
  set y₃ := h * (n * y * n⁻¹) * h⁻¹ with hy₃def
  have hy₃ : y₃ ∈ root 3 := R.invariant 3 (isRoot_of_pos_le (by norm_num) (by norm_num)) h hh _ hy3
  have hy₃1 : y₃ ≠ 1 := ne_one_conj hy1
  have hay' : a * y * a⁻¹ = y := by
    rw [mul_inv_eq_iff_eq_mul]; exact hay
  have hby : b * y * b⁻¹ ∈ Vsub root 5 6 :=
    Vsub_norm_negOne R (k := 5) (by norm_num) (by norm_num) hb
      (root_le_Vsub (by norm_num) (by norm_num) hy)
  have e1 : (a * b * a) * y * (a * b * a)⁻¹ = y₃ := bruhat_conj hbru y
  have e2 : a * (b * y * b⁻¹) * a⁻¹ = y₃ := by
    rw [← e1]
    calc a * (b * y * b⁻¹) * a⁻¹ = a * (b * (a * y * a⁻¹) * b⁻¹) * a⁻¹ := by rw [hay']
      _ = _ := by group
  have e3 : b * y * b⁻¹ = a⁻¹ * y₃ * a := by
    calc b * y * b⁻¹ = a⁻¹ * (a * (b * y * b⁻¹) * a⁻¹) * a := by group
      _ = a⁻¹ * y₃ * a := by rw [e2]
  have hc13 : ⁅a⁻¹, y₃⁆ ∈ Vsub root 2 3 := by
    have h := (rgd2_octComm R) 1 3 (by norm_num) (by norm_num) (by norm_num) a⁻¹
      ((root 1).inv_mem ha) y₃ hy₃
    refine (iSup₂_le (fun k hk => ?_) : (⨆ c ∈ Set.Ioo (1 : ℤ) 3, root c) ≤ Vsub root 2 3) h
    have hk' := Set.mem_Ioo.1 hk
    exact root_le_Vsub (by omega) (by omega)
  have hz : a⁻¹ * y₃ * a ∈ Vsub root 2 3 := by
    have e : a⁻¹ * y₃ * a = ⁅a⁻¹, y₃⁆ * y₃ := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact Subgroup.mul_mem _ hc13 (root_le_Vsub (by norm_num) (by norm_num) hy₃)
  rw [← e3] at hz
  have h1 := eq_one_of_mem_Vsub23_Vsub56 R hz hby
  apply hy1
  have : b * y * b⁻¹ = 1 := h1
  simpa [mul_inv_eq_one] using this


end CFSG.GH74.GLS.Stage4.Hex
