module

public import CFSG.GH74.Tits83.Section3D

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

namespace TitsSystem

variable {G : Type u} [Group G]

variable (T : TitsSystem G 8)

theorem lemma313_i (hT : T.Normalized) {u v : G} (hu : u ∈ T.U 2) (hv : v ∈ T.Uprime 8)
    (hv1 : v ≠ 1) :
    ∃ a ∈ T.Uprime 2, ∃ b ∈ T.Uprime 4, ∃ c ∈ T.Uprime 6, ∃ d ∈ T.U 7,
      ⁅v, a⁻¹ * u⁆ = b * c * d := by
  have hT2 : (T.shift 2).Normalized :=
    Normalized.shift (T := T) hT (s := 2) (by norm_num)
  have hu' : u ∈ (T.shift 2).U 0 := by rw [shift_U]; simpa using hu
  have hv' : v ∈ (T.shift 2).Uprime 6 := by rw [Uprime_shift]; simpa using hv
  obtain ⟨a4, ha4, x, hx, c6, hc6, d7, hd7, hvu⟩ :=
    lemma312' (T := T.shift 2) hT2 hu' hv'
  have ha4' : a4 ∈ T.Uprime 4 := by simpa [Uprime_shift] using ha4
  have hx' : x ∈ T.U 5 := by rw [shift_U] at hx; simpa using hx
  have hc6' : c6 ∈ T.Uprime 6 := by simpa [Uprime_shift] using hc6
  have hd7' : d7 ∈ T.U 7 := by rw [shift_U] at hd7; simpa using hd7
  obtain ⟨a, ha, d, hd, c, hc, hva⟩ := lemma38_surj (T := T) hT hv hv1 hx'
  have ha_inv : a⁻¹ ∈ T.Uprime 2 := (T.Uprime 2).inv_mem ha
  have hf : d⁻¹ * a4 ∈ T.Uprime 4 :=
    (T.Uprime 4).mul_mem ((T.Uprime 4).inv_mem hd) ha4'
  have he : ⁅d7⁻¹, a⁻¹⁆ ∈ T.Uprime 4 := by
    have hd7inv : d7⁻¹ ∈ T.U 7 := (T.U 7).inv_mem hd7'
    have h := (comm_odd_Uprime' (T := T) hT (j := 7) (show Odd (7 : ℤ) from ⟨3, by norm_num⟩)
      hd7inv ha_inv).1
    simpa using h
  have hcc : c⁻¹ * c6 ∈ T.Uprime 6 :=
    (T.Uprime 6).mul_mem ((T.Uprime 6).inv_mem hc) hc6'
  have hva_inv : ⁅v, a⁆⁻¹ = c⁻¹ * x⁻¹ * d⁻¹ := by
    rw [hva]
    group
  have hmid : x⁻¹ * d⁻¹ * a4 * x = d⁻¹ * a4 := by
    have hcomm : (d⁻¹ * a4) * x = x * (d⁻¹ * a4) :=
      T.Uprime_comm (j := 4) (k := 5) (by norm_num) (by norm_num) hf hx'
    calc x⁻¹ * d⁻¹ * a4 * x = x⁻¹ * (d⁻¹ * a4) * x := by group
      _ = x⁻¹ * ((d⁻¹ * a4) * x) := by group
      _ = x⁻¹ * (x * (d⁻¹ * a4)) := by rw [hcomm]
      _ = d⁻¹ * a4 := by group
  have hfc : c⁻¹ * (d⁻¹ * a4) = (d⁻¹ * a4) * c⁻¹ :=
    (T.Uprime_comm (j := 4) (k := 6) (by norm_num) (by norm_num) hf
      (T.Uprime_le 6 ((T.Uprime 6).inv_mem hc))).symm
  have hinner : ⁅v, a⁆⁻¹ * ⁅v, u⁆ = (d⁻¹ * a4) * (c⁻¹ * c6) * d7 := by
    rw [hva_inv, hvu]
    calc c⁻¹ * x⁻¹ * d⁻¹ * (a4 * x * c6 * d7)
        = c⁻¹ * (x⁻¹ * d⁻¹ * a4 * x) * c6 * d7 := by group
      _ = c⁻¹ * (d⁻¹ * a4) * c6 * d7 := by rw [hmid]
      _ = (d⁻¹ * a4) * (c⁻¹ * c6) * d7 := by
          rw [hfc]
          group
  have haf : a⁻¹ * (d⁻¹ * a4) = (d⁻¹ * a4) * a⁻¹ :=
    T.Uprime_comm (j := 2) (k := 4) (by norm_num) (by norm_num) ha_inv (T.Uprime_le 4 hf)
  have hacc : a⁻¹ * (c⁻¹ * c6) = (c⁻¹ * c6) * a⁻¹ :=
    T.Uprime_comm (j := 2) (k := 6) (by norm_num) (by norm_num) ha_inv (T.Uprime_le 6 hcc)
  have had7 : a⁻¹ * d7 * a = d7 * ⁅d7⁻¹, a⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  have hec : (c⁻¹ * c6) * ⁅d7⁻¹, a⁻¹⁆ = ⁅d7⁻¹, a⁻¹⁆ * (c⁻¹ * c6) :=
    (T.Uprime_comm (j := 4) (k := 6) (by norm_num) (by norm_num) he
      (T.Uprime_le 6 hcc)).symm
  have hed : d7 * ⁅d7⁻¹, a⁻¹⁆ = ⁅d7⁻¹, a⁻¹⁆ * d7 :=
    (T.Uprime_comm (j := 4) (k := 7) (by norm_num) (by norm_num) he hd7').symm
  refine ⟨a, ha, (d⁻¹ * a4) * ⁅d7⁻¹, a⁻¹⁆, (T.Uprime 4).mul_mem hf he,
    c⁻¹ * c6, hcc, d7, hd7', ?_⟩
  have h1 : ⁅v, a⁻¹ * u⁆ = a⁻¹ * (⁅v, a⁆⁻¹ * ⁅v, u⁆) * a := by
    simp only [commutatorElement_def]
    group
  rw [h1, hinner]
  calc a⁻¹ * ((d⁻¹ * a4) * (c⁻¹ * c6) * d7) * a
      = (a⁻¹ * (d⁻¹ * a4)) * (c⁻¹ * c6) * d7 * a := by group
    _ = ((d⁻¹ * a4) * a⁻¹) * (c⁻¹ * c6) * d7 * a := by rw [haf]
    _ = (d⁻¹ * a4) * (a⁻¹ * (c⁻¹ * c6)) * d7 * a := by group
    _ = (d⁻¹ * a4) * ((c⁻¹ * c6) * a⁻¹) * d7 * a := by rw [hacc]
    _ = (d⁻¹ * a4) * (c⁻¹ * c6) * (a⁻¹ * d7 * a) := by group
    _ = (d⁻¹ * a4) * (c⁻¹ * c6) * (d7 * ⁅d7⁻¹, a⁻¹⁆) := by rw [had7]
    _ = (d⁻¹ * a4) * (c⁻¹ * c6) * (⁅d7⁻¹, a⁻¹⁆ * d7) := by rw [hed]
    _ = (d⁻¹ * a4) * ((c⁻¹ * c6) * ⁅d7⁻¹, a⁻¹⁆) * d7 := by group
    _ = (d⁻¹ * a4) * (⁅d7⁻¹, a⁻¹⁆ * (c⁻¹ * c6)) * d7 := by rw [hec]
    _ = ((d⁻¹ * a4) * ⁅d7⁻¹, a⁻¹⁆) * (c⁻¹ * c6) * d7 := by group

@[expose] def Y313 : Subgroup G := T.Uprime 6 ⊔ T.U 7 ⊔ T.Uprime 8

theorem coe_Y313 :
    (T.Y313 : Set G) = (T.Uprime 6 : Set G) * (T.U 7 : Set G) * (T.Uprime 8 : Set G) := by
  have h67 : T.U 7 ≤ Subgroup.normalizer (T.Uprime 6 : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy x hx
    have h1 : y * x * y⁻¹ = x := by
      rw [show y * x = x * y from
        (T.Uprime_comm (j := 6) (k := 7) (by norm_num) (by norm_num) hx hy).symm]
      group
    rw [h1]
    exact hx
  have h8sup : T.Uprime 8 ≤
      Subgroup.normalizer ((T.Uprime 6 ⊔ T.U 7 : Subgroup G) : Set G) := by
    refine CFSG.LieType.Steinberg.le_normalizer_sup ?_ ?_
    · rw [Subgroup.le_normalizer_iff]
      intro y hy x hx
      have h1 : y * x * y⁻¹ = x := by
        rw [show y * x = x * y from
          (T.Uprime_comm (j := 6) (k := 8) (by norm_num) (by norm_num) hx
            (T.Uprime_le 8 hy)).symm]
        group
      rw [h1]
      exact hx
    · rw [Subgroup.le_normalizer_iff]
      intro y hy x hx
      have h1 : y * x * y⁻¹ = x := by
        rw [show y * x = x * y from
          (T.Uprime_comm (j := 8) (k := 7) (by norm_num) (by norm_num) hy hx)]
        group
      rw [h1]
      exact hx
  rw [show T.Y313 = (T.Uprime 6 ⊔ T.U 7) ⊔ T.Uprime 8 from rfl]
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ h8sup,
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ h67]

theorem le_normalizer_Y313 (hT : T.Normalized) :
    T.U 10 ≤ Subgroup.normalizer (T.Y313 : Set G) := by
  have hT2 : (T.shift 2).Normalized :=
    Normalized.shift (T := T) hT (s := 2) (by norm_num)
  refine CFSG.LieType.Steinberg.le_normalizer_of_map_conj_le fun g hg => ?_
  rw [CFSG.LieType.Steinberg.map_conj_le_iff]
  intro x hx
  have hx' : x ∈ (T.Uprime 6 : Set G) * (T.U 7 : Set G) * (T.Uprime 8 : Set G) := by
    rw [← T.coe_Y313]
    exact hx
  obtain ⟨y, hy, b, hb, rfl⟩ := hx'
  obtain ⟨c, hc, d, hd, rfl⟩ := hy
  have hgc : g * c * g⁻¹ = c := by
    rw [show g * c = c * g from
      (T.Uprime_comm (j := 6) (k := 10) (by norm_num) (by norm_num) hc hg).symm]
    group
  have hgb : g * b * g⁻¹ = b := by
    rw [show g * b = b * g from
      (T.Uprime_comm (j := 8) (k := 10) (by norm_num) (by norm_num) hb hg).symm]
    group
  have hcommd : ⁅d, g⁆ ∈ T.Uprime 8 := by
    have hd' : d ∈ (T.shift 2).U 5 := by rw [shift_U]; simpa using hd
    have hg' : g ∈ (T.shift 2).U 8 := by rw [shift_U]; simpa using hg
    have h := lemma310_ii (T := T.shift 2) hT2 (x := d) (g := g) hd' hg'
    simpa [Uprime_shift] using h
  have hgd : g * d * g⁻¹ = ⁅d, g⁆⁻¹ * d := by
    simp only [commutatorElement_def]
    group
  have hxeq : g * (c * d * b) * g⁻¹ = c * ((⁅d, g⁆⁻¹ * d) * b) := by
    rw [show g * (c * d * b) * g⁻¹ = (g * c * g⁻¹) * (g * d * g⁻¹) * (g * b * g⁻¹) by
      group]
    rw [hgc, hgd, hgb]
    group
  rw [hxeq]
  have hcY : c ∈ T.Y313 :=
    (show T.Uprime 6 ≤ T.Y313 from le_sup_left.trans le_sup_left) hc
  have hdY : d ∈ T.Y313 :=
    (show T.U 7 ≤ T.Y313 from le_sup_right.trans le_sup_left) hd
  have heY : ⁅d, g⁆⁻¹ ∈ T.Y313 :=
    (show T.Uprime 8 ≤ T.Y313 from le_sup_right) ((T.Uprime 8).inv_mem hcommd)
  have hbY : b ∈ T.Y313 := (show T.Uprime 8 ≤ T.Y313 from le_sup_right) hb
  exact T.Y313.mul_mem hcY (T.Y313.mul_mem (T.Y313.mul_mem heY hdY) hbY)

theorem lemma313_ii (hT : T.Normalized) {u v : G} (hu : u ∈ T.U 2) (hv : v ∈ T.Uprime 8)
    (hv1 : v ≠ 1)
    (h : ∃ b ∈ T.Uprime 4, ∃ c ∈ T.Uprime 6, ∃ d ∈ T.U 7, ⁅v, u⁆ = b * c * d) :
    u ∈ T.Usec 2 := by
  classical
  simp only [TitsSystem.Usec, Set.mem_setOf_eq]
  obtain ⟨b, hb, c, hc, d7, hd7, hvu⟩ := h
  by_cases hu1 : u = 1
  · exact Or.inl hu1
  right
  let up : G := T.nu 2 u
  let upp : G := T.nu' 2 u
  let m : G := T.mu 2 u
  have hup : up ∈ T.U 10 := by
    have h := (T.isMu_nu hu hu1).1
    simpa [up] using h
  have hupp : upp ∈ T.U 10 := by
    have h := (T.isMu_nu hu hu1).2.1
    simpa [upp] using h
  have hup1 : up ≠ 1 := T.nu_ne_one (by norm_num) hu hu1
  have hm : m = up * u * upp := rfl
  have hmv4 : m * v * m⁻¹ ∈ T.Uprime 4 := by
    have h := mu_conj_mem_Uprime (T := T) hu hu1 hv
    simpa [m, show 2 * 2 + 8 - 8 = 4 by norm_num] using h
  have hb_inv : b⁻¹ ∈ T.Uprime 4 := (T.Uprime 4).inv_mem hb
  have hc_inv : c⁻¹ ∈ T.Uprime 6 := (T.Uprime 6).inv_mem hc
  have hd7_inv : d7⁻¹ ∈ T.U 7 := (T.U 7).inv_mem hd7
  have huy : ⁅u, v⁆ = b⁻¹ * c⁻¹ * d7⁻¹ := by
    have h1 : ⁅u, v⁆ = ⁅v, u⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h1, hvu]
    have h2 : (b * c * d7)⁻¹ = d7⁻¹ * c⁻¹ * b⁻¹ := by group
    rw [h2]
    have hcd : c⁻¹ * d7⁻¹ = d7⁻¹ * c⁻¹ :=
      T.Uprime_comm (j := 6) (k := 7) (by norm_num) (by norm_num) hc_inv hd7_inv
    have hbd : b⁻¹ * d7⁻¹ = d7⁻¹ * b⁻¹ :=
      T.Uprime_comm (j := 4) (k := 7) (by norm_num) (by norm_num) hb_inv hd7_inv
    have hbc : b⁻¹ * c⁻¹ = c⁻¹ * b⁻¹ :=
      T.Uprime_comm (j := 4) (k := 6) (by norm_num) (by norm_num) hb_inv
        (T.Uprime_le 6 hc_inv)
    calc d7⁻¹ * c⁻¹ * b⁻¹ = c⁻¹ * d7⁻¹ * b⁻¹ := by rw [← hcd]
      _ = c⁻¹ * (d7⁻¹ * b⁻¹) := by group
      _ = c⁻¹ * (b⁻¹ * d7⁻¹) := by rw [← hbd]
      _ = (c⁻¹ * b⁻¹) * d7⁻¹ := by group
      _ = (b⁻¹ * c⁻¹) * d7⁻¹ := by rw [← hbc]
      _ = b⁻¹ * c⁻¹ * d7⁻¹ := by group
  have huv : u * v * u⁻¹ = b⁻¹ * (c⁻¹ * d7⁻¹ * v) := by
    have h1 : u * v * u⁻¹ = ⁅u, v⁆ * v := by
      simp only [commutatorElement_def]
      group
    rw [h1, huy]
    group
  let ζ : G := c⁻¹ * d7⁻¹ * v
  let η : G := up * ζ * up⁻¹
  have hcY : c⁻¹ ∈ T.Y313 :=
    (show T.Uprime 6 ≤ T.Y313 from le_sup_left.trans le_sup_left) hc_inv
  have hd7Y : d7⁻¹ ∈ T.Y313 :=
    (show T.U 7 ≤ T.Y313 from le_sup_right.trans le_sup_left) hd7_inv
  have hvY : v ∈ T.Y313 := (show T.Uprime 8 ≤ T.Y313 from le_sup_right) hv
  have hζ : ζ ∈ T.Y313 := by
    simp only [ζ]
    exact T.Y313.mul_mem (T.Y313.mul_mem hcY hd7Y) hvY
  have hη : η ∈ T.Y313 := by
    have hn := le_normalizer_Y313 (T := T) hT hup
    have hmem := (Subgroup.mem_normalizer_iff.mp hn ζ).mp hζ
    simpa [η] using hmem
  have huppv : upp * v = v * upp :=
    (T.Uprime_comm (j := 8) (k := 10) (by norm_num) (by norm_num) hv hupp).symm
  have hm2v : m * v * m⁻¹ = up * (u * v * u⁻¹) * up⁻¹ := by
    rw [hm]
    rw [show up * u * upp * v * (up * u * upp)⁻¹ =
      up * u * (upp * v * upp⁻¹) * u⁻¹ * up⁻¹ by group]
    rw [show upp * v * upp⁻¹ = v by rw [huppv]; group]
    group
  have hm2v' : m * v * m⁻¹ = b⁻¹ * (⁅b, up⁆ * η) := by
    rw [hm2v, huv]
    have hconj : up * b⁻¹ * up⁻¹ = b⁻¹ * ⁅b, up⁆ := by
      simp only [commutatorElement_def]
      group
    calc up * (b⁻¹ * ζ) * up⁻¹ = (up * b⁻¹ * up⁻¹) * (up * ζ * up⁻¹) := by group
      _ = (b⁻¹ * ⁅b, up⁆) * η := by rw [hconj]
      _ = b⁻¹ * (⁅b, up⁆ * η) := by group
  have hbuwin : ⁅b, up⁆ ∈ win T.U 5 9 := by
    have h := commutator_mem_win (T := T) (j := 4) (a := 5) (b := 10) (by norm_num)
      (by norm_num) (by norm_num) (T.Uprime_le 4 hb)
      (T.U_le_win (by norm_num) (by norm_num) hup)
    simpa using h
  have hYle : T.Y313 ≤ win T.U 6 8 := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact (T.Uprime_le 6).trans (T.U_le_win (by norm_num) (by norm_num))
    · exact T.U_le_win (by norm_num) (by norm_num)
    · exact (T.Uprime_le 8).trans (T.U_le_win (by norm_num) (by norm_num))
  have hηwin : η ∈ win T.U 5 9 :=
    (T.win_mono (a := 6) (b := 8) (c := 5) (d := 9) (by norm_num) (by norm_num)) (hYle hη)
  have hprodwin : ⁅b, up⁆ * η ∈ win T.U 5 9 :=
    (win T.U 5 9).mul_mem hbuwin hηwin
  have hcmp := eq_of_mul_eq_mul (T := T) (a := 4) (c := 4) (b := 9)
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [T.win_self]; exact T.Uprime_le 4 hb_inv)
    (by rw [T.win_self]; exact T.Uprime_le 4 hmv4)
    hprodwin (win T.U 5 9).one_mem
    (by rw [hm2v']; group)
  have hmv : m * v * m⁻¹ = b⁻¹ := hcmp.1.symm
  have hbuY : ⁅b, up⁆ ∈ T.Y313 := by
    have h1 : ⁅b, up⁆ * η = 1 := hcmp.2
    have h2 : ⁅b, up⁆ = η⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2]
    exact T.Y313.inv_mem hη
  have hb1 : b ≠ 1 := by
    intro h
    apply hv1
    have h2 : m * v * m⁻¹ = 1 := by rw [hmv, h, inv_one]
    have := congrArg (fun t => m⁻¹ * t * m) h2
    simpa [mul_assoc] using this
  have hT12 : (T.refl 12).Normalized :=
    Normalized.refl (T := T) hT (c := 12) (show Even (12 : ℤ) from ⟨6, by norm_num⟩)
  have hup_refl : up ∈ (T.refl 12).U 2 := by
    rw [refl_U]
    simpa using hup
  have hb_refl : b ∈ (T.refl 12).Uprime 8 := by
    rw [Uprime_refl]
    simpa using hb
  obtain ⟨a, ha, b', hb', c', hc', d', hd', hcomm⟩ :=
    lemma313_i (T := T.refl 12) hT12 hup_refl hb_refl hb1
  have ha10 : a ∈ T.Uprime 10 := by simpa [Uprime_refl] using ha
  have hb8 : b' ∈ T.Uprime 8 := by simpa [Uprime_refl] using hb'
  have hc6 : c' ∈ T.Uprime 6 := by simpa [Uprime_refl] using hc'
  have hd5 : d' ∈ T.U 5 := by rw [refl_U] at hd'; simpa using hd'
  have h36Y : ⁅b, a⁻¹⁆ ∈ T.Y313 := by
    have hT2 : (T.shift 2).Normalized :=
      Normalized.shift (T := T) hT (s := 2) (by norm_num)
    have hb2 : b ∈ (T.shift 2).Uprime 2 := by
      rw [Uprime_shift]
      simpa using hb
    have ha2 : a⁻¹ ∈ (T.shift 2).Uprime 8 := by
      rw [Uprime_shift]
      simpa using (T.Uprime 10).inv_mem ha10
    have h36 := lemma36_ii (T := T.shift 2) hb2 ha2
    obtain ⟨dd, hdd, ee, hee, ff, hff, heq⟩ := h36
    have hdd' : dd ∈ T.Uprime 6 := by simpa [Uprime_shift] using hdd
    have hee' : ee ∈ T.U 7 := by rw [shift_U] at hee; simpa using hee
    have hff' : ff ∈ T.Uprime 8 := by simpa [Uprime_shift] using hff
    have hddY : dd ∈ T.Y313 :=
      (show T.Uprime 6 ≤ T.Y313 from le_sup_left.trans le_sup_left) hdd'
    have heeY : ee ∈ T.Y313 :=
      (show T.U 7 ≤ T.Y313 from le_sup_right.trans le_sup_left) hee'
    have hffY : ff ∈ T.Y313 := (show T.Uprime 8 ≤ T.Y313 from le_sup_right) hff'
    rw [heq]
    exact T.Y313.mul_mem (T.Y313.mul_mem hddY heeY) hffY
  have hYle14 : T.Y313 ≤ win T.U 6 14 :=
    hYle.trans (T.win_mono (a := 6) (b := 8) (c := 6) (d := 14) (by norm_num) (by norm_num))
  have hcomm_a : a * ⁅b, up⁆ = ⁅b, up⁆ * a := by
    have hmem : ⁅b, up⁆ ∈ win T.U 6 14 := hYle14 hbuY
    exact T.Uprime_comm_win (j := 10) (a := 6) (b := 14) (by norm_num) (by norm_num)
      ha10 hmem
  have hconj_a : a⁻¹ * ⁅b, up⁆ * a = ⁅b, up⁆ := by
    calc a⁻¹ * ⁅b, up⁆ * a = a⁻¹ * (⁅b, up⁆ * a) := by group
      _ = a⁻¹ * (a * ⁅b, up⁆) := by rw [← hcomm_a]
      _ = ⁅b, up⁆ := by group
  have hsplit : ⁅b, a⁻¹ * up⁆ = ⁅b, a⁻¹⁆ * (a⁻¹ * ⁅b, up⁆ * a) := by
    simp only [commutatorElement_def]
    group
  have hconjmem : a⁻¹ * ⁅b, up⁆ * a ∈ T.Y313 := by
    rw [hconj_a]
    exact hbuY
  have hYall : ⁅b, a⁻¹ * up⁆ ∈ T.Y313 := by
    rw [hsplit]
    exact T.Y313.mul_mem h36Y hconjmem
  have hdc : d' * c' = c' * d' :=
    (T.Uprime_comm (j := 6) (k := 5) (by norm_num) (by norm_num) hc6 hd5).symm
  have hdb : d' * b' = b' * d' :=
    (T.Uprime_comm (j := 8) (k := 5) (by norm_num) (by norm_num) hb8 hd5).symm
  have hcb : c' * b' = b' * c' :=
    T.Uprime_comm (j := 6) (k := 8) (by norm_num) (by norm_num) hc6
      (T.Uprime_le 8 hb8)
  have hreorder : b' * c' * d' = d' * (c' * b') := by
    calc b' * c' * d' = b' * (c' * d') := by group
      _ = b' * (d' * c') := by rw [hdc]
      _ = (b' * d') * c' := by group
      _ = (d' * b') * c' := by rw [hdb]
      _ = d' * (b' * c') := by group
      _ = d' * (c' * b') := by rw [← hcb]
  have hcbwin : c' * b' ∈ win T.U 6 8 :=
    (win T.U 6 8).mul_mem
      (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 6 hc6))
      (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 8 hb8))
  have hd_one : d' = 1 := by
    have heq2 : d' * (c' * b') = (1 : G) * ⁅b, a⁻¹ * up⁆ := by
      rw [hcomm, hreorder]
      group
    have hcmp2 := eq_of_mul_eq_mul (T := T) (a := 5) (c := 5) (b := 8)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [T.win_self]; exact hd5)
      (by rw [T.win_self]; exact (T.U 5).one_mem)
      hcbwin (hYle hYall) heq2
    exact hcmp2.1
  have hcomm' : ⁅b, a⁻¹ * up⁆ = c' * b' := by
    rw [hcomm, hd_one]
    simpa using hcb.symm
  have hT4 : (T.shift 4).Normalized :=
    Normalized.shift (T := T) hT (s := 4) (show Even (4 : ℤ) from ⟨2, by norm_num⟩)
  have hb4 : b ∈ (T.shift 4).Uprime 0 := by
    rw [Uprime_shift]
    simpa using hb
  have hq4 : a⁻¹ * up ∈ (T.shift 4).U 6 := by
    rw [shift_U]
    exact (T.U 10).mul_mem (T.Uprime_le 10 ((T.Uprime 10).inv_mem ha10)) hup
  have hc6_4 : c' ∈ (T.shift 4).Uprime 2 := by
    rw [Uprime_shift]
    simpa using hc6
  have hb8_4 : b' ∈ (T.shift 4).Uprime 4 := by
    rw [Uprime_shift]
    simpa using hb8
  have h37 := lemma37 (T := T.shift 4) hb4 hq4 hc6_4 hb8_4 hcomm'
  have hup_eq_a : up = a := by
    rcases h37 with h | h
    · exact (inv_mul_eq_one.mp h).symm
    · exact absurd h hb1
  have hup10 : up ∈ T.Uprime 10 := by
    rw [hup_eq_a]
    exact ha10
  have hUeq : T.Uprime (2 - 8) = T.Uprime 10 := by
    have h := T.Uprime_add_two_mul (j := 10) (k := -1)
    simpa using h
  have hnueq : T.nu' (2 - 8) up = T.nu' 10 up := by
    have h := T.nu'_add_two_mul (by norm_num : 3 ≤ 8) (i := 10) (k := -1) up
    simpa using h
  have hnu10 : T.nu' 10 up = u := by
    have h := (T.mu_nu (by norm_num : 3 ≤ 8) hu hu1).2
    simpa [up] using h
  exact ⟨up, by rw [hUeq]; exact hup10, hup1, by rw [hnueq, hnu10]⟩

theorem Usec_subset (j : ℤ) : T.Usec j ⊆ (T.U j : Set G) := by
  intro x hx
  have hx' : x = 1 ∨ ∃ u ∈ T.Uprime (j - 8), u ≠ 1 ∧ x = T.nu' (j - 8) u := by
    simpa only [TitsSystem.Usec, Set.mem_setOf_eq] using hx
  rcases hx' with rfl | ⟨u, hu, hu1, rfl⟩
  · exact (T.U j).one_mem
  · have h := T.nu'_mem (T.Uprime_le (j - 8) hu) hu1
    rwa [show (j - 8) + ((8 : ℕ) : ℤ) = j by ring] at h

private theorem mem_Uprime_mul_Usec_two (hT : T.Normalized) {u : G} (hu : u ∈ T.U 2) :
    ∃ a ∈ T.Uprime 2, ∃ b ∈ T.Usec 2, u = a * b := by
  obtain ⟨v, hv, hv1⟩ :=
    exists_Uprime (T := T) hT (show Even (8 : ℤ) from ⟨4, by norm_num⟩)
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hcomm⟩ := lemma313_i (T := T) hT hu hv hv1
  have hbU : a⁻¹ * u ∈ T.Usec 2 := by
    refine lemma313_ii (T := T) hT ?_ hv hv1 ⟨b, hb, c, hc, d, hd, hcomm⟩
    exact (T.U 2).mul_mem ((T.U 2).inv_mem (T.Uprime_le 2 ha)) hu
  exact ⟨a, ha, a⁻¹ * u, hbU, by group⟩

theorem mem_Uprime_mul_Usec (hT : T.Normalized) {j : ℤ} (hj : Even j) {u : G}
    (hu : u ∈ T.U j) : ∃ a ∈ T.Uprime j, ∃ b ∈ T.Usec j, u = a * b := by
  obtain ⟨k, hk⟩ := hj
  have hs : Even (j - 2) := ⟨k - 1, by rw [hk]; ring⟩
  have hT' : (T.shift (j - 2)).Normalized := Normalized.shift (T := T) hT hs
  have hu' : u ∈ (T.shift (j - 2)).U 2 := by
    rw [shift_U]
    rwa [show 2 + (j - 2) = j by ring]
  obtain ⟨a, ha, b, hb, heq⟩ := mem_Uprime_mul_Usec_two (T := T.shift (j - 2)) hT' hu'
  refine ⟨a, ?_, b, ?_, heq⟩
  · have h := ha
    rw [Uprime_shift] at h
    rwa [show 2 + (j - 2) = j by ring] at h
  · have h := hb
    rw [Usec_shift] at h
    rwa [show 2 + (j - 2) = j by ring] at h

theorem lemma315 (hT : T.Normalized) {x y : G} (hx : x ∈ T.U 0) (hy : y ∈ T.U 4) :
    x * y = y * x := by
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    mem_Uprime_mul_Usec (T := T) hT (show Even (0 : ℤ) from ⟨0, by norm_num⟩) hx
  have hay : a * y = y * a :=
    T.Uprime_comm (j := 0) (k := 4) (by norm_num) (by norm_num) ha hy
  have hb' : b = 1 ∨ ∃ w ∈ T.Uprime (0 - 8), w ≠ 1 ∧ b = T.nu' (0 - 8) w := by
    simpa only [TitsSystem.Usec, Set.mem_setOf_eq] using hb
  rcases hb' with hb1 | ⟨w, hw, hw1, hbw⟩
  · rw [hb1, mul_one]
    exact hay
  · have hw8 : w ∈ T.Uprime 8 := by
      have h := T.Uprime_add_two_mul (j := 8) (k := -1)
      rw [show 8 + 16 * (-1) = 0 - 8 by norm_num] at h
      rwa [h] at hw
    have hbnu : T.nu' (0 - 8) w = T.nu' 8 w := by
      have h := T.nu'_add_two_mul (by norm_num : 3 ≤ 8) (i := 8) (k := -1) w
      rwa [show 8 + 2 * ((8 : ℕ) : ℤ) * (-1) = 0 - 8 by norm_num] at h
    have hwy : w * y = y * w :=
      T.Uprime_comm (j := 8) (k := 4) (by norm_num) (by norm_num) hw8 hy
    have h212 := lemma212_ii' (T := T) (by norm_num : 3 ≤ 8) (i := 8) (j := 4)
      (by norm_num) (T.Uprime_le 8 hw8) hw1 hy hwy
    have hν : y * T.nu 8 w = T.nu 8 w * y := h212.1
    have hm : y * T.mu 8 w = T.mu 8 w * y := h212.2
    have hνinv : y * (T.nu 8 w)⁻¹ = (T.nu 8 w)⁻¹ * y := by
      calc y * (T.nu 8 w)⁻¹ =
          (T.nu 8 w)⁻¹ * (T.nu 8 w) * y * (T.nu 8 w)⁻¹ := by group
        _ = (T.nu 8 w)⁻¹ * (T.nu 8 w * y) * (T.nu 8 w)⁻¹ := by group
        _ = (T.nu 8 w)⁻¹ * (y * (T.nu 8 w)) * (T.nu 8 w)⁻¹ := by rw [hν]
        _ = (T.nu 8 w)⁻¹ * y := by group
    have hywinv : y * w⁻¹ = w⁻¹ * y :=
      (T.Uprime_comm (j := 8) (k := 4) (by norm_num) (by norm_num)
        ((T.Uprime 8).inv_mem hw8) hy).symm
    have hyb' : y * b = b * y := by
      rw [hbw, hbnu]
      have hexp : T.nu' 8 w = w⁻¹ * (T.nu 8 w)⁻¹ * T.mu 8 w := by
        simp only [TitsSystem.mu]
        group
      rw [hexp]
      calc y * (w⁻¹ * (T.nu 8 w)⁻¹ * T.mu 8 w)
          = (y * w⁻¹) * (T.nu 8 w)⁻¹ * T.mu 8 w := by group
        _ = (w⁻¹ * y) * (T.nu 8 w)⁻¹ * T.mu 8 w := by rw [hywinv]
        _ = w⁻¹ * (y * (T.nu 8 w)⁻¹) * T.mu 8 w := by group
        _ = w⁻¹ * ((T.nu 8 w)⁻¹ * y) * T.mu 8 w := by rw [hνinv]
        _ = w⁻¹ * (T.nu 8 w)⁻¹ * (y * T.mu 8 w) := by group
        _ = w⁻¹ * (T.nu 8 w)⁻¹ * (T.mu 8 w * y) := by rw [hm]
        _ = (w⁻¹ * (T.nu 8 w)⁻¹ * T.mu 8 w) * y := by group
    have hyb : b * y = y * b := hyb'.symm
    calc (a * b) * y = a * (b * y) := by group
      _ = a * (y * b) := by rw [hyb]
      _ = (a * y) * b := by group
      _ = (y * a) * b := by rw [hay]
      _ = y * (a * b) := by group

theorem comm_even_add_four (hT : T.Normalized) {j : ℤ} (hj : Even j) {x y : G}
    (hx : x ∈ T.U j) (hy : y ∈ T.U (j + 4)) : x * y = y * x := by
  have hTj : (T.shift j).Normalized := Normalized.shift (T := T) hT hj
  have hx' : x ∈ (T.shift j).U 0 := by
    rw [shift_U]
    simpa using hx
  have hy' : y ∈ (T.shift j).U 4 := by
    rw [shift_U]
    simpa [add_comm] using hy
  exact lemma315 (T := T.shift j) hTj hx' hy'

theorem lemma316_i (hT : T.Normalized) {j : ℤ} (hj : Even j) {u : G}
    (hu : u ∈ T.Uprime j) (hu1 : u ≠ 1) : T.nu j u = (T.nu' j u)⁻¹ := by
  have huu : u⁻¹ = u := inv_eq_of_mul_eq_one_right (Uprime_mul_self (T := T) hT hj hu)
  have h1 := T.nu_inv (by norm_num : 3 ≤ 8) (T.Uprime_le j hu) hu1
  simpa [huu] using h1

theorem comm_Usec_mem (hT : T.Normalized) {u v : G} (hu : u ∈ T.Usec 2) (hv : v ∈ T.Uprime 8) :
    ∃ b ∈ T.Uprime 4, ∃ c ∈ T.Uprime 6, ∃ d ∈ T.U 7, ⁅u, v⁆ = b * c * d := by
  classical
  have hu' : u = 1 ∨ ∃ w ∈ T.Uprime (2 - 8), w ≠ 1 ∧ u = T.nu' (2 - 8) w := by
    simpa only [TitsSystem.Usec, Set.mem_setOf_eq] using hu
  by_cases hv1 : v = 1
  · refine ⟨1, (T.Uprime 4).one_mem, 1, (T.Uprime 6).one_mem, 1, (T.U 7).one_mem, ?_⟩
    rw [hv1]
    simp only [commutatorElement_def]
    group
  rcases hu' with rfl | ⟨w, hw, hw1, hu_eq⟩
  · refine ⟨1, (T.Uprime 4).one_mem, 1, (T.Uprime 6).one_mem, 1, (T.U 7).one_mem, ?_⟩
    simp only [commutatorElement_def]
    group
  have hw10 : w ∈ T.Uprime 10 := by
    have h := T.Uprime_add_two_mul (j := 10) (k := -1)
    rw [show 10 + 16 * (-1) = 2 - 8 by norm_num] at h
    rwa [h] at hw
  have hnu_eq : T.nu' (2 - 8) w = T.nu' 10 w := by
    have h := T.nu'_add_two_mul (by norm_num : 3 ≤ 8) (i := 10) (k := -1) w
    rwa [show 10 + 2 * ((8 : ℕ) : ℤ) * (-1) = 2 - 8 by norm_num] at h
  have hu10 : u = T.nu' 10 w := by rw [hu_eq, hnu_eq]
  have hu2 : u ∈ T.U 2 := Usec_subset (T := T) 2 hu
  let m : G := T.mu 10 w
  let y : G := m * v * m⁻¹
  have hmu : m = u⁻¹ * w * u := by
    have h16 := lemma316_i (T := T) hT (show Even (10 : ℤ) from ⟨5, by norm_num⟩) hw10 hw1
    have hupd : T.nu 10 w = u⁻¹ := by
      rw [h16, hu10]
    simp only [m, TitsSystem.mu]
    rw [hupd, ← hu10]
  have hy20 : y ∈ T.Uprime (2 * 10 + 8 - 8) := by
    have h := mu_conj_mem_Uprime (T := T) (i := 10) (j := 8) (T.Uprime_le 10 hw10) hw1 hv
    simpa [y] using h
  have h204 : T.Uprime (2 * 10 + 8 - 8) = T.Uprime 4 := by
    have h := T.Uprime_add_two_mul (j := 4) (k := 1)
    simpa using h
  have hy : y ∈ T.Uprime 4 := by
    rw [h204] at hy20
    exact hy20
  have hy_comm_u : u * y * u⁻¹ = y := by
    have h := T.Uprime_comm (j := 4) (k := 2) (by norm_num) (by norm_num) hy hu2
    rw [show u * y = y * u from h.symm]
    group
  have hstep : u * y * u⁻¹ = w * (u * v * u⁻¹) * w⁻¹ := by
    rw [show y = m * v * m⁻¹ from rfl, hmu]
    group
  have huv_eq : u * v * u⁻¹ = w⁻¹ * y * w := by
    have h1 : y = w * (u * v * u⁻¹) * w⁻¹ := by
      rw [← hstep]
      exact hy_comm_u.symm
    have := congrArg (fun t => w⁻¹ * t * w) h1
    simpa [mul_assoc] using this.symm
  have hcomm_yw : w⁻¹ * y * w = y * ⁅y⁻¹, w⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  have hy2 : y⁻¹ ∈ (T.shift 2).Uprime 2 := by
    rw [Uprime_shift]
    simpa using (T.Uprime 4).inv_mem hy
  have hw2 : w⁻¹ ∈ (T.shift 2).Uprime 8 := by
    rw [Uprime_shift]
    simpa using (T.Uprime 10).inv_mem hw10
  obtain ⟨c, hc0, d, hd0, e, he0, hcde⟩ := lemma36_ii (T := T.shift 2) hy2 hw2
  have hc : c ∈ T.Uprime 6 := by simpa [Uprime_shift] using hc0
  have hd : d ∈ T.U 7 := by rw [shift_U] at hd0; simpa using hd0
  have he : e ∈ T.Uprime 8 := by simpa [Uprime_shift] using he0
  have hfull : ⁅u, v⁆ = y * c * d * e * v⁻¹ := by
    have h1 : ⁅u, v⁆ = (u * v * u⁻¹) * v⁻¹ := by
      simp only [commutatorElement_def]
    rw [h1, huv_eq, hcomm_yw, hcde]
    group
  have hv8 : v ∈ T.U 8 := T.Uprime_le 8 hv
  have hwin : ⁅u, v⁆ ∈ win T.U 3 7 := by
    have h := commutator_mem_win (T := T) (j := 2) (a := 3) (b := 8)
      (by norm_num) (by norm_num) (by norm_num) (T.Usec_subset 2 hu)
      (T.U_le_win (by norm_num) (by norm_num) hv8)
    simpa using h
  have hleft : y * c * d ∈ win T.U 3 7 :=
    (win T.U 3 7).mul_mem ((win T.U 3 7).mul_mem
      (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 4 hy))
      (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 6 hc)))
      (T.U_le_win (by norm_num) (by norm_num) hd)
  have hright : e * v⁻¹ ∈ win T.U 8 8 := by
    rw [T.win_self]
    exact (T.U 8).mul_mem (T.Uprime_le 8 he) ((T.U 8).inv_mem hv8)
  have heq : y * c * d * (e * v⁻¹) = ⁅u, v⁆ * 1 := by
    rw [hfull]
    group
  have hcmp := eq_of_mul_eq_mul (T := T) (a := 3) (c := 7) (b := 8)
    (by norm_num) (by norm_num) (by norm_num) hleft hwin hright
    (win T.U 8 8).one_mem heq
  exact ⟨y, hy, c, hc, d, hd, hcmp.1.symm⟩

private theorem Uprime_mul_Usec_inj_two (hT : T.Normalized) {a a' b b' : G}
    (ha : a ∈ T.Uprime 2) (ha' : a' ∈ T.Uprime 2) (hb : b ∈ T.Usec 2)
    (hb' : b' ∈ T.Usec 2) (h : a * b = a' * b') : a = a' ∧ b = b' := by
  classical
  obtain ⟨v, hv, hv1⟩ :=
    exists_Uprime (T := T) hT (show Even (8 : ℤ) from ⟨4, by norm_num⟩)
  let c : G := a'⁻¹ * a
  have hc : c ∈ T.Uprime 2 :=
    (T.Uprime 2).mul_mem ((T.Uprime 2).inv_mem ha') ha
  have hcb : c * b = b' := by
    calc c * b = a'⁻¹ * (a * b) := by simp only [c]; group
      _ = a'⁻¹ * (a' * b') := by rw [h]
      _ = b' := by group
  obtain ⟨d, hd, e, he, f, hf, hcde⟩ := lemma36_ii (T := T) hc hv
  have hd_inv : d⁻¹ ∈ T.Uprime 4 := (T.Uprime 4).inv_mem hd
  have he_inv : e⁻¹ ∈ T.U 5 := (T.U 5).inv_mem he
  have hf_inv : f⁻¹ ∈ T.Uprime 6 := (T.Uprime 6).inv_mem hf
  have hvc : ⁅v, c⁆ = d⁻¹ * e⁻¹ * f⁻¹ := by
    have h1 : ⁅v, c⁆ = ⁅c, v⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h1, hcde]
    have h2 : (d * e * f)⁻¹ = f⁻¹ * e⁻¹ * d⁻¹ := by group
    rw [h2]
    have hfe : f⁻¹ * e⁻¹ = e⁻¹ * f⁻¹ :=
      T.Uprime_comm (j := 6) (k := 5) (by norm_num) (by norm_num) hf_inv he_inv
    have hfd : f⁻¹ * d⁻¹ = d⁻¹ * f⁻¹ :=
      T.Uprime_comm (j := 6) (k := 4) (by norm_num) (by norm_num) hf_inv
        (T.Uprime_le 4 hd_inv)
    have hed : e⁻¹ * d⁻¹ = d⁻¹ * e⁻¹ :=
      (T.Uprime_comm (j := 4) (k := 5) (by norm_num) (by norm_num) hd_inv he_inv).symm
    calc f⁻¹ * e⁻¹ * d⁻¹ = e⁻¹ * f⁻¹ * d⁻¹ := by rw [hfe]
      _ = e⁻¹ * (f⁻¹ * d⁻¹) := by group
      _ = e⁻¹ * (d⁻¹ * f⁻¹) := by rw [hfd]
      _ = (e⁻¹ * d⁻¹) * f⁻¹ := by group
      _ = (d⁻¹ * e⁻¹) * f⁻¹ := by rw [hed]
      _ = d⁻¹ * e⁻¹ * f⁻¹ := by group
  obtain ⟨p, hp, q, hq, r, hr, hpqr⟩ := comm_Usec_mem (T := T) hT hb hv
  have hp_inv : p⁻¹ ∈ T.Uprime 4 := (T.Uprime 4).inv_mem hp
  have hq_inv : q⁻¹ ∈ T.Uprime 6 := (T.Uprime 6).inv_mem hq
  have hr_inv : r⁻¹ ∈ T.U 7 := (T.U 7).inv_mem hr
  have hvb : ⁅v, b⁆ = p⁻¹ * q⁻¹ * r⁻¹ := by
    have h1 : ⁅v, b⁆ = ⁅b, v⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h1, hpqr]
    have h2 : (p * q * r)⁻¹ = r⁻¹ * q⁻¹ * p⁻¹ := by group
    rw [h2]
    have hqp : q⁻¹ * p⁻¹ = p⁻¹ * q⁻¹ :=
      (T.Uprime_comm (j := 4) (k := 6) (by norm_num) (by norm_num) hp_inv
        (T.Uprime_le 6 hq_inv)).symm
    have hrp : r⁻¹ * p⁻¹ = p⁻¹ * r⁻¹ :=
      (T.Uprime_comm (j := 4) (k := 7) (by norm_num) (by norm_num) hp_inv hr_inv).symm
    have hrq : r⁻¹ * q⁻¹ = q⁻¹ * r⁻¹ :=
      (T.Uprime_comm (j := 6) (k := 7) (by norm_num) (by norm_num) hq_inv hr_inv).symm
    calc r⁻¹ * q⁻¹ * p⁻¹ = q⁻¹ * r⁻¹ * p⁻¹ := by rw [hrq]
      _ = q⁻¹ * (r⁻¹ * p⁻¹) := by group
      _ = q⁻¹ * (p⁻¹ * r⁻¹) := by rw [hrp]
      _ = (q⁻¹ * p⁻¹) * r⁻¹ := by group
      _ = (p⁻¹ * q⁻¹) * r⁻¹ := by rw [hqp]
      _ = p⁻¹ * q⁻¹ * r⁻¹ := by group
  have hc_inv : c⁻¹ = c :=
    inv_eq_of_mul_eq_one_right
      (Uprime_mul_self (T := T) hT (show Even (2 : ℤ) from ⟨1, by norm_num⟩) hc)
  have hr_inv_eq : r⁻¹ = r := by
    exact inv_eq_of_mul_eq_one_right
      (lemma35_i (T := T) hT (j := 7) (show Odd (7 : ℤ) from ⟨3, by norm_num⟩) hr)
  have hcr : ⁅c, r⁻¹⁆ ∈ T.Uprime 4 := by
    rw [hr_inv_eq]
    have h := (comm_odd_Uprime' (T := T) hT (j := 7)
      (show Odd (7 : ℤ) from ⟨3, by norm_num⟩) hr hc).1
    have h2 : ⁅c, r⁆ = ⁅r, c⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h2]
    exact (T.Uprime 4).inv_mem h
  have hc_p : c * p⁻¹ * c⁻¹ = p⁻¹ := by
    have h := T.Uprime_comm (j := 2) (k := 4) (by norm_num) (by norm_num) hc
      (T.Uprime_le 4 hp_inv)
    rw [show c * p⁻¹ = p⁻¹ * c from h]
    group
  have hc_q : c * q⁻¹ * c⁻¹ = q⁻¹ := by
    have h := T.Uprime_comm (j := 2) (k := 6) (by norm_num) (by norm_num) hc
      (T.Uprime_le 6 hq_inv)
    rw [show c * q⁻¹ = q⁻¹ * c from h]
    group
  have hc_r : c * r⁻¹ * c⁻¹ = ⁅c, r⁻¹⁆ * r⁻¹ := by
    simp only [commutatorElement_def]
    group
  have hcbc : c * ⁅v, b⁆ * c⁻¹ = p⁻¹ * q⁻¹ * ⁅c, r⁻¹⁆ * r⁻¹ := by
    rw [hvb]
    calc c * (p⁻¹ * q⁻¹ * r⁻¹) * c⁻¹ =
        (c * p⁻¹ * c⁻¹) * (c * q⁻¹ * c⁻¹) * (c * r⁻¹ * c⁻¹) := by group
      _ = p⁻¹ * q⁻¹ * (⁅c, r⁻¹⁆ * r⁻¹) := by rw [hc_p, hc_q, hc_r]
      _ = p⁻¹ * q⁻¹ * ⁅c, r⁻¹⁆ * r⁻¹ := by group
  have hvb' : ⁅v, b'⁆ = ⁅v, c⁆ * (c * ⁅v, b⁆ * c⁻¹) := by
    rw [← hcb]
    simp only [commutatorElement_def]
    group
  have hEq1 : ⁅v, b'⁆ = d⁻¹ * e⁻¹ * f⁻¹ * p⁻¹ * q⁻¹ * ⁅c, r⁻¹⁆ * r⁻¹ := by
    rw [hvb', hvc, hcbc]
    group
  have hf_p : f⁻¹ * p⁻¹ = p⁻¹ * f⁻¹ :=
    (T.Uprime_comm (j := 4) (k := 6) (by norm_num) (by norm_num) hp_inv
      (T.Uprime_le 6 hf_inv)).symm
  have he_p : e⁻¹ * p⁻¹ = p⁻¹ * e⁻¹ :=
    (T.Uprime_comm (j := 4) (k := 5) (by norm_num) (by norm_num) hp_inv he_inv).symm
  have hq_g : q⁻¹ * ⁅c, r⁻¹⁆ = ⁅c, r⁻¹⁆ * q⁻¹ :=
    (T.Uprime_comm (j := 4) (k := 6) (by norm_num) (by norm_num) hcr
      (T.Uprime_le 6 hq_inv)).symm
  have hf_g : f⁻¹ * ⁅c, r⁻¹⁆ = ⁅c, r⁻¹⁆ * f⁻¹ :=
    (T.Uprime_comm (j := 4) (k := 6) (by norm_num) (by norm_num) hcr
      (T.Uprime_le 6 hf_inv)).symm
  have he_g : e⁻¹ * ⁅c, r⁻¹⁆ = ⁅c, r⁻¹⁆ * e⁻¹ :=
    (T.Uprime_comm (j := 4) (k := 5) (by norm_num) (by norm_num) hcr he_inv).symm
  have hEq1' : ⁅v, b'⁆ =
      (d⁻¹ * p⁻¹ * ⁅c, r⁻¹⁆) * e⁻¹ * (f⁻¹ * q⁻¹) * r⁻¹ := by
    rw [hEq1]
    calc d⁻¹ * e⁻¹ * f⁻¹ * p⁻¹ * q⁻¹ * ⁅c, r⁻¹⁆ * r⁻¹
        = d⁻¹ * e⁻¹ * (f⁻¹ * p⁻¹) * q⁻¹ * ⁅c, r⁻¹⁆ * r⁻¹ := by group
      _ = d⁻¹ * e⁻¹ * (p⁻¹ * f⁻¹) * q⁻¹ * ⁅c, r⁻¹⁆ * r⁻¹ := by rw [hf_p]
      _ = d⁻¹ * (e⁻¹ * p⁻¹) * f⁻¹ * q⁻¹ * ⁅c, r⁻¹⁆ * r⁻¹ := by group
      _ = d⁻¹ * (p⁻¹ * e⁻¹) * f⁻¹ * q⁻¹ * ⁅c, r⁻¹⁆ * r⁻¹ := by rw [he_p]
      _ = d⁻¹ * p⁻¹ * e⁻¹ * f⁻¹ * (q⁻¹ * ⁅c, r⁻¹⁆) * r⁻¹ := by group
      _ = d⁻¹ * p⁻¹ * e⁻¹ * f⁻¹ * (⁅c, r⁻¹⁆ * q⁻¹) * r⁻¹ := by rw [hq_g]
      _ = d⁻¹ * p⁻¹ * e⁻¹ * (f⁻¹ * ⁅c, r⁻¹⁆) * q⁻¹ * r⁻¹ := by group
      _ = d⁻¹ * p⁻¹ * e⁻¹ * (⁅c, r⁻¹⁆ * f⁻¹) * q⁻¹ * r⁻¹ := by rw [hf_g]
      _ = d⁻¹ * p⁻¹ * (e⁻¹ * ⁅c, r⁻¹⁆) * f⁻¹ * q⁻¹ * r⁻¹ := by group
      _ = d⁻¹ * p⁻¹ * (⁅c, r⁻¹⁆ * e⁻¹) * f⁻¹ * q⁻¹ * r⁻¹ := by rw [he_g]
      _ = (d⁻¹ * p⁻¹ * ⁅c, r⁻¹⁆) * e⁻¹ * (f⁻¹ * q⁻¹) * r⁻¹ := by group
  obtain ⟨p', hp', q', hq', r', hr', hpqr'⟩ := comm_Usec_mem (T := T) hT hb' hv
  have hq'_inv : q'⁻¹ ∈ T.Uprime 6 := (T.Uprime 6).inv_mem hq'
  have hp'_inv : p'⁻¹ ∈ T.Uprime 4 := (T.Uprime 4).inv_mem hp'
  have hr'_inv : r'⁻¹ ∈ T.U 7 := (T.U 7).inv_mem hr'
  have hEq2 : ⁅v, b'⁆ = p'⁻¹ * q'⁻¹ * r'⁻¹ := by
    have h1 : ⁅v, b'⁆ = ⁅b', v⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h1, hpqr']
    have h2 : (p' * q' * r')⁻¹ = r'⁻¹ * q'⁻¹ * p'⁻¹ := by group
    rw [h2]
    have hqp : q'⁻¹ * p'⁻¹ = p'⁻¹ * q'⁻¹ :=
      (T.Uprime_comm (j := 4) (k := 6) (by norm_num) (by norm_num) hp'_inv
        (T.Uprime_le 6 hq'_inv)).symm
    have hrp : r'⁻¹ * p'⁻¹ = p'⁻¹ * r'⁻¹ :=
      (T.Uprime_comm (j := 4) (k := 7) (by norm_num) (by norm_num) hp'_inv hr'_inv).symm
    have hrq : r'⁻¹ * q'⁻¹ = q'⁻¹ * r'⁻¹ :=
      (T.Uprime_comm (j := 6) (k := 7) (by norm_num) (by norm_num) hq'_inv hr'_inv).symm
    calc r'⁻¹ * q'⁻¹ * p'⁻¹ = q'⁻¹ * r'⁻¹ * p'⁻¹ := by rw [hrq]
      _ = q'⁻¹ * (r'⁻¹ * p'⁻¹) := by group
      _ = q'⁻¹ * (p'⁻¹ * r'⁻¹) := by rw [hrp]
      _ = (q'⁻¹ * p'⁻¹) * r'⁻¹ := by group
      _ = (p'⁻¹ * q'⁻¹) * r'⁻¹ := by rw [hqp]
      _ = p'⁻¹ * q'⁻¹ * r'⁻¹ := by group
  have hL : d⁻¹ * p⁻¹ * ⁅c, r⁻¹⁆ ∈ win T.U 4 4 := by
    rw [T.win_self]
    exact (T.U 4).mul_mem ((T.U 4).mul_mem (T.Uprime_le 4 hd_inv) (T.Uprime_le 4 hp_inv))
      (T.Uprime_le 4 hcr)
  have hL' : p'⁻¹ ∈ win T.U 4 4 := by
    rw [T.win_self]
    exact T.Uprime_le 4 hp'_inv
  have hR : e⁻¹ * (f⁻¹ * q⁻¹) * r⁻¹ ∈ win T.U 5 7 :=
    (win T.U 5 7).mul_mem ((win T.U 5 7).mul_mem
      (T.U_le_win (by norm_num) (by norm_num) he_inv)
      ((win T.U 5 7).mul_mem
        (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 6 hf_inv))
        (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 6 hq_inv))))
      (T.U_le_win (by norm_num) (by norm_num) hr_inv)
  have hR' : q'⁻¹ * r'⁻¹ ∈ win T.U 5 7 :=
    (win T.U 5 7).mul_mem
      (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 6 hq'_inv))
      (T.U_le_win (by norm_num) (by norm_num) hr'_inv)
  have hEqA : (d⁻¹ * p⁻¹ * ⁅c, r⁻¹⁆) * (e⁻¹ * (f⁻¹ * q⁻¹) * r⁻¹) =
      p'⁻¹ * (q'⁻¹ * r'⁻¹) := by
    calc (d⁻¹ * p⁻¹ * ⁅c, r⁻¹⁆) * (e⁻¹ * (f⁻¹ * q⁻¹) * r⁻¹)
        = d⁻¹ * p⁻¹ * ⁅c, r⁻¹⁆ * e⁻¹ * (f⁻¹ * q⁻¹) * r⁻¹ := by group
      _ = ⁅v, b'⁆ := by rw [hEq1']
      _ = p'⁻¹ * q'⁻¹ * r'⁻¹ := hEq2
      _ = p'⁻¹ * (q'⁻¹ * r'⁻¹) := by group
  have hA := eq_of_mul_eq_mul (T := T) (a := 4) (c := 4) (b := 7)
    (by norm_num) (by norm_num) (by norm_num) hL hL' hR hR' hEqA
  have hR6 : (f⁻¹ * q⁻¹) * r⁻¹ ∈ win T.U 6 7 :=
    (win T.U 6 7).mul_mem
      ((win T.U 6 7).mul_mem
        (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 6 hf_inv))
        (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 6 hq_inv)))
      (T.U_le_win (by norm_num) (by norm_num) hr_inv)
  have hR6' : q'⁻¹ * r'⁻¹ ∈ win T.U 6 7 :=
    (win T.U 6 7).mul_mem
      (T.U_le_win (by norm_num) (by norm_num) (T.Uprime_le 6 hq'_inv))
      (T.U_le_win (by norm_num) (by norm_num) hr'_inv)
  have hB := eq_of_mul_eq_mul (T := T) (a := 5) (c := 5) (b := 7)
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [T.win_self]; exact he_inv)
    (by rw [T.win_self]; exact (T.U 5).one_mem)
    hR6 hR6' (by simpa [mul_assoc] using hA.2)
  have he1 : e = 1 := inv_eq_one.mp hB.1
  have hvc_e : ⁅v, c⁆ = d⁻¹ * f⁻¹ := by
    rw [hvc, he1]
    group
  have hmem : ⁅v, c⁆ ∈ (T.Uprime 4 : Set G) * (T.Uprime 6 : Set G) := by
    rw [hvc_e]
    exact Set.mem_mul.mpr ⟨d⁻¹, hd_inv, f⁻¹, hf_inv, rfl⟩
  have hc1 : c = 1 := lemma38_i (T := T) hv hv1 hc hmem
  refine ⟨?_, ?_⟩
  · have h1 : a'⁻¹ * a = 1 := hc1
    exact (inv_mul_eq_one.mp h1).symm
  · calc b = 1 * b := by group
      _ = c * b := by rw [hc1]
      _ = b' := hcb

theorem Uprime_mul_Usec_inj (hT : T.Normalized) {j : ℤ} (hj : Even j) {a a' b b' : G}
    (ha : a ∈ T.Uprime j) (ha' : a' ∈ T.Uprime j) (hb : b ∈ T.Usec j) (hb' : b' ∈ T.Usec j)
    (h : a * b = a' * b') : a = a' ∧ b = b' := by
  obtain ⟨k, hk⟩ := hj
  have hs : Even (j - 2) := ⟨k - 1, by rw [hk]; ring⟩
  have hT' : (T.shift (j - 2)).Normalized := Normalized.shift (T := T) hT hs
  have ha2 : a ∈ (T.shift (j - 2)).Uprime 2 := by
    rw [Uprime_shift]
    rwa [show 2 + (j - 2) = j by ring]
  have ha2' : a' ∈ (T.shift (j - 2)).Uprime 2 := by
    rw [Uprime_shift]
    rwa [show 2 + (j - 2) = j by ring]
  have hb2 : b ∈ (T.shift (j - 2)).Usec 2 := by
    rw [Usec_shift]
    rwa [show 2 + (j - 2) = j by ring]
  have hb2' : b' ∈ (T.shift (j - 2)).Usec 2 := by
    rw [Usec_shift]
    rwa [show 2 + (j - 2) = j by ring]
  exact Uprime_mul_Usec_inj_two (T := T.shift (j - 2)) hT' ha2 ha2' hb2 hb2' h

theorem lemma316_ii (hT : T.Normalized) {j : ℤ} (hj : Even j) {x : G} (hx : x ∈ T.U j) :
    ∃ a ∈ T.Uprime j,
      x = a ∨ ∃ w ∈ T.Uprime (j + 8), w ≠ 1 ∧ x = T.nu (j + 8) w * a := by
  obtain ⟨a, ha, b, hb, heq⟩ :=
    mem_Uprime_mul_Usec (T := T) hT hj ((T.U j).inv_mem hx)
  have hx_eq : x = (a * b)⁻¹ := by
    calc x = (x⁻¹)⁻¹ := by group
      _ = (a * b)⁻¹ := by rw [heq]
  have hb' : b = 1 ∨ ∃ w ∈ T.Uprime (j - 8), w ≠ 1 ∧ b = T.nu' (j - 8) w := by
    simpa only [TitsSystem.Usec, Set.mem_setOf_eq] using hb
  obtain ⟨k, hk⟩ := hj
  have hj8 : Even (j - 8) := ⟨k - 4, by rw [hk]; ring⟩
  refine ⟨a⁻¹, (T.Uprime j).inv_mem ha, ?_⟩
  rcases hb' with hb1 | ⟨w, hw, hw1, hbw⟩
  · left
    rw [hx_eq, hb1, mul_one]
  · right
    have hw8 : w ∈ T.Uprime (j + 8) := by
      have h := T.Uprime_add_two_mul (j := j + 8) (k := -1)
      rw [show (j + 8) + 16 * (-1) = j - 8 by ring] at h
      rwa [h] at hw
    have hbnu : T.nu' (j - 8) w = T.nu' (j + 8) w := by
      have h := T.nu'_add_two_mul (by norm_num : 3 ≤ 8) (i := j + 8) (k := -1) w
      rwa [show (j + 8) + 2 * ((8 : ℕ) : ℤ) * (-1) = j - 8 by ring] at h
    have hnu : T.nu (j - 8) w = T.nu (j + 8) w := by
      have h := T.nu_add_two_mul (by norm_num : 3 ≤ 8) (i := j + 8) (k := -1) w
      rwa [show (j + 8) + 2 * ((8 : ℕ) : ℤ) * (-1) = j - 8 by ring] at h
    have hbinv : b⁻¹ = T.nu (j + 8) w := by
      rw [hbw, ← hnu]
      exact (lemma316_i (T := T) hT hj8 hw hw1).symm
    refine ⟨w, hw8, hw1, ?_⟩
    rw [hx_eq]
    calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
      _ = T.nu (j + 8) w * a⁻¹ := by rw [hbinv]

private theorem lemma316_iii_zero (hT : T.Normalized) {x : G} (hx : x ∈ T.U 0) :
    x * x ∈ T.Uprime 0 := by
  by_contra hxx
  have hx2 : x * x ∈ T.U 0 := (T.U 0).mul_mem hx hx
  obtain ⟨a, ha, hxcase⟩ :=
    lemma316_ii (T := T) hT (show Even (0 : ℤ) from ⟨0, by norm_num⟩) hx
  rcases hxcase with hxa | ⟨v, hv, hv1, hxv⟩
  · exact hxx (by rw [hxa]; exact (T.Uprime 0).mul_mem ha ha)
  · obtain ⟨a', ha', hx2case⟩ :=
      lemma316_ii (T := T) hT (show Even (0 : ℤ) from ⟨0, by norm_num⟩) hx2
    rcases hx2case with hx2a | ⟨v', hv', hv'1, hx2v'⟩
    · exact hxx (by rw [hx2a]; exact ha')
    · obtain ⟨u3, hu3, hu3'⟩ := Subgroup.exists_mem_ne_one_of_ne_bot (T.ne_bot 3)
      have hca : a * u3⁻¹ = u3⁻¹ * a :=
        T.Uprime_comm (j := 0) (k := 3) (by norm_num) (by norm_num) ha ((T.U 3).inv_mem hu3)
      have hca' : a' * u3⁻¹ = u3⁻¹ * a' :=
        T.Uprime_comm (j := 0) (k := 3) (by norm_num) (by norm_num) ha' ((T.U 3).inv_mem hu3)
      have hxcomm : ⁅x, u3⁻¹⁆ = ⁅T.nu 8 v, u3⁻¹⁆ := by
        rw [hxv]
        have hzero : ⁅a, u3⁻¹⁆ = 1 := by
          simp only [commutatorElement_def]
          rw [hca]
          group
        calc ⁅T.nu 8 v * a, u3⁻¹⁆ =
            T.nu 8 v * ⁅a, u3⁻¹⁆ * (T.nu 8 v)⁻¹ * ⁅T.nu 8 v, u3⁻¹⁆ := by
              simp only [commutatorElement_def]
              group
          _ = ⁅T.nu 8 v, u3⁻¹⁆ := by rw [hzero]; group
      have hcU : ⁅T.nu 8 v, u3⁻¹⁆ ∈ T.Uprime 2 := by
        have hz : (T.mu 3 u3)⁻¹ * v * T.mu 3 u3 ∈ T.Uprime 6 := by
          have h := mu_conj_mem_Uprime (T := T) (i := 3) (j := 8) ((T.U 3).inv_mem hu3)
            (inv_ne_one.mpr hu3') hv
          rw [T.mu_inv (by norm_num : 3 ≤ 8) hu3 hu3'] at h
          simpa using h
        have h := mu_conj_mem_Uprime (T := T) (i := 8) (j := 6) (T.Uprime_le 8 hv) hv1 hz
        have h18 : T.Uprime (2 * 8 + 8 - 6) = T.Uprime 2 := by
          have h := T.Uprime_add_two_mul (j := 2) (k := 1)
          simpa using h
        rw [h18] at h
        rw [lemma34_i (T := T) hT hu3 hu3' hv hv1]
        exact h
      have hc_comm : x * ⁅T.nu 8 v, u3⁻¹⁆ = ⁅T.nu 8 v, u3⁻¹⁆ * x :=
        (T.Uprime_comm (j := 2) (k := 0) (by norm_num) (by norm_num) hcU hx).symm
      have hc2 : ⁅T.nu 8 v, u3⁻¹⁆ * ⁅T.nu 8 v, u3⁻¹⁆ = 1 :=
        Uprime_mul_self (T := T) hT (show Even (2 : ℤ) from ⟨1, by norm_num⟩) hcU
      have hsq : ⁅x * x, u3⁻¹⁆ = 1 := by
        have h1 : ⁅x * x, u3⁻¹⁆ = x * ⁅x, u3⁻¹⁆ * x⁻¹ * ⁅x, u3⁻¹⁆ := by
          simp only [commutatorElement_def]
          group
        rw [h1, hxcomm]
        have h2 : x * ⁅T.nu 8 v, u3⁻¹⁆ * x⁻¹ = ⁅T.nu 8 v, u3⁻¹⁆ := by
          rw [hc_comm]
          group
        rw [h2, hc2]
      have hx2comm : ⁅x * x, u3⁻¹⁆ = ⁅T.nu 8 v', u3⁻¹⁆ := by
        rw [hx2v']
        have hzero : ⁅a', u3⁻¹⁆ = 1 := by
          simp only [commutatorElement_def]
          rw [hca']
          group
        calc ⁅T.nu 8 v' * a', u3⁻¹⁆ =
            T.nu 8 v' * ⁅a', u3⁻¹⁆ * (T.nu 8 v')⁻¹ * ⁅T.nu 8 v', u3⁻¹⁆ := by
              simp only [commutatorElement_def]
              group
          _ = ⁅T.nu 8 v', u3⁻¹⁆ := by rw [hzero]; group
      have hne : ⁅T.nu 8 v', u3⁻¹⁆ ≠ 1 := by
        rw [lemma34_i (T := T) hT hu3 hu3' hv' hv'1]
        intro h
        have hz : (T.mu 3 u3)⁻¹ * v' * T.mu 3 u3 = 1 := by
          have h2 := congrArg (fun t => (T.mu 8 v')⁻¹ * t * T.mu 8 v') h
          simpa [mul_assoc] using h2
        have hv'one : v' = 1 := by
          have h3 := congrArg (fun t => T.mu 3 u3 * t * (T.mu 3 u3)⁻¹) hz
          simpa [mul_assoc] using h3
        exact hv'1 hv'one
      rw [hx2comm] at hsq
      exact hne hsq

theorem lemma316_iii (hT : T.Normalized) {j : ℤ} (hj : Even j) {x : G} (hx : x ∈ T.U j) :
    x * x ∈ T.Uprime j := by
  have hTj : (T.shift j).Normalized := Normalized.shift (T := T) hT hj
  have hx' : x ∈ (T.shift j).U 0 := by
    rw [shift_U]
    simpa using hx
  have h := lemma316_iii_zero (T := T.shift j) hTj hx'
  have h' : x * x ∈ T.Uprime (0 + j) := by
    have := h
    rw [Uprime_shift] at this
    exact this
  rwa [zero_add] at h'

end TitsSystem

end CFSG.GH74.Tits83
