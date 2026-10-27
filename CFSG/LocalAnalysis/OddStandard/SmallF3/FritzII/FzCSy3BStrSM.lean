module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BStrH

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

variable {G : Type} [Group G]

namespace FzCSy3bStr

variable {x₁ x₂ t a b c : G} {Wp F P M₂ M₃ U : Subgroup G}

private theorem fzc_sy3_sm_x1_mem : x₁ ∈ baseGrp x₁ x₂ :=
  Subgroup.subset_closure (by simp)

private theorem fzc_sy3_sm_x2_mem : x₂ ∈ baseGrp x₁ x₂ :=
  Subgroup.subset_closure (by simp)

private theorem fzc_sy3_sm_ζ4 (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    (x₁ * x₂) ^ 4 = 1 := by
  have h1 : x₁ ^ 4 = 1 := by rw [← hs.ord₁]; exact pow_orderOf_eq_one x₁
  have h2 : x₂ ^ 4 = 1 := by rw [← hs.ord₂]; exact pow_orderOf_eq_one x₂
  rw [(show Commute x₁ x₂ from hs.comm).mul_pow 4, h1, h2, mul_one]

private theorem fzc_sy3_sm_x2_pow4 (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    x₂ ^ 4 = 1 := by
  rw [← hs.ord₂]; exact pow_orderOf_eq_one x₂

private theorem fzc_sy3_sm_t_sq (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    t * t = 1 := by
  simpa [pow_two] using hs.t_sq

private theorem fzc_sy3_sm_ζ_mem (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    x₁ * x₂ ∈ Wp :=
  hs.E_le_Wp (mul_mem (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp)))

private theorem fzc_sy3_sm_aU (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) : a ∈ U :=
  hs.chain.2.2.1 (hs.chain.2.1 hs.a_mem)

private theorem fzc_sy3_sm_sq_factor (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U)
    {g w : G} (hg2 : g * g ∈ Wp) (hw : w ∈ Wp) :
    (g * w) ^ 2 = (g * w * g⁻¹ * w) * (g * g) := by
  have hcomm : (g * g) * w = w * (g * g) := hs.Wp_comm (g * g) hg2 w hw
  rw [pow_two]
  calc (g * w) * (g * w) = ((g * w * g⁻¹) * (g * g)) * w := by group
    _ = (g * w * g⁻¹) * ((g * g) * w) := by group
    _ = (g * w * g⁻¹) * (w * (g * g)) := by rw [hcomm]
    _ = (g * w * g⁻¹ * w) * (g * g) := by group

private theorem fzc_sy3_sm_c_conj (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ e ∈ baseGrp x₁ x₂, ∃ m : ℕ, c * e * c⁻¹ * e = (x₁ * x₂) ^ m := by
  intro e he
  obtain ⟨i, j, -, -, rfl⟩ := fzc_sy3_coord hs.comm hs.ord₁ hs.ord₂ he
  have hcom : Commute x₁ x₂ := hs.comm
  refine ⟨i + j, ?_⟩
  calc c * (x₁ ^ i * x₂ ^ j) * c⁻¹ * (x₁ ^ i * x₂ ^ j)
      = (c * x₁ ^ i * c⁻¹) * (c * x₂ ^ j * c⁻¹) * (x₁ ^ i * x₂ ^ j) := by group
    _ = x₂ ^ i * x₁ ^ j * (x₁ ^ i * x₂ ^ j) := by
          rw [← conj_pow, ← conj_pow, hs.c_x₁, hs.c_x₂]
    _ = x₂ ^ i * (x₁ ^ j * x₁ ^ i) * x₂ ^ j := by group
    _ = x₂ ^ i * (x₁ ^ (j + i) * x₂ ^ j) := by group
    _ = x₂ ^ i * (x₂ ^ j * x₁ ^ (j + i)) := by rw [(hcom.pow_pow (j + i) j).eq]
    _ = x₂ ^ i * x₂ ^ j * x₁ ^ (j + i) := by group
    _ = x₂ ^ (i + j) * x₁ ^ (j + i) := by rw [← pow_add]
    _ = x₂ ^ (i + j) * x₁ ^ (i + j) := by rw [Nat.add_comm j i]
    _ = x₁ ^ (i + j) * x₂ ^ (i + j) := by
          rw [(hcom.pow_pow (i + j) (i + j)).eq.symm]
    _ = (x₁ * x₂) ^ (i + j) := by rw [← hcom.mul_pow (i + j)]

private theorem fzc_sy3_sm_a_conj (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ e ∈ baseGrp x₁ x₂, ∃ m : ℕ, a * e * a⁻¹ * e = (x₁ * x₂) ^ (2 * m) := by
  intro e he
  obtain ⟨i, j, -, -, rfl⟩ := fzc_sy3_coord hs.comm hs.ord₁ hs.ord₂ he
  have hcom : Commute x₁ x₂ := hs.comm
  have h1 : x₁ ^ 4 = 1 := by rw [← hs.ord₁]; exact pow_orderOf_eq_one x₁
  have h2 : x₂ ^ 4 = 1 := by rw [← hs.ord₂]; exact pow_orderOf_eq_one x₂
  rcases hs.a_x with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
  · refine ⟨0, ?_⟩
    rw [show 2 * 0 = 0 by norm_num, pow_zero]
    calc a * (x₁ ^ i * x₂ ^ j) * a⁻¹ * (x₁ ^ i * x₂ ^ j)
        = (a * x₁ ^ i * a⁻¹) * (a * x₂ ^ j * a⁻¹) * (x₁ ^ i * x₂ ^ j) := by group
      _ = (x₁ ^ 3) ^ i * (x₂ ^ 3) ^ j * (x₁ ^ i * x₂ ^ j) := by
            rw [← conj_pow, ← conj_pow, ha1, ha2]
      _ = x₁ ^ (3 * i) * x₂ ^ (3 * j) * (x₁ ^ i * x₂ ^ j) := by
            rw [← pow_mul, ← pow_mul]
      _ = x₁ ^ (3 * i) * (x₂ ^ (3 * j) * x₁ ^ i) * x₂ ^ j := by group
      _ = x₁ ^ (3 * i) * (x₁ ^ i * x₂ ^ (3 * j)) * x₂ ^ j := by
            rw [(hcom.pow_pow i (3 * j)).eq.symm]
      _ = (x₁ ^ (3 * i) * x₁ ^ i) * (x₂ ^ (3 * j) * x₂ ^ j) := by group
      _ = x₁ ^ (3 * i + i) * x₂ ^ (3 * j + j) := by rw [← pow_add, ← pow_add]
      _ = 1 := by
            rw [show 3 * i + i = 4 * i by ring, show 3 * j + j = 4 * j by ring,
              pow_mul, pow_mul, h1, h2]
            simp
  · refine ⟨i + j, ?_⟩
    have hxi : (x₁ * x₂ ^ 2) ^ i = x₁ ^ i * x₂ ^ (2 * i) := by
      rw [(hcom.pow_right 2).mul_pow i, ← pow_mul]
    have hxj : (x₁ ^ 2 * x₂) ^ j = x₁ ^ (2 * j) * x₂ ^ j := by
      rw [(hcom.pow_left 2).mul_pow j, ← pow_mul]
    have hae : a * (x₁ ^ i * x₂ ^ j) * a⁻¹ = x₁ ^ (i + 2 * j) * x₂ ^ (2 * i + j) := by
      calc a * (x₁ ^ i * x₂ ^ j) * a⁻¹
          = (a * x₁ ^ i * a⁻¹) * (a * x₂ ^ j * a⁻¹) := by group
        _ = (x₁ * x₂ ^ 2) ^ i * (x₁ ^ 2 * x₂) ^ j := by
              rw [← conj_pow, ← conj_pow, ha1, ha2]
        _ = (x₁ ^ i * x₂ ^ (2 * i)) * (x₁ ^ (2 * j) * x₂ ^ j) := by rw [hxi, hxj]
        _ = x₁ ^ i * (x₂ ^ (2 * i) * x₁ ^ (2 * j)) * x₂ ^ j := by group
        _ = x₁ ^ i * (x₁ ^ (2 * j) * x₂ ^ (2 * i)) * x₂ ^ j := by
              rw [(hcom.pow_pow (2 * j) (2 * i)).eq.symm]
        _ = (x₁ ^ i * x₁ ^ (2 * j)) * (x₂ ^ (2 * i) * x₂ ^ j) := by group
        _ = x₁ ^ (i + 2 * j) * x₂ ^ (2 * i + j) := by rw [← pow_add, ← pow_add]
    calc a * (x₁ ^ i * x₂ ^ j) * a⁻¹ * (x₁ ^ i * x₂ ^ j)
        = (x₁ ^ (i + 2 * j) * x₂ ^ (2 * i + j)) * (x₁ ^ i * x₂ ^ j) := by rw [hae]
      _ = x₁ ^ (i + 2 * j) * (x₂ ^ (2 * i + j) * x₁ ^ i) * x₂ ^ j := by group
      _ = x₁ ^ (i + 2 * j) * (x₁ ^ i * x₂ ^ (2 * i + j)) * x₂ ^ j := by
            rw [(hcom.pow_pow i (2 * i + j)).eq.symm]
      _ = (x₁ ^ (i + 2 * j) * x₁ ^ i) * (x₂ ^ (2 * i + j) * x₂ ^ j) := by group
      _ = x₁ ^ (i + 2 * j + i) * x₂ ^ (2 * i + j + j) := by rw [← pow_add, ← pow_add]
      _ = x₁ ^ (2 * (i + j)) * x₂ ^ (2 * (i + j)) := by
            rw [show i + 2 * j + i = 2 * (i + j) by ring,
              show 2 * i + j + j = 2 * (i + j) by ring]
      _ = (x₁ * x₂) ^ (2 * (i + j)) := by rw [← hcom.mul_pow (2 * (i + j))]

private theorem fzc_sy3_sm_x_sq (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ w ∈ Wp, ∃ m : ℕ, (a * w) ^ 2 = a ^ 2 * (x₁ * x₂) ^ (2 * m) := by
  intro w hw
  have hζW : x₁ * x₂ ∈ Wp := fzc_sy3_sm_ζ_mem hs
  have ha2 : a * a ∈ Wp := hs.sq_mem.1
  have hfac : (a * w) ^ 2 = (a * w * a⁻¹ * w) * (a * a) :=
    fzc_sy3_sm_sq_factor hs ha2 hw
  by_cases hwE : w ∈ baseGrp x₁ x₂
  · obtain ⟨m, hm⟩ := fzc_sy3_sm_a_conj hs w hwE
    refine ⟨m, ?_⟩
    rw [hfac, hm]
    rw [hs.Wp_comm ((x₁ * x₂) ^ (2 * m)) (pow_mem hζW (2 * m)) (a * a) ha2]
    conv_rhs => rw [pow_two]
  · have htw : t * w ∈ baseGrp x₁ x₂ := ((Wp_mem hs).mp hw).resolve_left hwE
    set e : G := t * w with he
    have heE : e ∈ baseGrp x₁ x₂ := by rw [he]; exact htw
    have hwe : w = e * t := by rw [he]; exact hs.fzc_eq_mul_t htw
    obtain ⟨m, hm⟩ := fzc_sy3_sm_a_conj hs e heE
    refine ⟨m + 1, ?_⟩
    have haeE : a * e * a⁻¹ ∈ baseGrp x₁ x₂ := hs.nrm_E a (fzc_sy3_sm_aU hs) e heE
    have haeW : a * e * a⁻¹ ∈ Wp := hs.E_le_Wp haeE
    have heW : e ∈ Wp := hs.E_le_Wp heE
    have htW : t ∈ Wp := hs.t_mem
    have hζ2W : (x₁ * x₂) ^ 2 ∈ Wp := pow_mem hζW 2
    have hte : t * e = e * t := (hs.fzc_commute_t_E e heE).eq
    have htζ2 : t * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * t :=
      hs.Wp_comm t htW ((x₁ * x₂) ^ 2) hζ2W
    have ht2 : t * t = 1 := fzc_sy3_sm_t_sq hs
    have hstep : (t * (x₁ * x₂) ^ 2) * (e * t) = (x₁ * x₂) ^ 2 * e := by
      calc (t * (x₁ * x₂) ^ 2) * (e * t)
          = t * (x₁ * x₂) ^ 2 * e * t := by group
        _ = (x₁ * x₂) ^ 2 * t * e * t := by rw [htζ2]
        _ = (x₁ * x₂) ^ 2 * (t * e) * t := by group
        _ = (x₁ * x₂) ^ 2 * (e * t) * t := by rw [hte]
        _ = (x₁ * x₂) ^ 2 * e * (t * t) := by group
        _ = (x₁ * x₂) ^ 2 * e := by rw [ht2, mul_one]
    have hvw : a * w * a⁻¹ * w = (x₁ * x₂) ^ (2 * m) * (x₁ * x₂) ^ 2 := by
      rw [hwe]
      calc a * (e * t) * a⁻¹ * (e * t)
          = (a * e * a⁻¹) * (a * t * a⁻¹) * (e * t) := by group
        _ = (a * e * a⁻¹) * (t * (x₁ * x₂) ^ 2) * (e * t) := by rw [hs.a_t]
        _ = (a * e * a⁻¹) * ((t * (x₁ * x₂) ^ 2) * (e * t)) := by group
        _ = (a * e * a⁻¹) * ((x₁ * x₂) ^ 2 * e) := by rw [hstep]
        _ = ((a * e * a⁻¹) * e) * (x₁ * x₂) ^ 2 := by
              rw [hs.Wp_comm ((x₁ * x₂) ^ 2) hζ2W e heW]; group
        _ = (x₁ * x₂) ^ (2 * m) * (x₁ * x₂) ^ 2 := by rw [hm]
    rw [hfac, hvw]
    rw [hs.Wp_comm ((x₁ * x₂) ^ (2 * m) * (x₁ * x₂) ^ 2)
      (mul_mem (pow_mem hζW (2 * m)) hζ2W) (a * a) ha2]
    conv_rhs => rw [pow_two]
    congr 1
    rw [← pow_add]
    congr 1

private theorem fzc_sy3_sm_y_sq (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ w ∈ Wp, ∃ m : ℕ, (c * w) ^ 2 = (x₁ * x₂) ^ m * t := by
  intro w hw
  have hζW : x₁ * x₂ ∈ Wp := fzc_sy3_sm_ζ_mem hs
  have hc2 : c * c ∈ Wp := hs.sq_mem.2.2.1
  have hfac : (c * w) ^ 2 = (c * w * c⁻¹ * w) * (c * c) :=
    fzc_sy3_sm_sq_factor hs hc2 hw
  have hcc : c * c = t := by rw [← pow_two]; exact hs.c_sq
  have hctc : c * t * c⁻¹ = t := by rw [← hcc]; group
  by_cases hwE : w ∈ baseGrp x₁ x₂
  · obtain ⟨m, hm⟩ := fzc_sy3_sm_c_conj hs w hwE
    refine ⟨m, ?_⟩
    rw [hfac, hm, hcc]
  · have htw : t * w ∈ baseGrp x₁ x₂ := ((Wp_mem hs).mp hw).resolve_left hwE
    set e : G := t * w with he
    have heE : e ∈ baseGrp x₁ x₂ := by rw [he]; exact htw
    have hwe : w = e * t := by rw [he]; exact hs.fzc_eq_mul_t htw
    obtain ⟨m, hm⟩ := fzc_sy3_sm_c_conj hs e heE
    refine ⟨m, ?_⟩
    have hte : t * e = e * t := (hs.fzc_commute_t_E e heE).eq
    have ht2 : t * t = 1 := fzc_sy3_sm_t_sq hs
    have hvw : c * w * c⁻¹ * w = (x₁ * x₂) ^ m := by
      rw [hwe]
      calc c * (e * t) * c⁻¹ * (e * t)
          = (c * e * c⁻¹) * (c * t * c⁻¹) * (e * t) := by group
        _ = (c * e * c⁻¹) * t * (e * t) := by rw [hctc]
        _ = (c * e * c⁻¹) * (t * e) * t := by group
        _ = (c * e * c⁻¹) * (e * t) * t := by rw [hte]
        _ = (c * e * c⁻¹) * e * (t * t) := by group
        _ = (c * e * c⁻¹) * e := by rw [ht2, mul_one]
        _ = (x₁ * x₂) ^ m := by rw [hm]
    rw [hfac, hvw, hcc]

private theorem fzc_sy3_sm_a2t (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∃ j : ℕ, (j = 1 ∨ j = 3) ∧ a ^ 2 * t = x₂ ^ 2 * (x₁ * x₂) ^ j := by
  have hcom : Commute x₁ x₂ := hs.comm
  have hx24 : x₂ ^ 4 = 1 := fzc_sy3_sm_x2_pow4 hs
  rcases hs.e₀ with h | h
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [h, pow_one]
    have h3 : x₂ ^ 3 = x₂ ^ 2 * x₂ := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ]
    calc x₁ * x₂ ^ 3 = x₁ * (x₂ ^ 2 * x₂) := by rw [h3]
      _ = x₁ * x₂ ^ 2 * x₂ := by group
      _ = x₂ ^ 2 * x₁ * x₂ := by rw [(hcom.pow_right 2).eq]
      _ = x₂ ^ 2 * (x₁ * x₂) := by group
  · refine ⟨3, Or.inr rfl, ?_⟩
    rw [h]
    have h25 : x₂ ^ 2 * x₂ ^ 3 = x₂ := by
      rw [← pow_add, show 2 + 3 = 1 + 4 by norm_num, pow_add, hx24, mul_one, pow_one]
    calc x₁ ^ 3 * x₂ = x₁ ^ 3 * (x₂ ^ 2 * x₂ ^ 3) := by rw [h25]
      _ = (x₁ ^ 3 * x₂ ^ 2) * x₂ ^ 3 := by group
      _ = (x₂ ^ 2 * x₁ ^ 3) * x₂ ^ 3 := by
            rw [hs.E_comm (x₁ ^ 3) (pow_mem fzc_sy3_sm_x1_mem 3) (x₂ ^ 2)
              (pow_mem fzc_sy3_sm_x2_mem 2)]
      _ = x₂ ^ 2 * (x₁ ^ 3 * x₂ ^ 3) := by group
      _ = x₂ ^ 2 * (x₁ * x₂) ^ 3 := by rw [← hcom.mul_pow 3]

theorem SM (hs : FzCSy3bStr x₁ x₂ t a b c Wp F P M₂ M₃ U) :
    ∀ x y : G, a⁻¹ * x ∈ Wp → c⁻¹ * y ∈ Wp →
      ∃ k : ℕ, x ^ 2 * (y ^ 2)⁻¹ = x₂ ^ 2 * (x₁ * x₂) ^ k := by
  intro x y hx hy
  set w : G := a⁻¹ * x with hw
  set w' : G := c⁻¹ * y with hw'
  have hxw : x = a * w := by rw [hw]; group
  have hyw : y = c * w' := by rw [hw']; group
  have hwmem : w ∈ Wp := by rw [hw]; exact hx
  have hw'mem : w' ∈ Wp := by rw [hw']; exact hy
  obtain ⟨m, hxm⟩ := fzc_sy3_sm_x_sq hs w hwmem
  obtain ⟨m', hym⟩ := fzc_sy3_sm_y_sq hs w' hw'mem
  obtain ⟨j, -, hjval⟩ := fzc_sy3_sm_a2t hs
  have hx2 : x ^ 2 = a ^ 2 * (x₁ * x₂) ^ (2 * m) := by rw [hxw, hxm]
  have hy2 : y ^ 2 = (x₁ * x₂) ^ m' * t := by rw [hyw, hym]
  have hζW : x₁ * x₂ ∈ Wp := fzc_sy3_sm_ζ_mem hs
  have hζ4 : (x₁ * x₂) ^ 4 = 1 := fzc_sy3_sm_ζ4 hs
  have hζinv : ((x₁ * x₂) ^ m')⁻¹ = (x₁ * x₂) ^ (3 * m') := by
    have h : (x₁ * x₂) ^ m' * (x₁ * x₂) ^ (3 * m') = 1 := by
      rw [← pow_add, show m' + 3 * m' = 4 * m' by ring, pow_mul, hζ4, one_pow]
    exact (eq_inv_of_mul_eq_one_right h).symm
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (fzc_sy3_sm_t_sq hs)
  have hswap : (x₁ * x₂) ^ (2 * m) * t = t * (x₁ * x₂) ^ (2 * m) :=
    hs.Wp_comm ((x₁ * x₂) ^ (2 * m)) (pow_mem hζW (2 * m)) t hs.t_mem
  refine ⟨j + 2 * m + 3 * m', ?_⟩
  rw [hx2, hy2, mul_inv_rev, hζinv, htinv]
  calc (a ^ 2 * (x₁ * x₂) ^ (2 * m)) * (t * (x₁ * x₂) ^ (3 * m'))
      = a ^ 2 * ((x₁ * x₂) ^ (2 * m) * t) * (x₁ * x₂) ^ (3 * m') := by group
    _ = a ^ 2 * (t * (x₁ * x₂) ^ (2 * m)) * (x₁ * x₂) ^ (3 * m') := by rw [hswap]
    _ = (a ^ 2 * t) * ((x₁ * x₂) ^ (2 * m) * (x₁ * x₂) ^ (3 * m')) := by group
    _ = (x₂ ^ 2 * (x₁ * x₂) ^ j) * (x₁ * x₂) ^ (2 * m + 3 * m') := by
          rw [hjval, ← pow_add]
    _ = x₂ ^ 2 * ((x₁ * x₂) ^ j * (x₁ * x₂) ^ (2 * m + 3 * m')) := by group
    _ = x₂ ^ 2 * (x₁ * x₂) ^ (j + (2 * m + 3 * m')) := by rw [← pow_add]
    _ = x₂ ^ 2 * (x₁ * x₂) ^ (j + 2 * m + 3 * m') := by
          rw [show j + (2 * m + 3 * m') = j + 2 * m + 3 * m' by ring]

end FzCSy3bStr

end CFSG.OddStandard.SmallF3.FritzII
