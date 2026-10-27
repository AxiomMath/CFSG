module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Levi

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup
open scoped commutatorElement Pointwise

@[expose] def uSign : List Bool → ℤ
  | [] => 1
  | false :: l => -uSign l
  | true :: l => uSign l

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem J_le_J₆_sup_J₁ : d.J ≤ d.J₆ ⊔ d.J₁ := by
  rintro _ ⟨⟨l, m⟩, rfl⟩
  obtain ⟨β, rfl⟩ := d.sq_surjective_units m
  have e : d.torus (l, β ^ 2) = d.hBCD β * d.torus (l * d.nmUnits β, 1) := by
    rw [hBCD_apply, ← map_mul]
    refine congrArg d.torus (Prod.ext ?_ (mul_one _).symm)
    change l = (d.nmUnits β)⁻¹ * (l * d.nmUnits β)
    rw [mul_comm l, inv_mul_cancel_left]
  rw [e]
  exact mul_mem (mem_sup_left (by rw [d.J₆_eq_range_hBCD]; exact ⟨β, rfl⟩))
    (mem_sup_right ((d.torus_mem_J₁_iff _).2 rfl))

theorem J_le_J₄_sup_J₂ : d.J ≤ d.J₄ ⊔ d.J₂ := by
  rintro _ ⟨⟨l, m⟩, rfl⟩
  obtain ⟨β, rfl⟩ := d.sq_surjective_units₀ l
  have e : d.torus (β ^ 2, m) = d.hA β * d.torus (1, d.unitsIncl β * m) := by
    rw [hA_apply, ← map_mul]
    refine congrArg d.torus (Prod.ext (mul_one _).symm ?_)
    change m = d.unitsIncl β⁻¹ * (d.unitsIncl β * m)
    rw [map_inv, inv_mul_cancel_left]
  rw [e]
  exact mul_mem (mem_sup_left (by rw [d.J₄_eq_range_hA]; exact ⟨β, rfl⟩))
    (mem_sup_right ((d.torus_mem_J₂_iff _).2 rfl))

theorem J₆_inf_J₁ : d.J₆ ⊓ d.J₁ = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨h6, h1⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨⟨l, m⟩, rfl, hm⟩ := d.mem_J₁.1 h1
  dsimp only at hm
  subst hm
  have hlm := (d.torus_mem_J₆_iff (l, 1)).1 h6
  dsimp only at hlm
  rw [Units.val_one, d.nm_one, mul_one] at hlm
  have hl : l = 1 := d.units₀_eq_one_of_sq (Units.ext (by
    rw [Units.val_pow_eq_pow_val, sq, hlm, Units.val_one]))
  rw [hl, mem_bot, show ((1 : (d.Γ₀)ˣ), (1 : d.Γˣ)) = 1 from rfl, map_one]

theorem eq_one_of_σ_mul_σσ_eq_one {m : d.Γ} (h : d.σ m * d.σ (d.σ m) = 1) : m = 1 := by
  have h1 : m * d.σ m = 1 := d.σ.injective (by rw [map_mul, map_one, h])
  have e : d.σ m = m⁻¹ := eq_inv_of_mul_eq_one_right h1
  have h2 : d.σ (d.σ m) = m := by rw [e, map_inv₀, e, inv_inv]
  have h3 : d.σ m = m := by conv_rhs => rw [← d.σ_cube m, h2]
  rw [h3] at h1
  exact d.sq_injective (by rw [sq, h1, one_pow])

theorem J₄_inf_J₂ : d.J₄ ⊓ d.J₂ = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨h4, h2⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨⟨l, m⟩, rfl, hl⟩ := d.mem_J₂.1 h2
  dsimp only at hl
  subst hl
  have hlm := (d.torus_mem_J₄_iff (1, m)).1 h4
  dsimp only at hlm
  rw [Units.val_one, OneMemClass.coe_one, one_mul] at hlm
  have hm : m = 1 := Units.ext (d.eq_one_of_σ_mul_σσ_eq_one hlm)
  rw [hm, mem_bot, show ((1 : (d.Γ₀)ˣ), (1 : d.Γˣ)) = 1 from rfl, map_one]

theorem u_mem_centralizer_J₁ : d.u ∈ centralizer (d.J₁ : Set X) := by
  rw [mem_centralizer_iff]
  intro g hg
  obtain ⟨⟨l, m⟩, rfl, hm⟩ := d.mem_J₁.1 hg
  dsimp only at hm
  subst hm
  have e : d.u * d.torus (l, 1) * d.u = d.torus (l, 1) := by
    rw [u_torus_eq, map_one, mul_one, inv_one]
  calc d.torus (l, 1) * d.u = d.u * d.torus (l, 1) * d.u * d.u := by rw [e]
    _ = d.u * d.torus (l, 1) := by rw [mul_assoc _ d.u, d.u_mul_self, mul_one]

theorem v_mem_centralizer_J₂ : d.v ∈ centralizer (d.J₂ : Set X) := by
  rw [mem_centralizer_iff]
  intro g hg
  obtain ⟨⟨l, m⟩, rfl, hl⟩ := d.mem_J₂.1 hg
  dsimp only at hl
  subst hl
  have e : d.v * d.torus (1, m) * d.v = d.torus (1, m) := by
    rw [v_torus_eq, inv_one, map_one, one_mul]
  calc d.torus (1, m) * d.v = d.v * d.torus (1, m) * d.v * d.v := by rw [e]
    _ = d.v * d.torus (1, m) := by rw [mul_assoc _ d.v, d.v_mul_self, mul_one]

theorem leviShort_le_centralizer_J₁ : d.leviShort ≤ centralizer (d.J₁ : Set X) := by
  rw [leviShort, closure_le]
  rintro g (hg | rfl)
  · rw [SetLike.mem_coe, mem_centralizer_iff]
    intro j hj
    exact ((mem_centralizer_iff.1 (mem_inf.1 hj).2) g hg).symm
  · exact d.u_mem_centralizer_J₁

theorem leviLong_le_centralizer_J₂ : d.leviLong ≤ centralizer (d.J₂ : Set X) := by
  rw [leviLong, closure_le]
  rintro g (hg | rfl)
  · rw [SetLike.mem_coe, mem_centralizer_iff]
    intro j hj
    exact ((mem_centralizer_iff.1 (mem_inf.1 hj).2) g hg).symm
  · exact d.v_mem_centralizer_J₂

theorem mem_J₆_of_mem_leviShort_of_mem_J {g : X} (hg : g ∈ d.leviShort) (hJ : g ∈ d.J) :
    g ∈ d.J₆ := by
  obtain ⟨x, hx, h, hh, e⟩ := d.exists_eq_mul_of_mem_leviShort_of_mem_B hg
    (le_sup_right (a := d.S) hJ)
  obtain ⟨-, rfl⟩ := d.eq_of_mul_eq_mul_of_S_J (one_mem d.S) (d.U₁_le_S hx) hJ hh.1
    (by rw [one_mul, e])
  exact hh

theorem mem_J₄_of_mem_leviLong_of_mem_J {g : X} (hg : g ∈ d.leviLong) (hJ : g ∈ d.J) :
    g ∈ d.J₄ := by
  obtain ⟨x, hx, h, hh, e⟩ := d.exists_eq_mul_of_mem_leviLong_of_mem_B hg
    (le_sup_right (a := d.S) hJ)
  obtain ⟨-, rfl⟩ := d.eq_of_mul_eq_mul_of_S_J (one_mem d.S) (d.U₂_le_S hx) hJ hh.1
    (by rw [one_mul, e])
  exact hh

theorem yamada_three_eight_four :
    normalizer (d.V : Set X) = normalizer (d.D : Set X) ∧
      normalizer (d.V : Set X) = d.D ⊔ (d.leviShort ⊔ d.J₁) ∧
      d.leviShort ⊓ d.J₁ = ⊥ ∧ d.J₁ ≤ centralizer (d.leviShort : Set X) ∧
      d.D ⊓ (d.leviShort ⊔ d.J₁) = ⊥ := by
  have hJ₁J : d.J₁ ≤ d.J := inf_le_left
  have hJK : d.J ≤ d.leviShort ⊔ d.J₁ :=
    d.J_le_J₆_sup_J₁.trans (sup_le_sup_right d.J₆_le_leviShort _)
  have hB : d.B ≤ d.D ⊔ (d.leviShort ⊔ d.J₁) := by
    refine sup_le ?_ (hJK.trans le_sup_right)
    rw [d.S_eq_sup]
    exact sup_le (d.U₁_le_leviShort.trans (le_sup_left.trans le_sup_right)) le_sup_left
  have hC : d.J₁ ≤ centralizer (d.leviShort : Set X) :=
    le_centralizer_iff.2 d.leviShort_le_centralizer_J₁
  refine ⟨d.normalizer_V_eq_normalizer_D, le_antisymm ?_ ?_, ?_, hC, ?_⟩
  · intro g hg
    rcases d.normalizer_V_cases hg with hgB | ⟨x, hx, h, hh, y, hy, rfl⟩
    · exact hB hgB
    · exact mul_mem (mul_mem (hB (mul_mem (le_sup_left (a := d.S) hx)
        (le_sup_right (a := d.S) hh))) (mem_sup_right (mem_sup_left d.u_mem_leviShort)))
        (mem_sup_right (mem_sup_left (d.U₁_le_leviShort hy)))
  · exact sup_le (d.D_le_S.trans d.S_le_normalizer_V)
      (sup_le d.leviShort_le_normalizer_V (hJ₁J.trans d.J_le_normalizer_V))
  · rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgK, hg1⟩ := Subgroup.mem_inf.1 hg
    have h6 := d.mem_J₆_of_mem_leviShort_of_mem_J hgK (hJ₁J hg1)
    rw [← d.J₆_inf_J₁]
    exact ⟨h6, hg1⟩
  · rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgD, hgKJ⟩ := Subgroup.mem_inf.1 hg
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _
      (hC.trans (centralizer_le_normalizer _))] at hgKJ
    obtain ⟨k, hk, j, hj, hkj⟩ := hgKJ
    replace hkj : k * j = g := hkj
    subst hkj
    have hkB : k ∈ d.B := by
      have := mul_mem (le_sup_left (a := d.S) (d.D_le_S hgD))
        (inv_mem (le_sup_right (a := d.S) (hJ₁J hj)))
      rwa [mul_inv_cancel_right] at this
    obtain ⟨x, hx, h, hh, rfl⟩ := d.exists_eq_mul_of_mem_leviShort_of_mem_B hk hkB
    obtain ⟨hxg, -⟩ := d.eq_of_mul_eq_mul_of_S_J (d.U₁_le_S hx) (d.D_le_S hgD)
      (mul_mem hh.1 (hJ₁J hj)) (one_mem _) (by rw [mul_one, mul_assoc])
    obtain ⟨a, rfl⟩ := hx
    have ha : a = 0 := d.x₁_mem_D_iff.1 (by rw [hxg]; exact hgD)
    rw [mem_bot, ← hxg, ha, d.x₁_zero]

theorem yamada_three_eight_five :
    normalizer (d.Y : Set X) = normalizer (d.W : Set X) ∧
      normalizer (d.Y : Set X) = normalizer (d.M : Set X) ∧
      normalizer (d.Y : Set X) = d.M ⊔ (d.leviLong ⊔ d.J₂) ∧
      d.leviLong ⊓ d.J₂ = ⊥ ∧ d.J₂ ≤ centralizer (d.leviLong : Set X) ∧
      d.M ⊓ (d.leviLong ⊔ d.J₂) = ⊥ := by
  have hJ₂J : d.J₂ ≤ d.J := inf_le_left
  have hJK : d.J ≤ d.leviLong ⊔ d.J₂ :=
    d.J_le_J₄_sup_J₂.trans (sup_le_sup_right d.J₄_le_leviLong _)
  have hB : d.B ≤ d.M ⊔ (d.leviLong ⊔ d.J₂) := by
    refine sup_le ?_ (hJK.trans le_sup_right)
    rw [d.S_eq_U₂_sup_M]
    exact sup_le (d.U₂_le_leviLong.trans (le_sup_left.trans le_sup_right)) le_sup_left
  have hC : d.J₂ ≤ centralizer (d.leviLong : Set X) :=
    le_centralizer_iff.2 d.leviLong_le_centralizer_J₂
  obtain ⟨hYW, hYM⟩ := d.normalizer_Y_eq_normalizer_W_and_M
  refine ⟨hYW, hYM, le_antisymm ?_ ?_, ?_, hC, ?_⟩
  · intro g hg
    rcases d.normalizer_Y_cases hg with hgB | ⟨x, hx, h, hh, y, hy, rfl⟩
    · exact hB hgB
    · exact mul_mem (mul_mem (hB (mul_mem (le_sup_left (a := d.S) hx)
        (le_sup_right (a := d.S) hh))) (mem_sup_right (mem_sup_left d.v_mem_leviLong)))
        (mem_sup_right (mem_sup_left (d.U₂_le_leviLong hy)))
  · exact sup_le (d.M_le_S.trans d.S_le_normalizer_Y)
      (sup_le d.leviLong_le_normalizer_Y (hJ₂J.trans d.J_le_normalizer_Y))
  · rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgK, hg2⟩ := Subgroup.mem_inf.1 hg
    have h4 := d.mem_J₄_of_mem_leviLong_of_mem_J hgK (hJ₂J hg2)
    rw [← d.J₄_inf_J₂]
    exact ⟨h4, hg2⟩
  · rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgM, hgKJ⟩ := Subgroup.mem_inf.1 hg
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _
      (hC.trans (centralizer_le_normalizer _))] at hgKJ
    obtain ⟨k, hk, j, hj, hkj⟩ := hgKJ
    replace hkj : k * j = g := hkj
    subst hkj
    have hkB : k ∈ d.B := by
      have := mul_mem (le_sup_left (a := d.S) (d.M_le_S hgM))
        (inv_mem (le_sup_right (a := d.S) (hJ₂J hj)))
      rwa [mul_inv_cancel_right] at this
    obtain ⟨x, hx, h, hh, rfl⟩ := d.exists_eq_mul_of_mem_leviLong_of_mem_B hk hkB
    obtain ⟨hxg, -⟩ := d.eq_of_mul_eq_mul_of_S_J (d.U₂_le_S hx) (d.M_le_S hgM)
      (mul_mem hh.1 (hJ₂J hj)) (one_mem _) (by simp only [mul_one, mul_assoc])
    obtain ⟨a, rfl⟩ := hx
    have ha : a = 0 := d.x₂_mem_M_iff.1 (by rw [hxg]; exact hgM)
    rw [mem_bot, ← hxg, ha, d.x₂_zero]

theorem J_commute {a b : X} (ha : a ∈ d.J) (hb : b ∈ d.J) : a * b = b * a := by
  obtain ⟨p, rfl⟩ := d.mem_J.1 ha
  obtain ⟨r, rfl⟩ := d.mem_J.1 hb
  rw [← map_mul, ← map_mul, mul_comm]

theorem J_le_normalizer_rootGroup (i : Fin 6) : d.J ≤ normalizer (d.rootGroup i : Set X) := by
  rintro _ ⟨h, rfl⟩
  fin_cases i
  · exact d.torus_mem_normalizer_U₁ h
  · exact d.torus_mem_normalizer_U₂ h
  · exact d.torus_mem_normalizer_U₃ h
  · exact d.torus_mem_normalizer_U₄ h
  · exact d.torus_mem_normalizer_U₅ h
  · exact d.torus_mem_normalizer_U₆ h

theorem conj_mem_Uminus {w j y : X} (hj : j ∈ d.J) (hy : y ∈ d.Uminus w) :
    j * y * j⁻¹ ∈ d.Uminus w := by
  have h : d.Uminus w ≤ (d.Uminus w).comap (MulAut.conj j).toMonoidHom := by
    refine iSup₂_le fun i hi z hz => ?_
    simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact le_iSup₂ (f := fun i (_ : ¬ d.rootGroup i ≤ d.conjS w) => d.rootGroup i) i hi
      ((mem_normalizer_iff.1 (d.J_le_normalizer_rootGroup i hj) z).1 hz)
  simpa using h hy

theorem bruhat_parts_of_commute {x h w y j : X} (hx : x ∈ d.S) (hh : h ∈ d.J) (hw : w ∈ d.weyl)
    (hy : y ∈ d.Uminus w) (hj : j ∈ d.J) (hjg : j * (x * h * w * y) * j⁻¹ = x * h * w * y) :
    j * x * j⁻¹ = x ∧ w * j * w⁻¹ = j ∧ j * y * j⁻¹ = y := by
  have hwj : w * j⁻¹ * w⁻¹ ∈ d.J := d.conj_mem_J hw (inv_mem hj)
  have hcomm : h * j = j * h := d.J_commute hh hj
  have e : j * (x * h * w * y) * j⁻¹ =
      (j * x * j⁻¹) * (h * (j * (w * j⁻¹ * w⁻¹))) * w * (j * y * j⁻¹) := by
    calc j * (x * h * w * y) * j⁻¹ = j * x * j⁻¹ * (j * h) * w * y * j⁻¹ := by group
      _ = j * x * j⁻¹ * (h * j) * w * y * j⁻¹ := by rw [hcomm]
      _ = _ := by group
  rw [e] at hjg
  have hjS : j ∈ normalizer (d.S : Set X) := by
    rw [d.normalizer_S]
    exact le_sup_right (a := d.S) hj
  obtain ⟨h1, h2, -, h4⟩ := d.bruhat_normal_form_unique
    ((mem_normalizer_iff.1 hjS x).1 hx) (mul_mem hh (mul_mem hj hwj)) hw
    (d.conj_mem_Uminus hj hy) hx hh hw hy hjg
  refine ⟨h1, ?_, h4⟩
  have h3 : j * (w * j⁻¹ * w⁻¹) = 1 := mul_eq_left.1 h2
  have h5 : w * j⁻¹ * w⁻¹ = j⁻¹ := eq_inv_of_mul_eq_one_right h3
  have h6 := congrArg (·⁻¹) h5
  simpa [mul_assoc] using h6

theorem torus_conj_nf (h : (d.Γ₀)ˣ × d.Γˣ) (a₁ : d.Γ) (a₂ : d.Γ₀) (a₃ a₄ : d.Γ)
    (a₅ a₆ : d.Γ₀) :
    d.torus h * d.nf (a₁, a₂, a₃, a₄, a₅, a₆) * (d.torus h)⁻¹ =
      d.nf ((h.2 : d.Γ) * a₁, (h.1 : d.Γ₀) * a₂, ((h.1 : d.Γ₀) : d.Γ) * h.2 * a₃,
        ((h.1 : d.Γ₀) : d.Γ) * d.σ h.2 * d.σ (d.σ h.2) * a₄, (h.1 : d.Γ₀) * d.nm h.2 * a₅,
        (h.1 : d.Γ₀) * (h.1 : d.Γ₀) * d.nm h.2 * a₆) := by
  rw [nf_apply, nf_apply, ← d.torus_x₁, ← d.torus_x₂, ← d.torus_x₃, ← d.torus_x₄,
    ← d.torus_x₅, ← d.torus_x₆]
  group

theorem eq_zero_of_mul_eq_self {K : Type*} [Field K] {c a : K} (hc : c ≠ 1) (h : c * a = a) :
    a = 0 := by
  have h1 : (c - 1) * a = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hc)

theorem exists_units₀_ne_one (hq : 4 ≤ q) : ∃ l : (d.Γ₀)ˣ, l ≠ 1 := by
  have h2 : 1 < Nat.card (d.Γ₀)ˣ := by
    rw [d.card_units_Γ₀]
    omega
  have := Finite.one_lt_card_iff_nontrivial.1 h2
  exact exists_ne 1

theorem exists_units_ne_one : ∃ m : d.Γˣ, m ≠ 1 := by
  have hq := d.two_le_q
  have h2 : 1 < Nat.card d.Γˣ := by
    rw [d.card_units_Γ]
    have : 8 ≤ q ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    omega
  have := Finite.one_lt_card_iff_nontrivial.1 h2
  exact exists_ne 1

theorem exists_mem_ker_nmUnits_ne_one : ∃ m : d.Γˣ, d.nmUnits m = 1 ∧ m ≠ 1 := by
  have hq := d.two_le_q
  have h2 : 1 < Nat.card d.nmUnits.ker := by
    rw [d.card_ker_nmUnits]
    nlinarith
  have := Finite.one_lt_card_iff_nontrivial.1 h2
  obtain ⟨⟨m, hm⟩, hne⟩ := exists_ne (1 : d.nmUnits.ker)
  exact ⟨m, hm, fun h => hne (Subtype.ext h)⟩

theorem coe_coe_ne_one {l : (d.Γ₀)ˣ} (hl : l ≠ 1) : ((l : d.Γ₀) : d.Γ) ≠ 1 := fun h =>
  hl (Units.ext (Subtype.ext h))

theorem coe_mul_self_ne_one {l : (d.Γ₀)ˣ} (hl : l ≠ 1) : (l : d.Γ₀) * (l : d.Γ₀) ≠ 1 := fun h =>
  hl (d.units₀_eq_one_of_sq (Units.ext (by rw [Units.val_pow_eq_pow_val, sq, h, Units.val_one])))

theorem σ_mul_σσ_ne_one {m : d.Γˣ} (hm : m ≠ 1) : d.σ (m : d.Γ) * d.σ (d.σ (m : d.Γ)) ≠ 1 :=
  fun h => hm (Units.ext (d.eq_one_of_σ_mul_σσ_eq_one h))

theorem nf_coords_of_commute {a₁ : d.Γ} {a₂ : d.Γ₀} {a₃ a₄ : d.Γ} {a₅ a₆ : d.Γ₀}
    {h : (d.Γ₀)ˣ × d.Γˣ} (hc : d.torus h * d.nf (a₁, a₂, a₃, a₄, a₅, a₆) =
      d.nf (a₁, a₂, a₃, a₄, a₅, a₆) * d.torus h) :
    (h.2 : d.Γ) * a₁ = a₁ ∧ (h.1 : d.Γ₀) * a₂ = a₂ ∧ ((h.1 : d.Γ₀) : d.Γ) * h.2 * a₃ = a₃ ∧
      ((h.1 : d.Γ₀) : d.Γ) * d.σ h.2 * d.σ (d.σ h.2) * a₄ = a₄ ∧
      (h.1 : d.Γ₀) * d.nm h.2 * a₅ = a₅ ∧ (h.1 : d.Γ₀) * (h.1 : d.Γ₀) * d.nm h.2 * a₆ = a₆ := by
  have e : d.torus h * d.nf (a₁, a₂, a₃, a₄, a₅, a₆) * (d.torus h)⁻¹ =
      d.nf (a₁, a₂, a₃, a₄, a₅, a₆) := by rw [hc, mul_inv_cancel_right]
  rw [torus_conj_nf] at e
  have := d.nf_injective e
  simp only [Prod.mk.injEq] at this
  exact this

theorem mem_U₁_of_mem_S_of_mem_centralizer_J₁ (hq : 4 ≤ q) {x : X} (hx : x ∈ d.S)
    (hc : x ∈ centralizer (d.J₁ : Set X)) : x ∈ d.U₁ := by
  obtain ⟨l, hl⟩ := d.exists_units₀_ne_one hq
  obtain ⟨⟨a₁, a₂, a₃, a₄, a₅, a₆⟩, rfl⟩ := d.mem_S.1 hx
  have e := (mem_centralizer_iff.1 hc) _ ((d.torus_mem_J₁_iff (l, 1)).2 rfl)
  obtain ⟨-, h2, h3, h4, h5, h6⟩ := d.nf_coords_of_commute e
  simp only [Units.val_one, map_one, mul_one, d.nm_one] at h2 h3 h4 h5 h6
  rw [eq_zero_of_mul_eq_self (fun h => hl (Units.ext h)) h2,
    eq_zero_of_mul_eq_self (d.coe_coe_ne_one hl) h3,
    eq_zero_of_mul_eq_self (d.coe_coe_ne_one hl) h4,
    eq_zero_of_mul_eq_self (fun h => hl (Units.ext h)) h5,
    eq_zero_of_mul_eq_self (d.coe_mul_self_ne_one hl) h6]
  exact (show d.nf (a₁, 0, 0, 0, 0, 0) ∈ d.U₁ by rw [d.nf_x₁]; exact d.x₁_mem_U₁ a₁)

theorem mem_U₂_of_mem_S_of_mem_centralizer_J₂ (hq : 4 ≤ q) {x : X} (hx : x ∈ d.S)
    (hc : x ∈ centralizer (d.J₂ : Set X)) : x ∈ d.U₂ := by
  obtain ⟨m, hm⟩ := d.exists_units_ne_one
  obtain ⟨l, hl⟩ := d.exists_units₀_ne_one hq
  obtain ⟨m', hm'⟩ := d.nmUnits_surjective l
  obtain ⟨⟨a₁, a₂, a₃, a₄, a₅, a₆⟩, rfl⟩ := d.mem_S.1 hx
  have e := (mem_centralizer_iff.1 hc) _ ((d.torus_mem_J₂_iff (1, m)).2 rfl)
  have e' := (mem_centralizer_iff.1 hc) _ ((d.torus_mem_J₂_iff (1, m')).2 rfl)
  obtain ⟨h1, -, h3, h4, -, -⟩ := d.nf_coords_of_commute e
  obtain ⟨-, -, -, -, h5, h6⟩ := d.nf_coords_of_commute e'
  simp only [Units.val_one, OneMemClass.coe_one, one_mul] at h1 h3 h4 h5 h6
  have hN : d.nm (m' : d.Γ) ≠ 1 := fun h => hl (by rw [← hm']; exact Units.ext h)
  have hm1 : (m : d.Γ) ≠ 1 := fun h => hm (Units.ext h)
  rw [eq_zero_of_mul_eq_self hm1 h1, eq_zero_of_mul_eq_self hm1 h3,
    eq_zero_of_mul_eq_self (d.σ_mul_σσ_ne_one hm) h4, eq_zero_of_mul_eq_self hN h5,
    eq_zero_of_mul_eq_self hN h6]
  exact (show d.nf (0, a₂, 0, 0, 0, 0) ∈ d.U₂ by rw [d.nf_x₂]; exact d.x₂_mem_U₂ a₂)

theorem conj_invol_mem_centralizer {w : X} (hw : w * w = 1) {T : Subgroup X}
    (hT : ∀ t ∈ T, w * t * w ∈ T) {z : X} (hz : z ∈ centralizer (T : Set X)) :
    w * z * w ∈ centralizer (T : Set X) := by
  rw [mem_centralizer_iff] at hz ⊢
  intro t ht
  have h1 := hz _ (hT t ht)
  calc t * (w * z * w) = w * ((w * t * w) * z) * w := by
        rw [show w * ((w * t * w) * z) * w = (w * w) * t * (w * z * w) by group, hw, one_mul]
    _ = w * (z * (w * t * w)) * w := by rw [h1]
    _ = w * z * w * t := by
        rw [show w * (z * (w * t * w)) * w = w * z * w * t * (w * w) by group, hw, mul_one]

theorem mul_eq_mul_of_conj_eq {G : Type*} [Group G] {j x : G} (h : j * x * j⁻¹ = x) :
    j * x = x * j := by
  calc j * x = j * x * j⁻¹ * j := by group
    _ = x * j := by rw [h]

theorem bruhat_parts_mem_centralizer {T : Subgroup X} (hTJ : T ≤ d.J) {x h w y : X}
    (hx : x ∈ d.S) (hh : h ∈ d.J) (hw : w ∈ d.weyl) (hy : y ∈ d.Uminus w)
    (hg : x * h * w * y ∈ centralizer (T : Set X)) :
    x ∈ centralizer (T : Set X) ∧ w ∈ centralizer (T : Set X) ∧
      y ∈ centralizer (T : Set X) := by
  have key : ∀ j ∈ T, j * x * j⁻¹ = x ∧ w * j * w⁻¹ = j ∧ j * y * j⁻¹ = y := fun j hj =>
    d.bruhat_parts_of_commute hx hh hw hy (hTJ hj) (by
      rw [(mem_centralizer_iff.1 hg) j hj, mul_inv_cancel_right])
  refine ⟨mem_centralizer_iff.2 fun j hj => mul_eq_mul_of_conj_eq (key j hj).1,
    mem_centralizer_iff.2 fun j hj => (mul_eq_mul_of_conj_eq (key j hj).2.1).symm,
    mem_centralizer_iff.2 fun j hj => mul_eq_mul_of_conj_eq (key j hj).2.2⟩

theorem J₄_le_and_v_mem_of {N : Subgroup X} (hU : d.U₂ ≤ N)
    (hv : ∀ z ∈ N, d.v * z * d.v ∈ N) : d.J₄ ≤ N ∧ d.v ∈ N := by
  have hg : d.v * d.x₂ 1 * d.v ∈ d.leviLong :=
    mul_mem (mul_mem d.v_mem_leviLong (d.x₂_mem_leviLong 1)) d.v_mem_leviLong
  rcases d.normalizer_Y_cases (d.leviLong_le_normalizer_Y hg) with hB | ⟨x, hx, h, hh, y, hy, he⟩
  · exact absurd hB (d.v_x₂_v_not_mem_B one_ne_zero)
  have hxh : x * h ∈ d.leviLong := by
    have := mul_mem (mul_mem hg (inv_mem (d.U₂_le_leviLong hy))) d.v_mem_leviLong
    rwa [he, show x * h * d.v * y * y⁻¹ * d.v = x * h * (d.v * d.v) by group, d.v_mul_self,
      mul_one] at this
  obtain ⟨x', hx', h', hh', hxh'⟩ := d.exists_eq_mul_of_mem_leviLong_of_mem_B hxh
    (mul_mem (le_sup_left (a := d.S) hx) (le_sup_right (a := d.S) hh))
  have hgN : d.v * d.x₂ 1 * d.v ∈ N := hv _ (hU (d.x₂_mem_U₂ 1))
  have hh'v : h' * d.v ∈ N := by
    have := mul_mem (mul_mem (inv_mem (hU hx')) hgN) (inv_mem (hU hy))
    rwa [he, hxh', show x'⁻¹ * (x' * h' * d.v * y) * y⁻¹ = h' * d.v by group] at this
  have hsq : ∀ t ∈ d.J₄, t * t ∈ N := by
    intro t ht
    have hvt : d.v * t * d.v = t⁻¹ := d.v_conj_eq_inv_of_mem_J₄ ht
    have htJ : t ∈ d.J := ht.1
    have hcomm : h' * t⁻¹ = t⁻¹ * h' := d.J_commute hh'.1 (inv_mem htJ)
    have hconj : t⁻¹ * (d.v * d.x₂ 1 * d.v) * t ∈ N := by
      have e : t⁻¹ * (d.v * d.x₂ 1 * d.v) * t = d.v * (t * d.x₂ 1 * t⁻¹) * d.v := by
        calc t⁻¹ * (d.v * d.x₂ 1 * d.v) * t = (d.v * t * d.v) * (d.v * d.x₂ 1 * d.v) * t := by
              rw [hvt]
          _ = d.v * t * (d.v * d.v) * d.x₂ 1 * d.v * t := by group
          _ = d.v * (t * d.x₂ 1 * t⁻¹) * (t * d.v * t) := by rw [d.v_mul_self]; group
          _ = d.v * (t * d.x₂ 1 * t⁻¹) * d.v := by
            congr 1
            calc t * d.v * t = d.v * (d.v * t * d.v) * t := by
                  rw [← mul_assoc, ← mul_assoc, d.v_mul_self, one_mul]
              _ = d.v := by rw [hvt, mul_assoc, inv_mul_cancel, mul_one]
      rw [e]
      obtain ⟨p, rfl⟩ := d.mem_J.1 htJ
      rw [d.torus_x₂]
      exact hv _ (hU (d.x₂_mem_U₂ _))
    have hU' : ∀ z ∈ d.U₂, t⁻¹ * z * t ∈ N := by
      obtain ⟨p, rfl⟩ := d.mem_J.1 htJ
      rintro _ ⟨c, rfl⟩
      rw [← map_inv, show d.torus p⁻¹ * d.x₂ c * d.torus p =
        d.torus p⁻¹ * d.x₂ c * (d.torus p⁻¹)⁻¹ by rw [map_inv, inv_inv], d.torus_x₂]
      exact hU (d.x₂_mem_U₂ _)
    have key : (t⁻¹ * x' * t)⁻¹ * (t⁻¹ * (d.v * d.x₂ 1 * d.v) * t) * (t⁻¹ * y * t)⁻¹ *
        (d.v * h'⁻¹) = t⁻¹ * t⁻¹ := by
      rw [he, hxh']
      calc (t⁻¹ * x' * t)⁻¹ * (t⁻¹ * (x' * h' * d.v * y) * t) * (t⁻¹ * y * t)⁻¹ *
            (d.v * h'⁻¹) = t⁻¹ * h' * (d.v * t * d.v) * h'⁻¹ := by group
        _ = t⁻¹ * t⁻¹ := by
          rw [hvt, mul_assoc t⁻¹ h' t⁻¹, hcomm, ← mul_assoc t⁻¹ t⁻¹ h', mul_inv_cancel_right]
    have hvh : d.v * h'⁻¹ ∈ N := by
      have := inv_mem hh'v
      rwa [mul_inv_rev, d.v_inv] at this
    have h3 : t⁻¹ * t⁻¹ ∈ N := by
      rw [← key]
      exact mul_mem (mul_mem (mul_mem (inv_mem (hU' _ hx')) hconj) (inv_mem (hU' _ hy))) hvh
    rw [← mul_inv_rev] at h3
    exact inv_mem_iff.1 h3
  have hJ₄ : d.J₄ ≤ N := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := d.exists_mul_self_eq_of_mem_J₄ ht
    exact hsq s hs
  refine ⟨hJ₄, ?_⟩
  have := mul_mem (inv_mem (hJ₄ hh')) hh'v
  rwa [inv_mul_cancel_left] at this

@[expose] def leviJ₀ : Subgroup X :=
  closure ((d.U₂ : Set X) ∪ d.U₅ ∪ d.U₆ ∪ {d.v, d.u * d.v * d.u, d.v * d.u * d.v * d.u * d.v})

theorem U₂_le_leviJ₀ : d.U₂ ≤ d.leviJ₀ := fun _ h => subset_closure (by simp [h])

theorem U₅_le_leviJ₀ : d.U₅ ≤ d.leviJ₀ := fun _ h => subset_closure (by simp [h])

theorem U₆_le_leviJ₀ : d.U₆ ≤ d.leviJ₀ := fun _ h => subset_closure (by simp [h])

theorem v_mem_leviJ₀ : d.v ∈ d.leviJ₀ := subset_closure (by simp)

theorem uvu_mem_leviJ₀ : d.u * d.v * d.u ∈ d.leviJ₀ := subset_closure (by simp)

theorem vuvuv_mem_leviJ₀ : d.v * d.u * d.v * d.u * d.v ∈ d.leviJ₀ := subset_closure (by simp)

theorem leviLong_le_leviJ₀ : d.leviLong ≤ d.leviJ₀ := by
  rw [leviLong, closure_le]
  rintro g (hg | rfl)
  · exact d.U₂_le_leviJ₀ hg
  · exact d.v_mem_leviJ₀

theorem u_conj_mem_leviJ₀_of_mem_leviLong {z : X} (hz : z ∈ d.leviLong) :
    d.u * z * d.u ∈ d.leviJ₀ := by
  have h : d.leviLong ≤ d.leviJ₀.comap (MulAut.conj d.u).toMonoidHom := by
    rw [leviLong, closure_le]
    rintro g (⟨a, rfl⟩ | rfl) <;>
      simp only [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    · rw [d.u_conj_x₂]
      exact d.U₅_le_leviJ₀ (d.x₅_mem_U₅ a)
    · rw [d.u_inv]
      exact d.uvu_mem_leviJ₀
  simpa [d.u_inv] using h hz

theorem J₀_le_J₂ : d.J₀ ≤ d.J₂ := by
  rw [d.yamada_three_five_four.1]
  exact inf_le_left.trans inf_le_left

theorem J₀_le_J₅ : d.J₀ ≤ d.J₅ := by
  rw [d.yamada_three_five_four.1]
  exact inf_le_left.trans inf_le_right

theorem J₀_le_J₆ : d.J₀ ≤ d.J₆ := by
  rw [d.yamada_three_five_four.1]
  exact inf_le_right

theorem J₀_le_J : d.J₀ ≤ d.J :=
  d.J₀_le_J₂.trans inf_le_left

theorem leviJ₀_le_centralizer_J₀ : d.leviJ₀ ≤ centralizer (d.J₀ : Set X) := by
  have hv : d.v ∈ centralizer (d.J₀ : Set X) :=
    centralizer_le (fun _ h => d.J₀_le_J₂ h) d.v_mem_centralizer_J₂
  have hT : ∀ t ∈ d.J₀, d.u * t * d.u ∈ d.J₀ := fun t ht => by
    rw [d.u_conj_eq_inv_of_mem_J₆ (d.J₀_le_J₆ ht)]
    exact inv_mem ht
  have huvu : d.u * d.v * d.u ∈ centralizer (d.J₀ : Set X) :=
    conj_invol_mem_centralizer d.u_mul_self hT hv
  rw [leviJ₀, closure_le]
  rintro g (((hg | hg) | hg) | hg)
  · exact le_centralizer_iff.1 (d.J₀_le_J₂.trans inf_le_right) hg
  · exact le_centralizer_iff.1 (d.J₀_le_J₅.trans inf_le_right) hg
  · exact le_centralizer_iff.1 (d.J₀_le_J₆.trans inf_le_right) hg
  · rcases hg with rfl | rfl | rfl
    · exact hv
    · exact huvu
    · rw [show d.v * d.u * d.v * d.u * d.v = d.v * (d.u * d.v * d.u) * d.v by group]
      exact mul_mem (mul_mem hv huvu) hv

theorem torus_one_mem_J₀ {m : d.Γˣ} (hm : d.nmUnits m = 1) : d.torus (1, m) ∈ d.J₀ := by
  have hN : d.nm (m : d.Γ) = 1 := congrArg Units.val hm
  rw [d.yamada_three_five_four.1]
  refine ⟨⟨(d.torus_mem_J₂_iff _).2 rfl, (d.torus_mem_J₅_iff _).2 ?_⟩,
    (d.torus_mem_J₆_iff _).2 ?_⟩ <;> simp [hN]

theorem mem_leviJ₀_of_mem_S_of_mem_centralizer_J₀ {x : X} (hx : x ∈ d.S)
    (hc : x ∈ centralizer (d.J₀ : Set X)) : x ∈ d.leviJ₀ := by
  obtain ⟨m, hm, hm1⟩ := d.exists_mem_ker_nmUnits_ne_one
  obtain ⟨⟨a₁, a₂, a₃, a₄, a₅, a₆⟩, rfl⟩ := d.mem_S.1 hx
  have e := (mem_centralizer_iff.1 hc) _ (d.torus_one_mem_J₀ hm)
  obtain ⟨h1, -, h3, h4, -, -⟩ := d.nf_coords_of_commute e
  simp only [Units.val_one, OneMemClass.coe_one, one_mul] at h1 h3 h4
  have hm1' : (m : d.Γ) ≠ 1 := fun h => hm1 (Units.ext h)
  rw [eq_zero_of_mul_eq_self hm1' h1, eq_zero_of_mul_eq_self hm1' h3,
    eq_zero_of_mul_eq_self (d.σ_mul_σσ_ne_one hm1) h4]
  show d.nf (0, a₂, 0, 0, a₅, a₆) ∈ d.leviJ₀
  rw [nf_apply, d.x₁_zero, d.x₃_zero, d.x₄_zero, one_mul, mul_one, mul_one]
  exact mul_mem (mul_mem (d.U₂_le_leviJ₀ (d.x₂_mem_U₂ _)) (d.U₅_le_leviJ₀ (d.x₅_mem_U₅ _)))
    (d.U₆_le_leviJ₀ ⟨_, rfl⟩)

theorem word_torus_J₀ (l : List Bool) {m : d.Γˣ} (hm : d.nmUnits m = 1) :
    d.word l * d.torus (1, m) * (d.word l)⁻¹ = d.torus (1, m ^ uSign l) := by
  induction l with
  | nil => simp [word_nil, uSign]
  | cons b l ih =>
    rw [word_cons, show d.gen b * d.word l * d.torus (1, m) * (d.gen b * d.word l)⁻¹ =
      d.gen b * (d.word l * d.torus (1, m) * (d.word l)⁻¹) * (d.gen b)⁻¹ by group, ih,
      d.gen_inv]
    cases b
    · change d.u * d.torus (1, m ^ uSign l) * d.u = d.torus (1, m ^ (-uSign l))
      rw [u_torus_eq, map_zpow, hm, one_zpow, one_mul, zpow_neg]
    · change d.v * d.torus (1, m ^ uSign l) * d.v = d.torus (1, m ^ uSign l)
      rw [v_torus_eq, inv_one, map_one, one_mul]

theorem weylWord_mem_leviJ₀_of_mem_centralizer_J₀ {k : Fin 12}
    (hk : d.weylWord k ∈ centralizer (d.J₀ : Set X)) : d.weylWord k ∈ d.leviJ₀ := by
  obtain ⟨m, hm, hm1⟩ := d.exists_mem_ker_nmUnits_ne_one
  have e := (mem_centralizer_iff.1 hk) _ (d.torus_one_mem_J₀ hm)
  have e' : d.torus (1, m ^ uSign (weylList k)) = d.torus (1, m) := by
    rw [← d.word_torus_J₀ _ hm]
    change d.weylWord k * d.torus (1, m) * (d.weylWord k)⁻¹ = d.torus (1, m)
    rw [← e, mul_inv_cancel_right]
  have hpow : m ^ uSign (weylList k) = m := congrArg Prod.snd (d.torus_injective e')
  have hneg : m ^ (-1 : ℤ) ≠ m := by
    intro h
    apply hm1
    refine d.units_eq_one_of_sq ?_
    rw [sq]
    nth_rewrite 1 [← h]
    rw [zpow_neg_one, inv_mul_cancel]
  have hsign : uSign (weylList k) = 1 := by
    have h2 : ∀ k : Fin 12, uSign (weylList k) = 1 ∨ uSign (weylList k) = -1 := by decide
    rcases h2 k with h | h
    · exact h
    · exact absurd (h ▸ hpow) hneg
  have h3 : ∀ k : Fin 12, uSign (weylList k) = 1 →
      k = 0 ∨ k = 2 ∨ k = 5 ∨ k = 7 ∨ k = 8 ∨ k = 10 := by decide
  have hv := d.v_mem_leviJ₀
  have huvu := d.uvu_mem_leviJ₀
  rcases h3 k hsign with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [weylWord_zero]
    exact one_mem _
  · rw [weylWord_two]
    exact hv
  · have e5 : d.weylWord 5 = d.u * d.v * d.u := by
      simp [weylWord, weylList, word, gen, mul_assoc]
    rw [e5]
    exact huvu
  · have e7 : d.weylWord 7 = d.u * d.v * d.u * d.v := by
      simp [weylWord, weylList, word, gen, mul_assoc]
    rw [e7]
    exact mul_mem huvu hv
  · have e8 : d.weylWord 8 = d.v * (d.u * d.v * d.u) := by
      simp [weylWord, weylList, word, gen, mul_assoc]
    rw [e8]
    exact mul_mem hv huvu
  · have e10 : d.weylWord 10 = d.v * d.u * d.v * d.u * d.v := by
      simp [weylWord, weylList, word, gen, mul_assoc]
    rw [e10]
    exact d.vuvuv_mem_leviJ₀

theorem centralizer_J₀_eq : centralizer (d.J₀ : Set X) = d.leviJ₀ ⊔ d.J := by
  refine le_antisymm (fun g hg => ?_) (sup_le d.leviJ₀_le_centralizer_J₀ fun j hj =>
    mem_centralizer_iff.2 fun t ht => d.J_commute (d.J₀_le_J ht) hj)
  obtain ⟨x, hx, h, hh, w, hw, y, hy, rfl⟩ := d.exists_bruhat_normal_form g
  obtain ⟨hxC, hwC, hyC⟩ := d.bruhat_parts_mem_centralizer d.J₀_le_J hx hh hw hy hg
  obtain ⟨k, rfl⟩ := d.exists_weylWord_eq hw
  exact mul_mem (mul_mem (mul_mem
    (mem_sup_left (d.mem_leviJ₀_of_mem_S_of_mem_centralizer_J₀ hx hxC)) (mem_sup_right hh))
    (mem_sup_left (d.weylWord_mem_leviJ₀_of_mem_centralizer_J₀ hwC)))
    (mem_sup_left (d.mem_leviJ₀_of_mem_S_of_mem_centralizer_J₀ (d.Uminus_le_S _ hy) hyC))

theorem torus_mul_v_conj_inv (l : (d.Γ₀)ˣ) (m : d.Γˣ) :
    d.torus (l, m) * (d.v * (d.torus (l, m))⁻¹ * d.v) = d.hA l := by
  rw [← map_inv, Prod.inv_mk, v_torus_eq, ← map_mul, hA_apply]
  congr 1
  refine Prod.ext ?_ ?_
  · change l * l⁻¹⁻¹ = l ^ 2
    rw [inv_inv, sq]
  · change m * (d.unitsIncl l⁻¹ * m⁻¹) = d.unitsIncl l⁻¹
    rw [mul_left_comm, mul_inv_cancel, mul_one]

theorem J_conj_v_mem_leviJ₀ {j : X} (hj : j ∈ d.J) : j * d.v * j⁻¹ ∈ d.leviJ₀ := by
  obtain ⟨⟨l, m⟩, rfl⟩ := d.mem_J.1 hj
  have e : d.torus (l, m) * d.v * (d.torus (l, m))⁻¹ =
      d.torus (l, m) * (d.v * (d.torus (l, m))⁻¹ * d.v) * d.v := by
    rw [show d.torus (l, m) * (d.v * (d.torus (l, m))⁻¹ * d.v) * d.v =
      d.torus (l, m) * d.v * (d.torus (l, m))⁻¹ * (d.v * d.v) by group, d.v_mul_self, mul_one]
  rw [e, torus_mul_v_conj_inv]
  refine mul_mem (d.leviLong_le_leviJ₀ (d.J₄_le_leviLong ?_)) d.v_mem_leviJ₀
  rw [d.J₄_eq_range_hA]
  exact ⟨l, rfl⟩

theorem J_le_normalizer_leviJ₀ : d.J ≤ normalizer (d.leviJ₀ : Set X) := by
  have := d.finite
  intro j hj
  have hv : j * d.v * j⁻¹ ∈ d.leviJ₀ := d.J_conj_v_mem_leviJ₀ hj
  have huvu : j * (d.u * d.v * d.u) * j⁻¹ ∈ d.leviJ₀ := by
    have hj' : d.u * j * d.u ∈ d.J := by
      have := d.conj_mem_J d.u_mem_weyl hj
      rwa [d.u_inv] at this
    obtain ⟨⟨l, m⟩, hlm⟩ := d.mem_J.1 hj'
    have e : j * (d.u * d.v * d.u) * j⁻¹ =
        d.u * ((d.u * j * d.u) * d.v * (d.u * j * d.u)⁻¹) * d.u := by
      rw [mul_inv_rev, mul_inv_rev, d.u_inv]
      calc j * (d.u * d.v * d.u) * j⁻¹ = (d.u * d.u) * j * (d.u * d.v * d.u) * j⁻¹ *
            (d.u * d.u) := by rw [d.u_mul_self]; group
        _ = _ := by group
    rw [e, ← hlm]
    have e2 : d.torus (l, m) * d.v * (d.torus (l, m))⁻¹ = d.hA l * d.v := by
      rw [← torus_mul_v_conj_inv]
      rw [show d.torus (l, m) * (d.v * (d.torus (l, m))⁻¹ * d.v) * d.v =
        d.torus (l, m) * d.v * (d.torus (l, m))⁻¹ * (d.v * d.v) by group, d.v_mul_self, mul_one]
    rw [e2]
    refine d.u_conj_mem_leviJ₀_of_mem_leviLong (mul_mem (d.J₄_le_leviLong ?_) d.v_mem_leviLong)
    rw [d.J₄_eq_range_hA]
    exact ⟨l, rfl⟩
  have hgen : ∀ g ∈ ((d.U₂ : Set X) ∪ d.U₅ ∪ d.U₆ ∪
      {d.v, d.u * d.v * d.u, d.v * d.u * d.v * d.u * d.v}), j * g * j⁻¹ ∈ d.leviJ₀ := by
    rintro g (((hg | hg) | hg) | hg)
    · exact d.U₂_le_leviJ₀ ((mem_normalizer_iff.1 (d.J_le_normalizer_rootGroup 1 hj) g).1 hg)
    · exact d.U₅_le_leviJ₀ ((mem_normalizer_iff.1 (d.J_le_normalizer_rootGroup 4 hj) g).1 hg)
    · exact d.U₆_le_leviJ₀ ((mem_normalizer_iff.1 (d.J_le_normalizer_rootGroup 5 hj) g).1 hg)
    · rcases hg with rfl | rfl | rfl
      · exact hv
      · exact huvu
      · rw [show j * (d.v * d.u * d.v * d.u * d.v) * j⁻¹ =
          (j * d.v * j⁻¹) * (j * (d.u * d.v * d.u) * j⁻¹) * (j * d.v * j⁻¹) by group]
        exact mul_mem (mul_mem hv huvu) hv
  have hle : d.leviJ₀ ≤ d.leviJ₀.comap (MulAut.conj j).toMonoidHom :=
    (closure_le _).2 fun g hg => by simpa using hgen g hg
  exact mem_normalizer_fintype fun n hn => by simpa using hle hn

theorem u_vuvuv_u : d.u * (d.v * d.u * d.v * d.u * d.v) * d.u = d.v * d.u * d.v * d.u * d.v := by
  have h := d.uvuvuv_eq
  calc d.u * (d.v * d.u * d.v * d.u * d.v) * d.u
      = d.u * (d.v * (d.u * (d.v * (d.u * d.v)))) * d.u := by simp only [mul_assoc]
    _ = d.v * (d.u * (d.v * (d.u * (d.v * d.u)))) * d.u := by rw [h]
    _ = d.v * d.u * d.v * d.u * d.v * (d.u * d.u) := by simp only [mul_assoc]
    _ = d.v * d.u * d.v * d.u * d.v := by rw [d.u_mul_self, mul_one]

theorem u_conj_mem_leviJ₀ {z : X} (hz : z ∈ d.leviJ₀) : d.u * z * d.u ∈ d.leviJ₀ := by
  have hle : d.leviJ₀ ≤ d.leviJ₀.comap (MulAut.conj d.u).toMonoidHom := by
    refine (closure_le _).2 fun g hg => ?_
    simp only [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, d.u_inv]
    rcases hg with (((⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨a, rfl⟩) | hg)
    · rw [d.u_x₂]
      exact d.U₅_le_leviJ₀ (d.x₅_mem_U₅ a)
    · rw [conj_symm_of_involution d.u_mul_self d.u_x₂ a]
      exact d.U₂_le_leviJ₀ (d.x₂_mem_U₂ a)
    · rw [d.u_x₆]
      exact d.U₆_le_leviJ₀ ⟨a, rfl⟩
    · rcases hg with rfl | rfl | rfl
      · exact d.uvu_mem_leviJ₀
      · rw [show d.u * (d.u * d.v * d.u) * d.u = (d.u * d.u) * d.v * (d.u * d.u) by group,
          d.u_mul_self, one_mul, mul_one]
        exact d.v_mem_leviJ₀
      · rw [d.u_vuvuv_u]
        exact d.vuvuv_mem_leviJ₀
  simpa [d.u_inv] using hle hz

theorem uvu_conj_x₂ (a : d.Γ₀) : d.u * d.v * d.u * d.x₂ a * (d.u * d.v * d.u)⁻¹ = d.x₆ a := by
  rw [conj_mul_conj, conj_mul_conj, d.u_conj_x₂, d.v_conj_x₅, d.u_conj_x₆]

theorem commutator_leviJ₀ : ⁅d.leviJ₀, d.leviJ₀⁆ = d.leviJ₀ := by
  have := d.finite
  set N := ⁅d.leviJ₀, d.leviJ₀⁆ with hN
  have hconj : ∀ g ∈ normalizer (d.leviJ₀ : Set X), ∀ z ∈ N, g * z * g⁻¹ ∈ N :=
    fun g hg z hz => conj_mem_commutator hg hz
  have hK : ∀ g ∈ d.leviJ₀, g ∈ normalizer (d.leviJ₀ : Set X) := fun g hg =>
    le_normalizer hg
  have hu : d.u ∈ normalizer (d.leviJ₀ : Set X) :=
    mem_normalizer_fintype fun z hz => by rw [d.u_inv]; exact d.u_conj_mem_leviJ₀ hz
  have h6 : d.U₆ ≤ N := by
    rintro _ ⟨a, rfl⟩
    have h := commutator_mem_commutator (d.U₂_le_leviJ₀ (d.x₂_mem_U₂ a))
      (d.U₅_le_leviJ₀ (d.x₅_mem_U₅ 1))
    rwa [d.comm₂₅, mul_one] at h
  have h2 : d.U₂ ≤ N := by
    rintro _ ⟨a, rfl⟩
    have h := hconj _ (inv_mem (hK _ d.uvu_mem_leviJ₀)) _ (h6 ⟨a, rfl⟩)
    rwa [← d.uvu_conj_x₂ a, inv_inv, show (d.u * d.v * d.u)⁻¹ * (d.u * d.v * d.u * d.x₂ a *
      (d.u * d.v * d.u)⁻¹) * (d.u * d.v * d.u) = d.x₂ a by group] at h
  have h5 : d.U₅ ≤ N := by
    rintro _ ⟨a, rfl⟩
    have h := hconj _ (hK _ d.v_mem_leviJ₀) _ (h6 ⟨a, rfl⟩)
    rwa [d.v_conj_x₆] at h
  have hv : d.v ∈ N := (d.J₄_le_and_v_mem_of h2 fun z hz => by
    simpa [d.v_inv] using hconj _ (hK _ d.v_mem_leviJ₀) z hz).2
  have huvu : d.u * d.v * d.u ∈ N := by
    simpa [d.u_inv] using hconj _ hu _ hv
  refine le_antisymm (commutator_le.2 fun g hg g' hg' => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hg') (inv_mem hg)) (inv_mem hg')) ((closure_le _).2 ?_)
  rintro g (((hg | hg) | hg) | hg)
  · exact h2 hg
  · exact h5 hg
  · exact h6 hg
  · rcases hg with rfl | rfl | rfl
    · exact hv
    · exact huvu
    · rw [show d.v * d.u * d.v * d.u * d.v = d.v * (d.u * d.v * d.u) * d.v by group]
      exact mul_mem (mul_mem hv huvu) hv

theorem coe_centralizer_J₀ : (centralizer (d.J₀ : Set X) : Set X) =
    (d.leviJ₀ : Set X) * (d.J : Set X) := by
  rw [d.centralizer_J₀_eq]
  exact coe_mul_of_right_le_normalizer_left _ _ d.J_le_normalizer_leviJ₀

theorem commutator_centralizer_J₀ :
    ⁅centralizer (d.J₀ : Set X), centralizer (d.J₀ : Set X)⁆ = d.leviJ₀ := by
  refine le_antisymm ?_ ?_
  · rw [commutator_le]
    intro g hg g' hg'
    rw [← SetLike.mem_coe, d.coe_centralizer_J₀] at hg hg'
    obtain ⟨k, hk, j, hj, rfl⟩ := hg
    obtain ⟨k', hk', j', hj', rfl⟩ := hg'
    have hjj : j * j' = j' * j := d.J_commute hj hj'
    have e : ⁅k * j, k' * j'⁆ = k * (j * k' * j⁻¹) * (j' * k⁻¹ * j'⁻¹) * k'⁻¹ := by
      rw [commutatorElement_def]
      calc k * j * (k' * j') * (k * j)⁻¹ * (k' * j')⁻¹
          = k * (j * k' * j⁻¹) * (j * j') * j⁻¹ * k⁻¹ * j'⁻¹ * k'⁻¹ := by group
        _ = k * (j * k' * j⁻¹) * (j' * j) * j⁻¹ * k⁻¹ * j'⁻¹ * k'⁻¹ := by rw [hjj]
        _ = _ := by group
    rw [e]
    have hn := d.J_le_normalizer_leviJ₀
    exact mul_mem (mul_mem (mul_mem hk ((mem_normalizer_iff.1 (hn hj) k').1 hk'))
      ((mem_normalizer_iff.1 (hn hj') _).1 (inv_mem hk))) (inv_mem hk')
  · calc d.leviJ₀ = ⁅d.leviJ₀, d.leviJ₀⁆ := d.commutator_leviJ₀.symm
      _ ≤ _ := commutator_mono d.leviJ₀_le_centralizer_J₀ d.leviJ₀_le_centralizer_J₀

end TrialityD4Data

end CFSG.LocalAnalysis.EvenBN.TrialityD4
