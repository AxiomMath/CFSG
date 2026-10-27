module

public import CFSG.Dihedral.Glauberman.DicksonMaxList

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open scoped MatrixGroups

private theorem mk_mem_range_pslToPGL {F : Type} [Field F]
    (h : Matrix.GeneralLinearGroup (Fin 2) F) (u : Fˣ)
    (hu : Matrix.GeneralLinearGroup.det h * u ^ 2 = 1) :
    Matrix.ProjGenLinGroup.mk h ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  obtain ⟨h', hh'⟩ : ∃ h' : Matrix.GeneralLinearGroup (Fin 2) F,
      h' = h * Matrix.GeneralLinearGroup.scalar (Fin 2) u := ⟨_, rfl⟩
  have hdet' : Matrix.GeneralLinearGroup.det h' = 1 := by
    rw [hh', map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
    exact hu
  have hdet : (h' : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet', Units.val_one]
  have hA : Matrix.SpecialLinearGroup.toGL
      (⟨(h' : Matrix (Fin 2) (Fin 2) F), hdet⟩ : Matrix.SpecialLinearGroup (Fin 2) F) = h' :=
    Units.ext rfl
  refine MonoidHom.mem_range.mpr
    ⟨(QuotientGroup.mk (⟨(h' : Matrix (Fin 2) (Fin 2) F), hdet⟩ :
        Matrix.SpecialLinearGroup (Fin 2) F) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F), ?_⟩
  show Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL
    (⟨(h' : Matrix (Fin 2) (Fin 2) F), hdet⟩ : Matrix.SpecialLinearGroup (Fin 2) F)) =
      Matrix.ProjGenLinGroup.mk h
  rw [hA, hh', map_mul, Matrix.ProjGenLinGroup.mk_scalar, mul_one]

private theorem exists_unit_sq_mul_eq_one {F : Type} [Field F] [Finite F] (h2 : (2 : F) = 0)
    (d : Fˣ) : ∃ u : Fˣ, d * u ^ 2 = 1 := by
  have hinj : Function.Injective (fun x : F => x ^ 2) := by
    intro a b hab
    have hab' : a ^ 2 = b ^ 2 := hab
    have h0 : (a - b) ^ 2 = 0 := by linear_combination hab' + b * (b - a) * h2
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0)
  obtain ⟨v, hv⟩ := Finite.surjective_of_injective hinj ((d⁻¹ : Fˣ) : F)
  have hv' : v ^ 2 = ((d⁻¹ : Fˣ) : F) := hv
  have hv0 : v ≠ 0 := by
    intro h0
    apply Units.ne_zero d⁻¹
    rw [← hv', h0, zero_pow two_ne_zero]
  refine ⟨Units.mk0 v hv0, Units.ext ?_⟩
  rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, hv', Units.val_one]
  exact Units.mul_inv d

private theorem orderOf_pslTwo_bound {F : Type} [Field F] [Finite F] {p m : ℕ}
    [hp : Fact p.Prime] (hcard : Nat.card F = p ^ m)
    (y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    0 < orderOf y ∧ orderOf y ≤ Nat.card F + 1 ∧
      (2 ∣ Nat.card F - 1 → orderOf y ≤ Nat.card F) := by
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  have hm : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hcard
    omega
  have hpq : p ∣ Nat.card F := by
    rw [hcard]
    exact dvd_pow_self p hm
  have hple : p ≤ Nat.card F := Nat.le_of_dvd (by omega) hpq
  have hp0 : 0 < p := hp.out.pos
  have hdvd := CFSG.Glauberman.Dickson.psl2_orderOf_dvd hcard y
  set g := Nat.gcd (Nat.card F - 1) 2 with hg
  have hg0 : 0 < g := by
    rw [hg]
    exact Nat.gcd_pos_of_pos_left _ (by omega)
  have hgle : g ≤ Nat.card F - 1 := by
    rw [hg]
    exact Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
  have hA : 0 < (Nat.card F - 1) / g := Nat.div_pos hgle hg0
  have hB : 0 < (Nat.card F + 1) / g := Nat.div_pos (by omega) hg0
  have hAle : (Nat.card F - 1) / g ≤ Nat.card F :=
    le_trans (Nat.div_le_self _ _) (by omega)
  have hBle : (Nat.card F + 1) / g ≤ Nat.card F + 1 := Nat.div_le_self _ _
  have hpos : 0 < orderOf y := by
    rcases hdvd with h | h | h
    · exact Nat.pos_of_ne_zero fun h0 => hp0.ne' (zero_dvd_iff.mp (h0 ▸ h))
    · exact Nat.pos_of_ne_zero fun h0 => hA.ne' (zero_dvd_iff.mp (h0 ▸ h))
    · exact Nat.pos_of_ne_zero fun h0 => hB.ne' (zero_dvd_iff.mp (h0 ▸ h))
  refine ⟨hpos, ?_, fun h2 => ?_⟩
  · rcases hdvd with h | h | h
    · exact le_trans (Nat.le_of_dvd hp0 h) (by omega)
    · exact le_trans (Nat.le_of_dvd hA h) (le_trans hAle (by omega))
    · exact le_trans (Nat.le_of_dvd hB h) hBle
  · have hg2 : g = 2 := hg.trans (Nat.gcd_eq_right h2)
    rcases hdvd with h | h | h
    · exact le_trans (Nat.le_of_dvd hp0 h) hple
    · exact le_trans (Nat.le_of_dvd hA h) hAle
    · have hB2 : (Nat.card F + 1) / g ≤ Nat.card F := by
        rw [hg2]
        omega
      exact le_trans (Nat.le_of_dvd hB h) hB2

private theorem orderOf_le_two_mul_orderOf_sq {G : Type*} [Group G] (x : G)
    (hpos : 0 < orderOf (x ^ 2)) : orderOf x ≤ 2 * orderOf (x ^ 2) := by
  refine Nat.le_of_dvd (by omega) ?_
  apply orderOf_dvd_of_pow_eq_one
  rw [pow_mul, pow_orderOf_eq_one]

theorem orderOf_pgl_two_le {F₀ : Type} [Field F₀] [Finite F₀] {p m : ℕ} [Fact p.Prime]
    (hcard : Nat.card F₀ = p ^ m) (x : PGL(2, F₀)) : orderOf x ≤ 2 * Nat.card F₀ := by
  obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
  have hq1 : 1 < Nat.card F₀ := Finite.one_lt_card
  have hm : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hcard
    omega
  by_cases hp2 : p = 2
  ·
    have h2 : (2 : F₀) = 0 := by
      have h0 : ((Nat.card F₀ : ℕ) : F₀) = 0 := by
        haveI : Fintype F₀ := Fintype.ofFinite F₀
        rw [Nat.card_eq_fintype_card]
        exact FiniteField.cast_card_eq_zero (K := F₀)
      rw [hcard, Nat.cast_pow] at h0
      have hp0 : (p : F₀) = 0 := (pow_eq_zero_iff hm).mp h0
      rw [hp2] at hp0
      exact_mod_cast hp0
    obtain ⟨u, hu⟩ := exists_unit_sq_mul_eq_one h2 (Matrix.GeneralLinearGroup.det g)
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (mk_mem_range_pslToPGL g u hu)
    have hord : orderOf (Matrix.ProjGenLinGroup.mk g) = orderOf y := by
      rw [← hy, orderOf_injective (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2)
        (R := F₀)) Matrix.ProjectiveSpecialLinearGroup.toPGL_injective y]
    obtain ⟨-, hle, -⟩ := orderOf_pslTwo_bound hcard y
    omega
  ·
    have hpprime : p.Prime := Fact.out
    have hpodd : p % 2 = 1 := hpprime.eq_two_or_odd.resolve_left hp2
    have hqodd : Nat.card F₀ % 2 = 1 := by
      rw [hcard, Nat.pow_mod, hpodd]
      simp
    have hodd : 2 ∣ Nat.card F₀ - 1 := by omega
    have hsq : (Matrix.ProjGenLinGroup.mk g) ^ 2 ∈
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F₀)).range := by
      rw [← map_pow Matrix.ProjGenLinGroup.mk g 2]
      refine mk_mem_range_pslToPGL (g ^ 2) (Matrix.GeneralLinearGroup.det g)⁻¹ ?_
      rw [map_pow, ← mul_pow, mul_inv_cancel, one_pow]
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hsq
    have hord : orderOf ((Matrix.ProjGenLinGroup.mk g) ^ 2) = orderOf y := by
      rw [← hy, orderOf_injective (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2)
        (R := F₀)) Matrix.ProjectiveSpecialLinearGroup.toPGL_injective y]
    obtain ⟨hpos, -, hbound⟩ := orderOf_pslTwo_bound hcard y
    have h1 := orderOf_le_two_mul_orderOf_sq (Matrix.ProjGenLinGroup.mk g)
      (by rw [hord]; exact hpos)
    have h3 := hbound hodd
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
