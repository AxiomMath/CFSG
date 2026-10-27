module

public import CFSG.CGT.Timmesfeld75.L2Sylow

public section

namespace CFSG.CGT.Timmesfeld75

open scoped MatrixGroups
open CFSG.Open

section OrderThree

variable {F : Type} [Field F] [CharP F 2]

theorem utriElt_mul_self (s : F) : utriElt s * utriElt s = 1 := by
  rw [← utriElt_add, CharTwo.add_self_eq_zero, utriElt_zero]

theorem ltriElt_mul_self (t : F) : ltriElt t * ltriElt t = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  apply sl2_ext
  all_goals sl2_simp
  · ring
  · ring
  · linear_combination t * h2
  · ring

theorem braid_utriElt_ltriElt {s t : F} (hst : s * t = 1) :
    utriElt s * ltriElt t * utriElt s = ltriElt t * utriElt s * ltriElt t := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  apply sl2_ext
  all_goals sl2_simp
  · ring
  · linear_combination s * hst + s * h2
  · linear_combination (-t) * hst + (-t) * h2
  · ring

theorem pow_three_utriElt_mul_ltriElt {s t : F} (hst : s * t = 1) :
    (utriElt s * ltriElt t) ^ 3 = 1 := by
  have h1 := braid_utriElt_ltriElt hst
  have ha := utriElt_mul_self s
  have hb := ltriElt_mul_self t
  calc (utriElt s * ltriElt t) ^ 3
      = (utriElt s * ltriElt t * utriElt s) * (ltriElt t * utriElt s * ltriElt t) := by
        simp only [pow_three, mul_assoc]
    _ = (utriElt s * ltriElt t * utriElt s) * (utriElt s * ltriElt t * utriElt s) := by rw [h1]
    _ = utriElt s * ltriElt t * (utriElt s * utriElt s) * ltriElt t * utriElt s := by group
    _ = utriElt s * (ltriElt t * ltriElt t) * utriElt s := by rw [ha]; group
    _ = 1 := by rw [hb, mul_one, ha]

theorem orderOf_utriElt_mul_ltriElt {s t : F} (hst : s * t = 1) :
    orderOf (utriElt s * ltriElt t) = 3 := by
  refine orderOf_eq_prime (pow_three_utriElt_mul_ltriElt hst) ?_
  intro h
  have h01 := congrArg (fun g : SL(2, F) => g 0 1) h
  sl2_simp at h01
  have hs : s = 0 := by linear_combination h01
  rw [hs, zero_mul] at hst
  exact zero_ne_one hst

end OrderThree

section ConjPairs

variable {F : Type} [Field F]

theorem exists_conj_utri_ltri_of_ne {a b : SL(2, F)}
    (hab : conjSubgroup a (utri F) ≠ conjSubgroup b (utri F)) :
    ∃ g : SL(2, F), conjSubgroup a (utri F) = conjSubgroup g (utri F) ∧
      conjSubgroup b (utri F) = conjSubgroup g (ltri F) := by
  obtain ⟨g, hg1, hg2⟩ := exists_conj_pair_normal_form hab
  refine ⟨g⁻¹, ?_, ?_⟩
  · calc conjSubgroup a (utri F) = conjSubgroup g⁻¹ (conjSubgroup (g * a) (utri F)) := by
          rw [conjSubgroup_conjSubgroup, inv_mul_cancel_left]
      _ = conjSubgroup g⁻¹ (utri F) := by rw [hg1]
  · calc conjSubgroup b (utri F) = conjSubgroup g⁻¹ (conjSubgroup (g * b) (utri F)) := by
          rw [conjSubgroup_conjSubgroup, inv_mul_cancel_left]
      _ = conjSubgroup g⁻¹ (ltri F) := by rw [hg2]

theorem sup_conjSubgroup_utri_eq_top {a b : SL(2, F)}
    (hab : conjSubgroup a (utri F) ≠ conjSubgroup b (utri F)) :
    conjSubgroup a (utri F) ⊔ conjSubgroup b (utri F) = ⊤ := by
  obtain ⟨g, hP, hQ⟩ := exists_conj_utri_ltri_of_ne hab
  rw [hP, hQ, ← conjSubgroup_sup_eq_sup, utri_sup_ltri, conjSubgroup_top]

end ConjPairs

section ConjPairsChar

variable {F : Type} [Field F] [CharP F 2]

theorem exists_mul_orderOf_three_of_conj_ne {a b : SL(2, F)}
    (hab : conjSubgroup a (utri F) ≠ conjSubgroup b (utri F)) :
    ∃ u ∈ conjSubgroup a (utri F), u ≠ 1 ∧
      ∃ v ∈ conjSubgroup b (utri F), v ≠ 1 ∧ orderOf (u * v) = 3 := by
  obtain ⟨g, hP, hQ⟩ := exists_conj_utri_ltri_of_ne hab
  have hu : (utriElt (1 : F) : SL(2, F)) ≠ 1 := utriElt_ne_one one_ne_zero
  have hl : (ltriElt (1 : F) : SL(2, F)) ≠ 1 := ltriElt_ne_one one_ne_zero
  refine ⟨g * utriElt 1 * g⁻¹, ?_, ?_, g * ltriElt 1 * g⁻¹, ?_, ?_, ?_⟩
  · rw [hP]
    exact conj_mem_conjSubgroup g (utriElt_mem_utri 1)
  · intro h
    apply hu
    have := congrArg (fun x => g⁻¹ * x * g) h
    simpa [mul_assoc] using this
  · rw [hQ]
    exact conj_mem_conjSubgroup g (ltriElt_mem_ltri 1)
  · intro h
    apply hl
    have := congrArg (fun x => g⁻¹ * x * g) h
    simpa [mul_assoc] using this
  · have e : g * utriElt (1 : F) * g⁻¹ * (g * ltriElt 1 * g⁻¹) =
        g * (utriElt 1 * ltriElt 1) * g⁻¹ := by group
    rw [e, ← orderOf_utriElt_mul_ltriElt (one_mul (1 : F))]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective _

end ConjPairsChar

section SylowPairs

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_conj_of_sylow_ne {P Q : Sylow 2 SL(2, F)} (hPQ : P ≠ Q) :
    ∃ a b : SL(2, F), conjSubgroup a (utri F) = (P : Subgroup SL(2, F)) ∧
      conjSubgroup b (utri F) = (Q : Subgroup SL(2, F)) ∧
      conjSubgroup a (utri F) ≠ conjSubgroup b (utri F) := by
  obtain ⟨a, ha⟩ := exists_conjSubgroup_utri_eq_of_sylow P
  obtain ⟨b, hb⟩ := exists_conjSubgroup_utri_eq_of_sylow Q
  refine ⟨a, b, ha, hb, ?_⟩
  rw [ha, hb]
  exact fun h => hPQ (Sylow.ext h)

theorem exists_mul_orderOf_three_of_ne {P Q : Sylow 2 SL(2, F)} (hPQ : P ≠ Q) :
    ∃ a ∈ (P : Subgroup SL(2, F)), a ≠ 1 ∧
      ∃ b ∈ (Q : Subgroup SL(2, F)), b ≠ 1 ∧ orderOf (a * b) = 3 := by
  obtain ⟨x, y, hx, hy, hne⟩ := exists_conj_of_sylow_ne hPQ
  rw [← hx, ← hy]
  exact exists_mul_orderOf_three_of_conj_ne hne

theorem sup_sylow_eq_top {P Q : Sylow 2 SL(2, F)} (hPQ : P ≠ Q) :
    (P : Subgroup SL(2, F)) ⊔ (Q : Subgroup SL(2, F)) = ⊤ := by
  obtain ⟨x, y, hx, hy, hne⟩ := exists_conj_of_sylow_ne hPQ
  rw [← hx, ← hy]
  exact sup_conjSubgroup_utri_eq_top hne

theorem eq_utri_of_isWC {A : Subgroup SL(2, F)} (hA : A ≤ utri F) (hA1 : A ≠ ⊥) (hWC : IsWC A) :
    A = utri F := by
  obtain ⟨⟨t, htA⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA1
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  obtain ⟨s₀, hs₀⟩ := mem_utri_iff.1 (hA htA)
  have hs₀0 : s₀ ≠ 0 := by
    rintro rfl
    rw [utriElt_zero] at hs₀
    exact ht1' hs₀
  refine le_antisymm hA fun g hg => ?_
  obtain ⟨s, rfl⟩ := mem_utri_iff.1 hg
  by_cases hs : s = 0
  · rw [hs, utriElt_zero]
    exact A.one_mem
  · obtain ⟨a, ha⟩ := exists_torusElt_conj_utriElt hs₀0 hs
    have hle : conjSubgroup (torusElt a) A ≤ Subgroup.centralizer ({t} : Set SL(2, F)) := by
      rw [hs₀, centralizer_utriElt hs₀0]
      rintro x ⟨y, hy, rfl⟩
      exact conj_mem_utri_of_mem_borel (torusElt_mem_borel a) (hA hy)
    have hconj := (hWC.2 t htA ht1').2 (torusElt a) hle
    have hmem : torusElt a * t * (torusElt a)⁻¹ ∈ conjSubgroup (torusElt a) A :=
      conj_mem_conjSubgroup _ htA
    rw [hconj, hs₀, ha] at hmem
    exact hmem

end SylowPairs

section PSL

variable {F : Type} [Field F] [CharP F 2]

theorem center_sl2_eq_bot : Subgroup.center SL(2, F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨c, hc, hcA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hc1 : c = 1 := CharTwo.sq_injective (by simpa using hc)
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hcA, hc1]
  simp [Matrix.one_apply]

@[expose] noncomputable def pslMulEquivSL : PSL(2, F) ≃* SL(2, F) :=
  (QuotientGroup.quotientMulEquivOfEq center_sl2_eq_bot).trans QuotientGroup.quotientBot

theorem isConj_of_orderOf_eq_two_psl [Finite F] {x y : PSL(2, F)} (hx : orderOf x = 2)
    (hy : orderOf y = 2) : IsConj x y := by
  have key : ∀ z : PSL(2, F), orderOf z = 2 →
      pslMulEquivSL z * pslMulEquivSL z = 1 ∧ pslMulEquivSL z ≠ 1 := by
    intro z hz
    refine ⟨?_, ?_⟩
    · have h := pow_orderOf_eq_one z
      rw [hz] at h
      rw [← map_mul, ← pow_two, h, map_one]
    · intro h
      rw [map_eq_one_iff _ pslMulEquivSL.injective] at h
      rw [h, orderOf_one] at hz
      omega
  obtain ⟨hx2, hx1⟩ := key x hx
  obtain ⟨hy2, hy1⟩ := key y hy
  have hc := isConj_of_mul_self_eq_one hx2 hx1 hy2 hy1
  have := MonoidHom.map_isConj (pslMulEquivSL (F := F)).symm.toMonoidHom hc
  simpa using this

end PSL

theorem isConj_of_orderOf_eq_two_psl_galoisField (f : ℕ) {x y : PSL(2, GaloisField 2 f)}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y :=
  isConj_of_orderOf_eq_two_psl hx hy

theorem involutionClass_of_psl2 {K : Type} [Group K]
    (h : ∃ f : ℕ, 2 ≤ f ∧ Nonempty (K ≃* PSL(2, GaloisField 2 f))) {x y : K}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  obtain ⟨f, -, ⟨e⟩⟩ := h
  have hc := isConj_of_orderOf_eq_two_psl_galoisField f (x := e x) (y := e y)
    ((orderOf_injective e.toMonoidHom e.injective x).trans hx)
    ((orderOf_injective e.toMonoidHom e.injective y).trans hy)
  have := MonoidHom.map_isConj e.symm.toMonoidHom hc
  simpa using this

section Dihedral

theorem isConj_of_orderOf_eq_two_dihedral {n : ℕ} (hn : Odd n) {x y : DihedralGroup n}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  have : NeZero n := ⟨hn.pos.ne'⟩
  have hrot : ∀ z : DihedralGroup n, orderOf z = 2 → ∃ i : ZMod n, z = DihedralGroup.sr i := by
    intro z hz
    rcases z with i | i
    · exfalso
      have h1 : orderOf (DihedralGroup.r i) ∣ n := by
        apply orderOf_dvd_of_pow_eq_one
        simp
      rw [hz] at h1
      exact (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 h1)
    · exact ⟨i, rfl⟩
  obtain ⟨i, rfl⟩ := hrot x hx
  obtain ⟨j, rfl⟩ := hrot y hy
  obtain ⟨m, hm⟩ := hn
  have hhalf : (2 : ZMod n) * ((m : ZMod n) + 1) = 1 := by
    have h0 : ((2 * m + 1 : ℕ) : ZMod n) = 0 := by rw [← hm]; exact ZMod.natCast_self n
    push_cast at h0
    linear_combination h0
  refine isConj_iff.2 ⟨DihedralGroup.r (((m : ZMod n) + 1) * (i - j)), ?_⟩
  rw [DihedralGroup.inv_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
  congr 1
  linear_combination (-(i - j)) * hhalf

theorem involutionClass_of_dihedral {K : Type} [Group K]
    (h : ∃ n : ℕ, Odd n ∧ 3 ≤ n ∧ Nonempty (K ≃* DihedralGroup n)) {x y : K}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  obtain ⟨n, hn, -, ⟨e⟩⟩ := h
  have hc := isConj_of_orderOf_eq_two_dihedral hn (x := e x) (y := e y)
    ((orderOf_injective e.toMonoidHom e.injective x).trans hx)
    ((orderOf_injective e.toMonoidHom e.injective y).trans hy)
  have := MonoidHom.map_isConj e.symm.toMonoidHom hc
  simpa using this

end Dihedral

end CFSG.CGT.Timmesfeld75
