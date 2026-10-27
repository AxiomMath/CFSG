module

public import CFSG.CharacterTheory.Wreathed.Coordinates

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KDType

open CFSG.Wreathed (Wreath element coordinateEquiv element_injective element_base_mul
  element_swap_mul element_base_pow element_zero element_right swap_exponent_cases)

@[expose] def wreathBaseSub (m : ℕ) : Subgroup (Wreath m) :=
  (RegularWreathProduct.rightHom : Wreath m →* Multiplicative (ZMod 2)).ker

theorem mem_wreathBaseSub {m : ℕ} (y : Wreath m) : y ∈ wreathBaseSub m ↔ y.right = 1 :=
  Iff.rfl

theorem exists_element {m : ℕ} (y : Wreath m) : ∃ a b : ZMod m, ∃ e : ZMod 2,
    y = element m a b e := by
  obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv m).symm.surjective y
  exact ⟨a, b, e, rfl⟩

theorem element_eq_iff {m : ℕ} {a b c d : ZMod m} {e f : ZMod 2} :
    element m a b e = element m c d f ↔ a = c ∧ b = d ∧ e = f := by
  constructor
  · intro h
    have h' : (fun x : ZMod m × ZMod m × ZMod 2 => element m x.1 x.2.1 x.2.2) (a, b, e) =
        (fun x : ZMod m × ZMod m × ZMod 2 => element m x.1 x.2.1 x.2.2) (c, d, f) := h
    have := element_injective m h'
    simpa only [Prod.mk.injEq] using this
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem exists_element_base {m : ℕ} {y : Wreath m} (hy : y ∈ wreathBaseSub m) :
    ∃ a b : ZMod m, y = element m a b 0 := by
  obtain ⟨a, b, e, rfl⟩ := exists_element y
  rw [mem_wreathBaseSub, element_right] at hy
  rcases swap_exponent_cases e with rfl | rfl
  · exact ⟨a, b, rfl⟩
  · exfalso
    have h : (Multiplicative.ofAdd (1 : ZMod 2) : Multiplicative (ZMod 2)) = 1 := hy
    exact absurd (Multiplicative.ofAdd.injective (h.trans (ofAdd_zero).symm)) (by decide)

theorem wreathBaseSub_comm {m : ℕ} {x y : Wreath m} (hx : x ∈ wreathBaseSub m)
    (hy : y ∈ wreathBaseSub m) : x * y = y * x := by
  obtain ⟨a, b, rfl⟩ := exists_element_base hx
  obtain ⟨c, d, rfl⟩ := exists_element_base hy
  rw [element_base_mul, element_base_mul, add_comm a c, add_comm b d]

theorem index_wreathBaseSub (m : ℕ) : (wreathBaseSub m).index = 2 := by
  have hsurj : Function.Surjective (RegularWreathProduct.rightHom :
      Wreath m →* Multiplicative (ZMod 2)) := fun q => ⟨RegularWreathProduct.inl q, by simp⟩
  rw [wreathBaseSub, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem zmod_two_mul_eq_zero {n : ℕ} (hn : 1 ≤ n) {x : ZMod (2 ^ n)} (hx : 2 * x = 0) :
    x = 0 ∨ x = ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) := by
  haveI : NeZero (2 ^ n) := ⟨by positivity⟩
  set k := x.val with hk
  have hkx : x = (k : ZMod (2 ^ n)) := (ZMod.natCast_zmod_val x).symm
  have hlt : k < 2 ^ n := ZMod.val_lt x
  have hdvd : 2 ^ n ∣ 2 * k := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [← hkx]
    exact hx
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow] at hdvd hlt
  obtain ⟨q, hq⟩ := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) hdvd
  have hq2 : q < 2 := by
    have h1 : 2 ^ (n - 1) * q < 2 ^ (n - 1) * 2 := by
      rw [← hq]
      omega
    exact Nat.lt_of_mul_lt_mul_left h1
  interval_cases q
  · left
    rw [hkx, hq]
    simp
  · right
    rw [hkx, hq]
    simp

@[expose] def halfCoord (n : ℕ) (i : Fin 2) : ZMod (2 ^ n) :=
  (((i : ℕ) * 2 ^ (n - 1) : ℕ) : ZMod (2 ^ n))

theorem halfCoord_of_two_mul_eq_zero {n : ℕ} (hn : 1 ≤ n) {x : ZMod (2 ^ n)} (hx : 2 * x = 0) :
    ∃ i : Fin 2, x = halfCoord n i := by
  rcases zmod_two_mul_eq_zero hn hx with h | h
  · exact ⟨0, by simp [halfCoord, h]⟩
  · exact ⟨1, by simp [halfCoord, h]⟩

@[expose] def wreathT1 (n : ℕ) : Set (Wreath (2 ^ n)) :=
  Set.range (fun p : Fin 2 × Fin 2 => element (2 ^ n) (halfCoord n p.1) (halfCoord n p.2) 0)

@[expose] def wreathT2 (n : ℕ) : Set (Wreath (2 ^ n)) :=
  Set.range (fun i : Fin 2 => element (2 ^ n) (halfCoord n i) (halfCoord n i) 0)

theorem base_two_torsion_mem {n : ℕ} (hn : 1 ≤ n) {y : Wreath (2 ^ n)}
    (hy : y ∈ wreathBaseSub (2 ^ n)) (hy2 : y ^ 2 = 1) : y ∈ wreathT1 n := by
  obtain ⟨a, b, rfl⟩ := exists_element_base hy
  rw [element_base_pow, ← element_zero, element_eq_iff] at hy2
  obtain ⟨ha, hb, -⟩ := hy2
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at ha hb
  obtain ⟨i, hi⟩ := halfCoord_of_two_mul_eq_zero hn ha
  obtain ⟨j, hj⟩ := halfCoord_of_two_mul_eq_zero hn hb
  subst hi
  subst hj
  exact ⟨(i, j), rfl⟩

theorem base_commute_two_torsion_mem {n : ℕ} (hn : 1 ≤ n) {y t : Wreath (2 ^ n)}
    (hy : y ∈ wreathBaseSub (2 ^ n)) (hy2 : y ^ 2 = 1) (ht : t ∉ wreathBaseSub (2 ^ n))
    (hcomm : y * t = t * y) : y ∈ wreathT2 n := by
  obtain ⟨a, b, rfl⟩ := exists_element_base hy
  obtain ⟨c, d, e, rfl⟩ := exists_element t
  have he : e = 1 := by
    rcases swap_exponent_cases e with rfl | rfl
    · exact absurd ((mem_wreathBaseSub _).mpr (by simp)) ht
    · rfl
  subst he
  rw [element_base_mul, element_swap_mul, element_eq_iff] at hcomm
  obtain ⟨h1, -, -⟩ := hcomm
  have hab : a = b := by
    have h1' := h1
    rw [add_comm c b] at h1'
    exact add_right_cancel h1'
  subst hab
  rw [element_base_pow, ← element_zero, element_eq_iff] at hy2
  obtain ⟨ha, -, -⟩ := hy2
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at ha
  obtain ⟨i, hi⟩ := halfCoord_of_two_mul_eq_zero hn ha
  subst hi
  exact ⟨i, rfl⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KDType
