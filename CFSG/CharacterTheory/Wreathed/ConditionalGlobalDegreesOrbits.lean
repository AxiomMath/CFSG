module

public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseCount

public section

namespace CFSG.Wreathed.ConditionalGlobalDegrees

open CFSG.Wreathed.ConditionalGeneralBase CFSG.Wreathed.ConditionalCompleteBase

theorem even_val_iff {m : ℕ} [NeZero m] (hm : 2 ∣ m) (x : ZMod m) :
    Even x.val ↔ ZMod.castHom hm (ZMod 2) x = 0 := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff_even]

theorem evenEven_iff_of_mem_orbit {m : ℕ} [NeZero m] (hm : 2 ∣ m) {I I' : ZMod m × ZMod m}
    (h : I' ∈ MulAction.orbit (dualGroup m) I) :
    (Even I'.1.val ∧ Even I'.2.val ↔ Even I.1.val ∧ Even I.2.val) := by
  rw [mem_orbit_dualGroup_iff, mem_dualSix_iff] at h
  simp only [even_val_iff hm]
  have key : ∀ a b : ZMod 2, (b = 0 ∧ a = 0 ↔ a = 0 ∧ b = 0) ∧
      (b = 0 ∧ -a - b = 0 ↔ a = 0 ∧ b = 0) ∧ (-a - b = 0 ∧ a = 0 ↔ a = 0 ∧ b = 0) ∧
      (a = 0 ∧ -a - b = 0 ↔ a = 0 ∧ b = 0) ∧ (-a - b = 0 ∧ b = 0 ↔ a = 0 ∧ b = 0) := by
    decide
  obtain ⟨k₁, k₂, k₃, k₄, k₅⟩ := key (ZMod.castHom hm (ZMod 2) I.1) (ZMod.castHom hm (ZMod 2) I.2)
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Iff.rfl
  · exact k₁
  · simpa only [map_sub, map_neg] using k₂
  · simpa only [map_sub, map_neg] using k₃
  · simpa only [map_sub, map_neg] using k₄
  · simpa only [map_sub, map_neg] using k₅

@[expose] def double (M m : ℕ) (x : ZMod M) : ZMod m :=
  ((2 * x.val : ℕ) : ZMod m)

@[expose] def double₂ (M m : ℕ) (I : ZMod M × ZMod M) : ZMod m × ZMod m :=
  (double M m I.1, double M m I.2)

variable {M m : ℕ} [NeZero M]

theorem double_add (hm : m = 2 * M) (x y : ZMod M) :
    double M m (x + y) = double M m x + double M m y := by
  subst hm
  rw [double, double, double, ZMod.val_add, ← Nat.mul_mod_mul_left, ZMod.natCast_mod]
  push_cast
  ring

omit [NeZero M] in
theorem double_zero : double M m 0 = 0 := by
  rw [double, ZMod.val_zero, mul_zero, Nat.cast_zero]

theorem double_neg (hm : m = 2 * M) (x : ZMod M) : double M m (-x) = -double M m x := by
  have h := double_add hm x (-x)
  rw [add_neg_cancel, double_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem double_sub (hm : m = 2 * M) (x y : ZMod M) :
    double M m (x - y) = double M m x - double M m y := by
  rw [sub_eq_add_neg, double_add hm, double_neg hm, ← sub_eq_add_neg]

theorem val_double (hm : m = 2 * M) (x : ZMod M) : (double M m x).val = 2 * x.val := by
  rw [double, ZMod.val_natCast, Nat.mod_eq_of_lt]
  have := ZMod.val_lt x
  omega

theorem double_injective (hm : m = 2 * M) : Function.Injective (double M m) := by
  intro x y h
  have h' := congrArg ZMod.val h
  rw [val_double hm, val_double hm] at h'
  exact ZMod.val_injective M (by omega)

theorem exists_double_of_even (hm : m = 2 * M) {y : ZMod m} (hy : Even y.val) :
    ∃ x : ZMod M, double M m x = y := by
  have hM0 := NeZero.ne M
  have : NeZero m := ⟨by omega⟩
  obtain ⟨a, ha⟩ := hy
  have hlt := ZMod.val_lt y
  have haM : a < M := by omega
  refine ⟨(a : ZMod M), ?_⟩
  rw [double, ZMod.val_natCast, Nat.mod_eq_of_lt haM, show 2 * a = y.val by omega,
    ZMod.natCast_zmod_val]

theorem double₂_injective (hm : m = 2 * M) : Function.Injective (double₂ M m) := fun _ _ h =>
  Prod.ext (double_injective hm (congrArg Prod.fst h)) (double_injective hm (congrArg Prod.snd h))

theorem dualSix_double₂ (hm : m = 2 * M) (I : ZMod M × ZMod M) :
    dualSix (double₂ M m I) = (dualSix I).map (double₂ M m) := by
  simp only [dualSix, double₂, List.map_cons, List.map_nil, double_sub hm, double_neg hm]

theorem ncard_orbit_double₂_eq_six_iff (hm : m = 2 * M) (I : ZMod M × ZMod M) :
    (MulAction.orbit (dualGroup m) (double₂ M m I)).ncard = 6 ↔
      (MulAction.orbit (dualGroup M) I).ncard = 6 := by
  rw [ncard_orbit_eq_six_iff, ncard_orbit_eq_six_iff, dualSix_double₂ hm,
    List.nodup_map_iff (double₂_injective hm)]

theorem mem_orbit_double₂_iff (hm : m = 2 * M) (I : ZMod M × ZMod M) (J : ZMod m × ZMod m) :
    J ∈ MulAction.orbit (dualGroup m) (double₂ M m I) ↔
      ∃ J' ∈ MulAction.orbit (dualGroup M) I, double₂ M m J' = J := by
  rw [mem_orbit_dualGroup_iff, dualSix_double₂ hm, List.mem_map]
  simp only [mem_orbit_dualGroup_iff]

theorem evenEven_iff_exists_double₂ (hm : m = 2 * M) (J : ZMod m × ZMod m) :
    (Even J.1.val ∧ Even J.2.val) ↔ ∃ I, double₂ M m I = J := by
  constructor
  · rintro ⟨h₁, h₂⟩
    obtain ⟨a, ha⟩ := exists_double_of_even hm h₁
    obtain ⟨b, hb⟩ := exists_double_of_even hm h₂
    exact ⟨(a, b), Prod.ext ha hb⟩
  · rintro ⟨I, rfl⟩
    exact ⟨⟨I.1.val, by rw [double₂, val_double hm, two_mul]⟩,
      ⟨I.2.val, by rw [double₂, val_double hm, two_mul]⟩⟩

theorem card_filter_evenEven {n : ℕ} (hn : 2 ≤ n) (V : Finset (ZMod (2 ^ n) × ZMod (2 ^ n)))
    (hV6 : ∀ I ∈ V, (MulAction.orbit (dualGroup (2 ^ n)) I).ncard = 6)
    (hVrep : ∀ I, (MulAction.orbit (dualGroup (2 ^ n)) I).ncard = 6 →
      ∃! I', I' ∈ V ∧ I' ∈ MulAction.orbit (dualGroup (2 ^ n)) I) :
    (V.filter fun I => Even I.1.val ∧ Even I.2.val).card =
      (2 ^ n / 2 - 1) * (2 ^ n / 2 - 2) / 6 := by
  have hm : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hM : 2 ^ n / 2 = 2 ^ (n - 1) := by
    rw [hm, Nat.mul_div_cancel_left _ (by norm_num)]
  let V' : Finset (ZMod (2 ^ (n - 1)) × ZMod (2 ^ (n - 1))) :=
    Finset.univ.filter fun I => double₂ (2 ^ (n - 1)) (2 ^ n) I ∈ V
  have hV'6 : ∀ I ∈ V', (MulAction.orbit (dualGroup (2 ^ (n - 1))) I).ncard = 6 := by
    intro I hI
    rw [← ncard_orbit_double₂_eq_six_iff hm]
    exact hV6 _ (Finset.mem_filter.mp hI).2
  have hV'rep : ∀ I, (MulAction.orbit (dualGroup (2 ^ (n - 1))) I).ncard = 6 →
      ∃! I', I' ∈ V' ∧ I' ∈ MulAction.orbit (dualGroup (2 ^ (n - 1))) I := by
    intro I hI
    obtain ⟨J, ⟨hJV, hJI⟩, huniq⟩ := hVrep _ ((ncard_orbit_double₂_eq_six_iff hm I).mpr hI)
    obtain ⟨J', hJ'I, rfl⟩ := (mem_orbit_double₂_iff hm I J).mp hJI
    refine ⟨J', ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJV⟩, hJ'I⟩, ?_⟩
    rintro K ⟨hKV, hKI⟩
    exact double₂_injective hm (huniq _ ⟨(Finset.mem_filter.mp hKV).2,
      (mem_orbit_double₂_iff hm I _).mpr ⟨K, hKI, rfl⟩⟩)
  have hcard := card_orbit_representatives_two_pow V' hV'6 hV'rep
  have hbij : V'.card = (V.filter fun I => Even I.1.val ∧ Even I.2.val).card := by
    apply Finset.card_bij (fun I _ => double₂ (2 ^ (n - 1)) (2 ^ n) I)
    · intro I hI
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hI).2,
        (evenEven_iff_exists_double₂ hm _).mpr ⟨I, rfl⟩⟩
    · intro I _ J _ h
      exact double₂_injective hm h
    · intro J hJ
      obtain ⟨hJV, hJe⟩ := Finset.mem_filter.mp hJ
      obtain ⟨I, rfl⟩ := (evenEven_iff_exists_double₂ hm J).mp hJe
      exact ⟨I, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJV⟩, rfl⟩
  rw [← hbij, hcard, hM]

theorem card_filter_not_evenEven {n : ℕ} (hn : 2 ≤ n) (V : Finset (ZMod (2 ^ n) × ZMod (2 ^ n)))
    (hV6 : ∀ I ∈ V, (MulAction.orbit (dualGroup (2 ^ n)) I).ncard = 6)
    (hVrep : ∀ I, (MulAction.orbit (dualGroup (2 ^ n)) I).ncard = 6 →
      ∃! I', I' ∈ V ∧ I' ∈ MulAction.orbit (dualGroup (2 ^ n)) I) :
    (V.filter fun I => ¬ (Even I.1.val ∧ Even I.2.val)).card = 2 ^ n * (2 ^ n - 2) / 8 := by
  have hm : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hM : 2 ^ n / 2 = 2 ^ (n - 1) := by
    rw [hm, Nat.mul_div_cancel_left _ (by norm_num)]
  have hM2 : 2 ≤ 2 ^ (n - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsum := Finset.card_filter_add_card_filter_not (s := V)
    (fun I : ZMod (2 ^ n) × ZMod (2 ^ n) => Even I.1.val ∧ Even I.2.val)
  rw [card_filter_evenEven hn V hV6 hVrep, card_orbit_representatives_two_pow V hV6 hVrep,
    hM] at hsum
  have h6m := six_dvd_two_pow_sub_one_mul_sub_two n
  have h6M := six_dvd_two_pow_sub_one_mul_sub_two (n - 1)
  generalize (V.filter fun I => ¬ (Even I.1.val ∧ Even I.2.val)).card = e at hsum ⊢
  rw [hm] at hsum h6m ⊢
  generalize 2 ^ (n - 1) = M at hsum h6m h6M hM2 ⊢
  obtain ⟨a, ha⟩ := h6m
  obtain ⟨b, hb⟩ := h6M
  rw [ha, hb, Nat.mul_div_cancel_left _ (by norm_num : 0 < 6),
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 6)] at hsum
  have h3 : 3 * (2 * M * (2 * M - 2)) = 3 * (8 * e) := by
    zify [show 1 ≤ 2 * M by omega, show 2 ≤ 2 * M by omega, show 1 ≤ M by omega, hM2]
      at ha hb hsum ⊢
    linear_combination 4 * ha - 4 * hb - 24 * hsum
  rw [Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3) h3,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 8)]

end CFSG.Wreathed.ConditionalGlobalDegrees
