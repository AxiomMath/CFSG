module

public import CFSG.Quasithin.Background.FixVLattice
public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Quasithin

section Fix

variable {W : Type} [CommGroup W]

theorem fixV_anti {X Y : Subgroup (MulAut W)} (h : X ≤ Y) : fixV Y ≤ fixV X :=
  fun _ hv x hx => hv x (h hx)

theorem mem_fixV_closure {S : Set (MulAut W)} {v : W} :
    v ∈ fixV (Subgroup.closure S) ↔ ∀ s ∈ S, s v = v := by
  constructor
  · intro hv s hs
    exact hv s (Subgroup.subset_closure hs)
  · intro h x hx
    induction hx using Subgroup.closure_induction with
    | mem s hs => exact h s hs
    | one => rfl
    | mul a b _ _ ha hb => rw [MulAut.mul_apply, hb, ha]
    | inv a _ ha =>
      calc a⁻¹ v = a⁻¹ (a v) := by rw [ha]
        _ = v := by simp

theorem mem_fixV_zpowers {g : MulAut W} {v : W} : v ∈ fixV (Subgroup.zpowers g) ↔ g v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem fixV_sup (X Y : Subgroup (MulAut W)) : fixV (X ⊔ Y) = fixV X ⊓ fixV Y :=
  CFSG.Quasithin.FixVLat.fixV_sup_eq X Y

theorem fixV_bot : fixV (⊥ : Subgroup (MulAut W)) = ⊤ := by
  ext v
  simp only [Subgroup.mem_top, iff_true]
  intro x hx
  rw [Subgroup.mem_bot.1 hx]
  rfl

variable [Finite W]

omit [Finite W] in
theorem index_fixV_closure_le (l : List (MulAut W)) :
    (fixV (Subgroup.closure {x | x ∈ l})).index ≤
      (l.map fun x => (fixV (Subgroup.zpowers x)).index).prod := by
  induction l with
  | nil =>
    have : (Subgroup.closure {x : MulAut W | x ∈ ([] : List (MulAut W))}) = ⊥ := by
      simp
    rw [this, fixV_bot]
    simp
  | cons x l ih =>
    have hcl : Subgroup.closure {y : MulAut W | y ∈ x :: l} =
        Subgroup.zpowers x ⊔ Subgroup.closure {y : MulAut W | y ∈ l} := by
      rw [Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
      congr 1
      ext y
      simp
    rw [hcl, fixV_sup, List.map_cons, List.prod_cons]
    exact Subgroup.index_inf_le.trans (Nat.mul_le_mul le_rfl ih)

omit [Finite W] in
theorem index_fixV_conj (h g : MulAut W) :
    (fixV (Subgroup.zpowers (h * g * h⁻¹))).index = (fixV (Subgroup.zpowers g)).index :=
  CFSG.Quasithin.FixVLat.index_fixV_zpowers_conj h g

theorem index_fixV_pow_le (g : MulAut W) (m : ℕ) :
    (fixV (Subgroup.zpowers (g ^ m))).index ≤ (fixV (Subgroup.zpowers g)).index := by
  have : Subgroup.zpowers (g ^ m) ≤ Subgroup.zpowers g := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers g) m
  exact Subgroup.index_antitone (fixV_anti this)

theorem index_fixV_mul_le (g h : MulAut W) :
    (fixV (Subgroup.zpowers (g * h))).index ≤
      (fixV (Subgroup.zpowers g)).index * (fixV (Subgroup.zpowers h)).index := by
  have hle : fixV (Subgroup.zpowers g) ⊓ fixV (Subgroup.zpowers h) ≤
      fixV (Subgroup.zpowers (g * h)) := by
    intro v hv
    rw [Subgroup.mem_inf, mem_fixV_zpowers, mem_fixV_zpowers] at hv
    rw [mem_fixV_zpowers, MulAut.mul_apply, hv.2, hv.1]
  exact (Subgroup.index_antitone hle).trans Subgroup.index_inf_le

theorem index_fixV_eq_two_pow (hW : ∀ w : W, w * w = 1) (X : Subgroup (MulAut W)) :
    ∃ m : ℕ, (fixV X).index = 2 ^ m := by
  have hp : IsPGroup 2 W := by
    intro w
    refine ⟨1, ?_⟩
    simpa [pow_one, sq] using hW w
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hp
  have hdvd : (fixV X).index ∣ 2 ^ n := by
    rw [← hn, ← Subgroup.card_mul_index (fixV X)]
    exact Dvd.intro_left _ rfl
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨m, hm⟩

theorem index_fixV_le_card (X : Subgroup (MulAut W)) : (fixV X).index ≤ Nat.card W := by
  rw [← Subgroup.card_mul_index (fixV X)]
  exact Nat.le_mul_of_pos_left _ Nat.card_pos

theorem two_pow_orderOf_le_index_fixV (hW : ∀ w : W, w * w = 1) {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {g : MulAut W} (hg : orderOf g = p) :
    2 ^ orderOf (2 : ZMod p) ≤ (fixV (Subgroup.zpowers g)).index := by
  have hpg : IsPGroup p (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  have hmod := hpg.card_modEq_card_fixedPoints W
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers g) W) =
      Nat.card (fixV (Subgroup.zpowers g)) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun w => by
      rw [MulAction.mem_fixedPoints, mem_fixV_zpowers]
      constructor
      · intro h
        exact h ⟨g, Subgroup.mem_zpowers g⟩
      · intro h x
        obtain ⟨k, hk⟩ := x.2
        have : ((x : MulAut W)) w = w := by
          rw [← hk]
          have h' : g⁻¹ w = w := by
            conv_lhs => rw [← h]
            exact MulAut.inv_apply_self W g w
          have : ∀ k : ℤ, (g ^ k) w = w := by
            intro k
            induction k using Int.induction_on with
            | zero => rfl
            | succ k ih => rw [zpow_add_one, MulAut.mul_apply, h, ih]
            | pred k ih => rw [zpow_sub_one, MulAut.mul_apply, h', ih]
          exact this k
        exact this
  rw [hfix] at hmod
  obtain ⟨m, hm⟩ := index_fixV_eq_two_pow hW (Subgroup.zpowers g)
  have hcard := Subgroup.card_mul_index (fixV (Subgroup.zpowers g))
  have hnw : g ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hg
    exact hp.out.one_lt.ne hg
  have hm1 : 1 ≤ m := by
    by_contra hm0
    have hm0 : m = 0 := by omega
    rw [hm0, pow_zero, Subgroup.index_eq_one] at hm
    apply hnw
    ext w
    have : w ∈ fixV (Subgroup.zpowers g) := by rw [hm]; trivial
    rw [mem_fixV_zpowers] at this
    simpa using this
  obtain ⟨a, ha⟩ : ∃ a : ℕ, Nat.card (fixV (Subgroup.zpowers g)) = 2 ^ a := by
    have hpf : IsPGroup 2 (fixV (Subgroup.zpowers g)) := by
      intro w
      refine ⟨1, ?_⟩
      have := hW w
      ext
      simpa [pow_one, sq] using this
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).1 hpf
    exact ⟨a, ha⟩
  have hWc : Nat.card W = 2 ^ a * 2 ^ m := by rw [← hcard, ha, hm]
  have hcop : Nat.Coprime p (2 ^ a) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp.out Nat.prime_two).2 hp2)
  have hdvd : p ∣ 2 ^ m - 1 := by
    have h1 : 2 ^ a * 2 ^ m ≡ 2 ^ a * 1 [MOD p] := by
      rw [← hWc, mul_one, ← ha]
      exact hmod
    have h2 : 2 ^ m ≡ 1 [MOD p] := Nat.ModEq.cancel_left_of_coprime hcop h1
    exact (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).1 h2.symm
  have h2m : (2 : ZMod p) ^ m = 1 := by
    have := (ZMod.natCast_eq_natCast_iff' (2 ^ m) 1 p).2 (by
      have h3 : 2 ^ m ≡ 1 [MOD p] := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).2 hdvd |>.symm
      exact h3)
    simpa using this
  have hord : orderOf (2 : ZMod p) ∣ m := orderOf_dvd_of_pow_eq_one h2m
  rw [hm]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.le_of_dvd (by omega) hord)

end Fix

theorem orderOf_two_zmod_7 : orderOf (2 : ZMod 7) = 3 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem orderOf_two_zmod_11 : orderOf (2 : ZMod 11) = 10 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem orderOf_two_zmod_17 : orderOf (2 : ZMod 17) = 8 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem orderOf_two_zmod_19 : orderOf (2 : ZMod 19) = 18 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem orderOf_two_zmod_23 : orderOf (2 : ZMod 23) = 11 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem orderOf_two_zmod_37 : orderOf (2 : ZMod 37) = 36 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem card_le_of_exponent_two {S : Type} [Group S] [Finite S] {a m : ℕ} (hcard : Nat.card S = 2 ^ a * m)
    (hm : Odd m) (B : Subgroup S) (hB : ∀ x ∈ B, x * x = 1) : Nat.card B ≤ 2 ^ a := by
  have hp : IsPGroup 2 B := by
    intro x
    refine ⟨1, ?_⟩
    ext
    simpa [pow_one, sq] using hB x x.2
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hp
  have hdvd : 2 ^ n ∣ 2 ^ a * m := by
    have := Subgroup.card_subgroup_dvd_card B
    rwa [hn, hcard] at this
  have hcop : Nat.Coprime (2 ^ n) m := by
    refine Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 ?_)
    intro h
    obtain ⟨k, hk⟩ := hm
    obtain ⟨j, hj⟩ := h
    omega
  have hdvd' : 2 ^ n ∣ 2 ^ a := hcop.dvd_of_dvd_mul_right hdvd
  rw [hn]
  exact Nat.pow_le_pow_right (by norm_num) ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd')

end CFSG.QuasithinUnique.Setup.X1
