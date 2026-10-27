module

public import CFSG.CGT.PushingUpLit.CGT6M.FixSub

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

section Basic

variable {V : Type} [CommGroup V]

@[expose] def deltaHom (x : MulAut V) : V →* V where
  toFun v := x v * v⁻¹
  map_one' := by simp
  map_mul' u v := by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem deltaHom_apply (x : MulAut V) (v : V) : deltaHom x v = x v * v⁻¹ := rfl

@[expose] def commSub (x : MulAut V) : Subgroup V := (deltaHom x).range

theorem deltaHom_mem_commSub (x : MulAut V) (v : V) : x v * v⁻¹ ∈ commSub x := ⟨v, rfl⟩

theorem ker_deltaHom (x : MulAut V) : (deltaHom x).ker = fixSub x := by
  ext v
  rw [MonoidHom.mem_ker, deltaHom_apply, mul_inv_eq_one, mem_fixSub]

theorem card_commSub_mul_card_fixSub [Finite V] (x : MulAut V) :
    Nat.card (commSub x) * Nat.card (fixSub x) = Nat.card V := by
  have h := Subgroup.card_ker_mul_card_range (deltaHom x)
  rw [ker_deltaHom] at h
  rw [mul_comm]
  exact h

theorem commSub_eq_bot_iff {x : MulAut V} : commSub x = ⊥ ↔ x = 1 := by
  constructor
  · intro h
    ext v
    have hv : x v * v⁻¹ ∈ commSub x := deltaHom_mem_commSub x v
    rw [h, Subgroup.mem_bot, mul_inv_eq_one] at hv
    exact hv
  · rintro rfl
    refine (Subgroup.eq_bot_iff_forall _).mpr fun w hw => ?_
    obtain ⟨v, rfl⟩ := hw
    exact mul_inv_cancel v

theorem apply_mem_commSub {x y : MulAut V} (hxy : x * y = y * x) {w : V} (hw : w ∈ commSub x) :
    y w ∈ commSub x := by
  obtain ⟨v, rfl⟩ := hw
  refine ⟨y v, ?_⟩
  have h : y (x v) = x (y v) := by
    have := congrArg (fun e : MulAut V => e v) hxy.symm
    simpa using this
  simp only [deltaHom_apply, map_mul, map_inv, h]

theorem card_commSub_conj [Finite V] (g x : MulAut V) :
    Nat.card (commSub (g * x * g⁻¹)) = Nat.card (commSub x) := by
  have h1 := card_commSub_mul_card_fixSub (g * x * g⁻¹)
  have h2 := card_commSub_mul_card_fixSub x
  rw [card_fixSub_conj] at h1
  have hpos : 0 < Nat.card (fixSub x) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

theorem map_commSub_conj (g x : MulAut V) :
    (commSub x).map (g : V ≃* V).toMonoidHom = commSub (g * x * g⁻¹) := by
  ext w
  constructor
  · rintro ⟨u, ⟨v, rfl⟩, rfl⟩
    refine ⟨g v, ?_⟩
    simp [deltaHom_apply]
  · rintro ⟨v, rfl⟩
    refine ⟨x (g⁻¹ v) * (g⁻¹ v)⁻¹, ⟨g⁻¹ v, rfl⟩, ?_⟩
    simp [deltaHom_apply, MulAut.mul_apply]

theorem commSub_pow_le (x : MulAut V) (n : ℕ) : commSub (x ^ n) ≤ commSub x := by
  induction n with
  | zero =>
    intro w hw
    obtain ⟨v, rfl⟩ := hw
    simp [deltaHom_apply]
  | succ n ih =>
    rintro w ⟨v, rfl⟩
    have h : (x ^ (n + 1)) v * v⁻¹ = ((x ^ n) (x v) * (x v)⁻¹) * (x v * v⁻¹) := by
      rw [pow_succ, MulAut.mul_apply]
      group
    rw [deltaHom_apply, h]
    exact Subgroup.mul_mem _ (ih ⟨x v, rfl⟩) (deltaHom_mem_commSub x v)

theorem commSub_pow_eq {x : MulAut V} (hx : x ^ 5 = 1) {k m : ℕ} (h : k * m % 5 = 1) :
    commSub (x ^ k) = commSub x := by
  refine le_antisymm (commSub_pow_le x k) ?_
  have h1 : (x ^ k) ^ m = x := by
    rw [← pow_mul, ← pow_mod_five hx, h, pow_one]
  have := commSub_pow_le (x ^ k) m
  rwa [h1] at this

theorem commSub_inf_fixSub_eq_bot {x : MulAut V} {m : ℕ} (hm : Odd m) (hx : x ^ m = 1)
    (hV : ∀ v : V, v ^ 2 = 1) : commSub x ⊓ fixSub x = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun w hw => ?_
  obtain ⟨hwc, hwf⟩ := hw
  obtain ⟨u, rfl⟩ := hwc
  set w := x u * u⁻¹ with hw
  have hfix : ∀ j : ℕ, (x ^ j) w = w := fun j => fixSub_le_pow x j hwf
  have hprod : ∏ j ∈ Finset.range m, (x ^ j) w = 1 := by
    have h1 : ∀ j : ℕ, (x ^ j) w = (x ^ (j + 1)) u / (x ^ j) u := by
      intro j
      rw [hw, map_mul, map_inv, pow_succ, MulAut.mul_apply, div_eq_mul_inv]
    simp_rw [h1]
    rw [Finset.prod_range_div (fun j : ℕ => (x ^ j) u) m]
    simp [hx]
  have hpow : w ^ m = w := by
    obtain ⟨k, hk⟩ := hm
    rw [hk, pow_succ, pow_mul, hV w, one_pow, one_mul]
  have : ∏ j ∈ Finset.range m, (x ^ j) w = w ^ m := by
    simp_rw [hfix]
    simp
  have hw1 : w = 1 := by rw [← hpow, ← this, hprod]
  exact hw1

theorem card_modEq_card_fixSub_prime [Finite V] {p : ℕ} [hp : Fact p.Prime] {x : MulAut V}
    (hx : x ^ p = 1) : Nat.card V ≡ Nat.card (fixSub x) [MOD p] := by
  by_cases hx1 : x = 1
  · subst hx1
    rw [fixSub_one, Subgroup.card_top]
  have hord : orderOf x = p := orderOf_eq_prime hx hx1
  let K := Subgroup.zpowers x
  have hK : IsPGroup p K := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hset : MulAction.fixedPoints K V = (fixSub x : Set V) := by
    ext v
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro hv
      exact hv ⟨x, Subgroup.mem_zpowers x⟩
    · intro hv u
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp u.2
      change (u : MulAut V) v = v
      rw [← hk]
      have h2 : v ∈ MulAction.fixedBy V x := by
        rw [MulAction.mem_fixedBy]; exact hv
      have h3 := MulAction.mem_fixedBy_zpow h2 k
      rwa [MulAction.mem_fixedBy] at h3
  have hmod := hK.card_modEq_card_fixedPoints V
  rw [hset] at hmod
  exact hmod

@[expose] def stabAut [Finite V] (M : Subgroup V) : Subgroup (MulAut V) where
  carrier := {x | ∀ m ∈ M, x m ∈ M}
  one_mem' := fun m hm => hm
  mul_mem' := fun {a b} ha hb m hm => ha _ (hb m hm)
  inv_mem' := fun {a} ha m hm => by
    have hinj : Function.Injective (fun m : M => (⟨a m, ha m m.2⟩ : M)) := fun m m' h =>
      Subtype.ext (a.injective (congrArg Subtype.val h))
    obtain ⟨m', hm'⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨m, hm⟩
    have h2 : a m' = m := congrArg Subtype.val hm'
    rw [← h2, MulAut.inv_apply_self]
    exact m'.2

@[expose] def restrictHom [Finite V] (M : Subgroup V) : stabAut M →* MulAut ↥M where
  toFun x :=
    { toFun := fun m => ⟨(x : MulAut V) m, x.2 m m.2⟩
      invFun := fun m => ⟨((x⁻¹ : stabAut M) : MulAut V) m, (x⁻¹ : stabAut M).2 m m.2⟩
      left_inv := fun m => Subtype.ext (by simp)
      right_inv := fun m => Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (map_mul (x : MulAut V) (a : V) (b : V)) }
  map_one' := MulEquiv.ext fun _ => rfl
  map_mul' := fun _ _ => MulEquiv.ext fun _ => rfl

theorem restrictHom_eq_one_iff [Finite V] (M : Subgroup V) (x : stabAut M) :
    restrictHom M x = 1 ↔ ∀ m ∈ M, (x : MulAut V) m = m := by
  constructor
  · intro h m hm
    have := congrArg (fun e : MulAut ↥M => ((e ⟨m, hm⟩ : M) : V)) h
    simp only [MulAut.one_apply] at this
    exact this
  · intro h
    ext m
    exact h m m.2

theorem card_fixSub_restrictHom [Finite V] (M : Subgroup V) (x : stabAut M) :
    Nat.card (fixSub (restrictHom M x)) = Nat.card ↥(M ⊓ fixSub (x : MulAut V)) :=
  Nat.card_congr
    { toFun := fun m => ⟨(m.1 : V), m.1.2, (congrArg Subtype.val m.2 : (x : MulAut V) m.1 = m.1)⟩
      invFun := fun v => ⟨⟨v.1, v.2.1⟩, Subtype.ext (v.2.2 : (x : MulAut V) v.1 = v.1)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_modEq_inf_fixSub_prime [Finite V] {p : ℕ} [Fact p.Prime] {x : MulAut V}
    (hx : x ^ p = 1) {M : Subgroup V} (hM : ∀ m ∈ M, x m ∈ M) :
    Nat.card M ≡ Nat.card ↥(M ⊓ fixSub x) [MOD p] := by
  let x' : stabAut M := ⟨x, hM⟩
  have hx' : x' ^ p = 1 := Subtype.ext hx
  have h := card_modEq_card_fixSub_prime (x := restrictHom M x') (by rw [← map_pow, hx', map_one])
  rwa [card_fixSub_restrictHom] at h

section Five

variable [Finite V]

omit [Finite V] in
theorem isPGroup_two_subgroup (hV : ∀ v : V, v ^ 2 = 1) (M : Subgroup V) : IsPGroup 2 ↥M :=
  fun m => ⟨1, Subtype.ext (by simpa using hV (m : V))⟩

theorem exists_card_eq_two_pow (hV : ∀ v : V, v ^ 2 = 1) (M : Subgroup V) :
    ∃ d : ℕ, Nat.card M = 2 ^ d :=
  (isPGroup_two_subgroup hV M).exists_card_eq

theorem card_eq_one_or_sixteen {x : MulAut V} (hx : x ^ 5 = 1) (hV : ∀ v : V, v ^ 2 = 1)
    {M : Subgroup V} (hM : ∀ m ∈ M, x m ∈ M) (hfix : M ⊓ fixSub x = ⊥)
    (hle : Nat.card M ≤ 16) : Nat.card M = 1 ∨ Nat.card M = 16 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := card_modEq_inf_fixSub_prime hx hM
  rw [hfix, Subgroup.card_bot] at h
  obtain ⟨d, hd⟩ := exists_card_eq_two_pow hV M
  rw [hd] at h hle ⊢
  have hd4 : d ≤ 4 := by
    by_contra hcon
    have h5 : 5 ≤ d := Nat.lt_of_not_le hcon
    have : 2 ^ 5 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) h5
    omega
  have key : d = 0 ∨ d = 4 := by
    interval_cases d
    · exact Or.inl rfl
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact Or.inr rfl
  rcases key with rfl | rfl
  · exact Or.inl (by norm_num)
  · exact Or.inr (by norm_num)

theorem card_commSub_eq_sixteen {x : MulAut V} (hx : x ^ 5 = 1) (hx1 : x ≠ 1)
    (hV : ∀ v : V, v ^ 2 = 1) (hle : Nat.card (commSub x) ≤ 16) : Nat.card (commSub x) = 16 := by
  have hM : ∀ m ∈ commSub x, x m ∈ commSub x := fun m hm => apply_mem_commSub rfl hm
  rcases card_eq_one_or_sixteen hx hV hM (commSub_inf_fixSub_eq_bot (by decide : Odd 5) hx hV)
    hle with h | h
  · exfalso
    apply hx1
    rw [← commSub_eq_bot_iff]
    exact Subgroup.eq_bot_of_card_eq _ h
  · exact h

theorem commSub_dichotomy {x y : MulAut V} (hxy : x * y = y * x) (hy5 : y ^ 5 = 1)
    (hV : ∀ v : V, v ^ 2 = 1) (hx : Nat.card (commSub x) = 16)
    (hy : Nat.card (commSub y) = 16) : commSub y ≤ fixSub x ∨ commSub x = commSub y := by
  let M : Subgroup V := (commSub y).map (deltaHom x)
  have hMy : M ≤ commSub y := by
    rintro w ⟨n, hn, rfl⟩
    exact Subgroup.mul_mem _ (apply_mem_commSub hxy.symm hn) (Subgroup.inv_mem _ hn)
  have hMx : M ≤ commSub x := by
    rintro w ⟨n, -, rfl⟩
    exact deltaHom_mem_commSub x n
  have hMinv : ∀ m ∈ M, y m ∈ M := by
    rintro w ⟨n, hn, rfl⟩
    refine ⟨y n, apply_mem_commSub rfl hn, ?_⟩
    have h : y (x n) = x (y n) := by
      have := congrArg (fun e : MulAut V => e n) hxy.symm
      simpa using this
    simp only [deltaHom_apply, map_mul, map_inv, h]
  have hfix : M ⊓ fixSub y = ⊥ :=
    le_bot_iff.mp (le_trans (inf_le_inf_right _ hMy)
      (le_of_eq (commSub_inf_fixSub_eq_bot (by decide : Odd 5) hy5 hV)))
  have hle : Nat.card M ≤ 16 := hy ▸ Subgroup.card_le_of_le hMy
  rcases card_eq_one_or_sixteen hy5 hV hMinv hfix hle with h | h
  · left
    have hbot : M = ⊥ := Subgroup.eq_bot_of_card_eq _ h
    intro n hn
    have : deltaHom x n ∈ M := ⟨n, hn, rfl⟩
    rw [hbot, Subgroup.mem_bot, deltaHom_apply, mul_inv_eq_one] at this
    exact this
  · right
    have h1 : M = commSub y := Subgroup.eq_of_le_of_card_ge hMy (by rw [h, hy])
    have h2 : M = commSub x := Subgroup.eq_of_le_of_card_ge hMx (by rw [h, hx])
    rw [← h1, ← h2]

theorem two_pow_ten_le_card_commSub {a : MulAut V} (ha11 : a ^ 11 = 1) (ha1 : a ≠ 1)
    (hV : ∀ v : V, v ^ 2 = 1) : 2 ^ 10 ≤ Nat.card (commSub a) := by
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hM : ∀ m ∈ commSub a, a m ∈ commSub a := fun m hm => apply_mem_commSub rfl hm
  have hfix := commSub_inf_fixSub_eq_bot (by decide : Odd 11) ha11 hV
  have h := card_modEq_inf_fixSub_prime ha11 hM
  rw [hfix, Subgroup.card_bot] at h
  obtain ⟨d, hd⟩ := exists_card_eq_two_pow hV (commSub a)
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply ha1
    rw [← commSub_eq_bot_iff]
    exact Subgroup.eq_bot_of_card_eq _ (by simpa using hd)
  rw [hd] at h ⊢
  have h10 : 10 ≤ d := by
    by_contra hlt
    have hlt : d < 10 := Nat.lt_of_not_le hlt
    interval_cases d
    · exact hd0 rfl
    all_goals exact absurd h (by decide)
  exact Nat.pow_le_pow_right (by norm_num) h10

omit [Finite V] in
theorem commSub_pow_eq_of_not_dvd {x : MulAut V} (hx : x ^ 5 = 1) {k : ℕ} (hk : ¬ 5 ∣ k) :
    commSub (x ^ k) = commSub x := by
  have hcop : Nat.Coprime k 5 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hk |>.symm
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num : 1 < 5)
  exact commSub_pow_eq hx hm

omit [Finite V] in
theorem fixSub_pow_eq_of_not_dvd {x : MulAut V} (hx : x ^ 5 = 1) {k : ℕ} (hk : ¬ 5 ∣ k) :
    fixSub (x ^ k) = fixSub x := by
  have hcop : Nat.Coprime k 5 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hk |>.symm
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num : 1 < 5)
  exact fixSub_pow_eq hx hm

omit [Finite V] in
theorem eq_one_of_fixSub_eq_top {x : MulAut V} (h : fixSub x = ⊤) : x = 1 := by
  ext v
  have : v ∈ fixSub x := h ▸ Subgroup.mem_top v
  exact this

omit [Finite V] in
theorem eq_one_of_fixSub_pow {x : MulAut V} (hx : x ^ 5 = 1) {k : ℕ} (hk : ¬ 5 ∣ k)
    (h : ∀ v : V, (x ^ k) v = v) : x = 1 := by
  refine eq_one_of_fixSub_eq_top ?_
  rw [← fixSub_pow_eq_of_not_dvd hx hk]
  exact eq_top_iff.mpr fun v _ => h v

end Five

end Basic

end CFSG.CGT.PushingUpLit.CGT6M
