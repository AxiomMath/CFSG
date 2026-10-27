module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.NormMap
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin

variable {V : Type} [CommGroup V]

theorem card_fiber_eq_card_stab [DecidableEq V] (K : Subgroup (MulAut V)) [Fintype ↥K] (w : V)
    (k₀ : ↥K) :
    (Finset.univ.filter fun k : ↥K => (k : MulAut V) w = (k₀ : MulAut V) w).card =
      (Finset.univ.filter fun k : ↥K => (k : MulAut V) w = w).card := by
  classical
  refine Finset.card_bij (fun k _ => k₀⁻¹ * k) ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    show (k₀ : MulAut V)⁻¹ ((k : MulAut V) w) = w
    rw [hk]
    exact MulAut.inv_apply_self V (k₀ : MulAut V) w
  · intro a _ b _ h
    simpa using h
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    refine ⟨k₀ * s, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show (k₀ : MulAut V) ((s : MulAut V) w) = (k₀ : MulAut V) w
    rw [hs]

theorem normK_eq_prod_image [DecidableEq V] (hV : ∀ v : V, v ^ 2 = 1)
    (K : Subgroup (MulAut V)) [Fintype ↥K] (hodd : Odd (Fintype.card ↥K)) (w : V) :
    normK K w = ∏ u ∈ Finset.univ.image (fun k : ↥K => (k : MulAut V) w), u := by
  classical
  rw [normK_apply, Finset.prod_comp (fun u : V => u) (fun k : ↥K => (k : MulAut V) w)]
  refine Finset.prod_congr rfl fun u hu => ?_
  obtain ⟨k₀, -, rfl⟩ := Finset.mem_image.mp hu
  have h1 := card_fiber_eq_card_stab K w k₀
  let S : Subgroup ↥K := MulAction.stabilizer ↥K w
  have h2 : (Finset.univ.filter fun k : ↥K => (k : MulAut V) w = w).card = Nat.card S := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  have h3 : Nat.card S ∣ Fintype.card ↥K := by
    rw [← Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card S
  have h4 : Odd (Nat.card S) := Odd.of_dvd_nat hodd h3
  rw [h1, h2]
  exact pow_odd_eq_self hV _ h4

theorem normK_eq_of_fixV (hV : ∀ v : V, v ^ 2 = 1) (E H H' : Subgroup (MulAut V)) [Fintype ↥E]
    [Fintype ↥H] (hoddE : Odd (Fintype.card ↥E)) (hoddH : Odd (Fintype.card ↥H)) (hHE : H ≤ E)
    (hdec : ∀ e ∈ E, ∃ h ∈ H, ∃ h' ∈ H', e = h * h') {w : V} (hw : w ∈ fixV H') :
    normK H w = normK E w := by
  classical
  rw [normK_eq_prod_image hV H hoddH, normK_eq_prod_image hV E hoddE]
  congr 1
  ext u
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨⟨h, hHE h.2⟩, rfl⟩
  · rintro ⟨e, rfl⟩
    obtain ⟨h, hh, h', hh', he⟩ := hdec e e.2
    refine ⟨⟨h, hh⟩, ?_⟩
    show h w = (e : MulAut V) w
    rw [he]
    show h w = h (h' w)
    rw [hw h' hh']

@[expose] def hypPart (E H : Subgroup (MulAut V)) [Fintype ↥E] : Subgroup V :=
  fixV H ⊓ (normK E).ker

theorem normK_hypPart_self (hV : ∀ v : V, v ^ 2 = 1) (E H : Subgroup (MulAut V)) [Fintype ↥E]
    [Fintype ↥H] (hoddH : Odd (Fintype.card ↥H)) {w : V} (hw : w ∈ hypPart E H) :
    normK H w = w :=
  normK_of_mem_fixV' H hoddH hV hw.1

theorem normK_hypPart_other (hV : ∀ v : V, v ^ 2 = 1) (E H H' : Subgroup (MulAut V))
    [Fintype ↥E] [Fintype ↥H] (hoddE : Odd (Fintype.card ↥E)) (hoddH : Odd (Fintype.card ↥H))
    (hHE : H ≤ E) (hdec : ∀ e ∈ E, ∃ h ∈ H, ∃ h' ∈ H', e = h * h') {w : V}
    (hw : w ∈ hypPart E H') : normK H w = 1 := by
  rw [normK_eq_of_fixV hV E H H' hoddE hoddH hHE hdec hw.1]
  exact hw.2

section Cycle

@[expose] def cycProd (y : MulAut V) (r : ℕ) (B : Subgroup V) : (Fin r → ↥B) →* V where
  toFun a := ∏ i : Fin r, (y ^ (i : ℕ)) (a i : V)
  map_one' := by simp
  map_mul' a b := by
    simp only [Pi.mul_apply, Subgroup.coe_mul, map_mul]
    exact Finset.prod_mul_distrib

theorem cycProd_apply (y : MulAut V) (r : ℕ) (B : Subgroup V) (a : Fin r → ↥B) :
    cycProd y r B a = ∏ i : Fin r, (y ^ (i : ℕ)) (a i : V) := rfl

theorem apply_cycProd (y : MulAut V) (n : ℕ) (hy : y ^ (n + 1) = 1) (B : Subgroup V)
    (a : Fin (n + 1) → ↥B) :
    y (cycProd y (n + 1) B a) = cycProd y (n + 1) B (a ∘ (finRotate (n + 1)).symm) := by
  rw [cycProd_apply, cycProd_apply, map_prod]
  refine (Fintype.prod_equiv (finRotate (n + 1)) _ _ fun i => ?_)
  show y ((y ^ (i : ℕ)) (a i : V)) = (y ^ ((finRotate (n + 1) i : Fin (n + 1)) : ℕ))
    ((a ∘ (finRotate (n + 1)).symm) (finRotate (n + 1) i) : V)
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  have h1 : y ^ ((finRotate (n + 1) i : Fin (n + 1)) : ℕ) = y ^ ((i : ℕ) + 1) := by
    rw [coe_finRotate]
    split_ifs with h
    · have : (i : ℕ) + 1 = n + 1 := by rw [h]; simp
      rw [this, hy, pow_zero]
    · rfl
  rw [h1, pow_succ']
  rfl

theorem eq_const_of_apply_eq (y : MulAut V) (n : ℕ) (hy : y ^ (n + 1) = 1) (B : Subgroup V)
    (hinj : Function.Injective (cycProd y (n + 1) B)) (a : Fin (n + 1) → ↥B)
    (ha : y (cycProd y (n + 1) B a) = cycProd y (n + 1) B a) : ∀ i, a i = a 0 := by
  rw [apply_cycProd y n hy B a] at ha
  have h1 : a ∘ (finRotate (n + 1)).symm = a := hinj ha
  have h2 : ∀ j, a (finRotate (n + 1) j) = a j := fun j => by
    have := congrFun h1 (finRotate (n + 1) j)
    simpa using this.symm
  have h3 : ∀ k : ℕ, ∀ hk : k < n + 1, a ⟨k, hk⟩ = a 0 := by
    intro k
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      have hk' : k < n + 1 := by omega
      have := h2 ⟨k, hk'⟩
      rw [finRotate_of_lt (by omega)] at this
      rw [show (⟨k + 1, hk⟩ : Fin (n + 1)) = ⟨(⟨k, hk'⟩ : Fin (n + 1)).val + 1, by simpa using hk⟩
        from rfl, this]
      exact ih hk'
  intro i
  exact h3 i.1 i.2

theorem card_pow_le_card_commV [Finite V] (y : MulAut V) (n : ℕ) (hy : y ^ (n + 1) = 1)
    (B : Subgroup V) (hinj : Function.Injective (cycProd y (n + 1) B)) :
    Nat.card B ^ n ≤ Nat.card (commV (Subgroup.zpowers y)) := by
  classical
  let D : V →* V :=
    { toFun := fun v => y v * v⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  let F : (Fin (n + 1) → ↥B) →* V := D.comp (cycProd y (n + 1) B)
  have hker : Nat.card F.ker ≤ Nat.card B := by
    refine Nat.card_le_card_of_injective (fun a : ↥F.ker => (a.1 0 : ↥B)) ?_
    intro a b hab
    have hconst : ∀ c : ↥F.ker, ∀ i, c.1 i = c.1 0 := fun c => by
      apply eq_const_of_apply_eq y n hy B hinj c.1
      have : D (cycProd y (n + 1) B c.1) = 1 := c.2
      exact mul_inv_eq_one.mp this
    apply Subtype.ext
    funext i
    rw [hconst a i, hconst b i]
    exact hab
  have hrange : F.range ≤ commV (Subgroup.zpowers y) := by
    rintro _ ⟨a, rfl⟩
    exact Subgroup.subset_closure ⟨y, Subgroup.mem_zpowers y, cycProd y (n + 1) B a, rfl⟩
  have h1 := Subgroup.card_ker_mul_card_range F
  have h2 : Nat.card (Fin (n + 1) → ↥B) = Nat.card B ^ (n + 1) := by
    rw [Nat.card_pi]
    simp
  have hpos : 0 < Nat.card B := Nat.card_pos
  have h3 : Nat.card B * Nat.card B ^ n ≤ Nat.card B * Nat.card F.range := by
    calc Nat.card B * Nat.card B ^ n = Nat.card B ^ (n + 1) := by ring
      _ = Nat.card F.ker * Nat.card F.range := by rw [← h2, h1]
      _ ≤ Nat.card B * Nat.card F.range := Nat.mul_le_mul_right _ hker
  exact (Nat.le_of_mul_le_mul_left h3 hpos).trans (Subgroup.card_le_of_le hrange)

end Cycle

section Conj

@[expose] def hypConj (g : MulAut V) (H : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  H.map (MulAut.conj g).toMonoidHom

theorem mem_hypConj {g : MulAut V} {H : Subgroup (MulAut V)} {k : MulAut V} :
    k ∈ hypConj g H ↔ ∃ h ∈ H, k = g * h * g⁻¹ := by
  unfold hypConj
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩

theorem normK_apply_of_mem_normalizer (E : Subgroup (MulAut V)) [Fintype ↥E] {g : MulAut V}
    (hg : g ∈ Subgroup.normalizer (E : Set (MulAut V))) (v : V) :
    normK E (g v) = g (normK E v) := by
  have h1 : ∀ e : ↥E, g⁻¹ * (e : MulAut V) * g ∈ E := fun e => by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) (e : MulAut V)).mp e.2
    simpa using this
  have h2 : ∀ e : ↥E, g * (e : MulAut V) * g⁻¹ ∈ E := fun e =>
    (Subgroup.mem_normalizer_iff.mp hg (e : MulAut V)).mp e.2
  let σ : ↥E ≃ ↥E :=
    { toFun := fun e => ⟨g⁻¹ * (e : MulAut V) * g, h1 e⟩
      invFun := fun e => ⟨g * (e : MulAut V) * g⁻¹, h2 e⟩
      left_inv := fun e => by ext; simp [mul_assoc]
      right_inv := fun e => by ext; simp [mul_assoc] }
  rw [normK_apply, normK_apply, map_prod]
  refine Fintype.prod_equiv σ _ _ fun e => ?_
  show (e : MulAut V) (g v) = g ((g⁻¹ * (e : MulAut V) * g) v)
  simp [MulAut.mul_apply]

theorem hypConj_le {E H : Subgroup (MulAut V)} (hHE : H ≤ E) {g : MulAut V}
    (hg : g ∈ Subgroup.normalizer (E : Set (MulAut V))) : hypConj g H ≤ E := by
  intro k hk
  obtain ⟨h, hh, rfl⟩ := mem_hypConj.mp hk
  exact (Subgroup.mem_normalizer_iff.mp hg h).mp (hHE hh)

theorem card_hypConj (g : MulAut V) (H : Subgroup (MulAut V)) :
    Nat.card (hypConj g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem cycProd_injective [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (E H : Subgroup (MulAut V))
    [Fintype ↥E] (hoddE : Odd (Fintype.card ↥E)) (hoddH : Odd (Nat.card ↥H)) (hHE : H ≤ E)
    {y : MulAut V} (hyE : y ∈ Subgroup.normalizer (E : Set (MulAut V))) (n : ℕ)
    (hdec : ∀ i j : Fin (n + 1), i ≠ j → ∀ e ∈ E, ∃ k ∈ hypConj (y ^ (i : ℕ)) H,
      ∃ k' ∈ hypConj (y ^ (j : ℕ)) H, e = k * k') :
    Function.Injective (cycProd y (n + 1) (hypPart E H)) := by
  classical
  rw [injective_iff_map_eq_one]
  intro a ha
  have hx : ∀ i : Fin (n + 1), (y ^ (i : ℕ)) (a i : V) ∈ hypPart E (hypConj (y ^ (i : ℕ)) H) := by
    intro i
    have hai := (a i).2
    refine ⟨fun k hk => ?_, ?_⟩
    · obtain ⟨h, hh, rfl⟩ := mem_hypConj.mp hk
      show (y ^ (i : ℕ) * h * (y ^ (i : ℕ))⁻¹) ((y ^ (i : ℕ)) (a i : V)) = (y ^ (i : ℕ)) (a i : V)
      simp only [MulAut.mul_apply, MulAut.inv_apply_self]
      rw [hai.1 h hh]
    · show normK E ((y ^ (i : ℕ)) (a i : V)) = 1
      rw [normK_apply_of_mem_normalizer E (pow_mem hyE (i : ℕ))]
      rw [show normK E (a i : V) = 1 from hai.2, map_one]
  have hKodd : ∀ i : Fin (n + 1), Odd (Nat.card ↥(hypConj (y ^ (i : ℕ)) H)) := fun i => by
    rw [card_hypConj]; exact hoddH
  funext j
  have : Fintype ↥(hypConj (y ^ (j : ℕ)) H) := Fintype.ofFinite _
  have hKjodd : Odd (Fintype.card ↥(hypConj (y ^ (j : ℕ)) H)) := by
    rw [← Nat.card_eq_fintype_card]; exact hKodd j
  have hKjE : hypConj (y ^ (j : ℕ)) H ≤ E := hypConj_le hHE (pow_mem hyE (j : ℕ))
  have hj := congrArg (normK (hypConj (y ^ (j : ℕ)) H)) ha
  rw [cycProd_apply, map_prod, map_one, Finset.prod_eq_single j] at hj
  · rw [normK_hypPart_self hV E _ hKjodd (hx j)] at hj
    have : (a j : V) = 1 := (MulEquiv.map_eq_one_iff (y ^ (j : ℕ))).mp hj
    exact Subtype.ext this
  · intro i _ hij
    exact normK_hypPart_other hV E _ _ hoddE hKjodd hKjE (hdec j i (Ne.symm hij)) (hx i)
  · intro hj'
    exact absurd (Finset.mem_univ j) hj'

end Conj

section Distinct

theorem mem_hypConj' {g : MulAut V} {H : Subgroup (MulAut V)} {k : MulAut V} :
    k ∈ hypConj g H ↔ g⁻¹ * k * g ∈ H := by
  rw [mem_hypConj]
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [mul_assoc] using hh
  · intro h
    exact ⟨g⁻¹ * k * g, h, by simp [mul_assoc]⟩

theorem hypConj_mul (g g' : MulAut V) (H : Subgroup (MulAut V)) :
    hypConj (g * g') H = hypConj g (hypConj g' H) := by
  ext k
  simp only [mem_hypConj', mul_inv_rev, mul_assoc]

theorem hypConj_one (H : Subgroup (MulAut V)) : hypConj 1 H = H := by
  ext k
  simp [mem_hypConj']

theorem hypConj_pow_eq {g : MulAut V} {H : Subgroup (MulAut V)} (h : hypConj g H = H) (m : ℕ) :
    hypConj (g ^ m) H = H := by
  induction m with
  | zero => rw [pow_zero, hypConj_one]
  | succ m ih => rw [pow_succ, hypConj_mul, h, ih]

theorem hypConj_inv_mul_eq {a b : MulAut V} {H : Subgroup (MulAut V)}
    (h : hypConj a H = hypConj b H) : hypConj (a⁻¹ * b) H = H := by
  rw [hypConj_mul, ← h, ← hypConj_mul, inv_mul_cancel, hypConj_one]

theorem hypConj_pow_ne {y : MulAut V} {r : ℕ} (hr : r.Prime) (hy : y ^ r = 1)
    {H : Subgroup (MulAut V)} (hne : hypConj y H ≠ H) {i j : ℕ} (hj : j < r) (hij : i < j) :
    hypConj (y ^ i) H ≠ hypConj (y ^ j) H := by
  intro h
  have h1 : hypConj ((y ^ i)⁻¹ * y ^ j) H = H := hypConj_inv_mul_eq h
  have h2 : (y ^ i)⁻¹ * y ^ j = y ^ (j - i) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add]
    congr 1
    omega
  rw [h2] at h1
  have hcop : Nat.Coprime (j - i) r :=
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hr).mpr (fun hd =>
      absurd (Nat.le_of_dvd (by omega) hd) (by omega))))
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr.one_lt
  have h3 : (y ^ (j - i)) ^ m = y := by
    rw [← pow_mul, ← Nat.div_add_mod ((j - i) * m) r, hm, pow_add, pow_mul, hy, one_pow, one_mul,
      pow_one]
  exact hne (by rw [← h3]; exact hypConj_pow_eq h1 m)

end Distinct

section Product

theorem exists_mul_of_ne_of_card [Finite V] {E K K' : Subgroup (MulAut V)} (hK : K ≤ E)
    (hK' : K' ≤ E) (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {p : ℕ} (hp : p.Prime)
    (hKc : Nat.card ↥E = p * Nat.card ↥K) (hK'c : Nat.card ↥E = p * Nat.card ↥K')
    (hne : K ≠ K') : ∀ e ∈ E, ∃ k ∈ K, ∃ k' ∈ K', e = k * k' := by
  let L : Subgroup (MulAut V) :=
    { carrier := {x | ∃ k ∈ K, ∃ k' ∈ K', x = k * k'}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, a', ha', rfl⟩ ⟨b, hb, b', hb', rfl⟩
        refine ⟨a * b, mul_mem ha hb, a' * b', mul_mem ha' hb', ?_⟩
        have : a' * b = b * a' := hcomm _ (hK' ha') _ (hK hb)
        calc a * a' * (b * b') = a * (a' * b) * b' := by group
          _ = a * (b * a') * b' := by rw [this]
          _ = a * b * (a' * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, a', ha', rfl⟩
        refine ⟨a⁻¹, inv_mem ha, a'⁻¹, inv_mem ha', ?_⟩
        have : a' * a = a * a' := hcomm _ (hK' ha') _ (hK ha)
        calc (a * a')⁻¹ = a'⁻¹ * a⁻¹ := by group
          _ = a⁻¹ * a'⁻¹ := by
            rw [← mul_inv_rev, ← mul_inv_rev, this]
            }
  have hKL : K ≤ L := fun k hk => ⟨k, hk, 1, one_mem _, by simp⟩
  have hK'L : K' ≤ L := fun k hk => ⟨1, one_mem _, k, hk, by simp⟩
  have hLE : L ≤ E := by
    rintro _ ⟨a, ha, a', ha', rfl⟩
    exact mul_mem (hK ha) (hK' ha')
  have hpos : 0 < Nat.card ↥K := Nat.card_pos
  obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le hKL
  have hdvd : Nat.card ↥K * t ∣ Nat.card ↥K * p := by
    rw [← ht, mul_comm (Nat.card ↥K) p, ← hKc]
    exact Subgroup.card_dvd_of_le hLE
  have ht' : t ∣ p := Nat.dvd_of_mul_dvd_mul_left hpos hdvd
  rcases (Nat.dvd_prime hp).mp ht' with rfl | rfl
  · exfalso
    have hLK : L = K := (Subgroup.eq_of_le_of_card_ge hKL (by rw [ht, mul_one])).symm
    have hKK' : Nat.card ↥K' = Nat.card ↥K := by
      have := hKc.symm.trans hK'c
      exact (Nat.eq_of_mul_eq_mul_left hp.pos this).symm
    have : K' = K := by
      refine Subgroup.eq_of_le_of_card_ge (hLK ▸ hK'L) ?_
      rw [hKK']
    exact hne this.symm
  · have hLE' : L = E := by
      refine Subgroup.eq_of_le_of_card_ge hLE ?_
      rw [ht, mul_comm, hKc]
    intro e he
    rw [← hLE'] at he
    exact he

end Product

section Orbit

theorem card_hypPart_pow_le [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (E H : Subgroup (MulAut V))
    [Fintype ↥E] (hoddE : Odd (Fintype.card ↥E)) (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hHE : H ≤ E) {p : ℕ} (hp : p.Prime) (hHc : Nat.card ↥E = p * Nat.card ↥H)
    (hoddH : Odd (Nat.card ↥H)) {y : MulAut V}
    (hyE : y ∈ Subgroup.normalizer (E : Set (MulAut V))) {r : ℕ} (hr : r.Prime) (hy : y ^ r = 1)
    (hne : hypConj y H ≠ H) :
    Nat.card (hypPart E H) ^ (r - 1) ≤ Nat.card (commV (Subgroup.zpowers y)) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by have := hr.one_lt; omega⟩
  have hdec : ∀ i j : Fin (n + 1), i ≠ j → ∀ e ∈ E, ∃ k ∈ hypConj (y ^ (i : ℕ)) H,
      ∃ k' ∈ hypConj (y ^ (j : ℕ)) H, e = k * k' := by
    intro i j hij
    have hne' : hypConj (y ^ (i : ℕ)) H ≠ hypConj (y ^ (j : ℕ)) H := by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
      · exact hypConj_pow_ne hr hy hne j.2 h
      · exact (hypConj_pow_ne hr hy hne i.2 h).symm
    refine exists_mul_of_ne_of_card (hypConj_le hHE (pow_mem hyE _))
      (hypConj_le hHE (pow_mem hyE _)) hcomm hp ?_ ?_ hne'
    · rw [card_hypConj]; exact hHc
    · rw [card_hypConj]; exact hHc
  have hinj := cycProd_injective hV E H hoddE hoddH hHE hyE n hdec
  exact card_pow_le_card_commV y n hy (hypPart E H) hinj

end Orbit

end CFSG.CGT.PushingUpLit.CGT6
