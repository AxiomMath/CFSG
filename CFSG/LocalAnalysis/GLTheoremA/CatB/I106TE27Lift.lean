module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.E27

open CFSG.Open Subgroup

@[expose] def prod3 {M : Type*} [Monoid M] (a₀ a₁ a₂ : M) (v : Fin 3 × Fin 3 × Fin 3) : M :=
  a₀ ^ (v.1 : ℕ) * a₁ ^ (v.2.1 : ℕ) * a₂ ^ (v.2.2 : ℕ)

theorem map_prod3 {M N F : Type*} [Monoid M] [Monoid N] [FunLike F M N] [MonoidHomClass F M N]
    (f : F) (a₀ a₁ a₂ : M) (v : Fin 3 × Fin 3 × Fin 3) :
    f (prod3 a₀ a₁ a₂ v) = prod3 (f a₀) (f a₁) (f a₂) v := by
  simp [prod3, map_mul, map_pow]

theorem prod3_zero {M : Type*} [Monoid M] (a₀ a₁ a₂ : M) : prod3 a₀ a₁ a₂ 0 = 1 := by
  simp [prod3]

section Commuting

variable {M : Type*} [Monoid M] {a₀ a₁ a₂ : M}

theorem pow_mul_pow_mul_pow (h01 : Commute a₀ a₁) (h02 : Commute a₀ a₂) (h12 : Commute a₁ a₂)
    (i j k i' j' k' : ℕ) :
    a₀ ^ i * a₁ ^ j * a₂ ^ k * (a₀ ^ i' * a₁ ^ j' * a₂ ^ k') =
      a₀ ^ (i + i') * a₁ ^ (j + j') * a₂ ^ (k + k') := by
  have c1 : Commute (a₁ ^ j * a₂ ^ k) (a₀ ^ i') :=
    (h01.pow_pow i' j).symm.mul_left (h02.pow_pow i' k).symm
  have c2 : Commute (a₂ ^ k) (a₁ ^ j') := (h12.pow_pow j' k).symm
  calc a₀ ^ i * a₁ ^ j * a₂ ^ k * (a₀ ^ i' * a₁ ^ j' * a₂ ^ k')
      = a₀ ^ i * ((a₁ ^ j * a₂ ^ k) * a₀ ^ i') * a₁ ^ j' * a₂ ^ k' := by
        simp only [mul_assoc]
    _ = a₀ ^ i * (a₀ ^ i' * (a₁ ^ j * a₂ ^ k)) * a₁ ^ j' * a₂ ^ k' := by rw [c1.eq]
    _ = a₀ ^ (i + i') * a₁ ^ j * (a₂ ^ k * a₁ ^ j') * a₂ ^ k' := by
        rw [pow_add]; simp only [mul_assoc]
    _ = a₀ ^ (i + i') * a₁ ^ j * (a₁ ^ j' * a₂ ^ k) * a₂ ^ k' := by rw [c2.eq]
    _ = a₀ ^ (i + i') * a₁ ^ (j + j') * a₂ ^ (k + k') := by
        simp only [pow_add, mul_assoc]

theorem prod3_mul_prod3 (h01 : Commute a₀ a₁) (h02 : Commute a₀ a₂) (h12 : Commute a₁ a₂)
    (h0 : a₀ ^ 3 = 1) (h1 : a₁ ^ 3 = 1) (h2 : a₂ ^ 3 = 1) (v w : Fin 3 × Fin 3 × Fin 3) :
    prod3 a₀ a₁ a₂ v * prod3 a₀ a₁ a₂ w = prod3 a₀ a₁ a₂ (v + w) := by
  simp only [prod3, Prod.fst_add, Prod.snd_add, Fin.val_add]
  rw [← pow_eq_pow_mod _ h0, ← pow_eq_pow_mod _ h1, ← pow_eq_pow_mod _ h2]
  exact pow_mul_pow_mul_pow h01 h02 h12 _ _ _ _ _ _

end Commuting

section Kernel

variable {H G : Type*} [Group H] [Group G]

@[expose] def LiftComm (f : H →* G) (x y : G) : Prop :=
  ∀ a b : H, f a = x → f b = y → Commute a b

variable {f : H →* G}

theorem LiftComm.symm {x y : G} (h : LiftComm f x y) : LiftComm f y x :=
  fun a b ha hb => (h b a hb ha).symm

theorem conj_eq_of_mem_center {z : H} (hz : z ∈ center H) (g : H) : z * g * z⁻¹ = g := by
  rw [← mem_center_iff.mp hz g]
  group

theorem conj_central_eq {z : H} (hz : z ∈ center H) (g : H) : g * z * g⁻¹ = z := by
  rw [mem_center_iff.mp hz g]
  group

theorem commute_of_commutator_eq_one {a b : H} (h : a * b * a⁻¹ * b⁻¹ = 1) : Commute a b := by
  show a * b = b * a
  have : a * b * (b * a)⁻¹ = 1 := by rw [← h]; group
  exact mul_inv_eq_one.mp this

theorem commutator_eq_of_lift (hc : ∀ z, f z = 1 → z ∈ center H) {a a' b b' : H}
    (ha : f a' = f a) (hb : f b' = f b) :
    a' * b' * a'⁻¹ * b'⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  obtain ⟨z₁, hz₁, rfl⟩ : ∃ z ∈ center H, a' = a * z :=
    ⟨a⁻¹ * a', hc _ (by simp [ha]), by group⟩
  obtain ⟨z₂, hz₂, rfl⟩ : ∃ z ∈ center H, b' = b * z :=
    ⟨b⁻¹ * b', hc _ (by simp [hb]), by group⟩
  calc a * z₁ * (b * z₂) * (a * z₁)⁻¹ * (b * z₂)⁻¹
      = a * z₁ * b * (z₂ * (z₁⁻¹ * a⁻¹) * z₂⁻¹) * b⁻¹ := by group
    _ = a * (z₁ * b * z₁⁻¹) * a⁻¹ * b⁻¹ := by rw [conj_eq_of_mem_center hz₂]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [conj_eq_of_mem_center hz₁]

theorem commutator_mem_center (hc : ∀ z, f z = 1 → z ∈ center H) {a b : H}
    (hab : f a * f b = f b * f a) : a * b * a⁻¹ * b⁻¹ ∈ center H :=
  hc _ (by simp only [map_mul, map_inv]; rw [hab]; group)

theorem liftComm_of_commute (hc : ∀ z, f z = 1 → z ∈ center H) {a b : H} (h : Commute a b) :
    LiftComm f (f a) (f b) := by
  intro a' b' ha' hb'
  apply commute_of_commutator_eq_one
  rw [commutator_eq_of_lift hc ha' hb']
  have : a * b = b * a := h
  rw [this]
  group

theorem eq_one_of_sq_eq_one (h3 : ∀ z, f z = 1 → ∃ n : ℕ, z ^ 3 ^ n = 1) {z : H}
    (hz : f z = 1) (h2 : z ^ 2 = 1) : z = 1 := by
  obtain ⟨n, hn⟩ := h3 z hz
  have hcop : Nat.Coprime 2 (3 ^ n) := Nat.Coprime.pow_right n (by norm_num)
  have hd : orderOf z ∣ Nat.gcd 2 (3 ^ n) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hn)
  rw [hcop.gcd_eq_one, Nat.dvd_one] at hd
  exact orderOf_eq_one_iff.mp hd

theorem commute_of_commutator_eq_inv (h3 : ∀ z, f z = 1 → ∃ n : ℕ, z ^ 3 ^ n = 1) {a b : H}
    (hab : f a * f b = f b * f a) (h : a * b * a⁻¹ * b⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹) :
    Commute a b := by
  apply commute_of_commutator_eq_one
  refine eq_one_of_sq_eq_one h3 ?_ ?_
  · simp only [map_mul, map_inv]; rw [hab]; group
  · calc (a * b * a⁻¹ * b⁻¹) ^ 2 = (a * b * a⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹) := sq _
      _ = (a * b * a⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹)⁻¹ :=
        congrArg (fun t => (a * b * a⁻¹ * b⁻¹) * t) h
      _ = 1 := mul_inv_cancel _

theorem liftComm_of_inv_fix (hsurj : Function.Surjective f)
    (hc : ∀ z, f z = 1 → z ∈ center H) (h3 : ∀ z, f z = 1 → ∃ n : ℕ, z ^ 3 ^ n = 1)
    {x y n : G} (hxy : x * y = y * x) (hnx : n * x * n⁻¹ = x⁻¹) (hny : n * y * n⁻¹ = y) :
    LiftComm f x y := by
  intro a b ha hb
  obtain ⟨m, rfl⟩ := hsurj n
  subst ha hb
  have hcz : a * b * a⁻¹ * b⁻¹ ∈ center H := commutator_mem_center hc hxy
  refine commute_of_commutator_eq_inv h3 hxy ?_
  calc a * b * a⁻¹ * b⁻¹ = m * (a * b * a⁻¹ * b⁻¹) * m⁻¹ := (conj_central_eq hcz m).symm
    _ = (m * a * m⁻¹) * (m * b * m⁻¹) * (m * a * m⁻¹)⁻¹ * (m * b * m⁻¹)⁻¹ := by group
    _ = a⁻¹ * b * a⁻¹⁻¹ * b⁻¹ := commutator_eq_of_lift hc (by simp [hnx]) (by simp [hny])
    _ = a⁻¹ * (a * b * a⁻¹ * b⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    _ = (a * b * a⁻¹ * b⁻¹)⁻¹ := conj_central_eq (Subgroup.inv_mem _ hcz) a⁻¹

theorem liftComm_of_cycle₂ (hsurj : Function.Surjective f)
    (hc : ∀ z, f z = 1 → z ∈ center H) (h3 : ∀ z, f z = 1 → ∃ n : ℕ, z ^ 3 ^ n = 1)
    {x y s : G} (hxy : x * y = y * x) (hsx : s * x * s⁻¹ = y) (hsy : s * y * s⁻¹ = x * y) :
    LiftComm f x y := by
  intro a b ha hb
  obtain ⟨m, rfl⟩ := hsurj s
  subst ha hb
  have hcz : a * b * a⁻¹ * b⁻¹ ∈ center H := commutator_mem_center hc hxy
  refine commute_of_commutator_eq_inv h3 hxy ?_
  calc a * b * a⁻¹ * b⁻¹ = m * (a * b * a⁻¹ * b⁻¹) * m⁻¹ := (conj_central_eq hcz m).symm
    _ = (m * a * m⁻¹) * (m * b * m⁻¹) * (m * a * m⁻¹)⁻¹ * (m * b * m⁻¹)⁻¹ := by group
    _ = b * (a * b) * b⁻¹ * (a * b)⁻¹ := commutator_eq_of_lift hc (by simp [hsx]) (by simp [hsy])
    _ = (a * b * a⁻¹ * b⁻¹)⁻¹ := by group

theorem liftComm_of_cycle₃ (hsurj : Function.Surjective f)
    (hc : ∀ z, f z = 1 → z ∈ center H) {x y w n : G} (hxy : x * y = y * x)
    (hxw : x * w = w * x) (hyw : y * w = w * y) (hnx : n * x * n⁻¹ = y)
    (hny : n * y * n⁻¹ = w) (hnw : n * w * n⁻¹ = x * y) :
    LiftComm f x y ∧ LiftComm f x w ∧ LiftComm f y w := by
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨b, rfl⟩ := hsurj y
  obtain ⟨d, rfl⟩ := hsurj w
  obtain ⟨m, rfl⟩ := hsurj n
  have zab := commutator_mem_center hc hxy
  have zad := commutator_mem_center hc hxw
  have zbd := commutator_mem_center hc hyw
  have e1 : a * b * a⁻¹ * b⁻¹ = b * d * b⁻¹ * d⁻¹ := by
    calc a * b * a⁻¹ * b⁻¹ = m * (a * b * a⁻¹ * b⁻¹) * m⁻¹ := (conj_central_eq zab m).symm
      _ = (m * a * m⁻¹) * (m * b * m⁻¹) * (m * a * m⁻¹)⁻¹ * (m * b * m⁻¹)⁻¹ := by group
      _ = b * d * b⁻¹ * d⁻¹ := commutator_eq_of_lift hc (by simp [hnx]) (by simp [hny])
  have e2 : a * d * a⁻¹ * d⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ := by
    calc a * d * a⁻¹ * d⁻¹ = m * (a * d * a⁻¹ * d⁻¹) * m⁻¹ := (conj_central_eq zad m).symm
      _ = (m * a * m⁻¹) * (m * d * m⁻¹) * (m * a * m⁻¹)⁻¹ * (m * d * m⁻¹)⁻¹ := by group
      _ = b * (a * b) * b⁻¹ * (a * b)⁻¹ :=
        commutator_eq_of_lift hc (by simp [hnx]) (by simp [hnw])
      _ = (a * b * a⁻¹ * b⁻¹)⁻¹ := by group
  have e3 : b * d * b⁻¹ * d⁻¹ = (a * d * a⁻¹ * d⁻¹)⁻¹ * (b * d * b⁻¹ * d⁻¹)⁻¹ := by
    calc b * d * b⁻¹ * d⁻¹ = m * (b * d * b⁻¹ * d⁻¹) * m⁻¹ := (conj_central_eq zbd m).symm
      _ = (m * b * m⁻¹) * (m * d * m⁻¹) * (m * b * m⁻¹)⁻¹ * (m * d * m⁻¹)⁻¹ := by group
      _ = d * (a * b) * d⁻¹ * (a * b)⁻¹ :=
        commutator_eq_of_lift hc (by simp [hny]) (by simp [hnw])
      _ = (a * d * a⁻¹ * d⁻¹)⁻¹ * (a * (b * d * b⁻¹ * d⁻¹)⁻¹ * a⁻¹) := by group
      _ = (a * d * a⁻¹ * d⁻¹)⁻¹ * (b * d * b⁻¹ * d⁻¹)⁻¹ := by
        rw [conj_central_eq (Subgroup.inv_mem _ zbd) a]
  have hab : a * b * a⁻¹ * b⁻¹ = 1 := by
    have h := e3
    rw [e2, ← e1, inv_inv, mul_inv_cancel] at h
    exact h
  have hbd : b * d * b⁻¹ * d⁻¹ = 1 := by rw [← e1]; exact hab
  have had : a * d * a⁻¹ * d⁻¹ = 1 := by rw [e2, hab, inv_one]
  exact ⟨liftComm_of_commute hc (commute_of_commutator_eq_one hab),
    liftComm_of_commute hc (commute_of_commutator_eq_one had),
    liftComm_of_commute hc (commute_of_commutator_eq_one hbd)⟩

theorem exists_lift_pow_three (hsurj : Function.Surjective f)
    (hc : ∀ z, f z = 1 → z ∈ center H) (h3 : ∀ z, f z = 1 → ∃ n : ℕ, z ^ 3 ^ n = 1)
    {x n : G} (hx : x ^ 3 = 1) (hn : n * x * n⁻¹ = x⁻¹) : ∃ a : H, f a = x ∧ a ^ 3 = 1 := by
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨m, rfl⟩ := hsurj n
  have hfz : f (m * a * m⁻¹ * a) = 1 := by
    simp only [map_mul, map_inv]
    rw [hn]
    group
  have hzc : m * a * m⁻¹ * a ∈ center H := hc _ hfz
  obtain ⟨k, hk⟩ := h3 _ hfz
  obtain ⟨j, hj⟩ : ∃ j, 3 ^ k = 2 * j + 1 := (Odd.pow (by decide : Odd 3) : Odd (3 ^ k))
  set z := m * a * m⁻¹ * a with hzdef
  set w := z ^ j with hwdef
  clear_value w z
  have hwc : w ∈ center H := by rw [hwdef]; exact Subgroup.pow_mem _ hzc j
  have hfw : f w = 1 := by rw [hwdef, map_pow, hfz, one_pow]
  have hzw : z * w = w⁻¹ := by
    refine mul_eq_one_iff_eq_inv.mp ?_
    calc z * w * w = z ^ (2 * j + 1) := by rw [hwdef]; group
      _ = 1 := by rw [← hj, hk]
  have hconj : m * (a * w) * m⁻¹ = (a * w)⁻¹ := by
    have h1 : m * (a * w) * m⁻¹ = (m * a * m⁻¹) * (m * w * m⁻¹) := by group
    have h2 : m * a * m⁻¹ = z * a⁻¹ := by rw [hzdef]; group
    have h4 : a⁻¹ * w = w * a⁻¹ := mem_center_iff.mp hwc a⁻¹
    calc m * (a * w) * m⁻¹ = z * a⁻¹ * w := by rw [h1, h2, conj_central_eq hwc m]
      _ = z * (w * a⁻¹) := by rw [mul_assoc, h4]
      _ = (z * w) * a⁻¹ := (mul_assoc z w a⁻¹).symm
      _ = (a * w)⁻¹ := by rw [hzw, mul_inv_rev]
  refine ⟨a * w, by rw [map_mul, hfw, mul_one], ?_⟩
  have hfy : f ((a * w) ^ 3) = 1 := by rw [map_pow, map_mul, hfw, mul_one, hx]
  have hyc : (a * w) ^ 3 ∈ center H := hc _ hfy
  have hyy : (a * w) ^ 3 = ((a * w) ^ 3)⁻¹ := by
    calc (a * w) ^ 3 = m * (a * w) ^ 3 * m⁻¹ := (conj_central_eq hyc m).symm
      _ = (m * (a * w) * m⁻¹) ^ 3 := conj_pow.symm
      _ = ((a * w) ^ 3)⁻¹ := by rw [hconj, inv_pow]
  refine eq_one_of_sq_eq_one h3 hfy ?_
  calc ((a * w) ^ 3) ^ 2 = (a * w) ^ 3 * (a * w) ^ 3 := sq _
    _ = (a * w) ^ 3 * ((a * w) ^ 3)⁻¹ := congrArg (fun t => (a * w) ^ 3 * t) hyy
    _ = 1 := mul_inv_cancel _

theorem exists_e27_of_lifts {a₀ a₁ a₂ : H} (h01 : Commute a₀ a₁) (h02 : Commute a₀ a₂)
    (h12 : Commute a₁ a₂) (h0 : a₀ ^ 3 = 1) (h1 : a₁ ^ 3 = 1) (h2 : a₂ ^ 3 = 1)
    (hinj : Function.Injective (prod3 (f a₀) (f a₁) (f a₂))) :
    ∃ E : Subgroup H, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧ ∀ z ∈ E, f z = 1 → z = 1 := by
  have hm := prod3_mul_prod3 h01 h02 h12 h0 h1 h2
  have hinv : ∀ v, (prod3 a₀ a₁ a₂ v)⁻¹ = prod3 a₀ a₁ a₂ (v + v) := by
    intro v
    rw [inv_eq_iff_mul_eq_one, hm]
    have hv : v + (v + v) = 0 := by revert v; decide
    rw [hv, prod3_zero]
  have hinj' : Function.Injective (prod3 a₀ a₁ a₂) := by
    intro v w h
    apply hinj
    simp only [← map_prod3, h]
  let E : Subgroup H :=
    { carrier := Set.range (prod3 a₀ a₁ a₂)
      mul_mem' := by
        rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
        exact ⟨v + w, (hm v w).symm⟩
      one_mem' := ⟨0, prod3_zero _ _ _⟩
      inv_mem' := by
        rintro _ ⟨v, rfl⟩
        exact ⟨v + v, (hinv v).symm⟩ }
  refine ⟨E, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_, ?_⟩
  · rintro ⟨_, v, rfl⟩ ⟨_, w, rfl⟩
    apply Subtype.ext
    show prod3 a₀ a₁ a₂ v * prod3 a₀ a₁ a₂ w = prod3 a₀ a₁ a₂ w * prod3 a₀ a₁ a₂ v
    rw [hm, hm, add_comm]
  · rintro _ ⟨v, rfl⟩
    have hv : v + v + v = 0 := by revert v; decide
    rw [pow_three, ← mul_assoc, hm, hm, hv, prod3_zero]
  · calc Nat.card E = Nat.card (Set.range (prod3 a₀ a₁ a₂)) := rfl
      _ = Nat.card (Fin 3 × Fin 3 × Fin 3) := Nat.card_range_of_injective hinj'
      _ = 3 ^ 3 := by simp
  · rintro _ ⟨v, rfl⟩ hv
    have : v = 0 := hinj (by rw [← map_prod3, hv, ← map_prod3, prod3_zero, map_one])
    rw [this, prod3_zero]

end Kernel

@[expose] def E27Lifts (G : Type*) [Group G] : Prop :=
  ∀ (H : Type) [Group H] (f : H →* G), Function.Surjective f →
    (∀ z, f z = 1 → z ∈ center H) → (∀ z, f z = 1 → ∃ n : ℕ, z ^ 3 ^ n = 1) →
    ∃ E : Subgroup H, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧ ∀ z ∈ E, f z = 1 → z = 1

section Witnesses

variable {G : Type*} [Group G]

theorem e27Lifts_of_liftComm {x₀ x₁ x₂ : G} (h0 : x₀ ^ 3 = 1) (h1 : x₁ ^ 3 = 1)
    (h2 : x₂ ^ 3 = 1) (hinj : Function.Injective (prod3 x₀ x₁ x₂))
    (hi0 : ∃ n, n * x₀ * n⁻¹ = x₀⁻¹) (hi1 : ∃ n, n * x₁ * n⁻¹ = x₁⁻¹)
    (hi2 : ∃ n, n * x₂ * n⁻¹ = x₂⁻¹)
    (hk : ∀ (H : Type) [Group H] (f : H →* G), Function.Surjective f →
      (∀ z, f z = 1 → z ∈ center H) → (∀ z, f z = 1 → ∃ n : ℕ, z ^ 3 ^ n = 1) →
      LiftComm f x₀ x₁ ∧ LiftComm f x₀ x₂ ∧ LiftComm f x₁ x₂) :
    E27Lifts G := by
  intro H _ f hs hc h3
  obtain ⟨k01, k02, k12⟩ := hk H f hs hc h3
  obtain ⟨n₀, hn₀⟩ := hi0
  obtain ⟨n₁, hn₁⟩ := hi1
  obtain ⟨n₂, hn₂⟩ := hi2
  obtain ⟨a₀, ha₀, ha₀3⟩ := exists_lift_pow_three hs hc h3 h0 hn₀
  obtain ⟨a₁, ha₁, ha₁3⟩ := exists_lift_pow_three hs hc h3 h1 hn₁
  obtain ⟨a₂, ha₂, ha₂3⟩ := exists_lift_pow_three hs hc h3 h2 hn₂
  subst ha₀ ha₁ ha₂
  exact exists_e27_of_lifts (k01 _ _ rfl rfl) (k02 _ _ rfl rfl) (k12 _ _ rfl rfl) ha₀3 ha₁3
    ha₂3 hinj

@[expose] def PairKill (x y : G) : Prop :=
  (∃ n, n * x * n⁻¹ = x⁻¹ ∧ n * y * n⁻¹ = y) ∨ (∃ n, n * x * n⁻¹ = x ∧ n * y * n⁻¹ = y⁻¹) ∨
    ∃ n, n * x * n⁻¹ = y ∧ n * y * n⁻¹ = x * y

theorem PairKill.liftComm {H : Type*} [Group H] {f : H →* G} (hsurj : Function.Surjective f)
    (hc : ∀ z, f z = 1 → z ∈ center H) (h3 : ∀ z, f z = 1 → ∃ n : ℕ, z ^ 3 ^ n = 1)
    {x y : G} (hxy : x * y = y * x) (h : PairKill x y) : LiftComm f x y := by
  rcases h with ⟨n, hx, hy⟩ | ⟨n, hx, hy⟩ | ⟨n, hx, hy⟩
  · exact liftComm_of_inv_fix hsurj hc h3 hxy hx hy
  · exact (liftComm_of_inv_fix hsurj hc h3 hxy.symm hy hx).symm
  · exact liftComm_of_cycle₂ hsurj hc h3 hxy hx hy

theorem e27Lifts_of_pairs {x₀ x₁ x₂ : G} (c01 : x₀ * x₁ = x₁ * x₀) (c02 : x₀ * x₂ = x₂ * x₀)
    (c12 : x₁ * x₂ = x₂ * x₁) (h0 : x₀ ^ 3 = 1) (h1 : x₁ ^ 3 = 1) (h2 : x₂ ^ 3 = 1)
    (hinj : Function.Injective (prod3 x₀ x₁ x₂)) (hi0 : ∃ n, n * x₀ * n⁻¹ = x₀⁻¹)
    (hi1 : ∃ n, n * x₁ * n⁻¹ = x₁⁻¹) (hi2 : ∃ n, n * x₂ * n⁻¹ = x₂⁻¹) (k01 : PairKill x₀ x₁)
    (k02 : PairKill x₀ x₂) (k12 : PairKill x₁ x₂) : E27Lifts G :=
  e27Lifts_of_liftComm h0 h1 h2 hinj hi0 hi1 hi2 fun _ _ _ hs hc h3 =>
    ⟨k01.liftComm hs hc h3 c01, k02.liftComm hs hc h3 c02, k12.liftComm hs hc h3 c12⟩

theorem e27Lifts_of_cycle₃ {x₀ x₁ x₂ n : G} (c01 : x₀ * x₁ = x₁ * x₀)
    (c02 : x₀ * x₂ = x₂ * x₀) (c12 : x₁ * x₂ = x₂ * x₁) (h0 : x₀ ^ 3 = 1) (h1 : x₁ ^ 3 = 1)
    (h2 : x₂ ^ 3 = 1) (hinj : Function.Injective (prod3 x₀ x₁ x₂))
    (hi0 : ∃ n, n * x₀ * n⁻¹ = x₀⁻¹) (hi1 : ∃ n, n * x₁ * n⁻¹ = x₁⁻¹)
    (hi2 : ∃ n, n * x₂ * n⁻¹ = x₂⁻¹) (hn0 : n * x₀ * n⁻¹ = x₁) (hn1 : n * x₁ * n⁻¹ = x₂)
    (hn2 : n * x₂ * n⁻¹ = x₀ * x₁) : E27Lifts G :=
  e27Lifts_of_liftComm h0 h1 h2 hinj hi0 hi1 hi2 fun _ _ _ hs hc _ =>
    liftComm_of_cycle₃ hs hc c01 c02 c12 hn0 hn1 hn2

end Witnesses

theorem E27Lifts.of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : E27Lifts G) : E27Lifts G' := by
  intro H _ f hs hc h3
  obtain ⟨E, hE, hcard, hker⟩ := h H (e.symm.toMonoidHom.comp f) (e.symm.surjective.comp hs)
    (fun z hz => hc z (by simpa using hz)) (fun z hz => h3 z (by simpa using hz))
  exact ⟨E, hE, hcard, fun z hz hfz => hker z hz (by simp [hfz])⟩

theorem E27Lifts.exists_of_quotient_center {G : Type*} [Group G] (h : E27Lifts G) {H : Type}
    [Group H] (φ : H ⧸ center H ≃* G) (hZ : ∀ z ∈ center H, ∃ n : ℕ, z ^ 3 ^ n = 1) :
    ∃ E : Subgroup H, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧ E ⊓ center H = ⊥ := by
  let f : H →* G := φ.toMonoidHom.comp (QuotientGroup.mk' (center H))
  have hf : ∀ z, f z = 1 ↔ z ∈ center H := by
    intro z
    simp [f, QuotientGroup.eq_one_iff]
  obtain ⟨E, hE, hcard, hker⟩ := h H f (φ.surjective.comp (QuotientGroup.mk'_surjective _))
    (fun z hz => (hf z).mp hz) (fun z hz => hZ z ((hf z).mp hz))
  refine ⟨E, hE, hcard, ?_⟩
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzE, hzZ⟩ := Subgroup.mem_inf.mp hz
  exact (Subgroup.mem_bot).mpr (hker z hzE ((hf z).mpr hzZ))

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.E27
