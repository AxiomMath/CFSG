module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_RedDefs

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open


theorem mt113_poly_aux {R : Type*} [Ring R] (s β : R) (hc : s*β = β*s) (hs : s^3 = 1)
    (hb : β^2+β+1 = 0) : (s-1)*(s-β)*(s-β^2) = 0 := by
  have hb3 : β^3 = 1 := by
    have : β^3 - 1 = (β-1)*(β^2+β+1) := by noncomm_ring
    rw [hb, mul_zero] at this
    exact sub_eq_zero.mp this
  have hb' : β^2+β = -1 := eq_neg_of_add_eq_zero_left hb
  have e : (s-β)*(s-β^2) = s^2+s+1 := by
    calc (s-β)*(s-β^2) = s*s - s*β^2 - β*s + β*β^2 := by noncomm_ring
      _ = s^2 - s*(β^2+β) + β^3 := by rw [← hc]; noncomm_ring
      _ = s^2+s+1 := by rw [hb', hb3]; noncomm_ring
  rw [mul_assoc, e]
  calc (s-1)*(s^2+s+1) = s^3 - 1 := by noncomm_ring
    _ = 0 := by rw [hs]; simp

theorem mt113_rep_lemma {M : Type*} [AddCommGroup M] {B' : Type*} [Group B']
    (hcomm : ∀ a b : B', a * b = b * a)
    (ρ : B' →* Module.End ℤ M) (h3 : ∀ c : B', c ^ 3 = 1)
    (hfix : ∀ c : B', (∃ x : M, x ≠ 0 ∧ ρ c x = x) → ∀ y, ρ c y = y) :
    (∀ c y, ρ c y = y) ∨ ∃ b : B', (∀ x, ρ b x = x → x = 0) ∧
      ∀ b' : B', ∃ k : ℕ, k < 3 ∧ ∀ y, ρ b' y = ρ (b ^ k) y := by
  by_cases hall : ∀ c y, ρ c y = y
  · exact Or.inl hall
  right
  simp only [not_forall] at hall
  obtain ⟨b, y₀, hy₀⟩ := hall
  have hbfree : ∀ x, ρ b x = x → x = 0 := by
    intro x hx
    by_contra hne
    exact hy₀ (hfix b ⟨x, hne, hx⟩ y₀)
  refine ⟨b, hbfree, fun b' => ?_⟩
  by_contra hcon
  simp only [not_exists, not_and, not_forall] at hcon
  have hkey : ∀ k : ℕ, ∀ x, ρ (b' * (b ^ k)⁻¹) (ρ (b ^ k) x) = ρ b' x := by
    intro k x
    rw [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]
  have hfree : ∀ k : ℕ, k < 3 → ∀ x, ρ (b' * (b ^ k)⁻¹) x = x → x = 0 := by
    intro k hk x hx
    by_contra hne
    obtain ⟨y, hy⟩ := hcon k hk
    have hall' := hfix _ ⟨x, hne, hx⟩
    apply hy
    have := hall' (ρ (b ^ k) y)
    rw [hkey] at this
    exact this
  have hinj : ∀ k : ℕ, k < 3 → ∀ x, (ρ b' - ρ b ^ k) x = 0 → x = 0 := by
    intro k hk x hx
    have hx' : ρ b' x = (ρ b ^ k) x := sub_eq_zero.mp hx
    rw [← map_pow] at hx'
    have hz : ρ (b' * (b ^ k)⁻¹) (ρ (b ^ k) x) = ρ (b ^ k) x := by rw [hkey, hx']
    have h0 := hfree k hk _ hz
    have : x = ρ (b ^ (3 - k)) (ρ (b ^ k) x) := by
      rw [← Module.End.mul_apply, ← map_mul, ← pow_add, Nat.sub_add_cancel (by omega) , h3, map_one]
      rfl
    rw [this, h0, map_zero]
  have hcb : ρ b' * ρ b = ρ b * ρ b' := by rw [← map_mul, ← map_mul, hcomm]
  have hb3 : ρ b ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  have hs3 : ρ b' ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  have hE : ρ b ^ 2 + ρ b + 1 = 0 := by
    have h1 : ρ b * (ρ b ^ 2 + ρ b + 1) = ρ b ^ 2 + ρ b + 1 := by
      calc ρ b * (ρ b ^ 2 + ρ b + 1) = ρ b ^ 3 + ρ b ^ 2 + ρ b := by noncomm_ring
        _ = _ := by rw [hb3]; abel
    ext x
    apply hbfree
    show ρ b (((ρ b ^ 2 + ρ b + 1 : Module.End ℤ M)) x) = ((ρ b ^ 2 + ρ b + 1 : Module.End ℤ M)) x
    rw [← Module.End.mul_apply, h1]
  have hP := mt113_poly_aux (ρ b') (ρ b) hcb hs3 hE
  have hv : ρ b y₀ - y₀ ≠ 0 := sub_ne_zero.mpr hy₀
  have h2 : (ρ b' - ρ b ^ 2) (ρ b y₀ - y₀) ≠ 0 := fun h => hv (hinj 2 (by omega) _ h)
  have h1 : (ρ b' - ρ b ^ 1) ((ρ b' - ρ b ^ 2) (ρ b y₀ - y₀)) ≠ 0 :=
    fun h => h2 (hinj 1 (by omega) _ h)
  have h0 : (ρ b' - ρ b ^ 0) ((ρ b' - ρ b ^ 1) ((ρ b' - ρ b ^ 2) (ρ b y₀ - y₀))) ≠ 0 :=
    fun h => h1 (hinj 0 (by omega) _ h)
  apply h0
  simp only [pow_zero, pow_one]
  have := LinearMap.congr_fun hP (ρ b y₀ - y₀)
  simpa [Module.End.mul_apply] using this


def mt113_toEnd (G : Type*) [CommGroup G] : Monoid.End G →* Module.End ℤ (Additive G) where
  toFun f := AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive f)
  map_one' := by ext x; rfl
  map_mul' f g := by ext x; rfl

theorem mt113_core {G : Type*} [Group G] (hG : ∀ x y : G, x * y = y * x)
    {B' : Type*} [Group B'] (hcomm : ∀ a b : B', a * b = b * a)
    (φ : B' →* Monoid.End G) (h3 : ∀ c : B', c ^ 3 = 1)
    (hfix : ∀ c : B', (∃ x : G, x ≠ 1 ∧ φ c x = x) → ∀ y, φ c y = y) :
    (∀ c y, φ c y = y) ∨ ∃ b : B', (∀ x, φ b x = x → x = 1) ∧
      ∀ b' : B', ∃ k : ℕ, k < 3 ∧ ∀ y, φ b' y = φ (b ^ k) y := by
  let _ : CommGroup G := { ‹Group G› with mul_comm := hG }
  have key := mt113_rep_lemma hcomm ((mt113_toEnd G).comp φ) h3 (by
    intro c ⟨x, hx0, hx⟩ y
    have hx0' : Additive.toMul x ≠ 1 := hx0
    have := hfix c ⟨Additive.toMul x, hx0', by
      have := congrArg Additive.toMul hx
      exact this⟩ (Additive.toMul y)
    exact congrArg Additive.ofMul this)
  rcases key with h | ⟨b, hb, hb'⟩
  · left
    intro c y
    exact Additive.ofMul.injective (h c (Additive.ofMul y))
  · right
    refine ⟨b, fun x hx => ?_, fun b' => ?_⟩
    · exact hb (Additive.ofMul x) (congrArg Additive.ofMul hx)
    · obtain ⟨k, hk, hy⟩ := hb' b'
      exact ⟨k, hk, fun y => Additive.ofMul.injective (hy (Additive.ofMul y))⟩

section QLevel

variable {Q : Type*} [Group Q]

theorem mt113_le_normalizer {B H : Subgroup Q} (h : ∀ b ∈ B, ∀ x ∈ H, b * x * b⁻¹ ∈ H) :
    B ≤ Subgroup.normalizer (H : Set Q) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h g hg x, fun hx => ?_⟩
  have := h g⁻¹ (B.inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem mt113_conj_mem {B H : Subgroup Q} (h : B ≤ Subgroup.normalizer (H : Set Q)) {b : Q}
    (hb : b ∈ B) {x : Q} (hx : x ∈ H) : b * x * b⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.mp (h hb) x).mp hx

theorem mt113_klein (a b : Q) (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    ∃ W : Subgroup Q, (W : Set Q) = {1, a, b, a * b} := by
  have hba : b * a = a * b := hab.symm
  have e1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have e2 : b * (a * b) = a := by rw [hab, ← mul_assoc, hb, one_mul]
  have e3 : a * b * a = b := by rw [hab, mul_assoc, ha, mul_one]
  have e4 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have e5 : a * b * (a * b) = 1 := by rw [← mul_assoc, e3, hb]
  refine ⟨{ carrier := {1, a, b, a * b}
            mul_mem' := ?_
            one_mem' := by simp
            inv_mem' := ?_ }, rfl⟩
  · intro x y hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp [ha, hb, e1, e2, e3, e4, e5, hba]
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right ha))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hb)))
    · exact Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right e5)))

theorem mt113_exists_min [Finite Q] (B S : Subgroup Q) (hS : S ≠ ⊥)
    (hBS : B ≤ Subgroup.normalizer (S : Set Q)) :
    ∃ T : Subgroup Q, T ≤ S ∧ T ≠ ⊥ ∧ B ≤ Subgroup.normalizer (T : Set Q) ∧
      ∀ T' : Subgroup Q, T' ≤ T → B ≤ Subgroup.normalizer (T' : Set Q) → T' = ⊥ ∨ T' = T := by
  obtain ⟨T, ⟨hTS, hTne, hTB⟩, hmin⟩ := (wellFounded_lt (α := Subgroup Q)).has_min
    {T | T ≤ S ∧ T ≠ ⊥ ∧ B ≤ Subgroup.normalizer (T : Set Q)} ⟨S, le_rfl, hS, hBS⟩
  refine ⟨T, hTS, hTne, hTB, fun T' hle hB' => ?_⟩
  by_cases h : T' = ⊥
  · exact Or.inl h
  · right
    by_contra hne
    exact hmin T' ⟨hle.trans hTS, h, hB'⟩ (lt_of_le_of_ne hle hne)

@[expose] def mt113_conj (B T : Subgroup Q) (hN : B ≤ Subgroup.normalizer (T : Set Q)) :
    ↥B →* Monoid.End ↥T where
  toFun c :=
    { toFun := fun x => ⟨c.1 * x.1 * c.1⁻¹, mt113_conj_mem hN c.2 x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  map_one' := MonoidHom.ext fun x => Subtype.ext (by
    change (1 : Q) * x.1 * (1 : Q)⁻¹ = x.1
    simp)
  map_mul' := fun c d => MonoidHom.ext fun x => Subtype.ext (by
    change _ = c.1 * (d.1 * x.1 * d.1⁻¹) * c.1⁻¹
    simp [mul_assoc])

theorem mt113_conj_apply (B T : Subgroup Q) (hN : B ≤ Subgroup.normalizer (T : Set Q)) (c : ↥B)
    (x : ↥T) : ((mt113_conj B T hN c x : ↥T) : Q) = c.1 * x.1 * c.1⁻¹ := rfl

variable {B T : Subgroup Q}

theorem mt113_abelian [Finite Q] (hT2 : IsPGroup 2 T) (hne : T ≠ ⊥)
    (hBT : B ≤ Subgroup.normalizer (T : Set Q))
    (hmin : ∀ T' : Subgroup Q, T' ≤ T → B ≤ Subgroup.normalizer (T' : Set Q) → T' = ⊥ ∨ T' = T) :
    ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have : Nontrivial T := ⟨⟨a, 1, ha⟩⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hT2.center_nontrivial
  obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center ↥T)
  have hzc : ∀ h ∈ T, h * z.1 = z.1 * h := fun h hh =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨h, hh⟩)
  have hz1' : z.1 ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  let Z : Subgroup Q := T ⊓ Subgroup.centralizer (T : Set Q)
  have hZT : Z ≤ T := inf_le_left
  have hZB : B ≤ Subgroup.normalizer (Z : Set Q) := by
    apply mt113_le_normalizer
    intro b hb x hx
    have hxT : x ∈ T := hZT hx
    have hxc : ∀ h ∈ T, h * x = x * h := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2
    refine ⟨mt113_conj_mem hBT hb hxT, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    have hh' : b⁻¹ * h * b ∈ T := by
      have := mt113_conj_mem hBT (B.inv_mem hb) hh
      simpa using this
    have := hxc _ hh'
    calc h * (b * x * b⁻¹) = b * ((b⁻¹ * h * b) * x) * b⁻¹ := by group
      _ = b * (x * (b⁻¹ * h * b)) * b⁻¹ := by rw [this]
      _ = b * x * b⁻¹ * h := by group
  have hZne : Z ≠ ⊥ := by
    intro h
    have : z.1 ∈ Z := ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun h hh => hzc h hh⟩
    rw [h] at this
    exact hz1' (Subgroup.mem_bot.mp this)
  rcases hmin Z hZT hZB with h | h
  · exact absurd h hZne
  · intro x hx y hy
    have : x ∈ Z := by rw [h]; exact hx
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp this).2 y hy).symm

theorem mt113_exp [Finite Q] (hT2 : IsPGroup 2 T) (hne : T ≠ ⊥)
    (hBT : B ≤ Subgroup.normalizer (T : Set Q))
    (hmin : ∀ T' : Subgroup Q, T' ≤ T → B ≤ Subgroup.normalizer (T' : Set Q) → T' = ⊥ ∨ T' = T)
    (hab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) : ∀ x ∈ T, x * x = 1 := by
  let V : Subgroup Q :=
    { carrier := {x | x ∈ T ∧ x * x = 1}
      mul_mem' := fun {x y} hx hy => ⟨T.mul_mem hx.1 hy.1, by
        calc x * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [hab y hy.1 x hx.1]
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨T.one_mem, one_mul 1⟩
      inv_mem' := fun {x} hx => ⟨T.inv_mem hx.1, by
        calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
          _ = 1 := by rw [hx.2, inv_one]⟩ }
  have hVT : V ≤ T := fun x hx => hx.1
  have hVB : B ≤ Subgroup.normalizer (V : Set Q) := by
    apply mt113_le_normalizer
    intro b hb x hx
    refine ⟨mt113_conj_mem hBT hb hx.1, ?_⟩
    calc b * x * b⁻¹ * (b * x * b⁻¹) = b * (x * x) * b⁻¹ := by group
      _ = 1 := by rw [hx.2]; group
  have hVne : V ≠ ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases hT2.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq T h) hne
    · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 h
      intro hV
      have h1 : x.1 ∈ V := by
        refine ⟨x.2, ?_⟩
        have : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
        have := congrArg Subtype.val this
        simpa [pow_two] using this
      rw [hV] at h1
      have : x = 1 := Subtype.ext (Subgroup.mem_bot.mp h1)
      rw [this, orderOf_one] at hx
      omega
  rcases hmin V hVT hVB with h | h
  · exact absurd h hVne
  · intro x hx
    have : x ∈ V := by rw [h]; exact hx
    exact this.2

theorem mt113_comm_B (hB : IsElemAbelian 3 B) : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a :=
  fun a ha b hb => congrArg Subtype.val (hB.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem mt113_fix (hB : IsElemAbelian 3 B)
    (hmin : ∀ T' : Subgroup Q, T' ≤ T → B ≤ Subgroup.normalizer (T' : Set Q) → T' = ⊥ ∨ T' = T)
    (hBT : B ≤ Subgroup.normalizer (T : Set Q)) {c : Q} (hc : c ∈ B) {x : Q} (hx : x ∈ T)
    (hx1 : x ≠ 1) (hcx : c * x * c⁻¹ = x) : ∀ y ∈ T, c * y * c⁻¹ = y := by
  let C : Subgroup Q := T ⊓ Subgroup.centralizer ({c} : Set Q)
  have hCT : C ≤ T := inf_le_left
  have hmem : ∀ g, g ∈ C ↔ g ∈ T ∧ c * g = g * c := fun g => by
    simp [C, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  have hCB : B ≤ Subgroup.normalizer (C : Set Q) := by
    apply mt113_le_normalizer
    intro b hb g hg
    obtain ⟨hgT, hgc⟩ := (hmem g).mp hg
    refine (hmem _).mpr ⟨mt113_conj_mem hBT hb hgT, ?_⟩
    have h1 : Commute c b := mt113_comm_B hB c hc b hb
    have h2 : Commute c g := hgc
    exact ((h1.mul_right h2).mul_right h1.inv_right)
  rcases hmin C hCT hCB with h | h
  · exfalso
    have : x ∈ C := (hmem x).mpr ⟨hx, by rw [mul_inv_eq_iff_eq_mul] at hcx; exact hcx⟩
    rw [h] at this
    exact hx1 (Subgroup.mem_bot.mp this)
  · intro y hy
    have : y ∈ C := by rw [h]; exact hy
    have := ((hmem y).mp this).2
    rw [mul_inv_eq_iff_eq_mul]
    exact this

theorem mt113_card [Finite Q] (hB : IsElemAbelian 3 B) (hne : T ≠ ⊥)
    (hBT : B ≤ Subgroup.normalizer (T : Set Q))
    (hmin : ∀ T' : Subgroup Q, T' ≤ T → B ≤ Subgroup.normalizer (T' : Set Q) → T' = ⊥ ∨ T' = T)
    (hab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hexp : ∀ x ∈ T, x * x = 1) :
    Nat.card T ≤ 4 := by
  obtain ⟨t, htT, ht1'⟩ : ∃ t : Q, t ∈ T ∧ t ≠ 1 := by
    obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨t.1, t.2, fun h => ht1 (Subtype.ext h)⟩
  have hfix := fun {c : Q} (hc : c ∈ B) {x : Q} (hx : x ∈ T) (hx1 : x ≠ 1)
    (hcx : c * x * c⁻¹ = x) => mt113_fix hB hmin hBT hc hx hx1 hcx
  by_cases hall : ∀ c ∈ B, ∀ x ∈ T, c * x * c⁻¹ = x
  ·
    have hz : Subgroup.zpowers t = T := by
      have hle : Subgroup.zpowers t ≤ T := (Subgroup.zpowers_le).mpr htT
      rcases hmin _ hle (mt113_le_normalizer fun b hb x hx => by
        rw [hall b hb x (hle hx)]; exact hx) with h | h
      · exact absurd (h ▸ Subgroup.mem_zpowers t) (by simpa using ht1')
      · exact h
    rw [← hz, Nat.card_zpowers]
    have : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hexp _ htT)
    exact (Nat.le_of_dvd (by norm_num) this).trans (by norm_num)
  · have hcore := mt113_core (G := ↥T) (B' := ↥B)
      (fun x y => Subtype.ext (hab x.1 x.2 y.1 y.2))
      (fun a b => Subtype.ext (mt113_comm_B hB a.1 a.2 b.1 b.2))
      (mt113_conj B T hBT)
      (fun c => Subtype.ext (by simpa using hB.2 c.1 c.2))
      (by
        rintro c ⟨x, hx1, hcx⟩ y
        have hx1' : (x : Q) ≠ 1 := fun h => hx1 (Subtype.ext h)
        have := hfix c.2 x.2 hx1' (congrArg Subtype.val hcx) y.1 y.2
        exact Subtype.ext this)
    rcases hcore with h | ⟨b, hbfree, hb⟩
    · exact absurd (fun c hc x hx => congrArg Subtype.val (h ⟨c, hc⟩ ⟨x, hx⟩)) hall
    · obtain ⟨bq, hbq⟩ : ∃ bq : Q, bq = b.1 := ⟨_, rfl⟩
      have hbB : bq ∈ B := hbq ▸ b.2
      have hb3 : bq * bq * bq = 1 := by
        have := hB.2 bq hbB
        simpa [pow_succ] using this
      have hfree : ∀ x ∈ T, bq * x * bq⁻¹ = x → x = 1 := fun x hx h => by
        have := hbfree ⟨x, hx⟩ (Subtype.ext (by rw [mt113_conj_apply, ← hbq]; exact h))
        exact congrArg Subtype.val this
      have hact : ∀ b' ∈ B, ∃ k : ℕ, k < 3 ∧
          ∀ y ∈ T, b' * y * b'⁻¹ = bq ^ k * y * (bq ^ k)⁻¹ := by
        intro b' hb'
        obtain ⟨k, hk, hy⟩ := hb ⟨b', hb'⟩
        refine ⟨k, hk, fun y hy' => ?_⟩
        have := congrArg Subtype.val (hy ⟨y, hy'⟩)
        rw [mt113_conj_apply, mt113_conj_apply] at this
        simpa [hbq] using this
      obtain ⟨t', ht'd⟩ : ∃ t' : Q, t' = bq * t * bq⁻¹ := ⟨_, rfl⟩
      have ht'T : t' ∈ T := ht'd ▸ mt113_conj_mem hBT hbB htT
      obtain ⟨t'', ht''d⟩ : ∃ t'' : Q, t'' = bq * t' * bq⁻¹ := ⟨_, rfl⟩
      have ht''T : t'' ∈ T := ht''d ▸ mt113_conj_mem hBT hbB ht'T
      have hback : bq * t'' * bq⁻¹ = t := by
        calc bq * t'' * bq⁻¹ = (bq * bq * bq) * t * (bq * bq * bq)⁻¹ := by
              rw [ht''d, ht'd]; group
          _ = t := by rw [hb3]; group
      have hu : t * t' * t'' = 1 := by
        apply hfree _ (T.mul_mem (T.mul_mem htT ht'T) ht''T)
        calc bq * (t * t' * t'') * bq⁻¹
            = (bq * t * bq⁻¹) * (bq * t' * bq⁻¹) * (bq * t'' * bq⁻¹) := by group
          _ = t' * t'' * t := by rw [← ht'd, ← ht''d, hback]
          _ = t * (t' * t'') := hab _ (T.mul_mem ht'T ht''T) t htT
          _ = t * t' * t'' := by rw [mul_assoc]
      have he5 : t * t' * (t * t') = 1 := by
        calc t * t' * (t * t') = t * (t' * t) * t' := by group
          _ = t * (t * t') * t' := by rw [hab t' ht'T t htT]
          _ = (t * t) * (t' * t') := by group
          _ = 1 := by rw [hexp t htT, hexp t' ht'T, one_mul]
      have ht''e : t'' = t * t' := by
        rw [eq_inv_of_mul_eq_one_right hu]
        exact inv_eq_of_mul_eq_one_right he5
      have hg1 : bq * t * bq⁻¹ = t' := ht'd.symm
      have hg2 : bq * t' * bq⁻¹ = t * t' := by rw [← ht''d, ht''e]
      have hg3 : bq * (t * t') * bq⁻¹ = t := by
        calc bq * (t * t') * bq⁻¹ = (bq * t * bq⁻¹) * (bq * t' * bq⁻¹) := by group
          _ = t' * (t * t') := by rw [hg1, hg2]
          _ = (t' * t) * t' := by rw [mul_assoc]
          _ = (t * t') * t' := by rw [hab t' ht'T t htT]
          _ = t * (t' * t') := by rw [mul_assoc]
          _ = t := by rw [hexp t' ht'T, mul_one]
      obtain ⟨W, hW⟩ := mt113_klein t t' (hexp t htT) (hexp t' ht'T) (hab t htT t' ht'T)
      have hWmem : ∀ x, x ∈ W ↔ x = 1 ∨ x = t ∨ x = t' ∨ x = t * t' := by
        intro x
        rw [← SetLike.mem_coe, hW]
        simp
      have hgW : ∀ x ∈ W, bq * x * bq⁻¹ ∈ W := by
        intro x hx
        rw [hWmem] at hx ⊢
        rcases hx with rfl | rfl | rfl | rfl
        · left; group
        · exact Or.inr (Or.inr (Or.inl hg1))
        · exact Or.inr (Or.inr (Or.inr hg2))
        · exact Or.inr (Or.inl hg3)
      have hWT : ∀ x ∈ W, x ∈ T := by
        intro x hx
        rw [hWmem] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact T.one_mem
        · exact htT
        · exact ht'T
        · exact T.mul_mem htT ht'T
      have hWB : B ≤ Subgroup.normalizer (W : Set Q) := by
        apply mt113_le_normalizer
        intro b' hb' x hx
        obtain ⟨k, hk, hy⟩ := hact b' hb'
        rw [hy x (hWT x hx)]
        interval_cases k
        · simpa using hx
        · simpa using hgW x hx
        · have : bq ^ 2 * x * (bq ^ 2)⁻¹ = bq * (bq * x * bq⁻¹) * bq⁻¹ := by
            rw [pow_two]; group
          rw [this]
          exact hgW _ (hgW x hx)
      have htW : t ∈ W := (hWmem t).mpr (Or.inr (Or.inl rfl))
      rcases hmin W (fun x hx => hWT x hx) hWB with h | h
      · exact absurd (h ▸ htW) (by simpa using ht1')
      · have h1 : Nat.card T = (W : Set Q).ncard := by
          rw [← h]; exact Nat.card_coe_set_eq _
        rw [h1, hW]
        have := Set.ncard_insert_le (1 : Q) ({t, t', t * t'} : Set Q)
        have := Set.ncard_insert_le t ({t', t * t'} : Set Q)
        have := Set.ncard_insert_le t' ({t * t'} : Set Q)
        have := Set.ncard_singleton (t * t')
        omega

end QLevel

theorem minT113_proved : MinT113 := by
  intro Q _ _ B S hB hS hS2 hBS
  obtain ⟨T, hTS, hTne, hTB, hmin⟩ := mt113_exists_min B S hS hBS
  have hT2 : IsPGroup 2 T := hS2.to_le hTS
  have hab := mt113_abelian hT2 hTne hTB hmin
  have hexp := mt113_exp hT2 hTne hTB hmin hab
  refine ⟨T, hTne, hT2, hTB, hmin, ⟨⟨⟨fun a b => Subtype.ext (hab a.1 a.2 b.1 b.2)⟩⟩,
    fun x hx => by rw [pow_two]; exact hexp x hx⟩, mt113_card hB hTne hTB hmin hab hexp⟩

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
