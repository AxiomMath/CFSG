module

public import CFSG.CGT.PushingUpLit.A78Sp4.F410
public import CFSG.CGT.PushingUpLit.A78Sp4.Torus
public import CFSG.CGT.PushingUpLit.A78Sp4.Stab

public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

open CFSG.ABGLocalTools
open scoped commutatorElement

section Forms

variable {K : Type*} [Field K] [CharP K 2]

theorem beta_add_right (x y y' : K × K) : beta x (y + y') = beta x y + beta x y' := by
  have h2 : (2 : K) = 0 := charTwo_two_eq_zero
  simp only [beta, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
  ext
  · ring
  · linear_combination (y.1 * y'.1 * x.2) * h2

omit [CharP K 2] in
theorem isDiagForm_of_axes {gb Γ : K × K →+ K × K}
    (hcomp : ∀ x y, Γ (beta x y) = beta (gb x) (gb y))
    (hax : (∀ r, (gb (r, 0)).2 = 0) ∧ ∀ s, (gb (0, s)).1 = 0)
    (hΓ : ∀ w, (Γ (0, w)).1 = 0) (hinj : Function.Injective gb) : IsDiagForm gb := by
  let f : K →+ K := (AddMonoidHom.fst K K).comp (gb.comp (AddMonoidHom.inl K K))
  let g : K →+ K := (AddMonoidHom.snd K K).comp (gb.comp (AddMonoidHom.inr K K))
  have hgb : ∀ r s, gb (r, s) = (f r, g s) := by
    intro r s
    have e : (r, s) = (r, 0) + (0, s) := by simp
    rw [e, map_add]
    refine Prod.ext ?_ ?_
    · show (gb (r, 0)).1 + (gb (0, s)).1 = f r
      rw [hax.2 s, add_zero]
      rfl
    · show (gb (r, 0)).2 + (gb (0, s)).2 = g s
      rw [hax.1 r, zero_add]
      rfl
  have hf1 : f 1 ≠ 0 := by
    intro h0
    have h1 : gb (1, 0) = gb 0 := by rw [hgb, h0, map_zero g, map_zero gb]; rfl
    have := hinj h1
    simp at this
  have hg1 : g 1 ≠ 0 := by
    intro h0
    have h1 : gb (0, 1) = gb 0 := by rw [hgb, h0, map_zero f, map_zero gb]; rfl
    have := hinj h1
    simp at this
  have key : ∀ r s', (Γ (r * s', 0)).1 = f r * g s' := by
    intro r s'
    have h := hcomp (r, 0) (0, s')
    rw [beta_fst_zero, hgb r 0, hgb 0 s', map_zero f, map_zero g, beta_fst_zero] at h
    have e : (r * s', r ^ 2 * s') = (r * s', 0) + (0, r ^ 2 * s') := by simp
    rw [e, map_add] at h
    have h1 := congrArg Prod.fst h
    rw [Prod.fst_add, hΓ, add_zero] at h1
    exact h1
  have hfg : ∀ s', f 1 * g s' = f s' * g 1 := by
    intro s'
    have e3 := key 1 s'
    have e4 := key s' 1
    rw [one_mul] at e3
    rw [mul_one] at e4
    exact e3.symm.trans e4
  have hmul : ∀ r s', f (r * s') * f 1 = f r * f s' := by
    intro r s'
    have e1 := key r s'
    have e2 := key (r * s') 1
    rw [mul_one] at e2
    have : f (r * s') * f 1 * g 1 = f r * f s' * g 1 := by
      calc f (r * s') * f 1 * g 1 = f (r * s') * g 1 * f 1 := by ring
        _ = f r * g s' * f 1 := by rw [← e2, e1]
        _ = f r * (f 1 * g s') := by ring
        _ = f r * (f s' * g 1) := by rw [hfg]
        _ = f r * f s' * g 1 := by ring
    exact mul_right_cancel₀ hg1 this
  let σ : K →+* K :=
    { toFun := fun r => f r / f 1
      map_one' := div_self hf1
      map_mul' := fun r s' => by
        show f (r * s') / f 1 = f r / f 1 * (f s' / f 1)
        rw [div_mul_div_comm, div_eq_div_iff hf1 (mul_ne_zero hf1 hf1), ← hmul r s']
        ring
      map_zero' := by simp
      map_add' := fun r s' => by
        show f (r + s') / f 1 = f r / f 1 + f s' / f 1
        rw [map_add, add_div] }
  refine ⟨f 1, g 1, σ, hf1, hg1, fun r s => ?_⟩
  rw [hgb]
  refine Prod.ext ?_ ?_
  · show f r = f 1 * (f r / f 1)
    field_simp
  · show g s = g 1 * (f s / f 1)
    have := hfg s
    field_simp
    linear_combination this

theorem isSwapForm_of_axes [Finite K] {gb Γ : K × K →+ K × K}
    (hcomp : ∀ x y, Γ (beta x y) = beta (gb x) (gb y))
    (hax : (∀ r, (gb (r, 0)).1 = 0) ∧ ∀ s, (gb (0, s)).2 = 0)
    (hΓ : ∀ w, (Γ (0, w)).2 = 0) (hinj : Function.Injective gb) : IsSwapForm gb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : K →+ K := (AddMonoidHom.fst K K).comp (gb.comp (AddMonoidHom.inr K K))
  let ψ : K →+ K := (AddMonoidHom.snd K K).comp (gb.comp (AddMonoidHom.inl K K))
  have hgb : ∀ r s, gb (r, s) = (φ s, ψ r) := by
    intro r s
    have e : (r, s) = (r, 0) + (0, s) := by simp
    rw [e, map_add]
    refine Prod.ext ?_ ?_
    · show (gb (r, 0)).1 + (gb (0, s)).1 = φ s
      rw [hax.1 r, zero_add]
      rfl
    · show (gb (r, 0)).2 + (gb (0, s)).2 = ψ r
      rw [hax.2 s, add_zero]
      rfl
  have hφ1 : φ 1 ≠ 0 := by
    intro h0
    have h1 : gb (0, 1) = gb 0 := by rw [hgb, h0, map_zero ψ, map_zero gb]; rfl
    have := hinj h1
    simp at this
  have hψ1 : ψ 1 ≠ 0 := by
    intro h0
    have h1 : gb (1, 0) = gb 0 := by rw [hgb, h0, map_zero φ, map_zero gb]; rfl
    have := hinj h1
    simp at this
  have key : ∀ r s', (Γ (r * s', 0)).2 = φ s' ^ 2 * ψ r := by
    intro r s'
    have h := hcomp (r, 0) (0, s')
    rw [beta_fst_zero, hgb r 0, hgb 0 s', map_zero φ, map_zero ψ] at h
    have hb : beta (0, ψ r) (φ s', 0) = (φ s' * ψ r, φ s' ^ 2 * ψ r) := by simp [beta]
    rw [hb] at h
    have e : (r * s', r ^ 2 * s') = (r * s', 0) + (0, r ^ 2 * s') := by simp
    rw [e, map_add] at h
    have h2 := congrArg Prod.snd h
    rw [Prod.snd_add, hΓ, add_zero] at h2
    exact h2
  have hrel : ∀ r, φ 1 ^ 2 * ψ r = φ r ^ 2 * ψ 1 := by
    intro r
    have e1 := key r 1
    have e2 := key 1 r
    rw [mul_one] at e1
    rw [one_mul] at e2
    exact e1.symm.trans e2
  have hmul : ∀ r s', φ (r * s') * φ 1 = φ r * φ s' := by
    intro r s'
    have e1 := key r s'
    have e2 := key 1 (r * s')
    rw [one_mul] at e2
    have h3 : φ (r * s') ^ 2 * ψ 1 = φ s' ^ 2 * ψ r := e2.symm.trans e1
    have h4 := hrel r
    have h5 : (φ (r * s') * φ 1) ^ 2 * ψ 1 = (φ r * φ s') ^ 2 * ψ 1 := by
      calc (φ (r * s') * φ 1) ^ 2 * ψ 1 = φ 1 ^ 2 * (φ (r * s') ^ 2 * ψ 1) := by ring
        _ = φ 1 ^ 2 * (φ s' ^ 2 * ψ r) := by rw [h3]
        _ = φ s' ^ 2 * (φ 1 ^ 2 * ψ r) := by ring
        _ = φ s' ^ 2 * (φ r ^ 2 * ψ 1) := by rw [h4]
        _ = (φ r * φ s') ^ 2 * ψ 1 := by ring
    have hsq := mul_right_cancel₀ hψ1 h5
    exact frobenius_inj K 2 (by simpa [frobenius_def] using hsq)
  let σ : K →+* K :=
    { toFun := fun r => φ r / φ 1
      map_one' := div_self hφ1
      map_mul' := fun r s' => by
        show φ (r * s') / φ 1 = φ r / φ 1 * (φ s' / φ 1)
        rw [div_mul_div_comm, div_eq_div_iff hφ1 (mul_ne_zero hφ1 hφ1), ← hmul r s']
        ring
      map_zero' := by simp
      map_add' := fun r s' => by
        show φ (r + s') / φ 1 = φ r / φ 1 + φ s' / φ 1
        rw [map_add, add_div] }
  obtain ⟨a, ha⟩ := exists_sq_eq (ψ 1)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hψ1 (by rw [← ha]; ring)
  refine ⟨a, φ 1, σ, ha0, hφ1, fun r s => ?_⟩
  rw [hgb]
  refine Prod.ext ?_ ?_
  · show φ s = φ 1 * (φ s / φ 1)
    field_simp
  · show ψ r = a ^ 2 * (φ r / φ 1) ^ 2
    rw [ha]
    have h4 := hrel r
    field_simp
    linear_combination h4

end Forms

section Four

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem pow_four_of_card (hK : Nat.card K = 4) (x : K) : x ^ 4 = x := by
  have := Fintype.ofFinite K
  have h := FiniteField.pow_card x
  rwa [← Nat.card_eq_fintype_card, hK] at h

omit [CharP K 2] in
theorem pow_three_of_card (hK : Nat.card K = 4) {x : K} (hx : x ≠ 0) : x ^ 3 = 1 := by
  have := Fintype.ofFinite K
  have h := FiniteField.pow_card_sub_one_eq_one x hx
  rwa [← Nat.card_eq_fintype_card, hK] at h

theorem ringHom_of_card_four (hK : Nat.card K = 4) (σ : K →+* K) :
    (∀ x, σ x = x) ∨ ∀ x, σ x = x ^ 2 := by
  obtain ⟨j, hj⟩ := exists_pow_of_ringHom σ
  have h4 : ∀ m : ℕ, ∀ x : K, x ^ 4 ^ m = x := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih => intro x; rw [pow_succ, pow_mul, ih, pow_four_of_card hK]
  rcases Nat.even_or_odd' j with ⟨m, rfl | rfl⟩
  · left
    intro x
    have e : (2 : ℕ) ^ (2 * m) = 4 ^ m := by rw [pow_mul]; norm_num
    rw [hj, e, h4]
  · right
    intro x
    have e : (2 : ℕ) ^ (2 * m + 1) = 4 ^ m * 2 := by rw [pow_succ, pow_mul]; norm_num
    rw [hj, e, pow_mul, h4]

theorem ringHom_sq_of_card_four (hK : Nat.card K = 4) (σ : K →+* K) (x : K) : σ (σ x) = x := by
  rcases ringHom_of_card_four hK σ with h1 | h1
  · rw [h1, h1]
  · rw [h1, h1, ← pow_mul]
    exact pow_four_of_card hK x

omit [CharP K 2] in
theorem exists_ne_zero_one_of_card (hK : Nat.card K = 4) : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
  classical
  obtain ⟨ω, hω⟩ := exists_avoid ({0, 1} : Finset K) (by
    calc ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
      _ < Nat.card K := by rw [hK]; norm_num)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
  exact ⟨ω, hω.1, hω.2⟩

theorem exists_sq_add_ne (hK : Nat.card K = 4) (a : K) : ∃ r : K, a * r ^ 2 + r ≠ 0 := by
  classical
  have h2 : (2 : K) = 0 := charTwo_two_eq_zero
  obtain ⟨r, hr⟩ := exists_avoid ({0, a⁻¹} : Finset K) (by
    calc ({0, a⁻¹} : Finset K).card ≤ 2 := Finset.card_le_two
      _ < Nat.card K := by rw [hK]; norm_num)
  refine ⟨r, fun h0 => hr ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have : r * (a * r + 1) = 0 := by linear_combination h0
  rcases mul_eq_zero.1 this with h | h
  · exact Or.inl h
  · right
    have h1 : a * r = 1 := by linear_combination h - h2
    exact eq_inv_of_mul_eq_one_right h1

theorem swap_four (hK : Nat.card K = 4) {gb : K × K →+ K × K} (hform : IsSwapForm gb) :
    4 < (Set.range (gb + AddMonoidHom.id (K × K))).ncard := by
  classical
  obtain ⟨a, b, σ, ha, hb, h⟩ := hform
  have h2 : (2 : K) = 0 := charTwo_two_eq_zero
  set κ := b * σ a ^ 2 with hκ
  have hκ0 : κ ≠ 0 := mul_ne_zero hb (pow_ne_zero _ ((map_ne_zero σ).2 ha))
  set F := gb + AddMonoidHom.id (K × K) with hF
  have hker : (F.ker : Set (K × K)) ⊆ {0, (κ⁻¹, a ^ 2 * σ κ⁻¹ ^ 2)} := by
    rintro ⟨r, s⟩ hrs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    have h0F : F (r, s) = 0 := AddMonoidHom.mem_ker.1 hrs
    have h1 : gb (r, s) + (r, s) = 0 := h0F
    rw [h] at h1
    have e1 : b * σ s + r = 0 := congrArg Prod.fst h1
    have e2 : a ^ 2 * σ r ^ 2 + s = 0 := congrArg Prod.snd h1
    have hs : s = a ^ 2 * σ r ^ 2 := by linear_combination e2 - (a ^ 2 * σ r ^ 2) * h2
    have hr : r = b * σ s := by linear_combination e1 - (b * σ s) * h2
    have hr2 : r = b * σ (a ^ 2 * σ r ^ 2) := by rw [← hs]; exact hr
    rw [map_mul, map_pow, map_pow, ringHom_sq_of_card_four hK] at hr2
    have hr3 : r * (κ * r - 1) = 0 := by rw [hκ]; linear_combination -hr2
    rcases mul_eq_zero.1 hr3 with h0 | h0
    · left
      have hs0 : s = 0 := by rw [hs, h0]; simp
      rw [h0, hs0]
      rfl
    · right
      have hrk : r = κ⁻¹ := eq_inv_of_mul_eq_one_left (by linear_combination h0)
      rw [hs, hrk]
  have hcard : Nat.card F.ker ≤ 2 := by
    have e0 : Nat.card F.ker = (F.ker : Set (K × K)).ncard := by
      rw [← Nat.card_coe_set_eq]; rfl
    rw [e0]
    calc (F.ker : Set (K × K)).ncard ≤ ({0, (κ⁻¹, a ^ 2 * σ κ⁻¹ ^ 2)} : Set (K × K)).ncard :=
          Set.ncard_le_ncard hker (Set.toFinite _)
      _ ≤ ({(κ⁻¹, a ^ 2 * σ κ⁻¹ ^ 2)} : Set (K × K)).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  have hkr := AddSubgroup.card_ker_mul_card_range F
  rw [Nat.card_prod, hK] at hkr
  have e1 : (Set.range F).ncard = Nat.card F.range := by
    rw [← Nat.card_coe_set_eq]
    rfl
  rw [e1]
  have h16 : 16 ≤ 2 * Nat.card F.range := by
    calc 16 = Nat.card F.ker * Nat.card F.range := by rw [hkr]
      _ ≤ 2 * Nat.card F.range := Nat.mul_le_mul_right _ hcard
  omega

end Four

section Polar

variable {K : Type*} [Field K] {G : Type*} [Group G] {J : Subgroup G}

theorem ker_mem_of_span (c : Cls2Coord K J) {S Q : Subgroup G} (hJS : J ≤ S)
    (hQn : ∀ s ∈ S, ∀ x ∈ Q, s * x * s⁻¹ ∈ Q)
    (hspan : ∀ w : K × K, ∃ a₁ ∈ Q ⊓ J, ∃ a₂ ∈ Q ⊓ J, ∃ y₁ y₂ : K × K,
      beta (c.π a₁) y₁ + beta (c.π a₂) y₂ = w) :
    ∀ z ∈ J, c.π z = 0 → z ∈ Q := by
  intro z hzJ hz0
  obtain ⟨a₁, ha₁, a₂, ha₂, y₁, y₂, hw⟩ := hspan (c.ζ z)
  obtain ⟨v₁, hv₁J, hv₁⟩ := c.π_surj y₁
  obtain ⟨v₂, hv₂J, hv₂⟩ := c.π_surj y₂
  have hcomm : ∀ a ∈ Q ⊓ J, ∀ v ∈ J, ⁅a, v⁆ ∈ Q ∧ ⁅a, v⁆ ∈ J := by
    intro a ha v hv
    refine ⟨?_, ?_⟩
    · have h1 := hQn v (hJS hv) a⁻¹ (Q.inv_mem ha.1)
      have : ⁅a, v⁆ = a * (v * a⁻¹ * v⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact Q.mul_mem ha.1 h1
    · rw [commutatorElement_def]
      exact J.mul_mem (J.mul_mem (J.mul_mem ha.2 hv) (J.inv_mem ha.2)) (J.inv_mem hv)
  obtain ⟨h1Q, h1J⟩ := hcomm a₁ ha₁ v₁ hv₁J
  obtain ⟨h2Q, h2J⟩ := hcomm a₂ ha₂ v₂ hv₂J
  obtain ⟨p1, z1⟩ := c.comm a₁ ha₁.2 v₁ hv₁J
  obtain ⟨p2, z2⟩ := c.comm a₂ ha₂.2 v₂ hv₂J
  have hq : c.ζ (⁅a₁, v₁⁆ * ⁅a₂, v₂⁆) = c.ζ z := by
    rw [c.ζ_mul _ h1J p1 _ h2J p2, z1, z2, hv₁, hv₂, hw]
  have hqπ : c.π (⁅a₁, v₁⁆ * ⁅a₂, v₂⁆) = 0 := by rw [c.π_mul _ h1J _ h2J, p1, p2, add_zero]
  rw [← c.ζ_inj _ (J.mul_mem h1J h2J) hqπ z hzJ hz0 hq]
  exact Q.mul_mem h1Q h2Q

theorem ker_mem_of_two_fst [CharP K 2] (c : Cls2Coord K J) {S Q : Subgroup G} (hJS : J ≤ S)
    (hQn : ∀ s ∈ S, ∀ x ∈ Q, s * x * s⁻¹ ∈ Q) {a₁ a₂ : G} (ha₁ : a₁ ∈ Q ⊓ J) (ha₂ : a₂ ∈ Q ⊓ J)
    (h1 : (c.π a₁).1 ≠ 0) (h2 : (c.π a₂).1 ≠ 0) (h12 : (c.π a₁).1 ≠ (c.π a₂).1) :
    ∀ z ∈ J, c.π z = 0 → z ∈ Q := by
  refine ker_mem_of_span c hJS hQn fun w => ?_
  obtain ⟨s₁, s₂, hs⟩ := exists_line_sum h1 h2 h12 w.1 w.2
  refine ⟨a₁, ha₁, a₂, ha₂, (0, s₁), (0, s₂), ?_⟩
  have e1 : ∀ x : K × K, ∀ t : K, beta x (0, t) = (x.1 * t, x.1 ^ 2 * t) := fun x t => by
    simp [beta]
  rw [e1, e1, Prod.mk_add_mk, hs]

theorem ker_mem_of_two_snd [CharP K 2] [Finite K] (c : Cls2Coord K J) {S Q : Subgroup G}
    (hJS : J ≤ S) (hQn : ∀ s ∈ S, ∀ x ∈ Q, s * x * s⁻¹ ∈ Q) {a₁ a₂ : G} (ha₁ : a₁ ∈ Q ⊓ J)
    (ha₂ : a₂ ∈ Q ⊓ J) (h1 : (c.π a₁).2 ≠ 0) (h2 : (c.π a₂).2 ≠ 0)
    (h12 : (c.π a₁).2 ≠ (c.π a₂).2) : ∀ z ∈ J, c.π z = 0 → z ∈ Q := by
  refine ker_mem_of_span c hJS hQn fun w => ?_
  obtain ⟨u, v, hs⟩ := exists_line_sum' h1 h2 h12 w.1 w.2
  refine ⟨a₁, ha₁, a₂, ha₂, (u, 0), (v, 0), ?_⟩
  have e1 : ∀ x : K × K, ∀ t : K, beta x (t, 0) = (t * x.2, t ^ 2 * x.2) := fun x t => by
    simp [beta]
  rw [e1, e1, Prod.mk_add_mk, hs]

end Polar

section Stability

variable {G : Type*} [Group G]

theorem qCenter_conj_mem_of {C Q : Subgroup G} (hQn : ∀ c ∈ C, ∀ x ∈ Q, c * x * c⁻¹ ∈ Q)
    {g : G} (hg : g ∈ C) {z : G} (hz : z ∈ qCenter Q) : g * z * g⁻¹ ∈ qCenter Q := by
  rw [mem_qCenter] at hz ⊢
  refine ⟨hQn g hg z hz.1, fun x hx => ?_⟩
  have h1 : g⁻¹ * x * g ∈ Q := by simpa using hQn g⁻¹ (C.inv_mem hg) x hx
  have h2 := hz.2 _ h1
  calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [h2]
    _ = (g * z * g⁻¹) * x := by group

theorem mem_of_stability [Finite G] {C Q : Subgroup G}
    (hQn : ∀ c ∈ C, ∀ x ∈ Q, c * x * c⁻¹ ∈ Q) (hQp : IsPGroup 2 Q)
    (hcent : ∀ c ∈ C, (∀ x ∈ Q, c * x = x * c) → c ∈ Q)
    (hmax : ∀ N : Subgroup G, N ≤ C → C ≤ Subgroup.normalizer (N : Set G) → IsPGroup 2 N → N ≤ Q)
    {d : G} (hd : d ∈ C) (hdQ : ∀ x ∈ Q, ⁅d, x⁆ ∈ qCenter Q)
    (hdZ : ∀ z ∈ qCenter Q, d * z = z * d) : d ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup G :=
    { carrier := {c | c ∈ C ∧ (∀ x ∈ Q, ⁅c, x⁆ ∈ qCenter Q) ∧ ∀ z ∈ qCenter Q, c * z = z * c}
      one_mem' := ⟨C.one_mem, fun x _ => by simp [(qCenter Q).one_mem], fun z _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨haC, ha1, ha2⟩ ⟨hbC, hb1, hb2⟩
        refine ⟨C.mul_mem haC hbC, fun x hx => ?_, fun z hz => ?_⟩
        · have e : ⁅a * b, x⁆ = (a * ⁅b, x⁆ * a⁻¹) * ⁅a, x⁆ := by
            simp only [commutatorElement_def]; group
          have e2 : a * ⁅b, x⁆ * a⁻¹ = ⁅b, x⁆ := by
            rw [ha2 _ (hb1 x hx), mul_assoc, mul_inv_cancel, mul_one]
          rw [e, e2]
          exact (qCenter Q).mul_mem (hb1 x hx) (ha1 x hx)
        · rw [mul_assoc, hb2 z hz, ← mul_assoc, ha2 z hz, mul_assoc]
      inv_mem' := by
        rintro a ⟨haC, ha1, ha2⟩
        have ha2' : ∀ z ∈ qCenter Q, a⁻¹ * z = z * a⁻¹ := fun z hz => by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ha2 z hz, mul_assoc, mul_inv_cancel, mul_one]
        refine ⟨C.inv_mem haC, fun x hx => ?_, ha2'⟩
        have e : ⁅a⁻¹, x⁆ = a⁻¹ * (⁅a, x⁆)⁻¹ * a := by
          simp only [commutatorElement_def]; group
        have hm : (⁅a, x⁆)⁻¹ ∈ qCenter Q := (qCenter Q).inv_mem (ha1 x hx)
        rw [e, ha2' _ hm, mul_assoc, inv_mul_cancel, mul_one]
        exact hm }
  have hNC : N ≤ C := fun c hc => hc.1
  have hconj : ∀ g ∈ C, ∀ c ∈ N, g * c * g⁻¹ ∈ N := by
    rintro g hg c ⟨hcC, hc1, hc2⟩
    refine ⟨C.mul_mem (C.mul_mem hg hcC) (C.inv_mem hg), fun x hx => ?_, fun z hz => ?_⟩
    · have hx' : g⁻¹ * x * g ∈ Q := by simpa using hQn g⁻¹ (C.inv_mem hg) x hx
      have e : ⁅g * c * g⁻¹, x⁆ = g * ⁅c, g⁻¹ * x * g⁆ * g⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact qCenter_conj_mem_of hQn hg (hc1 _ hx')
    · have hz' : g⁻¹ * z * g ∈ qCenter Q := by
        simpa using qCenter_conj_mem_of hQn (C.inv_mem hg) hz
      have h1 := hc2 _ hz'
      calc g * c * g⁻¹ * z = g * (c * (g⁻¹ * z * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * z * g) * c) * g⁻¹ := by rw [h1]
        _ = z * (g * c * g⁻¹) := by group
  have hCN : C ≤ Subgroup.normalizer (N : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨hconj g hg c, fun h => ?_⟩
    have := hconj g⁻¹ (C.inv_mem hg) _ h
    simpa [mul_assoc] using this
  have hNp : IsPGroup 2 N := by
    rintro ⟨c, hcC, hc1, hc2⟩
    have hpow : ∀ x ∈ Q, ∀ n : ℕ, c ^ n * x * (c ^ n)⁻¹ = ⁅c, x⁆ ^ n * x := by
      intro x hx n
      obtain ⟨t, ht⟩ : ∃ t, ⁅c, x⁆ = t := ⟨_, rfl⟩
      have hcx : c * t = t * c := by rw [← ht]; exact hc2 _ (hc1 x hx)
      have hcxc : c * x * c⁻¹ = t * x := by rw [← ht]; simp only [commutatorElement_def]; group
      rw [ht]
      induction n with
      | zero => simp
      | succ n ih =>
        have hc' : c * t ^ n * c⁻¹ = t ^ n := by
          rw [(Commute.pow_right hcx n).eq, mul_assoc, mul_inv_cancel, mul_one]
        calc c ^ (n + 1) * x * (c ^ (n + 1))⁻¹ = c * (c ^ n * x * (c ^ n)⁻¹) * c⁻¹ := by
              rw [pow_succ']; group
          _ = c * (t ^ n * x) * c⁻¹ := by rw [ih]
          _ = (c * t ^ n * c⁻¹) * (c * x * c⁻¹) := by group
          _ = t ^ n * (t * x) := by rw [hc', hcxc]
          _ = t ^ (n + 1) * x := by rw [pow_succ, mul_assoc]
    have hfix : ∀ x ∈ Q, c ^ Nat.card Q * x = x * c ^ Nat.card Q := by
      intro x hx
      have h1 : ⁅c, x⁆ ^ Nat.card Q = 1 := by
        have := pow_card_eq_one' (G := ↥Q) (x := (⟨_, (hc1 x hx).1⟩ : Q))
        exact congrArg Subtype.val this
      have h2 := hpow x hx (Nat.card Q)
      rw [h1, one_mul] at h2
      calc c ^ Nat.card Q * x = c ^ Nat.card Q * x * (c ^ Nat.card Q)⁻¹ * c ^ Nat.card Q := by
            group
        _ = x * c ^ Nat.card Q := by rw [h2]
    have hmem : c ^ Nat.card Q ∈ Q := hcent _ (C.pow_mem hcC _) hfix
    obtain ⟨k, hk⟩ := hQp ⟨_, hmem⟩
    obtain ⟨m, hm⟩ := hQp.exists_card_eq
    refine ⟨m + k, Subtype.ext ?_⟩
    have hk' : (c ^ Nat.card Q) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [hm, ← pow_mul, ← pow_add] at hk'
    simpa using hk'
  exact hmax N hNC hCN hNp ⟨hd, hdQ, hdZ⟩

theorem inv_mul_mem_of_sq [Finite G] {S J : Subgroup G} (hJn : (J.subgroupOf S).Normal)
    (hcyc : ∃ s ∈ S, ∀ x ∈ S, ∃ k : ℤ, (s ^ k)⁻¹ * x ∈ J) {x y : G} (hxS : x ∈ S) (hyS : y ∈ S)
    (hxJ : x ∉ J) (hyJ : y ∉ J) (hx : x * x ∈ J) (hy : y * y ∈ J) : x⁻¹ * y ∈ J := by
  classical
  have := hJn
  have : IsCyclic (S ⧸ J.subgroupOf S) := isCyclic_quot_of_gen hcyc
  have : Fintype (S ⧸ J.subgroupOf S) := Fintype.ofFinite _
  set a' : S ⧸ J.subgroupOf S := QuotientGroup.mk ⟨x, hxS⟩ with ha'
  set b' : S ⧸ J.subgroupOf S := QuotientGroup.mk ⟨y, hyS⟩ with hb'
  have hsq : ∀ (w : G) (hw : w ∈ S), w * w ∈ J →
      (QuotientGroup.mk ⟨w, hw⟩ : S ⧸ J.subgroupOf S) ^ 2 = 1 := by
    intro w hw hww
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa [pow_two] using hww
  have h1 : a' ≠ 1 := fun h1 => hxJ (Subgroup.mem_subgroupOf.1
    ((QuotientGroup.eq_one_iff (N := J.subgroupOf S) _).1 h1))
  have h2 : b' ≠ 1 := fun h2 => hyJ (Subgroup.mem_subgroupOf.1
    ((QuotientGroup.eq_one_iff (N := J.subgroupOf S) _).1 h2))
  by_contra hne
  have h3 : a' ≠ b' := fun h3 => hne (by
    have := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 h3)
    simpa using this)
  have hsub : ({1, a', b'} : Finset (S ⧸ J.subgroupOf S)) ⊆
      Finset.univ.filter (fun w : S ⧸ J.subgroupOf S => w ^ 2 = 1) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hw with rfl | rfl | rfl
    · simp
    · exact hsq x hxS hx
    · exact hsq y hyS hy
  have hcard3 : ({1, a', b'} : Finset (S ⧸ J.subgroupOf S)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using h3
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => h1 h.symm, fun h => h2 h.symm⟩
  have := Finset.card_le_card hsub
  have h4 := IsCyclic.card_pow_eq_one_le (α := S ⧸ J.subgroupOf S) (n := 2) (by norm_num)
  omega

end Stability

section Main

variable {G : Type} [Group G] {K : Type*} [Field K] {J : Subgroup G}

theorem ActsAs.π_commutator [CharP K 2] {c : Cls2Coord K J} {s : G} {gb Γ : K × K →+ K × K}
    (h : ActsAs c s gb Γ) (hs : ∀ x ∈ J, s * x * s⁻¹ ∈ J) {y : G} (hy : y ∈ J) :
    c.π ⁅s, y⁆ = gb (c.π y) + c.π y := by
  have e : ⁅s, y⁆ = (s * y * s⁻¹) * y⁻¹ := by simp [commutatorElement_def, mul_assoc]
  rw [e, c.π_mul _ (hs y hy) _ (J.inv_mem hy), h.π_conj y hy, c.π_inv hy]
  congr 1
  exact Prod.ext (CharTwo.neg_eq _) (CharTwo.neg_eq _)

variable [Finite G] {L L₂ V V₂ Z Z₂ T S M M₂ : Subgroup G} {e : ℕ}

theorem sp4_410_two (h : Sp4Loc G L L₂ V V₂ Z Z₂ J T S M M₂ e) (he : e = 2) :
    Sp4Stmt410 V V₂ Z Z₂ J := by
  subst he
  refine h.stmt410_of_central fun u hu hcen => ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({u} : Set G) with hC
  set Q := CFSG.Open.pCoreOf 2 C with hQ
  have hSC : S ≤ C := fun s hs => Subgroup.mem_centralizer_singleton_iff.2 (hcen s hs)
  have hQS : Q ≤ S := pCoreOf_le_of_isSylowOf (h.base.sylow.of_le hSC le_top)
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C
  have hQn : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := fun c hc q hq =>
    (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C hc) q).1 hq
  have hQnS : ∀ s ∈ S, ∀ x ∈ Q, s * x * s⁻¹ ∈ Q := fun s hs x hx => hQn s (hSC hs) x hx
  have hu2 : u * u = 1 := (h.base.elem_V u hu.1.1 u hu.1.1).2
  have hu1 : u ≠ 1 := fun h1 => hu.2.1 (h1 ▸ Z.one_mem)
  have hcentQ : ∀ s ∈ C, (∀ x ∈ Q, s * x = x * s) → s ∈ Q := fun s hs hsQ =>
    cent_le_pCoreOf h.charTwo hu2 hu1
      ⟨hs, Subgroup.mem_centralizer_iff.2 fun x hx => (hsQ x hx).symm⟩
  have hVJ : V ≤ J := by rw [← h.base.sup]; exact le_sup_left
  have hJn : ∀ s ∈ S, ∀ x ∈ J, s * x * s⁻¹ ∈ J := fun s hs x hx => h.base.conj_J hs hx
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have h2K : (2 : GaloisField 2 2) = 0 := charTwo_two_eq_zero
  obtain ⟨c, hV, hV₂, hZc, hZ₂c⟩ := exists_cls2 h.coords
  have hkerV : ∀ x ∈ J, c.π x = 0 → x ∈ V ⊓ V₂ := fun x hx h0 =>
    ⟨(hV x hx).2 (by rw [h0]; rfl), (hV₂ x hx).2 (by rw [h0]; rfl)⟩
  have hVker : ∀ x ∈ V ⊓ V₂, c.π x = 0 := fun x hx =>
    Prod.ext ((hV₂ x (hVJ hx.1)).1 hx.2) ((hV x (hVJ hx.1)).1 hx.1)
  have hZJc : ∀ v ∈ V ⊓ V₂, ∀ j ∈ J, v * j = j * v := fun v hv j hj =>
    c.ker_central (hVJ hv.1) (hVker v hv) hj
  have hcQJ : ∀ x ∈ Q, ∀ y ∈ J, ⁅x, y⁆ ∈ Q ⊓ J := by
    intro x hx y hy
    have hxS := hQS hx
    refine ⟨?_, ?_⟩
    · have h1 := hQnS y (h.base.J_le_S hy) x⁻¹ (Q.inv_mem hx)
      have : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact Q.mul_mem hx h1
    · have : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact J.mul_mem (hJn x hxS y hy) (J.inv_mem hy)
  have hkerQ : ∀ z ∈ J, c.π z = 0 → z ∈ Q := by
    by_contra hcon
    push Not at hcon
    obtain ⟨z₀, hz₀J, hz₀π, hz₀Q⟩ := hcon
    have hsmall : ∀ x ∈ Q, x ∉ J → ¬ 4 < (commSet c x).ncard := fun x hxQ _ hlt =>
      hz₀Q (z1_elem c h.base.J_le_S hJn hQnS (hQS hxQ) hxQ hlt z₀ hz₀J hz₀π)
    have hstr : ∀ x ∈ Q, x ∉ J → x * x ∈ J ∧
        (∃ y₁ ∈ J, (c.π ⁅x, y₁⁆).1 ≠ 0 ∧ (c.π ⁅x, y₁⁆).2 = 0) ∧
        ∃ y₂ ∈ J, (c.π ⁅x, y₂⁆).1 = 0 ∧ (c.π ⁅x, y₂⁆).2 ≠ 0 := by
      intro x hxQ hxJ
      have hxS := hQS hxQ
      have hsn : ∀ y ∈ J, x * y * x⁻¹ ∈ J := fun y hy => hJn x hxS y hy
      have hsn' : ∀ y ∈ J, x⁻¹ * y * x⁻¹⁻¹ ∈ J := fun y hy => hJn _ (S.inv_mem hxS) y hy
      have hsn'' : ∀ y ∈ J, x⁻¹ * y * x ∈ J := fun y hy => by simpa using hsn' y hy
      have hsn''' : ∀ y ∈ J, x⁻¹⁻¹ * y * x⁻¹ ∈ J := fun y hy => by simpa using hsn y hy
      obtain ⟨gb, Γ, hA⟩ := c.exists_actsAs hsn hsn''
      obtain ⟨gb', Γ', hA'⟩ := c.exists_actsAs hsn' hsn'''
      have hbij := hA.bijective hA' hsn hsn''
      have hcomp := hA.hcomp hsn
      by_cases hxT : x ∈ T
      · have hΓ : ∀ w, (Γ (0, w)).1 = 0 := by
          intro w
          obtain ⟨z, hzJ, hzπ, hzζ⟩ := c.ζ_surj (0, w)
          have hzZ : z ∈ Z := (hZc z hzJ).2 ⟨hzπ, by rw [hzζ]⟩
          have hxz : x * z * x⁻¹ ∈ Z := by
            rw [← (h.cross.T_normZ x hxT).1]
            exact mul_mem_cj x hzZ
          have h1 := ((hZc _ (hsn z hzJ)).1 hxz).2
          rwa [hA.ζ_conj z hzJ hzπ, hzζ] at h1
        obtain ⟨a, b, σ, ha, hb, hform⟩ := isDiagForm_of_axes hcomp
          (hA.axes_diag (h.base.wdiag c hV hV₂ hxT)) hΓ hbij.1
        rcases ringHom_of_card_four hK σ with hσ | hσ
        ·
          exfalso
          obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_one_of_card hK
          obtain ⟨y, hy, hy0⟩ := h.base.faithful c hV hV₂ hxS hxJ
          rw [hA.π_commutator hsn hy] at hy0
          have hgb : ∀ p : GaloisField 2 2 × GaloisField 2 2, gb p = (a * p.1, b * p.2) := by
            intro p
            rw [show p = (p.1, p.2) from rfl, hform, hσ, hσ]
          rw [hgb] at hy0
          have hab : a + 1 ≠ 0 ∨ b + 1 ≠ 0 := by
            by_contra hcon
            push Not at hcon
            apply hy0
            refine Prod.ext ?_ ?_
            · show a * (c.π y).1 + (c.π y).1 = 0
              linear_combination (c.π y).1 * hcon.1
            · show b * (c.π y).2 + (c.π y).2 = 0
              linear_combination (c.π y).2 * hcon.2
          rcases hab with ha1 | hb1
          · obtain ⟨y₁, hy₁, hπ₁⟩ := c.π_surj ((a + 1)⁻¹, 0)
            obtain ⟨y₂, hy₂, hπ₂⟩ := c.π_surj ((a + 1)⁻¹ * ω, 0)
            have e1 : c.π ⁅x, y₁⁆ = (1, 0) := by
              rw [hA.π_commutator hsn hy₁, hπ₁, hgb]
              refine Prod.ext ?_ ?_
              · show a * (a + 1)⁻¹ + (a + 1)⁻¹ = 1
                field_simp
              · show b * 0 + 0 = 0
                ring
            have e2 : c.π ⁅x, y₂⁆ = (ω, 0) := by
              rw [hA.π_commutator hsn hy₂, hπ₂, hgb]
              refine Prod.ext ?_ ?_
              · show a * ((a + 1)⁻¹ * ω) + (a + 1)⁻¹ * ω = ω
                field_simp
              · show b * 0 + 0 = 0
                ring
            refine hz₀Q (ker_mem_of_two_fst c h.base.J_le_S hQnS (hcQJ x hxQ y₁ hy₁)
              (hcQJ x hxQ y₂ hy₂) ?_ ?_ ?_ z₀ hz₀J hz₀π)
            · rw [e1]; exact one_ne_zero
            · rw [e2]; exact hω0
            · rw [e1, e2]; exact fun h => hω1 h.symm
          · obtain ⟨y₁, hy₁, hπ₁⟩ := c.π_surj (0, (b + 1)⁻¹)
            obtain ⟨y₂, hy₂, hπ₂⟩ := c.π_surj (0, (b + 1)⁻¹ * ω)
            have e1 : c.π ⁅x, y₁⁆ = (0, 1) := by
              rw [hA.π_commutator hsn hy₁, hπ₁, hgb]
              refine Prod.ext ?_ ?_
              · show a * 0 + 0 = 0
                ring
              · show b * (b + 1)⁻¹ + (b + 1)⁻¹ = 1
                field_simp
            have e2 : c.π ⁅x, y₂⁆ = (0, ω) := by
              rw [hA.π_commutator hsn hy₂, hπ₂, hgb]
              refine Prod.ext ?_ ?_
              · show a * 0 + 0 = 0
                ring
              · show b * ((b + 1)⁻¹ * ω) + (b + 1)⁻¹ * ω = ω
                field_simp
            refine hz₀Q (ker_mem_of_two_snd c h.base.J_le_S hQnS (hcQJ x hxQ y₁ hy₁)
              (hcQJ x hxQ y₂ hy₂) ?_ ?_ ?_ z₀ hz₀J hz₀π)
            · rw [e1]; exact one_ne_zero
            · rw [e2]; exact hω0
            · rw [e1, e2]; exact fun h => hω1 h.symm
        ·
          have hgb : ∀ p : GaloisField 2 2 × GaloisField 2 2,
              gb p = (a * p.1 ^ 2, b * p.2 ^ 2) := by
            intro p
            rw [show p = (p.1, p.2) from rfl, hform, hσ, hσ]
          refine ⟨?_, ?_, ?_⟩
          ·
            refine h.base.cent_S _ (S.mul_mem hxS hxS) fun j hj => ?_
            have hgg : gb (gb (c.π j)) = c.π j := by
              rw [hgb, hgb]
              refine Prod.ext ?_ ?_
              · show a * (a * (c.π j).1 ^ 2) ^ 2 = (c.π j).1
                calc a * (a * (c.π j).1 ^ 2) ^ 2 = a ^ 3 * (c.π j).1 ^ 4 := by ring
                  _ = (c.π j).1 := by rw [pow_three_of_card hK ha, pow_four_of_card hK, one_mul]
              · show b * (b * (c.π j).2 ^ 2) ^ 2 = (c.π j).2
                calc b * (b * (c.π j).2 ^ 2) ^ 2 = b ^ 3 * (c.π j).2 ^ 4 := by ring
                  _ = (c.π j).2 := by rw [pow_three_of_card hK hb, pow_four_of_card hK, one_mul]
            have e1 : x * x * j * (x * x)⁻¹ = x * (x * j * x⁻¹) * x⁻¹ := by group
            have hc1 : c.π (x * x * j * (x * x)⁻¹) = c.π j := by
              rw [e1, hA.π_conj _ (hsn j hj), hA.π_conj j hj, hgg]
            have hmemJ : x * x * j * (x * x)⁻¹ ∈ J := by
              rw [e1]
              exact hsn _ (hsn j hj)
            have e2 : ⁅x * x, j⁆ = (x * x * j * (x * x)⁻¹) * j⁻¹ := by
              simp [commutatorElement_def, mul_assoc]
            have hπ0 : c.π ⁅x * x, j⁆ = 0 := by
              rw [e2, c.π_mul _ hmemJ _ (J.inv_mem hj), hc1, c.π_inv hj, add_neg_cancel]
            have hmem : ⁅x * x, j⁆ ∈ J := by
              rw [e2]
              exact J.mul_mem hmemJ (J.inv_mem hj)
            exact hkerV _ hmem hπ0
          · obtain ⟨r, hr⟩ := exists_sq_add_ne hK a
            obtain ⟨y₁, hy₁, hπ₁⟩ := c.π_surj (r, 0)
            refine ⟨y₁, hy₁, ?_, ?_⟩
            · rw [hA.π_commutator hsn hy₁, hπ₁, hgb]
              exact hr
            · rw [hA.π_commutator hsn hy₁, hπ₁, hgb]
              show b * 0 ^ 2 + 0 = 0
              ring
          · obtain ⟨s, hs⟩ := exists_sq_add_ne hK b
            obtain ⟨y₂, hy₂, hπ₂⟩ := c.π_surj (0, s)
            refine ⟨y₂, hy₂, ?_, ?_⟩
            · rw [hA.π_commutator hsn hy₂, hπ₂, hgb]
              show a * 0 ^ 2 + 0 = 0
              ring
            · rw [hA.π_commutator hsn hy₂, hπ₂, hgb]
              exact hs
      ·
        exfalso
        have hΓ : ∀ w, (Γ (0, w)).2 = 0 := by
          intro w
          obtain ⟨z, hzJ, hzπ, hzζ⟩ := c.ζ_surj (0, w)
          have hzZ : z ∈ Z := (hZc z hzJ).2 ⟨hzπ, by rw [hzζ]⟩
          have hxz : x * z * x⁻¹ ∈ Z₂ := by
            rw [← (h.cross.swap_Z x hxS hxT).1]
            exact mul_mem_cj x hzZ
          have h1 := ((hZ₂c _ (hsn z hzJ)).1 hxz).2
          rwa [hA.ζ_conj z hzJ hzπ, hzζ] at h1
        have hform := isSwapForm_of_axes hcomp (hA.axes_swap (h.base.wswap c hV hV₂ hxS hxT)) hΓ
          hbij.1
        apply hsmall x hxQ hxJ
        rw [hA.commSet_eq_range hsn]
        exact swap_four hK hform
    have hcos : ∀ x ∈ Q, x ∉ J → ∀ y ∈ Q, y ∉ J → x⁻¹ * y ∈ J := fun x hx hxJ y hy hyJ =>
      inv_mul_mem_of_sq h.base.normal_J h.field.S_cyclic (hQS hx) (hQS hy) hxJ hyJ
        (hstr x hx hxJ).1 (hstr y hy hyJ).1
    have hZQ : ∀ w ∈ qCenter Q, w ∈ J := by
      intro w hw
      by_contra hwJ
      rw [mem_qCenter] at hw
      obtain ⟨-, ⟨y₁, hy₁J, h1, h1'⟩, ⟨y₂, hy₂J, h2, h2'⟩⟩ := hstr w hw.1 hwJ
      have hwS := hQS hw.1
      set a := ⁅w, y₁⁆ with hadef
      have ha := hcQJ w hw.1 y₁ hy₁J
      have hb : ⁅a, y₂⁆ ∈ Q := (hcQJ a ha.1 y₂ hy₂J).1
      have hwa : w * a * w⁻¹ = a := by
        rw [← hw.2 a ha.1, mul_assoc, mul_inv_cancel, mul_one]
      have hwb : w * ⁅a, y₂⁆ * w⁻¹ = ⁅a, y₂⁆ := by
        rw [← hw.2 _ hb, mul_assoc, mul_inv_cancel, mul_one]
      have hwai : w * a⁻¹ * w⁻¹ = a⁻¹ := by
        rw [show w * a⁻¹ * w⁻¹ = (w * a * w⁻¹)⁻¹ by group, hwa]
      have e : w * ⁅a, y₂⁆ * w⁻¹ = ⁅a, w * y₂ * w⁻¹⁆ := by
        calc w * ⁅a, y₂⁆ * w⁻¹ = (w * a * w⁻¹) * (w * y₂ * w⁻¹) * (w * a⁻¹ * w⁻¹) *
              (w * y₂ * w⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
          _ = a * (w * y₂ * w⁻¹) * a⁻¹ * (w * y₂ * w⁻¹)⁻¹ := by rw [hwa, hwai]
          _ = ⁅a, w * y₂ * w⁻¹⁆ := by rw [commutatorElement_def]
      have hwy : w * y₂ * w⁻¹ ∈ J := hJn w hwS y₂ hy₂J
      have e2 : c.ζ ⁅a, y₂⁆ = c.ζ ⁅a, w * y₂ * w⁻¹⁆ := by rw [← e, hwb]
      rw [(c.comm a ha.2 y₂ hy₂J).2, (c.comm a ha.2 _ hwy).2] at e2
      have e3 : c.π (w * y₂ * w⁻¹) = c.π ⁅w, y₂⁆ + c.π y₂ := by
        have : w * y₂ * w⁻¹ = ⁅w, y₂⁆ * y₂ := by simp [commutatorElement_def, mul_assoc]
        rw [this, c.π_mul _ (hcQJ w hw.1 y₂ hy₂J).2 _ hy₂J]
      rw [e3, beta_add_right] at e2
      have e4 : beta (c.π a) (c.π ⁅w, y₂⁆) = 0 := by
        have := congrArg (· - beta (c.π a) (c.π y₂)) e2
        simpa using this.symm
      have e5 := congrArg Prod.fst e4
      simp only [beta, Prod.fst_zero] at e5
      rw [h1', h2, mul_zero, add_zero] at e5
      exact mul_ne_zero h1 h2' e5
    have hz₀V : z₀ ∈ V ⊓ V₂ := hkerV z₀ hz₀J hz₀π
    have hz₀C : z₀ ∈ C := hSC (h.base.J_le_S hz₀J)
    have hcomm5 : ∀ x ∈ Q, ⁅z₀, x⁆ ∈ qCenter Q := by
      intro x hx
      rw [mem_qCenter]
      have hxS := hQS hx
      have hmemQ : ⁅z₀, x⁆ ∈ Q := by
        rw [commutatorElement_def]
        exact Q.mul_mem (hQn z₀ hz₀C x hx) (Q.inv_mem hx)
      have hmemV : ⁅z₀, x⁆ ∈ V ⊓ V₂ := by
        have : ⁅z₀, x⁆ = z₀ * (x * z₀⁻¹ * x⁻¹) := by simp [commutatorElement_def, mul_assoc]
        rw [this]
        exact (V ⊓ V₂).mul_mem hz₀V (h.base.conj_mem_inf hxS ((V ⊓ V₂).inv_mem hz₀V))
      refine ⟨hmemQ, fun y hy => ?_⟩
      by_cases hyJ : y ∈ J
      · exact (hZJc _ hmemV y hyJ).symm
      by_cases hxJ : x ∈ J
      · have : ⁅z₀, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hZJc z₀ hz₀V x hxJ)
        rw [this, one_mul, mul_one]
      have hj := hcos x hx hxJ y hy hyJ
      have hx2 := (hstr x hx hxJ).1
      have hv : x * z₀ * x⁻¹ ∈ V ⊓ V₂ := h.base.conj_mem_inf hxS hz₀V
      have hz₀2 : z₀ * z₀ = 1 := (h.base.elem_V z₀ hz₀V.1 z₀ hz₀V.1).2
      have hv2 : (x * z₀ * x⁻¹) * (x * z₀ * x⁻¹) = 1 := (h.base.elem_V _ hv.1 _ hv.1).2
      have hvz : z₀ * (x * z₀ * x⁻¹) = (x * z₀ * x⁻¹) * z₀ := (h.base.elem_V _ hz₀V.1 _ hv.1).1
      have hz₀i : z₀⁻¹ = z₀ := inv_eq_of_mul_eq_one_right hz₀2
      have hvi : (x * z₀ * x⁻¹)⁻¹ = x * z₀ * x⁻¹ := inv_eq_of_mul_eq_one_right hv2
      have hxxz : (x * x) * z₀⁻¹ = z₀⁻¹ * (x * x) := by
        rw [hz₀i]
        exact (hZJc z₀ hz₀V _ hx2).symm
      have hkey : x * ⁅z₀, x⁆ = ⁅z₀, x⁆ * x := by
        calc x * ⁅z₀, x⁆ = (x * z₀ * x⁻¹) * ((x * x) * z₀⁻¹) * x⁻¹ := by
              simp only [commutatorElement_def]; group
          _ = (x * z₀ * x⁻¹) * (z₀⁻¹ * (x * x)) * x⁻¹ := by rw [hxxz]
          _ = (x * z₀ * x⁻¹) * z₀ * x := by rw [hz₀i]; group
          _ = z₀ * (x * z₀ * x⁻¹) * x := by rw [hvz]
          _ = z₀ * (x * z₀ * x⁻¹)⁻¹ * x := by rw [hvi]
          _ = ⁅z₀, x⁆ * x := by simp only [commutatorElement_def]; group
      have hjc : (x⁻¹ * y) * ⁅z₀, x⁆ = ⁅z₀, x⁆ * (x⁻¹ * y) := (hZJc _ hmemV _ hj).symm
      calc y * ⁅z₀, x⁆ = x * ((x⁻¹ * y) * ⁅z₀, x⁆) := by group
        _ = x * (⁅z₀, x⁆ * (x⁻¹ * y)) := by rw [hjc]
        _ = (x * ⁅z₀, x⁆) * (x⁻¹ * y) := by group
        _ = (⁅z₀, x⁆ * x) * (x⁻¹ * y) := by rw [hkey]
        _ = ⁅z₀, x⁆ * y := by group
    apply hz₀Q
    refine mem_of_stability hQn hQp hcentQ (fun N hNC hCN hNp =>
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNC hCN hNp) hz₀C hcomm5
      fun w hw => hZJc z₀ hz₀V w (hZQ w hw)
  exact h.normalizer_of_le hu hcen hQS hQn fun x hx => hkerQ x (hVJ hx.1) (hVker x hx)

theorem sp4Chain410Two : Sp4Chain410Two :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hloc he => sp4_410_two hloc he

theorem sp4ChainGE3 : Sp4ChainGE3 := sp4ChainGE3_of_410 sp4Chain410GE3

theorem sp4ChainTwo : Sp4ChainTwo := sp4ChainTwo_of_410 sp4Chain410Two

end Main

end CFSG.CGT.PushingUpLit.A78Sp4
