module

public import CFSG.GH74.GLS.Stage4.T9Shape

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T9

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.Stage4.Rest.T6 CFSG.GH74.BNPair
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem t9_triv_of_inv {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (hS6 : S6Shape N4.toCh6)
    {v x : G} (hxP : x ∈ N4.P) (hc : x * v = v * x) (hi : v * x * v⁻¹ = x⁻¹) : x = 1 := by
  have h1 : x = x⁻¹ := by
    rw [← hi]
    calc x = (x * v) * v⁻¹ := by group
      _ = (v * x) * v⁻¹ := by rw [hc]
  have h3 : x * x = 1 := by
    calc x * x = x * x⁻¹ := by rw [← h1]
      _ = 1 := by group
  have hodd := t6_odd_of_pGroup h.prime h.p_ne_two hS6.P_pGroup hxP
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h3)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h4 | h4
  · exact orderOf_eq_one_iff.1 h4
  · rw [h4] at hodd; exact absurd hodd (by decide)

theorem t9_inv_X₁X₂ {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) {v : G}
    (hv₁ : ∀ y ∈ N4.X₁, v * y * v⁻¹ = y⁻¹) (hv₂ : ∀ y ∈ N4.X₂, v * y * v⁻¹ = y⁻¹) :
    ∀ x ∈ N4.X₁ ⊔ N4.X₂, v * x * v⁻¹ = x⁻¹ := by
  intro x hx
  have hX₁K : N4.X₁ ≤ N4.K₁ := X₁_le_K₁ h
  have hX₂K : N4.X₂ ≤ N4.K₂ := by rw [h.sec5.loc.K₂_eq]; exact le_sup_left
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm (fun x hx y hy =>
    h.sec5.loc.K_comm x (hX₁K hx) y (hX₂K hy)) x).1 hx
  have hab : a * b = b * a := h.sec5.loc.K_comm a (hX₁K ha) b (hX₂K hb)
  calc v * (a * b) * v⁻¹ = (v * a * v⁻¹) * (v * b * v⁻¹) := by group
    _ = a⁻¹ * b⁻¹ := by rw [hv₁ a ha, hv₂ b hb]
    _ = (b * a)⁻¹ := by group
    _ = (a * b)⁻¹ := by rw [hab]

theorem t9_zu_inv {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) {y : G}
    (hyK : y ∈ N.K₁ ⊔ N.K₂) (hy : u * y * u⁻¹ = y⁻¹) : (N.z * u) * y * (N.z * u)⁻¹ = y⁻¹ := by
  have hyz : y * N.z = N.z * y := h.zK y hyK
  calc (N.z * u) * y * (N.z * u)⁻¹ = N.z * (u * y * u⁻¹) * N.z⁻¹ := by group
    _ = N.z * y⁻¹ * N.z⁻¹ := by rw [hy]
    _ = (N.z * y * N.z⁻¹)⁻¹ := by group
    _ = y⁻¹ := by
      have : N.z * y * N.z⁻¹ = y := by
        calc N.z * y * N.z⁻¹ = (y * N.z) * N.z⁻¹ := by rw [hyz]
          _ = y := by group
      rw [this]

theorem t9_inter₀₁ {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (hS6 : S6Shape N4.toCh6) {x : G}
    (hx0 : x ∈ Subgroup.centralizer {N4.toT2N3.z} ⊓ N4.P) (hx1 : x ∈ RA N4.toT2N3 N4.p u) : x = 1 := by
  rw [t9_cent_z h hS6] at hx0
  have hxP : x ∈ N4.P := t9_R₂_le_P hS6 hx1.1
  have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.1 hx1.2
  exact t9_triv_of_inv h hS6 hxP hxu (t9_inv_X₁X₂ h h.sec5.loc.u_inv_X₁ h.sec5.loc.u_inv_X₂ x hx0)

theorem t9_inter₀₂ {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (hS6 : S6Shape N4.toCh6) {x : G}
    (hx0 : x ∈ Subgroup.centralizer {N4.toT2N3.z} ⊓ N4.P) (hx2 : x ∈ RB N4.toT2N3 N4.p u) : x = 1 := by
  rw [t9_cent_z h hS6] at hx0
  have hxP : x ∈ N4.P := t9_R₂_le_P hS6 hx2.1
  have hxu : x * (N4.toT2N3.z * u) = (N4.toT2N3.z * u) * x :=
    Subgroup.mem_centralizer_singleton_iff.1 hx2.2
  have hX₂K : N4.X₂ ≤ N4.K₂ := by rw [h.sec5.loc.K₂_eq]; exact le_sup_left
  refine t9_triv_of_inv h hS6 hxP hxu (t9_inv_X₁X₂ h (v := N4.toT2N3.z * u) ?_ ?_ x hx0)
  · intro y hy
    exact t9_zu_inv h (Subgroup.mem_sup_left (X₁_le_K₁ h hy)) (h.sec5.loc.u_inv_X₁ y hy)
  · intro y hy
    exact t9_zu_inv h (Subgroup.mem_sup_right (hX₂K hy)) (h.sec5.loc.u_inv_X₂ y hy)

theorem t9_inter₁₂ {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (hS6 : S6Shape N4.toCh6) {x : G}
    (hx1 : x ∈ RA N4.toT2N3 N4.p u) (hx2 : x ∈ RB N4.toT2N3 N4.p u) : x = 1 := by
  have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.1 hx1.2
  have hxzu : x * (N4.toT2N3.z * u) = (N4.toT2N3.z * u) * x :=
    Subgroup.mem_centralizer_singleton_iff.1 hx2.2
  have hxz : x * N4.toT2N3.z = N4.toT2N3.z * x := by
    calc x * N4.toT2N3.z = (x * (N4.toT2N3.z * u)) * u⁻¹ := by group
      _ = ((N4.toT2N3.z * u) * x) * u⁻¹ := by rw [hxzu]
      _ = N4.toT2N3.z * (u * x) * u⁻¹ := by group
      _ = N4.toT2N3.z * (x * u) * u⁻¹ := by rw [hxu]
      _ = N4.toT2N3.z * x := by group
  exact t9_inter₀₁ h hS6 ⟨Subgroup.mem_centralizer_singleton_iff.2 hxz, t9_R₂_le_P hS6 hx1.1⟩ hx1

def vv (N : T2N3 G) (k : ℕ) : G := (N.a ^ k)⁻¹ * N.z * N.a ^ k

omit [Finite G] in
theorem t9_vv₀ (N : T2N3 G) : vv N 0 = N.z := by simp [vv]

theorem t9_vv₁ {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) : vv N 1 = u := by
  have : N.a⁻¹ * N.z * N.a = u := h.sec5.u_eq
  simpa [vv] using this

theorem t9_vv₂ {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) : vv N 2 = N.z * u := by
  obtain ⟨-, -, e1⟩ := t9_a_facts h
  have : (N.a ^ 2)⁻¹ * N.z * N.a ^ 2 = N.z * u := by
    calc (N.a ^ 2)⁻¹ * N.z * N.a ^ 2 = (N.a ^ 2)⁻¹ * (N.a ^ 2 * (N.z * u) * (N.a ^ 2)⁻¹) * N.a ^ 2 := by
          rw [e1]
      _ = N.z * u := by group
  exact this

theorem t9_CC_inter {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (hS6 : S6Shape N4.toCh6) {k k' : ℕ}
    (hk : k ≤ 2) (hk' : k' ≤ 2) (hne : k ≠ k') {x : G}
    (hx : x ∈ Subgroup.centralizer {vv N4.toT2N3 k} ⊓ N4.P)
    (hx' : x ∈ Subgroup.centralizer {vv N4.toT2N3 k'} ⊓ N4.P) : x = 1 := by
  have e0 := t9_cent_z h hS6
  have e1 := t9_cent_u h hS6
  have e2 := t9_cent_zu h hS6
  interval_cases k <;> interval_cases k'
  · exact absurd rfl hne
  · rw [t9_vv₀] at hx
    rw [t9_vv₁ h] at hx'
    rw [e1] at hx'
    exact t9_inter₀₁ h hS6 hx hx'
  · rw [t9_vv₀] at hx
    rw [t9_vv₂ h, e2] at hx'
    exact t9_inter₀₂ h hS6 hx hx'
  · rw [t9_vv₁ h, e1] at hx
    rw [t9_vv₀] at hx'
    exact t9_inter₀₁ h hS6 hx' hx
  · exact absurd rfl hne
  · rw [t9_vv₁ h, e1] at hx
    rw [t9_vv₂ h, e2] at hx'
    exact t9_inter₁₂ h hS6 hx hx'
  · rw [t9_vv₂ h, e2] at hx
    rw [t9_vv₀] at hx'
    exact t9_inter₀₂ h hS6 hx' hx
  · rw [t9_vv₂ h, e2] at hx
    rw [t9_vv₁ h, e1] at hx'
    exact t9_inter₁₂ h hS6 hx' hx
  · exact absurd rfl hne

def base (N4 : T2N4 G) (t s : Bool) : Subgroup G :=
  if t then (if s then N4.X₂' else N4.X₂) else (if s then N4.X₁' else N4.X₁)

omit [Finite G] in
theorem t9_conjBy_one (A : Subgroup G) : BNPair.conjBy 1 A = A := by
  ext x
  rw [t9_mem_conjBy]
  simp

theorem t9_aH {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) (k : ℕ) {x : G} (hx : x ∈ N.H) :
    (N.a ^ k)⁻¹ * x * N.a ^ k ∈ N.H ∧ N.a ^ k * x * (N.a ^ k)⁻¹ ∈ N.H := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have h1 := (a_normH h ih1).1
    have h2 := (a_normH h ih2).2
    constructor
    · have : (N.a ^ (k + 1))⁻¹ * x * N.a ^ (k + 1) = N.a⁻¹ * ((N.a ^ k)⁻¹ * x * N.a ^ k) * N.a := by
        rw [pow_succ]; group
      rw [this]; exact h1
    · have : N.a ^ (k + 1) * x * (N.a ^ (k + 1))⁻¹ = N.a * (N.a ^ k * x * (N.a ^ k)⁻¹) * N.a⁻¹ := by
        rw [pow_succ']; group
      rw [this]; exact h2

theorem t9_baseH {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (t s : Bool) {x : G} (hx : x ∈ N4.H)
    {y : G} (hy : y ∈ base N4 t s) : x * y * x⁻¹ ∈ base N4 t s := by
  have hloc := h.sec5.loc
  cases t <;> cases s <;> simp only [base, Bool.false_eq_true, ite_false, ite_true] at hy ⊢
  · exact hloc.H_norm_X₁ x hx y hy
  · exact hloc.H_norm_X₁' x hx y hy
  · exact hloc.H_norm_X₂ x hx y hy
  · exact hloc.H_norm_X₂' x hx y hy

theorem t9_conjH {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (k : ℕ) (t s : Bool) {x : G}
    (hx : x ∈ N4.H) {y : G} (hy : y ∈ BNPair.conjBy (N4.a ^ k) (base N4 t s)) :
    x * y * x⁻¹ ∈ BNPair.conjBy (N4.a ^ k) (base N4 t s) := by
  rw [t9_mem_conjBy] at hy ⊢
  have hxH := (t9_aH h k hx).2
  have := t9_baseH h t s hxH hy
  have e : N4.a ^ k * (x * y * x⁻¹) * (N4.a ^ k)⁻¹ =
      (N4.a ^ k * x * (N4.a ^ k)⁻¹) * (N4.a ^ k * y * (N4.a ^ k)⁻¹) * (N4.a ^ k * x * (N4.a ^ k)⁻¹)⁻¹ := by
    group
  rw [e]
  exact this

omit [Finite G] in
theorem t9_hequiv_ker {H A B : Subgroup G} (hA : ∀ x ∈ H, ∀ y ∈ A, x * y * x⁻¹ ∈ A)
    (he : HEquiv H A B) {v : G} (hv : v ∈ H) :
    (∀ y ∈ A, v * y * v⁻¹ = y) ↔ (∀ y ∈ B, v * y * v⁻¹ = y) := by
  obtain ⟨φ, hφ⟩ := he
  constructor
  · intro hcent y' hy'
    obtain ⟨x, hx⟩ := φ.surjective ⟨y', hy'⟩
    have hx' : v * (x : G) * v⁻¹ ∈ A := hA v hv x x.2
    have h1 := hφ v hv x hx'
    have h2 : (⟨v * (x : G) * v⁻¹, hx'⟩ : ↥A) = x := Subtype.ext (hcent x x.2)
    rw [h2, hx] at h1
    exact h1.symm
  · intro hcent x hx
    have hx' : v * x * v⁻¹ ∈ A := hA v hv x hx
    have h1 := hφ v hv ⟨x, hx⟩ hx'
    have h2 := hcent _ (φ ⟨x, hx⟩).2
    have h3 : φ ⟨v * x * v⁻¹, hx'⟩ = φ ⟨x, hx⟩ := Subtype.ext (by rw [h1]; exact h2)
    have := φ.injective h3
    exact congrArg Subtype.val this

theorem t9_base_le_K₁ {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (s : Bool) :
    base N4 false s ≤ N4.K₁ := by
  cases s
  · simp only [base, Bool.false_eq_true, ite_false]; exact X₁_le_K₁ h
  · simp only [base, Bool.false_eq_true, ite_false, ite_true]
    rw [h.sec5.loc.K₁_eq]; exact le_sup_right

theorem t9_base_le_K₂ {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (s : Bool) :
    base N4 true s ≤ N4.K₂ := by
  cases s
  · simp only [base, ite_true, Bool.false_eq_true, ite_false]
    rw [h.sec5.loc.K₂_eq]; exact le_sup_left
  · simp only [base, ite_true]
    rw [h.sec5.loc.K₂_eq]; exact le_sup_right

theorem t9_base_le_K {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (t s : Bool) :
    base N4 t s ≤ N4.K₁ ⊔ N4.K₂ := by
  cases t
  · exact (t9_base_le_K₁ h s).trans le_sup_left
  · exact (t9_base_le_K₂ h s).trans le_sup_right

theorem t9_base_nontriv {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (t s : Bool) :
    ∃ x ∈ base N4 t s, x ≠ 1 := by
  have hloc := h.sec5.loc
  have hq₁ := hloc.q₁_ge
  have hq₂ := hloc.q₂_ge
  by_contra hcon
  push Not at hcon
  have hbot : base N4 t s = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.2 (hcon x hx)
  have hc : Nat.card ↥(base N4 t s) = 1 := by rw [hbot]; exact Subgroup.card_bot
  cases t <;> cases s <;> simp only [base, Bool.false_eq_true, ite_false, ite_true] at hc
  · rw [hloc.card_X₁] at hc; omega
  · rw [hloc.card_X₁'] at hc; omega
  · rw [hloc.card_X₂] at hc; omega
  · rw [hloc.card_X₂'] at hc; omega

theorem t9_vv_mem_H {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) (k : ℕ) : vv N k ∈ N.H :=
  (t9_aH h k h.sec5.loc.z_mem_H).1

theorem t9_vv_cent {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (k : ℕ) (t s : Bool) {y : G}
    (hy : y ∈ BNPair.conjBy (N4.a ^ k) (base N4 t s)) :
    vv N4.toT2N3 k * y * (vv N4.toT2N3 k)⁻¹ = y := by
  rw [t9_mem_conjBy] at hy
  have hyz : (N4.a ^ k * y * (N4.a ^ k)⁻¹) * N4.toT2N3.z = N4.toT2N3.z * (N4.a ^ k * y * (N4.a ^ k)⁻¹) :=
    h.zK _ (t9_base_le_K h t s hy)
  have e : vv N4.toT2N3 k * y * (vv N4.toT2N3 k)⁻¹ =
      (N4.a ^ k)⁻¹ * (N4.toT2N3.z * (N4.a ^ k * y * (N4.a ^ k)⁻¹) * N4.toT2N3.z⁻¹) * N4.a ^ k := by
    simp only [vv]; group
  rw [e]
  have : N4.toT2N3.z * (N4.a ^ k * y * (N4.a ^ k)⁻¹) * N4.toT2N3.z⁻¹ = N4.a ^ k * y * (N4.a ^ k)⁻¹ := by
    calc N4.toT2N3.z * (N4.a ^ k * y * (N4.a ^ k)⁻¹) * N4.toT2N3.z⁻¹
        = ((N4.a ^ k * y * (N4.a ^ k)⁻¹) * N4.toT2N3.z) * N4.toT2N3.z⁻¹ := by rw [hyz]
      _ = N4.a ^ k * y * (N4.a ^ k)⁻¹ := by group
  rw [this]; group

theorem t9_inequiv_gen {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (hS6 : S6Shape N4.toCh6)
    {k k' : ℕ} (hk : k ≤ 2) (hk' : k' ≤ 2) {t t' s s' : Bool}
    (hne : (k, t, s) ≠ (k', t', s'))
    (hP : BNPair.conjBy (N4.a ^ k) (base N4 t s) ≤ N4.P)
    (hP' : BNPair.conjBy (N4.a ^ k') (base N4 t' s') ≤ N4.P) :
    ¬ HEquiv N4.H (BNPair.conjBy (N4.a ^ k) (base N4 t s))
      (BNPair.conjBy (N4.a ^ k') (base N4 t' s')) := by
  intro hE
  have ker : ∀ {v : G}, v ∈ N4.H → ((∀ y ∈ BNPair.conjBy (N4.a ^ k) (base N4 t s), v * y * v⁻¹ = y) ↔
      (∀ y ∈ BNPair.conjBy (N4.a ^ k') (base N4 t' s'), v * y * v⁻¹ = y)) :=
    fun {_} hv => t9_hequiv_ker (fun x hx y hy => t9_conjH h k t s hx hy) hE hv
  have hloc := h.sec5.loc
  by_cases hkk : k = k'
  · subst hkk
    by_cases htt : t = t'
    · subst htt
      have hss : s ≠ s' := fun hs => hne (by rw [hs])
      have hboth : BNPair.conjBy (N4.a ^ k) (base N4 t false) ≤ N4.P ∧
          BNPair.conjBy (N4.a ^ k) (base N4 t true) ≤ N4.P := by
        cases s <;> cases s'
        · exact absurd rfl hss
        · exact ⟨hP, hP'⟩
        · exact ⟨hP', hP⟩
        · exact absurd rfl hss
      have hz : N4.toT2N3.z ∈ base N4 t false ⊔ base N4 t true := by
        cases t
        · have e : base N4 false false ⊔ base N4 false true = N4.K₁ := by
            simp only [base, Bool.false_eq_true, ite_false, ite_true]
            exact hloc.K₁_eq.symm
          rw [e]; exact hloc.z_mem_K₁
        · have e : base N4 true false ⊔ base N4 true true = N4.K₂ := by
            simp only [base, Bool.false_eq_true, ite_false, ite_true]
            exact hloc.K₂_eq.symm
          rw [e]; exact hloc.z_mem_K₂
      have hz' : (N4.a ^ k)⁻¹ * N4.toT2N3.z * N4.a ^ k ∈ N4.P := by
        have hmem : (N4.a ^ k)⁻¹ * N4.toT2N3.z * N4.a ^ k ∈
            BNPair.conjBy (N4.a ^ k) (base N4 t false ⊔ base N4 t true) := by
          rw [t9_mem_conjBy]
          have : N4.a ^ k * ((N4.a ^ k)⁻¹ * N4.toT2N3.z * N4.a ^ k) * (N4.a ^ k)⁻¹ = N4.toT2N3.z := by
            group
          rw [this]; exact hz
        have hle : BNPair.conjBy (N4.a ^ k) (base N4 t false ⊔ base N4 t true) ≤ N4.P := by
          unfold BNPair.conjBy
          rw [Subgroup.map_sup]
          exact sup_le hboth.1 hboth.2
        exact hle hmem
      have hz2 : N4.toT2N3.z * N4.toT2N3.z = 1 := h.ctx.zz
      have hsq : ((N4.a ^ k)⁻¹ * N4.toT2N3.z * N4.a ^ k) * ((N4.a ^ k)⁻¹ * N4.toT2N3.z * N4.a ^ k) = 1 := by
        calc ((N4.a ^ k)⁻¹ * N4.toT2N3.z * N4.a ^ k) * ((N4.a ^ k)⁻¹ * N4.toT2N3.z * N4.a ^ k)
            = (N4.a ^ k)⁻¹ * (N4.toT2N3.z * N4.toT2N3.z) * N4.a ^ k := by group
          _ = 1 := by rw [hz2]; group
      have hinv : ((N4.a ^ k)⁻¹ * N4.toT2N3.z * N4.a ^ k)⁻¹ = (N4.a ^ k)⁻¹ * N4.toT2N3.z * N4.a ^ k :=
        inv_eq_of_mul_eq_one_right hsq
      have hz1 := t9_triv_of_inv h hS6 (v := (N4.a ^ k)⁻¹ * N4.toT2N3.z * N4.a ^ k) hz' rfl (by
        calc ((N4.a ^ k)⁻¹ * N4.toT2N3.z * N4.a ^ k) * ((N4.a ^ k)⁻¹ * N4.toT2N3.z * N4.a ^ k) *
            ((N4.a ^ k)⁻¹ * N4.toT2N3.z * N4.a ^ k)⁻¹ = (N4.a ^ k)⁻¹ * N4.toT2N3.z * N4.a ^ k := by group
          _ = ((N4.a ^ k)⁻¹ * N4.toT2N3.z * N4.a ^ k)⁻¹ := hinv.symm)
      have : N4.toT2N3.z = 1 := by
        have : N4.a ^ k * ((N4.a ^ k)⁻¹ * N4.toT2N3.z * N4.a ^ k) * (N4.a ^ k)⁻¹ = N4.toT2N3.z := by group
        rw [← this, hz1]; group
      exact h.ctx.z_ne this
    ·
      obtain ⟨h₁, hh₁, hh₁z⟩ : ∃ h₁ ∈ N4.H ⊓ N4.K₁, h₁ ∉ Subgroup.zpowers N4.toT2N3.z := by
        by_contra hcon
        push Not at hcon
        have hle : N4.H ⊓ N4.K₁ ≤ Subgroup.zpowers N4.toT2N3.z := fun x hx => hcon x hx
        have h1 := Subgroup.card_le_of_le hle
        rw [hloc.card_H_K₁, Nat.card_zpowers, hloc.z_ord] at h1
        have := hloc.q₁_ge
        omega
      set v : G := (N4.a ^ k)⁻¹ * h₁ * N4.a ^ k with hv
      have hvH : v ∈ N4.H := (t9_aH h k hh₁.1).1
      have hcentK₂ : ∀ s₀ : Bool, ∀ y ∈ BNPair.conjBy (N4.a ^ k) (base N4 true s₀), v * y * v⁻¹ = y := by
        intro s₀ y hy
        rw [t9_mem_conjBy] at hy
        have hc : h₁ * (N4.a ^ k * y * (N4.a ^ k)⁻¹) = (N4.a ^ k * y * (N4.a ^ k)⁻¹) * h₁ :=
          hloc.K_comm h₁ hh₁.2 _ (t9_base_le_K₂ h s₀ hy)
        calc v * y * v⁻¹ = (N4.a ^ k)⁻¹ * (h₁ * (N4.a ^ k * y * (N4.a ^ k)⁻¹) * h₁⁻¹) * N4.a ^ k := by
              rw [hv]; group
          _ = (N4.a ^ k)⁻¹ * ((N4.a ^ k * y * (N4.a ^ k)⁻¹) * h₁ * h₁⁻¹) * N4.a ^ k := by rw [hc]
          _ = y := by group
      have hncentK₁ : ∀ s₀ : Bool, ¬ ∀ y ∈ BNPair.conjBy (N4.a ^ k) (base N4 false s₀), v * y * v⁻¹ = y := by
        intro s₀ hall
        obtain ⟨x₀, hx₀, hx₀1⟩ := t9_base_nontriv h false s₀
        have hy : (N4.a ^ k)⁻¹ * x₀ * N4.a ^ k ∈ BNPair.conjBy (N4.a ^ k) (base N4 false s₀) := by
          rw [t9_mem_conjBy]
          have : N4.a ^ k * ((N4.a ^ k)⁻¹ * x₀ * N4.a ^ k) * (N4.a ^ k)⁻¹ = x₀ := by group
          rw [this]; exact hx₀
        have h1 := hall _ hy
        have h2 : h₁ * x₀ * h₁⁻¹ = x₀ := by
          have : (N4.a ^ k)⁻¹ * (h₁ * x₀ * h₁⁻¹) * N4.a ^ k = (N4.a ^ k)⁻¹ * x₀ * N4.a ^ k := by
            rw [← h1, hv]; group
          have h3 := congrArg (fun w => N4.a ^ k * w * (N4.a ^ k)⁻¹) this
          simpa using h3
        have hfpf : h₁ * x₀ * h₁⁻¹ = x₀ → x₀ = 1 := by
          cases s₀
          · exact hloc.H_fpf₁ h₁ hh₁ hh₁z x₀ hx₀
          · exact hloc.H_fpf₁' h₁ hh₁ hh₁z x₀ hx₀
        exact hx₀1 (hfpf h2)
      cases t <;> cases t'
      · exact absurd rfl htt
      ·
        exact hncentK₁ s ((ker hvH).2 (hcentK₂ s'))
      · exact hncentK₁ s' ((ker hvH).1 (hcentK₂ s))
      · exact absurd rfl htt
  ·
    obtain ⟨y', hy'mem, hy'1⟩ := t9_base_nontriv h t' s'
    let y₁ : G := (N4.a ^ k')⁻¹ * y' * N4.a ^ k'
    have hy₁ : y₁ ∈ BNPair.conjBy (N4.a ^ k') (base N4 t' s') := by
      rw [t9_mem_conjBy]
      have : N4.a ^ k' * ((N4.a ^ k')⁻¹ * y' * N4.a ^ k') * (N4.a ^ k')⁻¹ = y' := by group
      rw [this]; exact hy'mem
    have hy₁1 : y₁ ≠ 1 := by
      intro h1
      apply hy'1
      have : y' = N4.a ^ k' * y₁ * (N4.a ^ k')⁻¹ := by simp only [y₁]; group
      rw [this, h1]; group
    have hcent : ∀ y ∈ BNPair.conjBy (N4.a ^ k') (base N4 t' s'),
        vv N4.toT2N3 k * y * (vv N4.toT2N3 k)⁻¹ = y := (ker (t9_vv_mem_H h k)).1
          (fun y hy => t9_vv_cent h k t s hy)
    have h1 : y₁ ∈ Subgroup.centralizer {vv N4.toT2N3 k} ⊓ N4.P := by
      refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, hP' hy₁⟩
      have := hcent y₁ hy₁
      calc y₁ * vv N4.toT2N3 k = (vv N4.toT2N3 k * y₁ * (vv N4.toT2N3 k)⁻¹) * vv N4.toT2N3 k := by rw [this]
        _ = vv N4.toT2N3 k * y₁ := by group
    have h2 : y₁ ∈ Subgroup.centralizer {vv N4.toT2N3 k'} ⊓ N4.P := by
      refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, hP' hy₁⟩
      have := t9_vv_cent h k' t' s' hy₁
      calc y₁ * vv N4.toT2N3 k' = (vv N4.toT2N3 k' * y₁ * (vv N4.toT2N3 k')⁻¹) * vv N4.toT2N3 k' := by rw [this]
        _ = vv N4.toT2N3 k' * y₁ := by group
    exact hy₁1 (t9_CC_inter h hS6 hk hk' hkk h1 h2)

def tri (i : ℤ) : ℕ × Bool × Bool :=
  if i = 1 then (0, false, false) else if i = 2 then (2, true, true) else
  if i = 3 then (1, false, true) else if i = 4 then (0, true, false) else
  if i = 5 then (2, false, false) else if i = 6 then (1, true, true) else
  if i = -1 then (0, false, true) else if i = -2 then (2, true, false) else
  if i = -3 then (1, false, false) else if i = -4 then (0, true, true) else
  if i = -5 then (2, false, true) else if i = -6 then (1, true, false) else (0, false, false)

theorem t9_tri_le {i : ℤ} (hi : IsRoot 6 i) : (tri i).1 ≤ 2 := by
  obtain ⟨hi0, hi6⟩ := hi
  have hi1 : -6 ≤ i := by omega
  have hi2 : i ≤ 6 := by omega
  interval_cases i <;> first | exact absurd rfl hi0 | decide

theorem t9_tri_inj {i j : ℤ} (hi : IsRoot 6 i) (hj : IsRoot 6 j) (hij : i ≠ j) : tri i ≠ tri j := by
  obtain ⟨hi0, hi6⟩ := hi
  obtain ⟨hj0, hj6⟩ := hj
  have hi1 : -6 ≤ i := by omega
  have hi2 : i ≤ 6 := by omega
  have hj1 : -6 ≤ j := by omega
  have hj2 : j ≤ 6 := by omega
  interval_cases i <;> interval_cases j <;>
    first | exact absurd rfl hij | exact absurd rfl hi0 | exact absurd rfl hj0 | decide

omit [Finite G] in
theorem t9_root_eq (N4 : T2N4 G) {i : ℤ} (hi : IsRoot 6 i) :
    N4.toCh6.root i = BNPair.conjBy (N4.a ^ (tri i).1) (base N4 (tri i).2.1 (tri i).2.2) := by
  obtain ⟨hi0, hi6⟩ := hi
  have hi1 : -6 ≤ i := by omega
  have hi2 : i ≤ 6 := by omega
  interval_cases i <;> first | exact absurd rfl hi0 | (simp [Ch6Notation.root, tri, base, t9_conjBy_one]; rfl)

theorem t9_inequiv {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (hS6 : S6Shape N4.toCh6) :
    ∀ i j : ℤ, IsRoot 6 i → IsRoot 6 j → N4.toCh6.root i ≤ N4.toCh6.P → N4.toCh6.root j ≤ N4.toCh6.P →
      i ≠ j → ¬ HEquiv N4.toCh6.H (N4.toCh6.root i) (N4.toCh6.root j) := by
  intro i j hi hj hPi hPj hij
  have e1 := t9_root_eq N4 hi
  have e2 := t9_root_eq N4 hj
  rw [e1] at hPi ⊢
  rw [e2] at hPj ⊢
  exact t9_inequiv_gen h hS6 (t9_tri_le hi) (t9_tri_le hj) (t9_tri_inj hi hj hij) hPi hPj

theorem t9_cent_of_conj {N : T2N3 G} {u : G} {p : ℕ} (h : T6Ctx N u p) (g : G) {A : Subgroup G}
    (hA : A ≤ N.K₁ ⊔ N.K₂) {s : G} (hs : s ∈ BNPair.conjBy g A) :
    s * (g⁻¹ * N.z * g) = (g⁻¹ * N.z * g) * s := by
  rw [t9_mem_conjBy] at hs
  have hsz : (g * s * g⁻¹) * N.z = N.z * (g * s * g⁻¹) := h.zK _ (hA hs)
  calc s * (g⁻¹ * N.z * g) = g⁻¹ * ((g * s * g⁻¹) * N.z) * g := by group
    _ = g⁻¹ * (N.z * (g * s * g⁻¹)) * g := by rw [hsz]
    _ = (g⁻¹ * N.z * g) * s := by group

omit [Finite G] in
theorem t9_factor_mem_P {N4 : T2N4 G} {α β γ δ : Bool} (hsh : N4.toCh6.Shape α β γ δ) :
    (∀ x ∈ BNPair.conjBy N4.a (if α then N4.X₁' else N4.X₁), x ∈ N4.P) ∧
    (∀ x ∈ BNPair.conjBy N4.a (if β then N4.X₂' else N4.X₂), x ∈ N4.P) ∧
    (∀ x ∈ BNPair.conjBy (N4.a ^ 2) (if γ then N4.X₁' else N4.X₁), x ∈ N4.P) ∧
    (∀ x ∈ BNPair.conjBy (N4.a ^ 2) (if δ then N4.X₂' else N4.X₂), x ∈ N4.P) := by
  have hSh : (N4.P : Set G) = (N4.X₁ : Set G) * (N4.X₂ : Set G) *
      (BNPair.conjBy N4.a (if α then N4.X₁' else N4.X₁) : Set G) *
      (BNPair.conjBy N4.a (if β then N4.X₂' else N4.X₂) : Set G) *
      (BNPair.conjBy (N4.a ^ 2) (if γ then N4.X₁' else N4.X₁) : Set G) *
      (BNPair.conjBy (N4.a ^ 2) (if δ then N4.X₂' else N4.X₂) : Set G) := hsh
  have o : ∀ A : Subgroup G, (1 : G) ∈ (A : Set G) := fun A => A.one_mem
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have : x ∈ (N4.P : Set G) := by
      rw [hSh]
      have e : x = 1 * 1 * x * 1 * 1 * 1 := by simp
      rw [e]
      exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul
        (o _) (o _)) hx) (o _)) (o _)) (o _)
    exact this
  · have : x ∈ (N4.P : Set G) := by
      rw [hSh]
      have e : x = 1 * 1 * 1 * x * 1 * 1 := by simp
      rw [e]
      exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul
        (o _) (o _)) (o _)) hx) (o _)) (o _)
    exact this
  · have : x ∈ (N4.P : Set G) := by
      rw [hSh]
      have e : x = 1 * 1 * 1 * 1 * x * 1 := by simp
      rw [e]
      exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul
        (o _) (o _)) (o _)) (o _)) hx) (o _)
    exact this
  · have : x ∈ (N4.P : Set G) := by
      rw [hSh]
      have e : x = 1 * 1 * 1 * 1 * 1 * x := by simp
      rw [e]
      exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul
        (o _) (o _)) (o _)) (o _)) (o _)) hx
    exact this

theorem t9_comm_R {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (hS6 : S6Shape N4.toCh6) :
    ∀ α β γ δ : Bool, N4.toCh6.Shape α β γ δ → ∀ S₁ ∈ N4.toCh6.Rfac α β γ δ,
      ∀ S₂ ∈ N4.toCh6.Rfac α β γ δ, ∀ x ∈ S₁, ∀ y ∈ S₂, ⁅x, y⁆ ∈ N4.toCh6.X₂ := by
  intro α β γ δ hsh
  obtain ⟨hP1, hP2, hP3, hP4⟩ := t9_factor_mem_P hsh
  have hu : N4.a⁻¹ * N4.toT2N3.z * N4.a = u := h.sec5.u_eq
  have hzu : (N4.a ^ 2)⁻¹ * N4.toT2N3.z * N4.a ^ 2 = N4.toT2N3.z * u := t9_vv₂ h
  have hA1 : (if α then N4.X₁' else N4.X₁) ≤ N4.K₁ ⊔ N4.K₂ := (t9_A_le h α).trans le_sup_left
  have hB1 : (if β then N4.X₂' else N4.X₂) ≤ N4.K₁ ⊔ N4.K₂ := (t9_B_le h β).trans le_sup_right
  have hA2 : (if γ then N4.X₁' else N4.X₁) ≤ N4.K₁ ⊔ N4.K₂ := (t9_A_le h γ).trans le_sup_left
  have hB2 : (if δ then N4.X₂' else N4.X₂) ≤ N4.K₁ ⊔ N4.K₂ := (t9_B_le h δ).trans le_sup_right
  have hfac : ∀ S ∈ N4.toCh6.Rfac α β γ δ, ∀ x ∈ S, x ∈ R₂ N4.toT2N3 N4.p := by
    intro S hS x hx
    simp only [Ch6Notation.Rfac, Set.mem_insert_iff, Set.mem_singleton_iff] at hS
    have hRA : ∀ x ∈ Subgroup.centralizer {u} ⊓ N4.P, x ∈ R₂ N4.toT2N3 N4.p := fun x hx => by
      rw [t9_cent_u h hS6] at hx; exact hx.1
    have hRB : ∀ x ∈ Subgroup.centralizer {N4.toT2N3.z * u} ⊓ N4.P, x ∈ R₂ N4.toT2N3 N4.p := fun x hx => by
      rw [t9_cent_zu h hS6] at hx; exact hx.1
    rcases hS with rfl | rfl | rfl | rfl
    · refine hRA x ⟨?_, hP1 x hx⟩
      have := t9_cent_of_conj h N4.a hA1 hx
      rw [hu] at this
      exact Subgroup.mem_centralizer_singleton_iff.2 this
    · refine hRA x ⟨?_, hP2 x hx⟩
      have := t9_cent_of_conj h N4.a hB1 hx
      rw [hu] at this
      exact Subgroup.mem_centralizer_singleton_iff.2 this
    · refine hRB x ⟨?_, hP3 x hx⟩
      have := t9_cent_of_conj h (N4.a ^ 2) hA2 hx
      rw [hzu] at this
      exact Subgroup.mem_centralizer_singleton_iff.2 this
    · refine hRB x ⟨?_, hP4 x hx⟩
      have := t9_cent_of_conj h (N4.a ^ 2) hB2 hx
      rw [hzu] at this
      exact Subgroup.mem_centralizer_singleton_iff.2 this
  intro S₁ hS₁ S₂ hS₂ x hx y hy
  exact hS6.R₂_comm x (hfac S₁ hS₁ x hx) y (hfac S₂ hS₂ y hy)

theorem t9_shape_core {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (hS6 : S6Shape N4.toCh6) :
    Ch6Shape N4.toCh6 := by
  obtain ⟨α, β, hRA⟩ := t9_RA_shape h hS6
  obtain ⟨γ, δ, hRB⟩ := t9_RB_shape h hS6
  have hsh := t9_shape_set h hS6 hRA hRB
  have hu : N4.a⁻¹ * N4.toT2N3.z * N4.a = u := h.sec5.u_eq
  refine ⟨⟨α, β, γ, δ, hsh, ?_, ?_, ?_⟩, t9_inequiv h hS6, t9_comm_R h hS6⟩
  · exact t9_cent_z h hS6
  · show Subgroup.centralizer {N4.a⁻¹ * N4.toT2N3.z * N4.a} ⊓ N4.P = _
    rw [hu, t9_cent_u h hS6, hRA]
    rfl
  · show Subgroup.centralizer {N4.toT2N3.z * (N4.a⁻¹ * N4.toT2N3.z * N4.a)} ⊓ N4.P = _
    rw [hu, t9_cent_zu h hS6, hRB]
    rfl

theorem t9_shape {N4 : T2N4 G} {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (hS6 : Ch6S6 N4.toCh6) :
    Ch6Shape N4.toCh6 :=
  t9_shape_core h hS6.toShape

end CFSG.GH74.GLS.Stage4.Rest.T9
