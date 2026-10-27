module

public import CFSG.ClassicalInvolution.SolvableCase.SL2Three

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc

open scoped MatrixGroups

private theorem sl2lc_pow8 : ∀ g : SL(2, ZMod 3), g ^ 8 = 1 → g ^ 4 = 1 := by
  decide +kernel

private theorem sl2lc_decomp :
    ∃ a : SL(2, ZMod 3), a ^ 3 = 1 ∧
      ∀ l : SL(2, ZMod 3), ∃ k : SL(2, ZMod 3), k ^ 4 = 1 ∧ ∃ i < 3, l = k * a ^ i := by
  decide +kernel

private theorem sl2lc_central :
    ∀ c : SL(2, ZMod 3), (∀ k : SL(2, ZMod 3), k ^ 4 = 1 → c * k = k * c) →
      c * c = 1 ∧ ∀ l : SL(2, ZMod 3), c * l = l * c := by
  decide +kernel

private theorem sl2lc_mem_iff {G : Type*} [Group G] {Λ K : Subgroup G}
    (e : ↥Λ ≃* SL(2, ZMod 3)) (hKΛ : K ≤ Λ) (h8 : Nat.card ↥K = 8) (u : ↥Λ) :
    (u : G) ∈ K ↔ e u ^ 4 = 1 := by
  set Q : Subgroup SL(2, ZMod 3) := (K.subgroupOf Λ).map e.toMonoidHom with hQdef
  have hcardQ : Nat.card Q = 8 := by
    rw [hQdef, Subgroup.card_map_of_injective e.injective, ← h8]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKΛ).toEquiv
  have hle : Q ≤ sl2ThreeQ := by
    intro s hs
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hs
    have hyK : (y : G) ∈ K := hy
    have h1 : (⟨y, hyK⟩ : ↥K) ^ 8 = 1 := by
      have := pow_card_eq_one' (x := (⟨y, hyK⟩ : ↥K))
      rwa [h8] at this
    have h2 : y ^ 8 = 1 := by
      apply Subtype.ext
      simpa using congrArg (fun z : ↥K => (z : G)) h1
    rw [mem_sl2ThreeQ_iff]
    show (e y) ^ 4 = 1
    apply sl2lc_pow8
    rw [← map_pow, h2, map_one]
  have hQeq : Q = sl2ThreeQ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [natCard_sl2ThreeQ, hcardQ])
  constructor
  · intro hu
    have : e u ∈ Q := Subgroup.mem_map.2 ⟨u, hu, rfl⟩
    rw [hQeq] at this
    exact mem_sl2ThreeQ_iff.1 this
  · intro h4
    have : e u ∈ Q := by rw [hQeq]; exact mem_sl2ThreeQ_iff.2 h4
    obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.1 this
    have : y = u := e.injective hyu
    subst this
    exact hy

theorem sl2_facts {G : Type*} [Group G] {Λ K : Subgroup G} (e : ↥Λ ≃* SL(2, ZMod 3))
    (hKΛ : K ≤ Λ) (h8 : Nat.card ↥K = 8) :
    (∀ l ∈ Λ, ∀ k ∈ K, l * k * l⁻¹ ∈ K) ∧
    (∃ a ∈ Λ, a ^ 3 = 1 ∧ ∀ l ∈ Λ, ∃ k ∈ K, ∃ i : ℕ, l = k * a ^ i) ∧
    (∀ c ∈ Λ, (∀ k ∈ K, c * k = k * c) → c * c = 1 ∧ ∀ l ∈ Λ, c * l = l * c) := by
  have hK := sl2lc_mem_iff e hKΛ h8
  obtain ⟨a₀, ha₀, hdec⟩ := sl2lc_decomp
  refine ⟨?_, ⟨(e.symm a₀ : G), (e.symm a₀).2, ?_, ?_⟩, ?_⟩
  · intro l hl k hk
    have hk4 : (e ⟨k, hKΛ hk⟩) ^ 4 = 1 := (hK ⟨k, hKΛ hk⟩).1 hk
    refine (hK (⟨l, hl⟩ * ⟨k, hKΛ hk⟩ * ⟨l, hl⟩⁻¹)).2 ?_
    rw [map_mul, map_mul, map_inv]
    exact mem_sl2ThreeQ_iff.1 (sl2ThreeQ_normal.conj_mem _ (mem_sl2ThreeQ_iff.2 hk4) _)
  · have h : (e.symm a₀) ^ 3 = 1 := by rw [← map_pow, ha₀, map_one]
    simpa using congrArg (fun u : ↥Λ => (u : G)) h
  · intro l hl
    obtain ⟨k₀, hk₀, i, -, hli⟩ := hdec (e ⟨l, hl⟩)
    refine ⟨(e.symm k₀ : G), (hK (e.symm k₀)).2 (by simpa using hk₀), i, ?_⟩
    have h : (⟨l, hl⟩ : ↥Λ) = e.symm k₀ * (e.symm a₀) ^ i := by
      apply e.injective
      rw [map_mul, map_pow, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, ← hli]
    simpa using congrArg (fun u : ↥Λ => (u : G)) h
  · intro c hc hck
    have h1 : ∀ k₀ : SL(2, ZMod 3), k₀ ^ 4 = 1 → e ⟨c, hc⟩ * k₀ = k₀ * e ⟨c, hc⟩ := by
      intro k₀ hk₀
      have hkK : ((e.symm k₀ : ↥Λ) : G) ∈ K := (hK (e.symm k₀)).2 (by simpa using hk₀)
      have h' : (⟨c, hc⟩ : ↥Λ) * e.symm k₀ = e.symm k₀ * ⟨c, hc⟩ := Subtype.ext (hck _ hkK)
      simpa using congrArg e h'
    obtain ⟨h2, h3⟩ := sl2lc_central _ h1
    refine ⟨?_, ?_⟩
    · have h4 : (⟨c, hc⟩ : ↥Λ) * ⟨c, hc⟩ = 1 := e.injective (by rw [map_mul, h2, map_one])
      simpa using congrArg (fun u : ↥Λ => (u : G)) h4
    · intro l hl
      have h4 : (⟨c, hc⟩ : ↥Λ) * ⟨l, hl⟩ = ⟨l, hl⟩ * ⟨c, hc⟩ :=
        e.injective (by rw [map_mul, map_mul]; exact h3 _)
      exact congrArg Subtype.val h4

theorem centralizes_of_normalizes {G : Type*} [Group G] {Λ K : Subgroup G}
    (e : ↥Λ ≃* SL(2, ZMod 3)) (hKΛ : K ≤ Λ) (h8 : Nat.card ↥K = 8) {x : G}
    (hx : ∀ l ∈ Λ, x * l * x⁻¹ ∈ Λ) (hxK : ∀ k ∈ K, x * k = k * x) :
    ∀ l ∈ Λ, x * l = l * x := by
  obtain ⟨hKn, ⟨a, haΛ, ha3, hdec⟩, hcent⟩ := sl2_facts e hKΛ h8
  have hcΛ : x * a * x⁻¹ * a⁻¹ ∈ Λ := Λ.mul_mem (hx a haΛ) (Λ.inv_mem haΛ)
  have hck : ∀ k ∈ K, (x * a * x⁻¹ * a⁻¹) * k = k * (x * a * x⁻¹ * a⁻¹) := by
    intro k hk
    have hk' : a⁻¹ * k * a ∈ K := by simpa using hKn a⁻¹ (Λ.inv_mem haΛ) k hk
    have h1 : x⁻¹ * (a⁻¹ * k * a) = (a⁻¹ * k * a) * x⁻¹ :=
      ((Commute.inv_left (hxK _ hk') : Commute x⁻¹ _)).eq
    calc x * a * x⁻¹ * a⁻¹ * k
        = x * a * (x⁻¹ * (a⁻¹ * k * a)) * a⁻¹ := by group
      _ = x * a * ((a⁻¹ * k * a) * x⁻¹) * a⁻¹ := by rw [h1]
      _ = x * k * a * x⁻¹ * a⁻¹ := by group
      _ = k * x * a * x⁻¹ * a⁻¹ := by rw [hxK k hk]
      _ = k * (x * a * x⁻¹ * a⁻¹) := by group
  obtain ⟨hc2, hcl⟩ := hcent _ hcΛ hck
  have hcomm : Commute (x * a * x⁻¹ * a⁻¹) a := hcl a haΛ
  have h1 : x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹) * a := by group
  have h2 : (x * a * x⁻¹) ^ 3 = 1 := by
    rw [conj_pow, ha3]; group
  have h3 : ((x * a * x⁻¹ * a⁻¹) * a) ^ 3 = x * a * x⁻¹ * a⁻¹ := by
    rw [hcomm.mul_pow, ha3, pow_succ, sq, hc2, one_mul, mul_one]
  have hc1 : x * a * x⁻¹ * a⁻¹ = 1 := by
    rw [← h3, ← h1, h2]
  have hxa : Commute x a := by
    have : x * a * x⁻¹ = a := mul_inv_eq_one.1 hc1
    exact mul_inv_eq_iff_eq_mul.1 this
  intro l hl
  obtain ⟨k, hk, i, rfl⟩ := hdec l hl
  have hxk : Commute x k := hxK k hk
  exact (hxk.mul_right (hxa.pow_right i)).eq

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc
