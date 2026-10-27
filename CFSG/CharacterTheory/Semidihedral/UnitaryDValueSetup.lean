module

public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterBasis

public section

namespace CFSG.Semidihedral.UnitaryDValue

open CFSG.TwoRankLowerBound.Helpers

structure DValueData (G : Type) [Group G] [Fintype G] where
  p : ℕ
  f : ℕ
  m : ℕ
  x : G
  z : G
  y : G
  t : G
  A : Subgroup G
  W : Subgroup G
  S : Sylow 2 G
  prime_p : p.Prime
  ne_two : p ≠ 2
  one_le_f : 1 ≤ f
  five_lt_q : 5 < p ^ f
  m_pow : ∃ k : ℕ, m = 2 ^ k
  m_dvd : m ∣ p ^ f + 1
  odd_quot : Odd ((p ^ f + 1) / m)
  index_ne_two : ∀ H : Subgroup G, H.index ≠ 2
  x_order : orderOf x = 2
  involution_conj : ∀ i : G, orderOf i = 2 → IsConj i x
  z_order : orderOf z = 2
  z_comm : x * z = z * x
  z_ne : z ≠ x
  A_le : A ≤ Subgroup.centralizer {x}
  A_central : ∀ a ∈ A, ∀ g ∈ Subgroup.centralizer ({x} : Set G), g * a = a * g
  A_cyclic : IsCyclic A
  A_odd : Odd (Nat.card A)
  A_dvd : m * Nat.card A ∣ p ^ f + 1
  A_confine : ∀ r ∈ A, r ≠ 1 → Subgroup.centralizer {r} ≤ Subgroup.centralizer {x}
  card_G : Nat.card G = m * Nat.card A * (p ^ f) ^ 3 * (p ^ f - 1) * ((p ^ f) ^ 3 + 1)
  card_N : Nat.card (Subgroup.centralizer ({x} : Set G)) =
    m * Nat.card A * (p ^ f * ((p ^ f) ^ 2 - 1))
  card_C : Nat.card (Subgroup.centralizer {x} ⊓ Subgroup.centralizer {z} : Subgroup G) =
    m * Nat.card A * (p ^ f + 1)
  C_comm : ∀ a ∈ Subgroup.centralizer {x} ⊓ Subgroup.centralizer {z},
    ∀ b ∈ Subgroup.centralizer {x} ⊓ Subgroup.centralizer {z}, a * b = b * a
  C_involutions : ∀ c ∈ Subgroup.centralizer {x} ⊓ Subgroup.centralizer {z}, c * c = 1 →
    c = 1 ∨ c = x ∨ c = z ∨ c = x * z
  W_cyclic : IsCyclic W
  W_card : m * Nat.card W = p ^ f + 1
  W_le : W ≤ Subgroup.centralizer {x} ⊓ Subgroup.centralizer {z}
  W_inf_A : W ⊓ A = ⊥
  y_comm : x * y = y * x
  y_z : y * z * y⁻¹ = x * z
  y_W : ∀ w ∈ W, y * w * y⁻¹ = w⁻¹
  t_x : t * x * t⁻¹ = z
  t_z : t * z * t⁻¹ = x * z
  S_le : (S : Subgroup G) ≤ Subgroup.centralizer {x}
  W_centralizer : ∀ w ∈ W, w ≠ 1 →
    Subgroup.centralizer {x} ⊓ Subgroup.centralizer {w} ≤ Subgroup.centralizer {z}
  real_odd_degree : ∀ (basis : FiniteIrreducibleCharacterBasis G) (χ : basis.index),
    (∀ g, starRingEnd ℂ ((basis.representation χ).character g) =
      (basis.representation χ).character g) →
    Odd (Module.finrank ℂ (basis.representation χ).vector) →
    Module.finrank ℂ (basis.representation χ).vector = 1 ∨
    Module.finrank ℂ (basis.representation χ).vector = (p ^ f) ^ 3 ∨
    Module.finrank ℂ (basis.representation χ).vector = (p ^ f) ^ 2 - p ^ f + 1 ∨
    Module.finrank ℂ (basis.representation χ).vector = p ^ f * ((p ^ f) ^ 2 - p ^ f + 1)

section General

variable {G : Type*} [Group G]

theorem eq_of_conj_eq {g a b : G} (h : g * a * g⁻¹ = g * b * g⁻¹) : a = b := by
  simpa using h

theorem conj_mul_eq (a b c : G) : (a * b) * c * (a * b)⁻¹ = a * (b * c * b⁻¹) * a⁻¹ := by
  group

theorem comm_of_conj_eq {g a : G} (h : g * a * g⁻¹ = a) : g * a = a * g := by
  calc g * a = g * a * g⁻¹ * g := by group
    _ = a * g := by rw [h]

theorem conj_eq_of_comm {g a : G} (h : g * a = a * g) : g * a * g⁻¹ = a := by
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

theorem orderOf_conj_eq (g c : G) : orderOf (g * c * g⁻¹) = orderOf c := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective c
  simpa using this

theorem mem_zpowers_cube_of_two_element {r : G} {k : ℕ} (hr : orderOf r = 2 ^ k) :
    r ∈ Subgroup.zpowers (r ^ 3) := by
  have hcop : Nat.Coprime 3 (orderOf r) := by
    rw [hr]
    exact Nat.Coprime.pow_right _ (by norm_num)
  exact mem_zpowers_pow_iff.mpr hcop

theorem conj_conj_eq (g r a : G) :
    (g * r * g⁻¹) * a * (g * r * g⁻¹)⁻¹ = g * (r * (g⁻¹ * a * g) * r⁻¹) * g⁻¹ := by
  group

theorem sq_mod_three_of_not_dvd {k : ℕ} (hk : ¬ 3 ∣ k) : k ^ 2 % 3 = 1 := by
  have : k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases this with h | h <;> simp [Nat.pow_mod, h]

section CommPrimary

@[expose] def commPrimaryPart (H : Subgroup G) (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (r : ℕ)
    [Fact r.Prime] : Subgroup G where
  carrier := {c | c ∈ H ∧ ∃ k : ℕ, orderOf c = r ^ k}
  one_mem' := ⟨H.one_mem, 0, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, i, hi⟩ ⟨hb, j, hj⟩
    refine ⟨H.mul_mem ha hb, ?_⟩
    have hcomm : Commute a b := hH a ha b hb
    have hdvd : orderOf (a * b) ∣ r ^ max i j := by
      refine (hcomm.orderOf_mul_dvd_lcm).trans (Nat.lcm_dvd ?_ ?_)
      · rw [hi]
        exact Nat.pow_dvd_pow r (le_max_left i j)
      · rw [hj]
        exact Nat.pow_dvd_pow r (le_max_right i j)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (Fact.out : r.Prime)).mp hdvd
    exact ⟨k, hk⟩
  inv_mem' := by
    rintro a ⟨ha, i, hi⟩
    exact ⟨H.inv_mem ha, i, by rw [orderOf_inv, hi]⟩

theorem mem_commPrimaryPart {H : Subgroup G} {hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a} {r : ℕ}
    [Fact r.Prime] {c : G} :
    c ∈ commPrimaryPart H hH r ↔ c ∈ H ∧ ∃ k : ℕ, orderOf c = r ^ k := Iff.rfl

theorem commPrimaryPart_le (H : Subgroup G) (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (r : ℕ)
    [Fact r.Prime] : commPrimaryPart H hH r ≤ H := fun _ h => h.1

theorem isPGroup_commPrimaryPart (H : Subgroup G) (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (r : ℕ) [Fact r.Prime] : IsPGroup r (commPrimaryPart H hH r) := by
  intro c
  obtain ⟨-, k, hk⟩ := c.2
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hk, pow_orderOf_eq_one]

theorem card_commPrimaryPart [Finite G] (H : Subgroup G)
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (r : ℕ) [Fact r.Prime] :
    Nat.card (commPrimaryPart H hH r) = r ^ (Nat.card H).factorization r := by
  obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow r H))
  have hnormal : ∀ K : Subgroup H, K.Normal := fun K => ⟨fun a ha g => by
    have : g * a * g⁻¹ = a := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hH g g.2 a a.2, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]
    exact ha⟩
  have heq : commPrimaryPart H hH r = (R : Subgroup H).map H.subtype := by
    ext c
    constructor
    · rintro ⟨hc, k, hk⟩
      have hp : IsPGroup r (Subgroup.zpowers (⟨c, hc⟩ : H)) := by
        apply IsPGroup.of_card (n := k)
        rw [Nat.card_zpowers, Subgroup.orderOf_mk, hk]
      have := hnormal (Subgroup.zpowers (⟨c, hc⟩ : H))
      have hle := hp.le_sylow_of_normal R
      exact ⟨⟨c, hc⟩, hle (Subgroup.mem_zpowers _), rfl⟩
    · rintro ⟨d, hd, rfl⟩
      refine ⟨d.2, ?_⟩
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp R.isPGroup') ⟨d, hd⟩
      refine ⟨k, ?_⟩
      rw [Subgroup.orderOf_mk] at hk
      rw [Subgroup.coe_subtype, Subgroup.orderOf_coe, hk]
  rw [heq, Subgroup.card_map_of_injective H.subtype_injective, Sylow.card_eq_multiplicity]

end CommPrimary

end General

namespace DValueData

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

abbrev q : ℕ := D.p ^ D.f

abbrev N : Subgroup G := Subgroup.centralizer {D.x}

abbrev C : Subgroup G := Subgroup.centralizer {D.x} ⊓ Subgroup.centralizer {D.z}

abbrev T : Subgroup G := Subgroup.closure {D.x, D.z}

@[expose] def CharacterExtend : Prop :=
  ∀ θ₀ : D.A →* ℂˣ, ∃ θ : Subgroup.centralizer ({D.x} : Set G) →* ℂˣ,
    (∀ c : Subgroup.centralizer ({D.x} : Set G), (c : G) ∈ (D.S : Subgroup G) → θ c = 1) ∧
    ∀ (c : Subgroup.centralizer ({D.x} : Set G)) (h : (c : G) ∈ D.A), θ c = θ₀ ⟨c, h⟩

@[expose] def CharacterTrivial : Prop :=
  ∀ θ : Subgroup.centralizer ({D.x} : Set G) →* ℂˣ,
    (∀ c : Subgroup.centralizer ({D.x} : Set G), (c : G) ∈ (D.S : Subgroup G) → θ c = 1) →
    (∀ g ∈ Subgroup.normalizer ((Subgroup.closure {D.x, D.z} : Subgroup G) : Set G),
      ∀ c c' : Subgroup.centralizer ({D.x} : Set G),
        (c : G) ∈ Subgroup.centralizer ((Subgroup.closure {D.x, D.z} : Subgroup G) : Set G) →
        (c' : G) = g * c * g⁻¹ → θ c' = θ c) →
    ∀ c : Subgroup.centralizer ({D.x} : Set G), θ c = 1

@[expose] def PrincipalPair : Prop :=
  ∀ basis : FiniteIrreducibleCharacterBasis G, ∃ χ₁ ψ : basis.index,
    Module.finrank ℂ (basis.representation χ₁).vector = D.q ^ 3 ∧
    Module.finrank ℂ (basis.representation ψ).vector = D.q ^ 3 + 1 ∧
    ((basis.representation ψ).character D.x = (D.q : ℂ) + 1 ∨
      (basis.representation ψ).character D.x = -((D.q : ℂ) + 1)) ∧
    ∀ g : G, Odd (orderOf g) →
      (basis.representation ψ).character g = (basis.representation χ₁).character g + 1

theorem x_mul_self : D.x * D.x = 1 := by
  rw [← pow_two, ← D.x_order, pow_orderOf_eq_one]

theorem z_mul_self : D.z * D.z = 1 := by
  rw [← pow_two, ← D.z_order, pow_orderOf_eq_one]

theorem x_inv : D.x⁻¹ = D.x := inv_eq_of_mul_eq_one_right D.x_mul_self

theorem z_inv : D.z⁻¹ = D.z := inv_eq_of_mul_eq_one_right D.z_mul_self

theorem xz_mul_self : D.x * D.z * (D.x * D.z) = 1 := by
  calc D.x * D.z * (D.x * D.z) = D.x * (D.z * D.x) * D.z := by group
    _ = D.x * (D.x * D.z) * D.z := by rw [D.z_comm]
    _ = (D.x * D.x) * (D.z * D.z) := by group
    _ = 1 := by rw [D.x_mul_self, D.z_mul_self, one_mul]

theorem xz_inv : (D.x * D.z)⁻¹ = D.x * D.z := inv_eq_of_mul_eq_one_right D.xz_mul_self

theorem x_ne_one : D.x ≠ 1 := by
  intro h
  have := D.x_order
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem z_ne_one : D.z ≠ 1 := by
  intro h
  have := D.z_order
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem xz_ne_one : D.x * D.z ≠ 1 := by
  intro h
  apply D.z_ne
  have : D.z = D.x⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [this, D.x_inv]

theorem xz_ne_x : D.x * D.z ≠ D.x := by
  intro h
  apply D.z_ne_one
  calc D.z = D.x⁻¹ * (D.x * D.z) := by group
    _ = 1 := by rw [h, inv_mul_cancel]

theorem xz_ne_z : D.x * D.z ≠ D.z := by
  intro h
  apply D.x_ne_one
  calc D.x = D.x * D.z * D.z⁻¹ := by group
    _ = 1 := by rw [h, mul_inv_cancel]

theorem mem_T_iff {g : G} : g ∈ D.T ↔ g = 1 ∨ g = D.x ∨ g = D.z ∨ g = D.x * D.z := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul a b _ _ ha hb =>
      have h1 : D.z * (D.x * D.z) = D.x := by
        rw [← mul_assoc, ← D.z_comm, mul_assoc, D.z_mul_self, mul_one]
      have h2 : D.x * (D.x * D.z) = D.z := by rw [← mul_assoc, D.x_mul_self, one_mul]
      have h3 : D.x * D.z * D.z = D.x := by rw [mul_assoc, D.z_mul_self, mul_one]
      have h4 : D.x * D.z * D.x = D.z := by
        rw [mul_assoc, ← D.z_comm, ← mul_assoc, D.x_mul_self, one_mul]
      have h5 := D.xz_mul_self
      have h6 : D.z * D.x = D.x * D.z := D.z_comm.symm
      rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
        simp only [one_mul, mul_one, D.x_mul_self, D.z_mul_self, h1, h2, h3, h4, h5, h6,
          true_or, or_true]
    | inv a _ ha =>
      rcases ha with rfl | rfl | rfl | rfl
      · exact Or.inl inv_one
      · exact Or.inr (Or.inl D.x_inv)
      · exact Or.inr (Or.inr (Or.inl D.z_inv))
      · exact Or.inr (Or.inr (Or.inr D.xz_inv))
  · have hx : D.x ∈ D.T := Subgroup.subset_closure (by simp)
    have hz : D.z ∈ D.T := Subgroup.subset_closure (by simp)
    rintro (rfl | rfl | rfl | rfl)
    · exact D.T.one_mem
    · exact hx
    · exact hz
    · exact D.T.mul_mem hx hz

theorem x_mem_T : D.x ∈ D.T := D.mem_T_iff.mpr (Or.inr (Or.inl rfl))

theorem z_mem_T : D.z ∈ D.T := D.mem_T_iff.mpr (Or.inr (Or.inr (Or.inl rfl)))

theorem centralizer_T : Subgroup.centralizer (D.T : Set G) = D.C := by
  ext g
  rw [Subgroup.centralizer_closure, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact ⟨(h D.x (Set.mem_insert _ _)).symm, (h D.z (Set.mem_insert_of_mem _ rfl)).symm⟩
  · rintro ⟨h1, h2⟩ a ha
    rcases ha with rfl | rfl
    · exact h1.symm
    · exact h2.symm

theorem mem_C_iff {g : G} : g ∈ D.C ↔ g * D.x = D.x * g ∧ g * D.z = D.z * g := by
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]

theorem C_le_N : D.C ≤ D.N := inf_le_left

theorem z_mem_N : D.z ∈ D.N := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact D.z_comm.symm

theorem y_mem_N : D.y ∈ D.N := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact D.y_comm.symm

theorem x_mem_C : D.x ∈ D.C := D.mem_C_iff.mpr ⟨rfl, D.z_comm⟩

theorem z_mem_C : D.z ∈ D.C := D.mem_C_iff.mpr ⟨D.z_comm.symm, rfl⟩

theorem T_le_C : D.T ≤ D.C := by
  intro g hg
  rcases D.mem_T_iff.mp hg with rfl | rfl | rfl | rfl
  · exact D.C.one_mem
  · exact D.x_mem_C
  · exact D.z_mem_C
  · exact D.C.mul_mem D.x_mem_C D.z_mem_C

theorem A_le_C : D.A ≤ D.C := by
  intro a ha
  refine D.mem_C_iff.mpr ⟨?_, ?_⟩
  · have hx : D.x ∈ D.N := by
      rw [Subgroup.mem_centralizer_singleton_iff]
    exact (D.A_central a ha D.x hx).symm
  · exact (D.A_central a ha D.z D.z_mem_N).symm

theorem A_comm_N {a g : G} (ha : a ∈ D.A) (hg : g ∈ D.N) : g * a = a * g := D.A_central a ha g hg

theorem y_x : D.y * D.x * D.y⁻¹ = D.x := by
  rw [← D.y_comm, mul_assoc, mul_inv_cancel, mul_one]

theorem y_xz : D.y * (D.x * D.z) * D.y⁻¹ = D.z := by
  have h : D.y * (D.x * D.z) * D.y⁻¹ = (D.y * D.x * D.y⁻¹) * (D.y * D.z * D.y⁻¹) := by group
  rw [h, D.y_x, D.y_z, ← mul_assoc, D.x_mul_self, one_mul]

theorem t_xz : D.t * (D.x * D.z) * D.t⁻¹ = D.x := by
  have h : D.t * (D.x * D.z) * D.t⁻¹ = (D.t * D.x * D.t⁻¹) * (D.t * D.z * D.t⁻¹) := by group
  rw [h, D.t_x, D.t_z, ← mul_assoc, ← D.z_comm, mul_assoc, D.z_mul_self, mul_one]

theorem t_not_mem_N : D.t ∉ D.N := by
  intro h
  rw [Subgroup.mem_centralizer_singleton_iff] at h
  apply D.z_ne
  rw [← D.t_x, h, mul_assoc, mul_inv_cancel, mul_one]

theorem t_inv_z : D.t⁻¹ * D.z * D.t = D.x := by
  calc D.t⁻¹ * D.z * D.t = D.t⁻¹ * (D.t * D.x * D.t⁻¹) * D.t := by rw [D.t_x]
    _ = D.x := by group

theorem t_inv_xz : D.t⁻¹ * (D.x * D.z) * D.t = D.z := by
  calc D.t⁻¹ * (D.x * D.z) * D.t = D.t⁻¹ * (D.t * D.z * D.t⁻¹) * D.t := by rw [D.t_z]
    _ = D.z := by group

theorem t_inv_x : D.t⁻¹ * D.x * D.t = D.x * D.z := by
  calc D.t⁻¹ * D.x * D.t = D.t⁻¹ * (D.t * (D.x * D.z) * D.t⁻¹) * D.t := by rw [D.t_xz]
    _ = D.x * D.z := by group

theorem mem_normalizer_T_of {g : G} (hx : g * D.x * g⁻¹ ∈ D.T) (hz : g * D.z * g⁻¹ ∈ D.T) :
    g ∈ Subgroup.normalizer (D.T : Set G) := by
  have hle : D.T.map (MulAut.conj g).toMonoidHom ≤ D.T := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    intro a ha
    rcases ha with rfl | rfl
    · exact hx
    · exact hz
  have hcard : Nat.card (D.T.map (MulAut.conj g).toMonoidHom) = Nat.card D.T :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have heq : D.T.map (MulAut.conj g).toMonoidHom = D.T :=
    Subgroup.eq_of_le_of_card_ge hle hcard.ge
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    rw [← heq]
    exact ⟨a, ha, rfl⟩
  · intro ha
    rw [← heq] at ha
    obtain ⟨b, hb, hba⟩ := ha
    have h' : g * b * g⁻¹ = g * a * g⁻¹ := hba
    have : b = a := by simpa using h'
    rw [← this]
    exact hb

theorem y_mem_normalizer_T : D.y ∈ Subgroup.normalizer (D.T : Set G) :=
  D.mem_normalizer_T_of (by rw [D.y_x]; exact D.x_mem_T)
    (by rw [D.y_z]; exact D.T.mul_mem D.x_mem_T D.z_mem_T)

theorem t_mem_normalizer_T : D.t ∈ Subgroup.normalizer (D.T : Set G) :=
  D.mem_normalizer_T_of (by rw [D.t_x]; exact D.z_mem_T)
    (by rw [D.t_z]; exact D.T.mul_mem D.x_mem_T D.z_mem_T)


theorem mem_C_iff_conj {g : G} : g ∈ D.C ↔ g * D.x * g⁻¹ = D.x ∧ g * D.z * g⁻¹ = D.z := by
  rw [D.mem_C_iff]
  exact ⟨fun h => ⟨conj_eq_of_comm h.1, conj_eq_of_comm h.2⟩,
    fun h => ⟨comm_of_conj_eq h.1, comm_of_conj_eq h.2⟩⟩

theorem y_inv_x : D.y⁻¹ * D.x * D.y = D.x := by
  calc D.y⁻¹ * D.x * D.y = D.y⁻¹ * (D.y * D.x * D.y⁻¹) * D.y := by rw [D.y_x]
    _ = D.x := by group

theorem y_inv_xz : D.y⁻¹ * (D.x * D.z) * D.y = D.z := by
  calc D.y⁻¹ * (D.x * D.z) * D.y = D.y⁻¹ * (D.y * D.z * D.y⁻¹) * D.y := by rw [D.y_z]
    _ = D.z := by group

theorem y_inv_z : D.y⁻¹ * D.z * D.y = D.x * D.z := by
  calc D.y⁻¹ * D.z * D.y = D.y⁻¹ * (D.x * D.x * D.z) * D.y := by rw [D.x_mul_self, one_mul]
    _ = (D.y⁻¹ * D.x * D.y) * (D.y⁻¹ * (D.x * D.z) * D.y) := by group
    _ = D.x * D.z := by rw [D.y_inv_x, D.y_inv_xz]

theorem conj_mem_T_ne_one {g : G} (hg : g ∈ Subgroup.normalizer (D.T : Set G)) {v : G}
    (hv : v ∈ D.T) (hv1 : v ≠ 1) : g * v * g⁻¹ = D.x ∨ g * v * g⁻¹ = D.z ∨
      g * v * g⁻¹ = D.x * D.z := by
  have hmem : g * v * g⁻¹ ∈ D.T := (Subgroup.mem_normalizer_iff.mp hg v).mp hv
  rcases D.mem_T_iff.mp hmem with h | h | h | h
  · exfalso
    apply hv1
    have : v = g⁻¹ * (g * v * g⁻¹) * g := by group
    rw [this, h]
    group
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem normalizer_T_fix_x {g : G} (hg : g ∈ Subgroup.normalizer (D.T : Set G))
    (hgx : g * D.x * g⁻¹ = D.x) : g ∈ D.C ∨ D.y⁻¹ * g ∈ D.C := by
  rcases D.conj_mem_T_ne_one hg D.z_mem_T D.z_ne_one with h | h | h
  · exact absurd (eq_of_conj_eq (h.trans hgx.symm)) D.z_ne
  · exact Or.inl (D.mem_C_iff_conj.mpr ⟨hgx, h⟩)
  · right
    refine D.mem_C_iff_conj.mpr ⟨?_, ?_⟩
    · rw [conj_mul_eq, hgx, inv_inv, D.y_inv_x]
    · rw [conj_mul_eq, h, inv_inv, D.y_inv_xz]

theorem normalizer_T_cases {g : G} (hg : g ∈ Subgroup.normalizer (D.T : Set G)) :
    ∃ i j : ℕ, i < 3 ∧ j < 2 ∧ (D.t ^ i * D.y ^ j)⁻¹ * g ∈ D.C := by
  have htN := D.t_mem_normalizer_T
  have key : ∀ g ∈ Subgroup.normalizer (D.T : Set G), g * D.x * g⁻¹ = D.x →
      ∃ j : ℕ, j < 2 ∧ (D.y ^ j)⁻¹ * g ∈ D.C := by
    intro g hg hgx
    rcases D.normalizer_T_fix_x hg hgx with h | h
    · exact ⟨0, by norm_num, by simpa using h⟩
    · exact ⟨1, by norm_num, by simpa using h⟩
  rcases D.conj_mem_T_ne_one hg D.x_mem_T D.x_ne_one with h | h | h
  · obtain ⟨j, hj, hjC⟩ := key g hg h
    exact ⟨0, j, by norm_num, hj, by simpa using hjC⟩
  · have hg' : D.t⁻¹ * g ∈ Subgroup.normalizer (D.T : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ htN) hg
    have hx' : D.t⁻¹ * g * D.x * (D.t⁻¹ * g)⁻¹ = D.x := by
      rw [conj_mul_eq, h, inv_inv, D.t_inv_z]
    obtain ⟨j, hj, hjC⟩ := key _ hg' hx'
    refine ⟨1, j, by norm_num, hj, ?_⟩
    have he : (D.t ^ 1 * D.y ^ j)⁻¹ * g = (D.y ^ j)⁻¹ * (D.t⁻¹ * g) := by
      rw [pow_one, mul_inv_rev, mul_assoc]
    rw [he]
    exact hjC
  · have hg' : D.t⁻¹ * (D.t⁻¹ * g) ∈ Subgroup.normalizer (D.T : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ htN) (Subgroup.mul_mem _ (Subgroup.inv_mem _ htN) hg)
    have hx' : D.t⁻¹ * (D.t⁻¹ * g) * D.x * (D.t⁻¹ * (D.t⁻¹ * g))⁻¹ = D.x := by
      rw [conj_mul_eq, conj_mul_eq, h, inv_inv, D.t_inv_xz, D.t_inv_z]
    obtain ⟨j, hj, hjC⟩ := key _ hg' hx'
    refine ⟨2, j, by norm_num, hj, ?_⟩
    have he : (D.t ^ 2 * D.y ^ j)⁻¹ * g = (D.y ^ j)⁻¹ * (D.t⁻¹ * (D.t⁻¹ * g)) := by
      rw [pow_two, mul_inv_rev, mul_inv_rev, mul_assoc, mul_assoc]
    rw [he]
    exact hjC

theorem t_cube_mem_C : D.t ^ 3 ∈ D.C := by
  have h3 : D.t ^ 3 = D.t * (D.t * D.t) := by rw [pow_succ, pow_two, mul_assoc]
  refine D.mem_C_iff_conj.mpr ⟨?_, ?_⟩
  · rw [h3, conj_mul_eq, conj_mul_eq, D.t_x, D.t_z, D.t_xz]
  · rw [h3, conj_mul_eq, conj_mul_eq, D.t_z, D.t_xz, D.t_x]

theorem y_t_y_inv_t_mem_C : D.y * D.t * D.y⁻¹ * D.t ∈ D.C := by
  have he : D.y * D.t * D.y⁻¹ * D.t = D.y * (D.t * (D.y⁻¹ * D.t)) := by group
  refine D.mem_C_iff_conj.mpr ⟨?_, ?_⟩
  · rw [he, conj_mul_eq, conj_mul_eq, conj_mul_eq, D.t_x, inv_inv, D.y_inv_z, D.t_xz, D.y_x]
  · rw [he, conj_mul_eq, conj_mul_eq, conj_mul_eq, D.t_z, inv_inv, D.y_inv_xz, D.t_z, D.y_xz]

theorem eq_x_of_central_involution {i : G} (hi : i ∈ D.N) (hcent : ∀ g ∈ D.N, g * i = i * g)
    (hi2 : i * i = 1) (hi1 : i ≠ 1) : i = D.x := by
  have hiC : i ∈ D.C := by
    refine D.mem_C_iff.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hi)
    · exact (hcent D.z D.z_mem_N).symm
  rcases D.C_involutions i hiC hi2 with h | h | h | h
  · exact absurd h hi1
  · exact h
  · exfalso
    have h1 := conj_eq_of_comm (hcent D.y D.y_mem_N)
    rw [h, D.y_z] at h1
    exact D.xz_ne_z h1
  · exfalso
    have h1 := conj_eq_of_comm (hcent D.y D.y_mem_N)
    rw [h, D.y_xz] at h1
    exact D.xz_ne_z h1.symm


theorem centralizer_A_eq {r : G} (hr : r ∈ D.A) (hr1 : r ≠ 1) :
    Subgroup.centralizer {r} = D.N := by
  refine le_antisymm (D.A_confine r hr hr1) fun g hg => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact D.A_central r hr g hg

theorem mem_N_of_conj_mem_A {a g : G} (ha : a ∈ D.A) (ha1 : a ≠ 1) (hga : g * a * g⁻¹ ∈ D.A) :
    g ∈ D.N := by
  have hga1 : g * a * g⁻¹ ≠ 1 := by
    intro h
    apply ha1
    have : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [this, h]
    group
  have hconj : ∀ n ∈ D.N, g⁻¹ * n * g ∈ D.N := by
    intro n hn
    rw [← D.centralizer_A_eq hga hga1] at hn
    rw [← D.centralizer_A_eq ha ha1, Subgroup.mem_centralizer_singleton_iff]
    rw [Subgroup.mem_centralizer_singleton_iff] at hn
    calc g⁻¹ * n * g * a = g⁻¹ * (n * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * n) * g := by rw [hn]
      _ = a * (g⁻¹ * n * g) := by group
  have hxN : D.x ∈ D.N := by rw [Subgroup.mem_centralizer_singleton_iff]
  have hcent : ∀ n ∈ D.N, n * (g * D.x * g⁻¹) = (g * D.x * g⁻¹) * n := by
    intro n hn
    have h1 := hconj n hn
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    calc n * (g * D.x * g⁻¹) = g * ((g⁻¹ * n * g) * D.x) * g⁻¹ := by group
      _ = g * (D.x * (g⁻¹ * n * g)) * g⁻¹ := by rw [h1]
      _ = (g * D.x * g⁻¹) * n := by group
  have hmem : g * D.x * g⁻¹ ∈ D.N := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcent D.x hxN).symm
  have hinv : g * D.x * g⁻¹ * (g * D.x * g⁻¹) = 1 := by
    calc g * D.x * g⁻¹ * (g * D.x * g⁻¹) = g * (D.x * D.x) * g⁻¹ := by group
      _ = 1 := by rw [D.x_mul_self, mul_one, mul_inv_cancel]
  have hne : g * D.x * g⁻¹ ≠ 1 := by
    intro h
    apply D.x_ne_one
    have : D.x = g⁻¹ * (g * D.x * g⁻¹) * g := by group
    rw [this, h]
    group
  have hgx := D.eq_x_of_central_involution hmem (fun n hn => hcent n hn) hinv hne
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact comm_of_conj_eq hgx

theorem conj_eq_of_mem_A {a g : G} (ha : a ∈ D.A) (hga : g * a * g⁻¹ ∈ D.A) :
    g * a * g⁻¹ = a := by
  by_cases ha1 : a = 1
  · rw [ha1, mul_one, mul_inv_cancel]
  · exact conj_eq_of_comm (D.A_central a ha g (D.mem_N_of_conj_mem_A ha ha1 hga))

@[expose] def primaryPart (r : ℕ) [Fact r.Prime] : Subgroup G := commPrimaryPart D.C D.C_comm r

theorem mem_primaryPart {r : ℕ} [Fact r.Prime] {c : G} :
    c ∈ D.primaryPart r ↔ c ∈ D.C ∧ ∃ k : ℕ, orderOf c = r ^ k := Iff.rfl

theorem primaryPart_le_C (r : ℕ) [Fact r.Prime] : D.primaryPart r ≤ D.C := fun _ h => h.1

theorem isPGroup_primaryPart (r : ℕ) [Fact r.Prime] : IsPGroup r (D.primaryPart r) :=
  isPGroup_commPrimaryPart _ _ r

theorem card_primaryPart (r : ℕ) [Fact r.Prime] :
    Nat.card (D.primaryPart r) = r ^ (Nat.card D.C).factorization r :=
  card_commPrimaryPart _ _ r

theorem conj_mem_C {g c : G} (hg : g ∈ Subgroup.normalizer (D.T : Set G)) (hc : c ∈ D.C) :
    g * c * g⁻¹ ∈ D.C := by
  rw [← D.centralizer_T] at hc ⊢
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro v hv
  have hv' : g⁻¹ * v * g ∈ D.T := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) v).mp hv
    simpa using h
  have h1 := hc _ hv'
  calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * v := by group

theorem conj_mem_primaryPart {r : ℕ} [Fact r.Prime] {g c : G}
    (hg : g ∈ Subgroup.normalizer (D.T : Set G)) (hc : c ∈ D.primaryPart r) :
    g * c * g⁻¹ ∈ D.primaryPart r := by
  obtain ⟨hcC, k, hk⟩ := hc
  exact ⟨D.conj_mem_C hg hcC, k, by rw [← hk]; exact orderOf_conj_eq g c⟩

theorem mem_normalizer_primaryPart {r : ℕ} [Fact r.Prime] {g : G}
    (hg : g ∈ Subgroup.normalizer (D.T : Set G)) :
    g ∈ Subgroup.normalizer (D.primaryPart r : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · exact D.conj_mem_primaryPart hg
  · intro h
    have h' := D.conj_mem_primaryPart (Subgroup.inv_mem _ hg) h
    convert h' using 1
    group

abbrev U : Subgroup G := @primaryPart G _ _ D 2 ⟨Nat.prime_two⟩

theorem x_mem_U : D.x ∈ D.U := ⟨D.x_mem_C, 1, by rw [D.x_order, pow_one]⟩

theorem z_mem_U : D.z ∈ D.U := ⟨D.z_mem_C, 1, by rw [D.z_order, pow_one]⟩

theorem orderOf_xz : orderOf (D.x * D.z) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact D.xz_mul_self) D.xz_ne_one

theorem xz_mem_U : D.x * D.z ∈ D.U := ⟨D.C.mul_mem D.x_mem_C D.z_mem_C, 1, by
  rw [D.orderOf_xz, pow_one]⟩

theorem mem_T_of_mem_U {u : G} (hu : u ∈ D.U) (hu2 : u * u = 1) : u ∈ D.T := by
  rw [D.mem_T_iff]
  exact D.C_involutions u hu.1 hu2

theorem normalizer_U_le {g : G} (hg : g ∈ Subgroup.normalizer (D.U : Set G)) :
    g ∈ Subgroup.normalizer (D.T : Set G) := by
  have key : ∀ v ∈ D.U, v * v = 1 → g * v * g⁻¹ ∈ D.T := by
    intro v hv hv2
    refine D.mem_T_of_mem_U ((Subgroup.mem_normalizer_iff.mp hg v).mp hv) ?_
    calc g * v * g⁻¹ * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
      _ = 1 := by rw [hv2, mul_one, mul_inv_cancel]
  exact D.mem_normalizer_T_of (key _ D.x_mem_U D.x_mul_self) (key _ D.z_mem_U D.z_mul_self)

theorem two_element_fixes {r : G} (hr : r ∈ Subgroup.normalizer (D.T : Set G)) {k : ℕ}
    (hrk : orderOf r = 2 ^ k) :
    r * D.x * r⁻¹ = D.x ∨ r * D.z * r⁻¹ = D.z ∨ r * (D.x * D.z) * r⁻¹ = D.x * D.z := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have hxz_eq : r * (D.x * D.z) * r⁻¹ = (r * D.x * r⁻¹) * (r * D.z * r⁻¹) := by group
  have e1 : D.z * (D.x * D.z) = D.x := by
    rw [← mul_assoc, ← D.z_comm, mul_assoc, D.z_mul_self, mul_one]
  have e2 : D.x * D.z * D.x = D.z := by
    rw [mul_assoc, ← D.z_comm, ← mul_assoc, D.x_mul_self, one_mul]
  have h3' : r ^ 3 = r * (r * r) := by rw [pow_succ, pow_two, mul_assoc]
  have hcube : r ^ 3 ∈ D.C := by
    rcases D.conj_mem_T_ne_one hr D.x_mem_T D.x_ne_one with hx | hx | hx
    · exact absurd hx h1
    ·
      rcases D.conj_mem_T_ne_one hr D.z_mem_T D.z_ne_one with hz | hz | hz
      · exfalso
        apply h3
        rw [hxz_eq, hx, hz, D.z_comm]
      · exact absurd hz h2
      · have hxz : r * (D.x * D.z) * r⁻¹ = D.x := by rw [hxz_eq, hx, hz, e1]
        refine D.mem_C_iff_conj.mpr ⟨?_, ?_⟩
        · rw [h3', conj_mul_eq, conj_mul_eq, hx, hz, hxz]
        · rw [h3', conj_mul_eq, conj_mul_eq, hz, hxz, hx]
    ·
      rcases D.conj_mem_T_ne_one hr D.z_mem_T D.z_ne_one with hz | hz | hz
      · have hxz : r * (D.x * D.z) * r⁻¹ = D.z := by rw [hxz_eq, hx, hz, e2]
        refine D.mem_C_iff_conj.mpr ⟨?_, ?_⟩
        · rw [h3', conj_mul_eq, conj_mul_eq, hx, hxz, hz]
        · rw [h3', conj_mul_eq, conj_mul_eq, hz, hx, hxz]
      · exact absurd hz h2
      · exfalso
        exact D.z_ne (eq_of_conj_eq (hz.trans hx.symm))
  have hrC : r ∈ D.C := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_cube_of_two_element hrk)
    rw [← hn]
    exact D.C.zpow_mem hcube n
  exact h1 (D.mem_C_iff_conj.mp hrC).1

@[expose] noncomputable def threeExponent : ℕ :=
  (orderOf D.t / 3 ^ (orderOf D.t).factorization 3) ^ 2

theorem threeExponent_mod : D.threeExponent % 3 = 1 :=
  sq_mod_three_of_not_dvd (Nat.not_dvd_ordCompl Nat.prime_three (orderOf_pos D.t).ne')

theorem conj_t_pow_of_mod {e : ℕ} (he : e % 3 = 1) :
    D.t ^ e * D.x * (D.t ^ e)⁻¹ = D.z ∧ D.t ^ e * D.z * (D.t ^ e)⁻¹ = D.x * D.z := by
  obtain ⟨j, rfl⟩ : ∃ j, e = 3 * j + 1 := ⟨e / 3, by omega⟩
  have hc : D.t ^ (3 * j) ∈ D.C := by
    rw [pow_mul]
    exact D.C.pow_mem D.t_cube_mem_C j
  have hcx := D.mem_C_iff_conj.mp hc
  have hsplit : D.t ^ (3 * j + 1) = D.t ^ (3 * j) * D.t := pow_succ _ _
  refine ⟨?_, ?_⟩
  · rw [hsplit, conj_mul_eq, D.t_x, hcx.2]
  · rw [hsplit, conj_mul_eq, D.t_z]
    exact conj_eq_of_comm (D.C_comm _ hc _ (D.C.mul_mem D.x_mem_C D.z_mem_C))

@[expose] noncomputable def tThree : G := D.t ^ D.threeExponent

theorem tThree_order : ∃ b : ℕ, orderOf D.tThree = 3 ^ b := by
  have hsplit : 3 ^ (orderOf D.t).factorization 3 *
      (orderOf D.t / 3 ^ (orderOf D.t).factorization 3) = orderOf D.t :=
    Nat.ordProj_mul_ordCompl_eq_self (orderOf D.t) 3
  have hdvd : orderOf D.tThree ∣ 3 ^ (orderOf D.t).factorization 3 := by
    apply orderOf_dvd_of_pow_eq_one
    unfold tThree threeExponent
    rw [← pow_mul, pow_two, mul_assoc, mul_comm _ (3 ^ _), hsplit, mul_comm, pow_mul,
      pow_orderOf_eq_one, one_pow]
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  exact ⟨b, hb⟩

@[expose] noncomputable def toThree : DValueData G where
  __ := D
  t := D.tThree
  t_x := (D.conj_t_pow_of_mod D.threeExponent_mod).1
  t_z := (D.conj_t_pow_of_mod D.threeExponent_mod).2

theorem mem_U_of_mem_normalizer {w : G}
    (hw : ∀ g ∈ ({1, D.t⁻¹, D.t⁻¹ * D.t⁻¹} : Set G),
      D.N ⊓ Subgroup.centralizer {g * w * g⁻¹} ≤ D.C)
    {r : G} (hr : r ∈ Subgroup.centralizer {w}) {k : ℕ} (hrk : orderOf r = 2 ^ k)
    (hrU : r ∈ Subgroup.normalizer (D.U : Set G)) : r ∈ D.U := by
  have hrT := D.normalizer_U_le hrU
  have htN := D.t_mem_normalizer_T
  have key : ∀ g ∈ ({1, D.t⁻¹, D.t⁻¹ * D.t⁻¹} : Set G),
      g ∈ Subgroup.normalizer (D.T : Set G) →
      (g * r * g⁻¹) * D.x * (g * r * g⁻¹)⁻¹ = D.x → r ∈ D.U := by
    intro g hg hgT hfix
    have h1 : g * r * g⁻¹ ∈ D.N := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact comm_of_conj_eq hfix
    have h2 : g * r * g⁻¹ ∈ Subgroup.centralizer {g * w * g⁻¹} := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hr ⊢
      calc g * r * g⁻¹ * (g * w * g⁻¹) = g * (r * w) * g⁻¹ := by group
        _ = g * (w * r) * g⁻¹ := by rw [hr]
        _ = g * w * g⁻¹ * (g * r * g⁻¹) := by group
    have h3 : g * r * g⁻¹ ∈ D.C := hw g hg ⟨h1, h2⟩
    have h4 : g * r * g⁻¹ ∈ D.U := ⟨h3, k, by rw [orderOf_conj_eq, hrk]⟩
    have h5 := D.conj_mem_primaryPart (r := 2) (Subgroup.inv_mem _ hgT) h4
    convert h5 using 1
    group
  rcases D.two_element_fixes hrT hrk with h | h | h
  · refine key 1 (by simp) (Subgroup.one_mem _) ?_
    simpa using h
  · refine key D.t⁻¹ (by simp) (Subgroup.inv_mem _ htN) ?_
    rw [conj_conj_eq, inv_inv, D.t_x, h, D.t_inv_z]
  · refine key (D.t⁻¹ * D.t⁻¹) (by simp)
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ htN) (Subgroup.inv_mem _ htN)) ?_
    have hg1 : (D.t⁻¹ * D.t⁻¹)⁻¹ * D.x * (D.t⁻¹ * D.t⁻¹) = D.x * D.z := by
      rw [mul_inv_rev, inv_inv, show D.t * D.t * D.x * (D.t⁻¹ * D.t⁻¹) =
        D.t * (D.t * D.x * D.t⁻¹) * D.t⁻¹ by group, D.t_x, D.t_z]
    have hg2 : (D.t⁻¹ * D.t⁻¹) * (D.x * D.z) * (D.t⁻¹ * D.t⁻¹)⁻¹ = D.x := by
      rw [conj_mul_eq, inv_inv, D.t_inv_xz, D.t_inv_z]
    rw [conj_conj_eq, hg1, h, hg2]

theorem eq_U_of_isPGroup {w : G}
    (hw : ∀ g ∈ ({1, D.t⁻¹, D.t⁻¹ * D.t⁻¹} : Set G),
      D.N ⊓ Subgroup.centralizer {g * w * g⁻¹} ≤ D.C)
    {R : Subgroup G} (hR : IsPGroup 2 R) (hUR : D.U ≤ R)
    (hRw : R ≤ Subgroup.centralizer {w}) : R = D.U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hlt : D.U.subgroupOf R < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne ?_
    refine le_antisymm (fun r hr => ?_) hUR
    have : (⟨r, hr⟩ : R) ∈ D.U.subgroupOf R := by rw [htop]; exact Subgroup.mem_top _
    exact this
  have := hR.isNilpotent
  obtain ⟨r, hrN, hrU⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (D.U.subgroupOf R) hlt)
  apply hrU
  have hrG : (r : G) ∈ Subgroup.normalizer (D.U : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    rw [Subgroup.mem_normalizer_iff] at hrN
    constructor
    · intro hu
      have h := (hrN ⟨u, hUR hu⟩).mp hu
      exact h
    · intro hu
      have huR : u ∈ R := by
        have : u = (r : G)⁻¹ * ((r : G) * u * (r : G)⁻¹) * r := by group
        rw [this]
        exact R.mul_mem (R.mul_mem (R.inv_mem r.2) (hUR hu)) r.2
      exact (hrN ⟨u, huR⟩).mpr hu
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR) r
  rw [← Subgroup.orderOf_coe] at hk
  exact D.mem_U_of_mem_normalizer hw (hRw r.2) hk hrG

@[expose] noncomputable def sylowU {w : G} (hwC : w ∈ D.C)
    (hw : ∀ g ∈ ({1, D.t⁻¹, D.t⁻¹ * D.t⁻¹} : Set G),
      D.N ⊓ Subgroup.centralizer {g * w * g⁻¹} ≤ D.C) :
    Sylow 2 (Subgroup.centralizer ({w} : Set G)) where
  toSubgroup := D.U.subgroupOf (Subgroup.centralizer {w})
  isPGroup' := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (D.isPGroup_primaryPart 2).comap_of_injective _ Subtype.val_injective
  is_maximal' := by
    intro Q hQ hle
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hUw : D.U ≤ Subgroup.centralizer {w} := by
      intro u hu
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact D.C_comm u hu.1 w hwC
    have hQ' : IsPGroup 2 (Q.map (Subgroup.centralizer {w}).subtype) := hQ.map _
    have hUQ : D.U ≤ Q.map (Subgroup.centralizer {w}).subtype := by
      intro u hu
      exact ⟨⟨u, hUw hu⟩, hle hu, rfl⟩
    have hQw : Q.map (Subgroup.centralizer {w}).subtype ≤ Subgroup.centralizer {w} := by
      rintro _ ⟨c, -, rfl⟩
      exact c.2
    have heq := D.eq_U_of_isPGroup hw hQ' hUQ hQw
    ext c
    constructor
    · intro hc
      change (c : G) ∈ D.U
      rw [← heq]
      exact ⟨c, hc, rfl⟩
    · intro hc
      exact hle hc

theorem coe_sylowU {w : G} (hwC : w ∈ D.C)
    (hw : ∀ g ∈ ({1, D.t⁻¹, D.t⁻¹ * D.t⁻¹} : Set G),
      D.N ⊓ Subgroup.centralizer {g * w * g⁻¹} ≤ D.C) :
    ((D.sylowU hwC hw : Subgroup (Subgroup.centralizer ({w} : Set G))) =
      D.U.subgroupOf (Subgroup.centralizer {w})) := rfl

end DValueData

end CFSG.Semidihedral.UnitaryDValue
