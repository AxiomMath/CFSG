module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbedding

open Equiv CFSG.Open

@[expose] def a9PermC₁ : Perm (Fin 9) := swap 0 2 * swap 0 1

@[expose] def a9PermC₂ : Perm (Fin 9) := swap 3 5 * swap 3 4

@[expose] def a9PermC₃ : Perm (Fin 9) := swap 6 8 * swap 6 7

@[expose] def a9PermSigma : Perm (Fin 9) :=
  (swap 0 6 * swap 0 3) * (swap 1 7 * swap 1 4) * (swap 2 8 * swap 2 5)

@[expose] def a9PermG : Perm (Fin 9) :=
  (swap 1 6 * swap 1 2 * swap 1 3) * (swap 4 7 * swap 4 8 * swap 4 5)

@[expose] def a9PermBase (a b c : ℕ) : Perm (Fin 9) :=
  a9PermC₁ ^ a * a9PermC₂ ^ b * a9PermC₃ ^ c

@[expose] def a9c₁ : alternatingGroup (Fin 9) :=
  ⟨a9PermC₁, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def a9c₂ : alternatingGroup (Fin 9) :=
  ⟨a9PermC₂, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def a9c₃ : alternatingGroup (Fin 9) :=
  ⟨a9PermC₃, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def a9σ : alternatingGroup (Fin 9) :=
  ⟨a9PermSigma, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def a9z : alternatingGroup (Fin 9) := a9c₁ * a9c₂ * a9c₃

@[expose] def a9g : alternatingGroup (Fin 9) :=
  ⟨a9PermG, Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem coe_a9c_pow (a b c : ℕ) :
    ((a9c₁ ^ a * a9c₂ ^ b * a9c₃ ^ c : alternatingGroup (Fin 9)) : Perm (Fin 9)) =
      a9PermBase a b c := rfl

theorem a9c₁_pow_three : a9c₁ ^ 3 = 1 := Subtype.ext (show a9PermC₁ ^ 3 = 1 by decide)

theorem a9c₂_pow_three : a9c₂ ^ 3 = 1 := Subtype.ext (show a9PermC₂ ^ 3 = 1 by decide)

theorem a9c₃_pow_three : a9c₃ ^ 3 = 1 := Subtype.ext (show a9PermC₃ ^ 3 = 1 by decide)

theorem commute_a9c₁_a9c₂ : Commute a9c₁ a9c₂ :=
  Subtype.ext (show a9PermC₁ * a9PermC₂ = a9PermC₂ * a9PermC₁ by decide)

theorem commute_a9c₁_a9c₃ : Commute a9c₁ a9c₃ :=
  Subtype.ext (show a9PermC₁ * a9PermC₃ = a9PermC₃ * a9PermC₁ by decide)

theorem commute_a9c₂_a9c₃ : Commute a9c₂ a9c₃ :=
  Subtype.ext (show a9PermC₂ * a9PermC₃ = a9PermC₃ * a9PermC₂ by decide)

theorem a9c_pow_mul (a b c a' b' c' : ℕ) :
    a9c₁ ^ a * a9c₂ ^ b * a9c₃ ^ c * (a9c₁ ^ a' * a9c₂ ^ b' * a9c₃ ^ c') =
      a9c₁ ^ (a + a') * a9c₂ ^ (b + b') * a9c₃ ^ (c + c') := by
  simp only [pow_add, mul_assoc]
  rw [(commute_a9c₁_a9c₃.pow_pow a' c).symm.left_comm,
    (commute_a9c₁_a9c₂.pow_pow a' b).symm.left_comm,
    (commute_a9c₂_a9c₃.pow_pow b' c).symm.left_comm]

theorem a9c_pow_three_mul (a b c : ℕ) :
    a9c₁ ^ (3 * a) * a9c₂ ^ (3 * b) * a9c₃ ^ (3 * c) = 1 := by
  simp only [pow_mul, a9c₁_pow_three, a9c₂_pow_three, a9c₃_pow_three, one_pow, mul_one]

theorem a9z_pow (n : ℕ) : a9z ^ n = a9c₁ ^ n * a9c₂ ^ n * a9c₃ ^ n := by
  rw [a9z, (commute_a9c₁_a9c₃.mul_left commute_a9c₂_a9c₃).mul_pow, commute_a9c₁_a9c₂.mul_pow]

def a9Base : Subgroup (alternatingGroup (Fin 9)) where
  carrier := {x | ∃ a b c : ℕ, x = a9c₁ ^ a * a9c₂ ^ b * a9c₃ ^ c}
  mul_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨a + a', b + b', c + c', a9c_pow_mul a b c a' b' c'⟩
  one_mem' := ⟨0, 0, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, rfl⟩
    refine ⟨2 * a, 2 * b, 2 * c, inv_eq_of_mul_eq_one_right ?_⟩
    rw [a9c_pow_mul, show a + 2 * a = 3 * a by ring, show b + 2 * b = 3 * b by ring,
      show c + 2 * c = 3 * c by ring, a9c_pow_three_mul]

theorem mem_a9Base {x : alternatingGroup (Fin 9)} :
    x ∈ a9Base ↔ ∃ a b c : ℕ, x = a9c₁ ^ a * a9c₂ ^ b * a9c₃ ^ c := Iff.rfl

theorem exists_fin_of_mem_a9Base {x : alternatingGroup (Fin 9)} (hx : x ∈ a9Base) :
    ∃ a b c : Fin 3, x = a9c₁ ^ (a : ℕ) * a9c₂ ^ (b : ℕ) * a9c₃ ^ (c : ℕ) := by
  obtain ⟨a, b, c, rfl⟩ := mem_a9Base.mp hx
  refine ⟨⟨a % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨b % 3, Nat.mod_lt _ (by norm_num)⟩,
    ⟨c % 3, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
  rw [pow_eq_pow_mod a a9c₁_pow_three, pow_eq_pow_mod b a9c₂_pow_three,
    pow_eq_pow_mod c a9c₃_pow_three]

theorem a9z_mem : a9z ∈ a9Base := mem_a9Base.mpr ⟨1, 1, 1, by simp [a9z]⟩

theorem isElemAbelian_a9Base : IsElemAbelian 3 a9Base := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, b, c, hx⟩ := mem_a9Base.mp x.2
    obtain ⟨a', b', c', hy⟩ := mem_a9Base.mp y.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx, hy, a9c_pow_mul, a9c_pow_mul, add_comm a,
      add_comm b, add_comm c]
  · obtain ⟨a, b, c, rfl⟩ := mem_a9Base.mp hx
    rw [pow_three, a9c_pow_mul, a9c_pow_mul, show a + (a + a) = 3 * a by ring,
      show b + (b + b) = 3 * b by ring, show c + (c + c) = 3 * c by ring, a9c_pow_three_mul]

theorem a9PermBase_apply (a b c : Fin 3) :
    ((a9PermBase a b c) 0 : ℕ) = a ∧ ((a9PermBase a b c) 3 : ℕ) = 3 + b ∧
      ((a9PermBase a b c) 6 : ℕ) = 6 + c := by
  revert a b c
  decide

theorem card_a9Base : Nat.card a9Base = 3 ^ 3 := by
  let f : Fin 3 × Fin 3 × Fin 3 → a9Base := fun t =>
    ⟨a9c₁ ^ (t.1 : ℕ) * a9c₂ ^ (t.2.1 : ℕ) * a9c₃ ^ (t.2.2 : ℕ), mem_a9Base.mpr ⟨_, _, _, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun s t hst => ?_, fun x => ?_⟩
    · have h : a9PermBase s.1 s.2.1 s.2.2 = a9PermBase t.1 t.2.1 t.2.2 := by
        rw [← coe_a9c_pow, ← coe_a9c_pow]
        exact congrArg (fun x : a9Base => ((x : alternatingGroup (Fin 9)) : Perm (Fin 9))) hst
      obtain ⟨h1, h2, h3⟩ := a9PermBase_apply s.1 s.2.1 s.2.2
      obtain ⟨h1', h2', h3'⟩ := a9PermBase_apply t.1 t.2.1 t.2.2
      rw [h] at h1 h2 h3
      exact Prod.ext (Fin.ext (h1.symm.trans h1')) (Prod.ext (Fin.ext (by omega))
        (Fin.ext (by omega)))
    · obtain ⟨a, b, c, h⟩ := exists_fin_of_mem_a9Base x.2
      exact ⟨(a, b, c), Subtype.ext h.symm⟩
  rw [← Nat.card_eq_of_bijective f hf]
  simp

theorem a9σ_pow_three : a9σ ^ 3 = 1 := Subtype.ext (show a9PermSigma ^ 3 = 1 by decide)

theorem a9σ_ne_one : a9σ ≠ 1 := fun h =>
  absurd (congrArg Subtype.val h) (show a9PermSigma ≠ 1 by decide)

theorem a9z_ne_one : a9z ≠ 1 := fun h =>
  absurd (congrArg Subtype.val h) (show a9PermC₁ * a9PermC₂ * a9PermC₃ ≠ 1 by decide)

theorem commute_a9σ_a9z : Commute a9σ a9z := Subtype.ext
  (show a9PermSigma * (a9PermC₁ * a9PermC₂ * a9PermC₃) =
    a9PermC₁ * a9PermC₂ * a9PermC₃ * a9PermSigma by decide)

theorem a9g_conj_a9z : a9g * a9z * a9g⁻¹ = a9σ := Subtype.ext
  (show a9PermG * (a9PermC₁ * a9PermC₂ * a9PermC₃) * a9PermG⁻¹ = a9PermSigma by decide)

theorem a9g_conj_a9σ : a9g * a9σ * a9g⁻¹ = a9z⁻¹ := Subtype.ext
  (show a9PermG * a9PermSigma * a9PermG⁻¹ = (a9PermC₁ * a9PermC₂ * a9PermC₃)⁻¹ by decide)

theorem a9PermSigma_conj (a b c : Fin 3) :
    a9PermSigma * a9PermBase a b c * a9PermSigma⁻¹ = a9PermBase c a b := by
  revert a b c
  decide

theorem a9PermSigma_fix (a b c : Fin 3) :
    a9PermSigma * a9PermBase a b c * a9PermSigma⁻¹ = a9PermBase a b c →
      a9PermBase a b c = a9PermBase a a a := by
  revert a b c
  decide

theorem a9PermSigma_ne (a b c : Fin 3) : a9PermSigma ≠ a9PermBase a b c := by
  revert a b c
  decide

theorem a9σ_conj_mem {x : alternatingGroup (Fin 9)} (hx : x ∈ a9Base) :
    a9σ * x * a9σ⁻¹ ∈ a9Base := by
  obtain ⟨a, b, c, rfl⟩ := exists_fin_of_mem_a9Base hx
  exact mem_a9Base.mpr ⟨c, a, b, Subtype.ext (a9PermSigma_conj a b c)⟩

theorem a9σ_mem_normalizer :
    a9σ ∈ Subgroup.normalizer (a9Base : Set (alternatingGroup (Fin 9))) := by
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨a9σ_conj_mem, fun hx => ?_⟩
  have h := a9σ_conj_mem (a9σ_conj_mem hx)
  have e : a9σ * (a9σ * (a9σ * x * a9σ⁻¹) * a9σ⁻¹) * a9σ⁻¹ =
      a9σ ^ 3 * x * (a9σ ^ 3)⁻¹ := by
    rw [pow_three']
    group
  rwa [e, a9σ_pow_three, one_mul, inv_one, mul_one] at h

theorem a9σ_not_mem : a9σ ∉ a9Base := fun h => by
  obtain ⟨a, b, c, h⟩ := exists_fin_of_mem_a9Base h
  exact a9PermSigma_ne a b c (congrArg Subtype.val h)

theorem exists_eq_a9z_pow_of_conj_eq {x : alternatingGroup (Fin 9)} (hx : x ∈ a9Base)
    (h : a9σ * x * a9σ⁻¹ = x) : ∃ n : ℕ, x = a9z ^ n := by
  obtain ⟨a, b, c, rfl⟩ := exists_fin_of_mem_a9Base hx
  refine ⟨a, Subtype.ext ?_⟩
  have h' := a9PermSigma_fix a b c (congrArg Subtype.val h)
  rw [a9z_pow, coe_a9c_pow, coe_a9c_pow, h']

theorem isPGroup_a9Base_sup : IsPGroup 3 (a9Base ⊔ Subgroup.zpowers a9σ : Subgroup _) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine IsPGroup.to_sup_of_normal_left' (IsPGroup.of_card card_a9Base)
    (IsPGroup.of_card (n := 1) ?_) (Subgroup.zpowers_le.mpr a9σ_mem_normalizer)
  rw [Nat.card_zpowers, orderOf_eq_prime a9σ_pow_three a9σ_ne_one, pow_one]

end CFSG.AGLEmbedding
