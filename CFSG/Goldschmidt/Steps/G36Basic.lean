module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG

public section

namespace CFSG.Goldschmidt

open CFSG.Open

@[expose] def G36Local (L : Type*) [Group L] (A₀ : Subgroup L) : Prop :=
  ∃ y ∈ Subgroup.normalizer (A₀ : Set L), Odd (orderOf y) ∧
    (∀ b ∈ ⁅A₀, Subgroup.zpowers y⁆, ∀ c ∈ ⁅A₀, Subgroup.zpowers y⁆, b ≠ 1 → c ≠ 1 →
      ∃ k : ℕ, (y ^ k)⁻¹ * b * y ^ k = c) ∧
    (∀ a ∈ A₀, a * y = y * a → a ∈ Subgroup.center L) ∧
    ((∃ m : ℕ, y ^ m ∈ Subgroup.centralizer (A₀ : Set L) ∧
        ∀ z ∈ Subgroup.normalizer (A₀ : Set L), z ^ m ∈ Subgroup.centralizer (A₀ : Set L) →
          z ∈ Subgroup.zpowers y ⊔ Subgroup.centralizer (A₀ : Set L)) ∨
      (IsGoldSz8Cover L ∧
        ((Subgroup.centralizer (A₀ : Set L)).subgroupOf
          (Subgroup.normalizer (A₀ : Set L))).index = 56 ∧
        y ∉ Subgroup.centralizer (A₀ : Set L) ∧ y ^ 7 ∈ Subgroup.centralizer (A₀ : Set L) ∧
        ∀ x ∈ Subgroup.normalizer (A₀ : Set L),
          x⁻¹ * y * x ∈ Subgroup.zpowers y ⊔ Subgroup.centralizer (A₀ : Set L) →
          x ∈ Subgroup.zpowers y ⊔ Subgroup.centralizer (A₀ : Set L)))

structure G36Hyp (L : Type*) [Group L] (A₀ : Subgroup L) (T₀ : Sylow 2 L) : Prop where
  quasisimple : CFSG.Open.IsQuasisimple L
  elem : IsElemAbelian 2 A₀
  le : A₀ ≤ T₀
  closed : ∀ a ∈ A₀, ∀ g : L, g⁻¹ * a * g ∈ (T₀ : Subgroup L) → g⁻¹ * a * g ∈ A₀
  not_le_center : ¬ A₀ ≤ Subgroup.center L
  center_two : ∀ z ∈ Subgroup.center L, ∀ k : ℕ, z ^ 2 ^ k = 1 → z ∈ A₀

section Elements

variable {L : Type*} [Group L]

theorem pow_two_pow_mul_eq_one {x y : L} (hxy : Commute x y) {a b : ℕ} (hx : x ^ 2 ^ a = 1)
    (hy : y ^ 2 ^ b = 1) : (x * y) ^ 2 ^ (a + b) = 1 := by
  rw [hxy.mul_pow, pow_add, pow_mul, hx, one_pow, one_mul, mul_comm, pow_mul, hy, one_pow]

theorem eq_one_of_pow_two_pow_eq_one [Finite L] {N : Subgroup L} (hN : Odd (Nat.card N)) {x : L}
    (hx : x ∈ N) {k : ℕ} (h : x ^ 2 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hx
  have hcop : Nat.Coprime (2 ^ k) (Nat.card N) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hN)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)

theorem exists_pow_two_pow_eq_one {P : Subgroup L} (hP : IsPGroup 2 P) {x : L}
    (hx : x ∈ P) : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem exists_odd_pow [Finite L] (g : L) :
    ∃ k : ℕ, Odd (orderOf (g ^ k)) ∧ ∀ {M : Type*} [Group M] (φ : L →* M),
      Odd (orderOf (φ g)) → Subgroup.zpowers (φ (g ^ k)) = Subgroup.zpowers (φ g) := by
  have hpos : orderOf g ≠ 0 := (orderOf_pos g).ne'
  refine ⟨2 ^ (orderOf g).factorization 2, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (Nat.ordProj_dvd _ _)]
    exact Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two hpos)
  · intro M _ φ hodd
    rw [map_pow]
    apply le_antisymm
    · exact (Subgroup.zpowers_le).mpr
        (Subgroup.pow_mem (Subgroup.zpowers (φ g)) (Subgroup.mem_zpowers (φ g)) _)
    · have hcop : Nat.Coprime (2 ^ (orderOf g).factorization 2) (orderOf (φ g)) :=
        Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
      refine (Subgroup.zpowers_le).mpr ?_
      have := Subgroup.pow_mem (Subgroup.zpowers (φ g ^ 2 ^ (orderOf g).factorization 2))
        (Subgroup.mem_zpowers (φ g ^ 2 ^ (orderOf g).factorization 2)) m
      rwa [hm] at this

theorem mem_normalizer_of_conj_mem [Finite L] {H : Subgroup L} {g : L}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set L) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact h x
  · intro hx
    rw [← heq] at hx
    obtain ⟨w, hw, hwx⟩ := hx
    have : w = x := by
      have := hwx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      exact mul_left_cancel (mul_right_cancel this)
    exact this ▸ hw

end Elements

namespace G36Hyp

variable {L : Type*} [Group L] [Finite L] {A₀ : Subgroup L} {T₀ : Sylow 2 L}

omit [Finite L] in
theorem mul_comm (h : G36Hyp L A₀ T₀) {a b : L} (ha : a ∈ A₀) (hb : b ∈ A₀) : a * b = b * a :=
  congrArg Subtype.val (h.elem.1.is_comm.comm (⟨a, ha⟩ : A₀) ⟨b, hb⟩)

omit [Finite L] in
theorem sq_eq_one (h : G36Hyp L A₀ T₀) {a : L} (ha : a ∈ A₀) : a ^ 2 = 1 := h.elem.2 a ha

omit [Finite L] in
theorem exists_pow_eq_one (_h : G36Hyp L A₀ T₀) {t : L} (ht : t ∈ (T₀ : Subgroup L)) :
    ∃ k : ℕ, t ^ 2 ^ k = 1 :=
  exists_pow_two_pow_eq_one T₀.isPGroup' ht

omit [Finite L] in
theorem mem_sylow_of_mk_mem (h : G36Hyp L A₀ T₀) {g : L} {k : ℕ} (hg : g ^ 2 ^ k = 1)
    (hgT : (g : L ⧸ Subgroup.center L) ∈
      (T₀ : Subgroup L).map (QuotientGroup.mk' (Subgroup.center L))) :
    g ∈ (T₀ : Subgroup L) := by
  obtain ⟨t, ht, hte⟩ := hgT
  have hz : t⁻¹ * g ∈ Subgroup.center L := by
    rw [← QuotientGroup.eq]
    exact hte
  have htg : Commute t⁻¹ g := by
    have hc := Subgroup.mem_center_iff.mp hz t⁻¹
    have : g = t * (t⁻¹ * g) := by group
    show t⁻¹ * g = g * t⁻¹
    conv_rhs => rw [this]
    rw [mul_assoc, ← hc]
    group
  obtain ⟨a, ha⟩ := h.exists_pow_eq_one ht
  have hta : t⁻¹ ^ 2 ^ a = 1 := by rw [inv_pow, ha, inv_one]
  have hzA : t⁻¹ * g ∈ A₀ := h.center_two _ hz _ (pow_two_pow_mul_eq_one htg hta hg)
  have : g = t * (t⁻¹ * g) := by group
  rw [this]
  exact (T₀ : Subgroup L).mul_mem ht (h.le hzA)

omit [Finite L] in
theorem mem_of_mk_mem (h : G36Hyp L A₀ T₀) {t : L} (ht : t ∈ (T₀ : Subgroup L))
    (htA : (t : L ⧸ Subgroup.center L) ∈ A₀.map (QuotientGroup.mk' (Subgroup.center L))) :
    t ∈ A₀ := by
  obtain ⟨a, ha, hae⟩ := htA
  have hz : a⁻¹ * t ∈ Subgroup.center L := by
    rw [← QuotientGroup.eq]
    exact hae
  have hzT : a⁻¹ * t ∈ (T₀ : Subgroup L) :=
    (T₀ : Subgroup L).mul_mem ((T₀ : Subgroup L).inv_mem (h.le ha)) ht
  obtain ⟨k, hk⟩ := h.exists_pow_eq_one hzT
  have hzA : a⁻¹ * t ∈ A₀ := h.center_two _ hz k hk
  have : t = a * (a⁻¹ * t) := by group
  rw [this]
  exact A₀.mul_mem ha hzA

end G36Hyp

end CFSG.Goldschmidt
