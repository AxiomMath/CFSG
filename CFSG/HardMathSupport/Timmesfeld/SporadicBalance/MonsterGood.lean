module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterKleinThree

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.Monster.Existence

section Good

variable {G : Type} [Group G]

@[expose] def PairData (x : G) : Prop :=
  ∃ a b : G, a ∈ Subgroup.centralizer ({x} : Set G) ∧ b ∈ Subgroup.centralizer ({x} : Set G) ∧
    orderOf a = 2 ∧ orderOf b = 2 ∧ a * b = b * a ∧ a ≠ b ∧
    Nat.card ↥(Subgroup.centralizer ({a} : Set G)) = 2 * monsterBabyOrder ∧
    Nat.card ↥(Subgroup.centralizer ({b} : Set G)) = 2 * monsterBabyOrder

@[expose] def Good (x : G) : Prop := InvertedByTwoA x ∨ PairData x

theorem pairData_conj {x : G} (h : PairData x) (c : G) : PairData (c * x * c⁻¹) := by
  obtain ⟨a, b, haC, hbC, ha, hb, hab, hne, hca, hcb⟩ := h
  have hconj : ∀ z : G, z ∈ Subgroup.centralizer ({x} : Set G) →
      c * z * c⁻¹ ∈ Subgroup.centralizer ({c * x * c⁻¹} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    calc c * z * c⁻¹ * (c * x * c⁻¹) = c * (z * x) * c⁻¹ := by group
      _ = c * (x * z) * c⁻¹ := by rw [hz]
      _ = c * x * c⁻¹ * (c * z * c⁻¹) := by group
  refine ⟨c * a * c⁻¹, c * b * c⁻¹, hconj a haC, hconj b hbC, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← ha]; exact (MulEquiv.orderOf_eq (MulAut.conj c) a)
  · rw [← hb]; exact (MulEquiv.orderOf_eq (MulAut.conj c) b)
  · calc c * a * c⁻¹ * (c * b * c⁻¹) = c * (a * b) * c⁻¹ := by group
      _ = c * (b * a) * c⁻¹ := by rw [hab]
      _ = c * b * c⁻¹ * (c * a * c⁻¹) := by group
  · intro h
    apply hne
    have := congrArg (fun y => c⁻¹ * y * c) h
    simpa [mul_assoc] using this
  · rw [natCard_centralizer_conj']; exact hca
  · rw [natCard_centralizer_conj']; exact hcb

theorem invertedByTwoA_conj {x : G} (h : InvertedByTwoA x) (c : G) : InvertedByTwoA (c * x * c⁻¹) := by
  have := h.map (MulAut.conj c)
  simpa [MulAut.conj_apply] using this

theorem good_conj {x : G} (h : Good x) (c : G) : Good (c * x * c⁻¹) :=
  h.imp (fun h => invertedByTwoA_conj h c) (fun h => pairData_conj h c)

theorem good_conj_iff (x c : G) : Good (c * x * c⁻¹) ↔ Good x := by
  refine ⟨fun h => ?_, fun h => good_conj h c⟩
  have := good_conj h c⁻¹
  simpa [mul_assoc] using this

theorem pow_mul_eq_self {p : ℕ} {x : G} (hx : x ^ p = 1) {k k' : ℕ} (h : k * k' % p = 1) :
    x ^ (k * k') = x := by
  have h1 : k * k' = p * (k * k' / p) + 1 := by
    have := Nat.div_add_mod (k * k') p
    omega
  rw [h1, pow_add, pow_mul, hx, one_pow, one_mul, pow_one]

theorem centralizer_pow_eq_of_coprime {p : ℕ} (hp : p.Prime) {x : G} (hx : x ^ p = 1) {k : ℕ}
    (hk : Nat.Coprime k p) :
    Subgroup.centralizer ({x ^ k} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  obtain ⟨k', -, hk'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hk hp.one_lt
  ext z
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h2 : z * (x ^ k) ^ k' = (x ^ k) ^ k' * z :=
      (Commute.pow_right (show Commute z (x ^ k) from h) k').eq
    rwa [← pow_mul, pow_mul_eq_self hx hk'] at h2
  · intro h
    exact (Commute.pow_right (show Commute z x from h) k).eq

theorem invertedByTwoA_pow {p : ℕ} (hp : p.Prime) {x : G} (hx : x ^ p = 1) {k : ℕ}
    (hk : Nat.Coprime k p) : InvertedByTwoA x ↔ InvertedByTwoA (x ^ k) := by
  obtain ⟨k', -, hk'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hk hp.one_lt
  constructor
  · rintro ⟨α, h1, h2, h3⟩
    refine ⟨α, h1, h2, ?_⟩
    rw [← conj_pow, h3, inv_pow]
  · rintro ⟨α, h1, h2, h3⟩
    refine ⟨α, h1, h2, ?_⟩
    have := congrArg (fun y => y ^ k') h3
    simp only [← conj_pow, inv_pow, ← pow_mul, pow_mul_eq_self hx hk'] at this
    have hy : (α * x * α⁻¹) ^ p = 1 := by rw [conj_pow, hx]; group
    rw [pow_mul_eq_self hy hk'] at this
    exact this

theorem good_pow_iff {p : ℕ} (hp : p.Prime) {x : G} (hx : x ^ p = 1) {k : ℕ}
    (hk : Nat.Coprime k p) : Good (x ^ k) ↔ Good x := by
  unfold Good PairData
  rw [centralizer_pow_eq_of_coprime hp hx hk, ← invertedByTwoA_pow hp hx hk]

end Good

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
