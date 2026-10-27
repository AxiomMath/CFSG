module

public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KDType

theorem pow_apply_of_apply_eq {V : Type} [Group V] {f : MulAut V} {x : V} (h : f x = x)
    (m : ℕ) : (f ^ m) x = x := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ', MulAut.mul_apply, ih, h]

theorem apply_eq_of_pow_apply_eq {V : Type} [Group V] {σ : MulAut V} (h7 : σ ^ 7 = 1)
    {k : ℕ} (hk0 : 0 < k) (hk7 : k < 7) {x : V} (hx : (σ ^ k) x = x) : σ x = x := by
  have hm : ∀ k < 7, 0 < k → ∃ m < 7, k * m % 7 = 1 := by decide
  obtain ⟨m, -, hmk⟩ := hm k hk7 hk0
  have hdiv : k * m = 7 * (k * m / 7) + 1 := by
    have := Nat.div_add_mod (k * m) 7
    omega
  have hσ : σ = (σ ^ k) ^ m := by
    rw [← pow_mul, hdiv, pow_succ, pow_mul, h7, one_pow, one_mul]
  rw [hσ]
  exact pow_apply_of_apply_eq hx m

theorem pow_apply_comm {V : Type} [Group V] (σ : MulAut V) (i : ℕ) (x : V) :
    (σ ^ i) (σ x) = σ ((σ ^ i) x) := by
  rw [← MulAut.mul_apply, ← MulAut.mul_apply, (Commute.self_pow σ i).eq]

theorem pow_apply_ne_of_lt {V : Type} [Group V] {σ : MulAut V} (h7 : σ ^ 7 = 1) {x : V}
    (hx : σ x ≠ x) {i j : ℕ} (hj : j < 7) (hij : i < j) : (σ ^ i) x ≠ (σ ^ j) x := by
  intro h
  have hsplit : (σ ^ j) x = (σ ^ i) ((σ ^ (j - i)) x) := by
    rw [← MulAut.mul_apply, ← pow_add, Nat.add_sub_cancel' hij.le]
  rw [hsplit] at h
  have h' : x = (σ ^ (j - i)) x := (MulEquiv.injective (σ ^ i)) h
  exact hx (apply_eq_of_pow_apply_eq h7 (by omega) (by omega) h'.symm)

theorem pow_apply_inj {V : Type} [Group V] {σ : MulAut V} (h7 : σ ^ 7 = 1) {x : V}
    (hx : σ x ≠ x) {i j : ℕ} (hi : i < 7) (hj : j < 7) (h : (σ ^ i) x = (σ ^ j) x) :
    i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact absurd h (pow_apply_ne_of_lt h7 hx hj hij)
  · exact hij
  · exact absurd h.symm (pow_apply_ne_of_lt h7 hx hi hij)

theorem pow_apply_ne_one {V : Type} [Group V] {σ : MulAut V} (h7 : σ ^ 7 = 1) {x : V}
    (hx : σ x ≠ x) {i : ℕ} (hi : i < 7) : (σ ^ i) x ≠ 1 := by
  intro h
  have h7x : (σ ^ (7 - i)) ((σ ^ i) x) = x := by
    rw [← MulAut.mul_apply, ← pow_add, Nat.sub_add_cancel hi.le, h7, MulAut.one_apply]
  rw [h, map_one] at h7x
  apply hx
  rw [← h7x, map_one]

theorem pow_apply_mem {V : Type} [Group V] {σ : MulAut V} {T : Set V}
    (hinv : ∀ v ∈ T, σ v ∈ T) {v : V} (hv : v ∈ T) (j : ℕ) : (σ ^ j) v ∈ T := by
  induction j with
  | zero => simpa using hv
  | succ j ih => rw [pow_succ', MulAut.mul_apply]; exact hinv _ ih

theorem card_invariant_ge_seven {V : Type} [Group V] [Finite V] (hV : Nat.card V = 8)
    {σ : MulAut V} (h7 : σ ^ 7 = 1) (h1 : σ ≠ 1) {T : Set V} (hinv : ∀ v ∈ T, σ v ∈ T)
    (hT : ∃ v ∈ T, v ≠ 1) : 7 ≤ Nat.card T := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  have hV' : Fintype.card V = 8 := by rw [← Nat.card_eq_fintype_card]; exact hV
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra hcon
    push_neg at hcon
    exact h1 (MulEquiv.ext fun y => hcon y)
  let f : Fin 7 → V := fun i => (σ ^ (i : ℕ)) x
  have hfinj : Function.Injective f := fun i j hij =>
    Fin.ext (pow_apply_inj h7 hx i.isLt j.isLt hij)
  have hfne : ∀ i, f i ≠ 1 := fun i => pow_apply_ne_one h7 hx i.isLt
  have hS : Finset.univ.image f = Finset.univ.erase 1 := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_erase.mpr ⟨hfne i, Finset.mem_univ _⟩
    · rw [Finset.card_image_of_injective _ hfinj, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Finset.card_univ, hV', Fintype.card_fin]
  obtain ⟨v, hvT, hv1⟩ := hT
  have hvmem : v ∈ Finset.univ.image f := by
    rw [hS]
    exact Finset.mem_erase.mpr ⟨hv1, Finset.mem_univ _⟩
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hvmem
  have hvx : σ v ≠ v := by
    intro hfix
    apply hx
    rw [← hi] at hfix
    simp only [f] at hfix
    have hc : (σ ^ (i : ℕ)) (σ x) = (σ ^ (i : ℕ)) x := by
      rw [pow_apply_comm]
      exact hfix
    exact (MulEquiv.injective (σ ^ (i : ℕ))) hc
  let g : Fin 7 → T := fun j => ⟨(σ ^ (j : ℕ)) v, pow_apply_mem hinv hvT j⟩
  have hgi : Function.Injective g := fun j k hjk => by
    have h := congrArg Subtype.val hjk
    exact Fin.ext (pow_apply_inj h7 hvx j.isLt k.isLt h)
  have hle := Nat.card_le_card_of_injective g hgi
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hle
  exact hle

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KDType
