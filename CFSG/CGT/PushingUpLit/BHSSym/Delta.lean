module

public import CFSG.Quasithin.Background.G6Natural
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.CGT.PushingUpLit.BHSSym

open CFSG.Quasithin CFSG.Quasithin.G6

@[expose] def rootVec (m : ℕ) (i j : Fin m) : coreMod m :=
  ⟨Multiplicative.ofAdd (Pi.single i 1 + Pi.single j 1 : Fin m → ZMod 2), by
    rw [mem_coreMod]
    simp only [toAdd_ofAdd, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']
    simp only [Finset.mem_univ, ite_true]
    exact CharTwo.add_self_eq_zero (1 : ZMod 2)⟩

theorem toAdd_rootVec (m : ℕ) (i j k : Fin m) :
    Multiplicative.toAdd ((rootVec m i j : coreMod m) : PermMod m) k =
      (Pi.single i 1 : Fin m → ZMod 2) k + (Pi.single j 1 : Fin m → ZMod 2) k := rfl

theorem toAdd_mul_coreMod {m : ℕ} (v w : coreMod m) (k : Fin m) :
    Multiplicative.toAdd ((v * w : coreMod m) : PermMod m) k =
      Multiplicative.toAdd (v : PermMod m) k + Multiplicative.toAdd (w : PermMod m) k := rfl

theorem coreMod_ext {m : ℕ} {v w : coreMod m}
    (h : ∀ k, Multiplicative.toAdd (v : PermMod m) k = Multiplicative.toAdd (w : PermMod m) k) :
    v = w := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext k
  exact h k

theorem coreAct_rootVec (m : ℕ) (σ : Equiv.Perm (Fin m)) (i j : Fin m) :
    coreAct m σ (rootVec m i j) = rootVec m (σ i) (σ j) := by
  refine coreMod_ext fun k => ?_
  show Multiplicative.toAdd (permAct m σ (rootVec m i j : PermMod m)) k = _
  rw [permAct_apply, toAdd_rootVec, toAdd_rootVec]
  simp only [Pi.single_apply, Equiv.Perm.inv_eq_iff_eq]

theorem rootVec_comm (m : ℕ) (i j : Fin m) : rootVec m i j = rootVec m j i := by
  refine coreMod_ext fun k => ?_
  rw [toAdd_rootVec, toAdd_rootVec, add_comm]

theorem rootVec_mul (m : ℕ) (i j l : Fin m) :
    rootVec m i j * rootVec m j l = rootVec m i l := by
  refine coreMod_ext fun k => ?_
  rw [toAdd_mul_coreMod, toAdd_rootVec, toAdd_rootVec, toAdd_rootVec]
  have h : ∀ a b c : ZMod 2, a + b + (b + c) = a + c := by decide
  exact h _ _ _

@[expose] def rootBasisCoord (k : ℕ) (c : Fin k → ZMod 2) (i : Fin (k + 1)) : ZMod 2 :=
  ∑ j : Fin k, c j * ((Pi.single j.castSucc 1 : Fin (k + 1) → ZMod 2) i +
    (Pi.single j.succ 1 : Fin (k + 1) → ZMod 2) i)

theorem rootBasisCoord_add (k : ℕ) (c c' : Fin k → ZMod 2) (i : Fin (k + 1)) :
    rootBasisCoord k (c + c') i = rootBasisCoord k c i + rootBasisCoord k c' i := by
  simp [rootBasisCoord, add_mul, Finset.sum_add_distrib]

theorem rootBasisCoord_zero (k : ℕ) (i : Fin (k + 1)) : rootBasisCoord k 0 i = 0 := by
  simp [rootBasisCoord]

theorem sum_rootBasisCoord (k : ℕ) (c : Fin k → ZMod 2) : ∑ i, rootBasisCoord k c i = 0 := by
  unfold rootBasisCoord
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.sum_pi_single']
  simp [CharTwo.add_self_eq_zero (1 : ZMod 2)]

@[expose] def rootBasisHom (k : ℕ) : Multiplicative (Fin k → ZMod 2) →* coreMod (k + 1) where
  toFun c := ⟨Multiplicative.ofAdd (rootBasisCoord k (Multiplicative.toAdd c)), by
    rw [mem_coreMod]
    exact sum_rootBasisCoord k _⟩
  map_one' := coreMod_ext fun i => rootBasisCoord_zero k i
  map_mul' c c' := coreMod_ext fun i => rootBasisCoord_add k _ _ i

theorem toAdd_rootBasisHom (k : ℕ) (c : Multiplicative (Fin k → ZMod 2)) (i : Fin (k + 1)) :
    Multiplicative.toAdd ((rootBasisHom k c : coreMod (k + 1)) : PermMod (k + 1)) i =
      rootBasisCoord k (Multiplicative.toAdd c) i := rfl

theorem rootBasisCoord_castSucc (k : ℕ) (c : Fin k → ZMod 2) (j₀ : Fin k)
    (hmin : ∀ j, j < j₀ → c j = 0) : rootBasisCoord k c j₀.castSucc = c j₀ := by
  unfold rootBasisCoord
  rw [Finset.sum_eq_single j₀]
  · have h3 : j₀.castSucc ≠ j₀.succ := (Fin.castSucc_lt_succ).ne
    simp [h3]
  · intro j _ hj
    have h1 : j₀.castSucc ≠ j.castSucc := fun h => hj (Fin.castSucc_injective _ h).symm
    by_cases h2 : j₀.castSucc = j.succ
    · have : j < j₀ := by
        rw [Fin.lt_def]
        have := congrArg Fin.val h2
        simp at this
        omega
      rw [hmin j this, zero_mul]
    · simp [h1, h2]
  · intro h
    exact absurd (Finset.mem_univ j₀) h

theorem rootBasisHom_injective (k : ℕ) : Function.Injective (rootBasisHom k) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  by_contra hne
  have hd : Multiplicative.toAdd c ≠ 0 := fun h => hne (Multiplicative.toAdd.injective h)
  obtain ⟨j₁, hj₁⟩ : ∃ j, Multiplicative.toAdd c j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hd (funext hcon)
  obtain ⟨j₀, hj₀, hmin⟩ := (wellFounded_lt (α := Fin k)).has_min
    {j | Multiplicative.toAdd c j ≠ 0} ⟨j₁, hj₁⟩
  have hz : ∀ j, j < j₀ → Multiplicative.toAdd c j = 0 := fun j hj => by
    by_contra h
    exact hmin j h hj
  have h0 := congrArg (fun v : coreMod (k + 1) => Multiplicative.toAdd (v : PermMod (k + 1))
    j₀.castSucc) hc
  simp only [toAdd_rootBasisHom] at h0
  rw [rootBasisCoord_castSucc k _ j₀ hz] at h0
  exact hj₀ h0

@[expose] def coreModEquiv (k : ℕ) : coreMod (k + 1) ≃ (Fin k → ZMod 2) where
  toFun v := fun j => Multiplicative.toAdd (v : PermMod (k + 1)) j.castSucc
  invFun c := ⟨Multiplicative.ofAdd (Fin.snoc c (∑ j, c j) : Fin (k + 1) → ZMod 2), by
    rw [mem_coreMod, Fin.sum_univ_castSucc]
    simp only [toAdd_ofAdd, Fin.snoc_castSucc, Fin.snoc_last]
    exact CharTwo.add_self_eq_zero _⟩
  left_inv v := by
    refine coreMod_ext fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have h := v.2
      rw [mem_coreMod, Fin.sum_univ_castSucc] at h
      simp only [toAdd_ofAdd, Fin.snoc_last]
      exact CharTwo.add_eq_zero.1 h
    · simp only [toAdd_ofAdd, Fin.snoc_castSucc]
  right_inv c := by
    funext j
    simp only [toAdd_ofAdd, Fin.snoc_castSucc]

theorem card_coreMod_succ (k : ℕ) : Nat.card (coreMod (k + 1)) = 2 ^ k := by
  rw [Nat.card_congr (coreModEquiv k), Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]

theorem rootBasisHom_bijective (k : ℕ) : Function.Bijective (rootBasisHom k) := by
  refine (rootBasisHom_injective k).bijective_of_nat_card_le ?_
  rw [card_coreMod_succ, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]

noncomputable def rootBasis (k : ℕ) : Multiplicative (Fin k → ZMod 2) ≃* coreMod (k + 1) :=
  MulEquiv.ofBijective (rootBasisHom k) (rootBasisHom_bijective k)

theorem rootBasis_single (k : ℕ) (j : Fin k) :
    rootBasis k (Multiplicative.ofAdd (Pi.single j 1)) =
      rootVec (k + 1) j.castSucc j.succ := by
  refine coreMod_ext fun i => ?_
  show rootBasisCoord k (Pi.single j 1) i = _
  rw [toAdd_rootVec]
  unfold rootBasisCoord
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'
    simp [hj']
  · intro h
    exact absurd (Finset.mem_univ j) h

@[expose] def extZero {k : ℕ} (c : Fin k → ZMod 2) (n : ℕ) : ZMod 2 :=
  if h : n < k then c ⟨n, h⟩ else 0

theorem extZero_of_lt {k : ℕ} (c : Fin k → ZMod 2) {n : ℕ} (h : n < k) :
    extZero c n = c ⟨n, h⟩ := by
  simp [extZero, h]

theorem extZero_of_ge {k : ℕ} (c : Fin k → ZMod 2) {n : ℕ} (h : k ≤ n) : extZero c n = 0 := by
  simp [extZero, not_lt.2 h]

theorem sum_ite_val_eq {k : ℕ} (c : Fin k → ZMod 2) (n : ℕ) :
    (∑ j : Fin k, if n = (j : ℕ) then c j else 0) = extZero c n := by
  by_cases h : n < k
  · rw [extZero_of_lt c h, Finset.sum_eq_single ⟨n, h⟩]
    · simp
    · intro j _ hj
      have : n ≠ j := fun e => hj (Fin.ext e.symm)
      simp [this]
    · simp
  · rw [extZero_of_ge c (not_lt.1 h)]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : n ≠ j := fun e => h (e ▸ j.2)
    simp [this]

theorem sum_neighbours {k : ℕ} (c : Fin k → ZMod 2) (i : Fin k) :
    (∑ j : Fin k, if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then c j else 0) =
      extZero c (i + 1) + (if 0 < (i : ℕ) then extZero c (i - 1) else 0) := by
  have hsplit : ∀ j : Fin k, (if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then c j else 0) =
      (if (i : ℕ) + 1 = j then c j else 0) + (if (j : ℕ) + 1 = i then c j else 0) := by
    intro j
    by_cases h1 : (i : ℕ) + 1 = j <;> by_cases h2 : (j : ℕ) + 1 = i <;> simp [h1, h2]
    omega
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib, sum_ite_val_eq]
  congr 1
  by_cases hi : 0 < (i : ℕ)
  · simp only [hi, ↓reduceIte]
    rw [← sum_ite_val_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : (j : ℕ) + 1 = i ↔ (i : ℕ) - 1 = j := by omega
    simp only [this]
  · simp only [hi, ↓reduceIte]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : ¬ (j : ℕ) + 1 = i := by omega
    simp [this]

theorem cartan_inj {k : ℕ} (hk : Even k) (c : Fin k → ZMod 2)
    (h : ∀ i : Fin k, (∑ j : Fin k, if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then c j else 0) = 0) :
    c = 0 := by
  have hE : ∀ i : ℕ, i < k → extZero c (i + 1) + (if 0 < i then extZero c (i - 1) else 0) = 0 :=
    fun i hi => by
      have := h ⟨i, hi⟩
      rwa [sum_neighbours] at this
  obtain ⟨m, hm⟩ := hk
  have hodd : ∀ t : ℕ, 2 * t + 1 < k → extZero c (2 * t + 1) = 0 := by
    intro t
    induction t with
    | zero =>
      intro ht
      have := hE 0 (by omega)
      simpa using this
    | succ t ih =>
      intro ht
      have h1 := hE (2 * t + 2) (by omega)
      have hpos : 0 < 2 * t + 2 := by omega
      simp only [hpos, ↓reduceIte] at h1
      have h2 : 2 * t + 2 - 1 = 2 * t + 1 := by omega
      rw [h2, ih (by omega)] at h1
      simpa [add_assoc, show 2 * (t + 1) + 1 = 2 * t + 2 + 1 by omega] using h1
  have heven : ∀ r : ℕ, 2 * r + 2 ≤ k → extZero c (k - 2 - 2 * r) = 0 := by
    intro r
    induction r with
    | zero =>
      intro hr
      have h1 := hE (k - 1) (by omega)
      have hpos : 0 < k - 1 := by omega
      simp only [hpos, ↓reduceIte] at h1
      have h2 : k - 1 + 1 = k := by omega
      have h3 : k - 1 - 1 = k - 2 - 2 * 0 := by omega
      rw [h2, h3, extZero_of_ge c (le_refl k)] at h1
      simpa using h1
    | succ r ih =>
      intro hr
      have h1 := hE (k - 2 - 2 * (r + 1) + 1) (by omega)
      have hpos : 0 < k - 2 - 2 * (r + 1) + 1 := by omega
      simp only [hpos, ↓reduceIte] at h1
      have h2 : k - 2 - 2 * (r + 1) + 1 + 1 = k - 2 - 2 * r := by omega
      have h3 : k - 2 - 2 * (r + 1) + 1 - 1 = k - 2 - 2 * (r + 1) := by omega
      rw [h2, h3, ih (by omega), zero_add] at h1
      exact h1
  funext j
  show c j = 0
  have hj : extZero c j = 0 := by
    rcases Nat.even_or_odd (j : ℕ) with he | ho
    · obtain ⟨a, ha⟩ := he
      have := heven (m - 1 - a) (by omega)
      have h4 : k - 2 - 2 * (m - 1 - a) = j := by omega
      rwa [h4] at this
    · obtain ⟨a, ha⟩ := ho
      have := hodd a (by omega)
      rwa [← ha] at this
  rwa [extZero_of_lt c j.2] at hj

end CFSG.CGT.PushingUpLit.BHSSym
