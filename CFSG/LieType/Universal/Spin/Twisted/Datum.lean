module

public import CFSG.LieType.Universal.Spin.Twisted.Frame
public import CFSG.LieType.Universal.Spin.Datum

public section

namespace CFSG.LieType.Universal.Spin.Twisted

open CliffordAlgebra QuadraticMap CFSG.LieType.RootSystem CFSG.LieType.CurtisTits

variable (n : ℕ) {K : Type*} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

@[expose] noncomputable def twShortRootGroup (v : Fin (n - 1) → ℤ) :
    Subgroup (spinGroup (quadMinus n K b c)) :=
  ⨆ (i : Fin (n - 1)) (s : Bool) (_ : v = Pi.single i (boolSign s)), (twShortRoot n hirr i s).range

theorem twShortRootGroup_eq (i : Fin (n - 1)) (s : Bool) :
    twShortRootGroup n hirr (Pi.single i (boolSign s)) = (twShortRoot n hirr i s).range := by
  refine le_antisymm (iSup_le fun i' => iSup_le fun s' => iSup_le fun h => ?_) ?_
  · obtain ⟨rfl, hs⟩ := (single_eq_single_iff' (boolSign_ne_zero s)).mp h
    obtain rfl := boolSign_injective hs
    exact le_rfl
  · exact le_iSup_of_le i (le_iSup_of_le s (le_iSup_of_le rfl le_rfl))

theorem twShortRootGroup_add {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) :
    twShortRootGroup n hirr (Pi.single i (boolSign s) + Pi.single j (boolSign t)) = ⊥ := by
  refine eq_bot_iff.mpr (iSup_le fun i' => iSup_le fun s' => iSup_le fun h => ?_)
  exact absurd h.symm (single_ne_single_add_single hij (boolSign_ne_zero s) (boolSign_ne_zero t))

@[expose] noncomputable def minusRootGroup (γ : Fin (n - 1) → ℤ) :
    Subgroup (spinGroup (quadMinus n K b c)) :=
  (minusFrame n b c).longRootGroup (toStdB (n - 1) γ) ⊔ twShortRootGroup n hirr (toStdB (n - 1) γ)

@[expose] noncomputable def minusDatum : UniversalRootDatum (spinGroup (quadMinus n K b c)) where
  rank := n - 1
  cartan := cartanB (n - 1)
  isFiniteType := isFiniteType_cartanB (n - 1)
  divisible := ∅
  rootGroup := minusRootGroup n hirr

theorem minusDatum_roots :
    (minusDatum n hirr).roots = RootSystem.roots (isFiniteType_cartanB (n - 1)) ∅ :=
  rfl

theorem minusRootGroup_eq_long {γ : Fin (n - 1) → ℤ} {i j : Fin (n - 1)} (hij : i ≠ j)
    (s t : Bool) (h : toStdB (n - 1) γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    minusRootGroup n hirr γ = ((minusFrame n b c).longRoot hij s t).range := by
  rw [minusRootGroup, h, HypFrame.longRootGroup_eq, twShortRootGroup_add n hirr hij, sup_bot_eq]

theorem minusRootGroup_eq_short {γ : Fin (n - 1) → ℤ} (i : Fin (n - 1)) (s : Bool)
    (h : toStdB (n - 1) γ = Pi.single i (boolSign s)) :
    minusRootGroup n hirr γ = (twShortRoot n hirr i s).range := by
  rw [minusRootGroup, h, HypFrame.longRootGroup_single, twShortRootGroup_eq, bot_sup_eq]

theorem mem_minusRootGroup_long_iff {γ : Fin (n - 1) → ℤ} {i j : Fin (n - 1)} (hij : i ≠ j)
    (s t : Bool) (h : toStdB (n - 1) γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    {x : spinGroup (quadMinus n K b c)} :
    x ∈ minusRootGroup n hirr γ ↔ ∃ a : K, x = (minusFrame n b c).longRoot hij s t (.ofAdd a) := by
  rw [minusRootGroup_eq_long n hirr hij s t h, MonoidHom.mem_range]
  exact ⟨fun ⟨a, ha⟩ => ⟨Multiplicative.toAdd a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨_, ha.symm⟩⟩

theorem mem_minusRootGroup_short_iff {γ : Fin (n - 1) → ℤ} (i : Fin (n - 1)) (s : Bool)
    (h : toStdB (n - 1) γ = Pi.single i (boolSign s)) {x : spinGroup (quadMinus n K b c)} :
    x ∈ minusRootGroup n hirr γ ↔ ∃ p : Fin 2 → K, x = twShortRoot n hirr i s (.ofAdd p) := by
  rw [minusRootGroup_eq_short n hirr i s h, MonoidHom.mem_range]
  exact ⟨fun ⟨p, hp⟩ => ⟨Multiplicative.toAdd p, hp.symm⟩, fun ⟨p, hp⟩ => ⟨_, hp.symm⟩⟩

theorem longRoot_mem_minusRootGroup {γ : Fin (n - 1) → ℤ} {i j : Fin (n - 1)} (hij : i ≠ j)
    (s t : Bool) (h : toStdB (n - 1) γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    (a : K) : (minusFrame n b c).longRoot hij s t (.ofAdd a) ∈ minusRootGroup n hirr γ :=
  (mem_minusRootGroup_long_iff n hirr hij s t h).mpr ⟨a, rfl⟩

theorem twShortRoot_mem_minusRootGroup {γ : Fin (n - 1) → ℤ} (i : Fin (n - 1)) (s : Bool)
    (h : toStdB (n - 1) γ = Pi.single i (boolSign s)) (p : Fin 2 → K) :
    twShortRoot n hirr i s (.ofAdd p) ∈ minusRootGroup n hirr γ :=
  (mem_minusRootGroup_short_iff n hirr i s h).mpr ⟨p, rfl⟩

theorem exists_toStdB_eq_of_mem_roots {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) :
    (∃ (i j : Fin (n - 1)) (_ : i ≠ j) (s t : Bool),
        toStdB (n - 1) γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) ∨
      ∃ (i : Fin (n - 1)) (s : Bool), toStdB (n - 1) γ = Pi.single i (boolSign s) := by
  rw [rootsB_eq] at hγ
  rcases hγ with ⟨i, j, s, t, hij, hs, ht, h⟩ | ⟨i, s, hs, h⟩
  · obtain ⟨s', rfl⟩ := exists_boolSign_eq hs
    obtain ⟨t', rfl⟩ := exists_boolSign_eq ht
    exact Or.inl ⟨i, j, hij, s', t', h⟩
  · obtain ⟨s', rfl⟩ := exists_boolSign_eq hs
    exact Or.inr ⟨i, s', h⟩

theorem mem_roots_of_toStdB_eq_long {γ : Fin (n - 1) → ℤ} {i j : Fin (n - 1)} (hij : i ≠ j)
    (s t : Bool) (h : toStdB (n - 1) γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅ := by
  rw [rootsB_eq]
  exact Or.inl ⟨i, j, boolSign s, boolSign t, hij, boolSign_eq_one_or_eq_neg_one s,
    boolSign_eq_one_or_eq_neg_one t, h⟩

theorem mem_roots_of_toStdB_eq_short {γ : Fin (n - 1) → ℤ} (i : Fin (n - 1)) (s : Bool)
    (h : toStdB (n - 1) γ = Pi.single i (boolSign s)) :
    γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅ := by
  rw [rootsB_eq]
  exact Or.inr ⟨i, boolSign s, boolSign_eq_one_or_eq_neg_one s, h⟩

theorem toStdB_single_of_lt' {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    toStdB (n - 1) (Pi.single k 1) =
      Pi.single k (boolSign true) + Pi.single ⟨k.val + 1, hk⟩ (boolSign false) := by
  rw [toStdB_single_of_lt _ hk, boolSign_true, boolSign_false, Pi.single_neg, sub_eq_add_neg]

theorem toStdB_neg_single_of_lt' {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    toStdB (n - 1) (-Pi.single k 1) =
      Pi.single ⟨k.val + 1, hk⟩ (boolSign true) + Pi.single k (boolSign false) := by
  rw [toStdB_neg, toStdB_single_of_lt _ hk, boolSign_true, boolSign_false, neg_sub,
    Pi.single_neg, sub_eq_add_neg]

theorem toStdB_single_of_not_lt' {k : Fin (n - 1)} (hk : ¬k.val + 1 < n - 1) :
    toStdB (n - 1) (Pi.single k 1) = Pi.single k (boolSign true) := by
  rw [toStdB_single_of_not_lt _ hk, boolSign_true]

theorem toStdB_neg_single_of_not_lt' {k : Fin (n - 1)} (hk : ¬k.val + 1 < n - 1) :
    toStdB (n - 1) (-Pi.single k 1) = Pi.single k (boolSign false) := by
  rw [toStdB_neg, toStdB_single_of_not_lt _ hk, boolSign_false, Pi.single_neg]

theorem succ_ne_of_lt {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    k ≠ (⟨k.val + 1, hk⟩ : Fin (n - 1)) :=
  Fin.ne_of_val_ne (by simp)

theorem minusRootGroup_single_of_lt {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    minusRootGroup n hirr (Pi.single k 1) =
      ((minusFrame n b c).longRoot (succ_ne_of_lt n hk) true false).range :=
  minusRootGroup_eq_long n hirr _ true false (toStdB_single_of_lt' n hk)

theorem minusRootGroup_neg_single_of_lt {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    minusRootGroup n hirr (-Pi.single k 1) =
      ((minusFrame n b c).longRoot (succ_ne_of_lt n hk).symm true false).range :=
  minusRootGroup_eq_long n hirr _ true false (toStdB_neg_single_of_lt' n hk)

theorem minusRootGroup_single_of_not_lt {k : Fin (n - 1)} (hk : ¬k.val + 1 < n - 1) :
    minusRootGroup n hirr (Pi.single k 1) = (shortPosHom n hirr k).range :=
  minusRootGroup_eq_short n hirr k true (toStdB_single_of_not_lt' n hk)

theorem minusRootGroup_neg_single_of_not_lt {k : Fin (n - 1)} (hk : ¬k.val + 1 < n - 1) :
    minusRootGroup n hirr (-Pi.single k 1) = (shortNegHom n hirr k).range :=
  minusRootGroup_eq_short n hirr k false (toStdB_neg_single_of_not_lt' n hk)

theorem rankOne_minusRootGroup_of_lt {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    rankOne (minusRootGroup n hirr) k =
      ((minusFrame n b c).longSL2 (succ_ne_of_lt n hk) true false).range := by
  rw [rankOne, minusRootGroup_single_of_lt n hirr hk, minusRootGroup_neg_single_of_lt n hirr hk]
  refine le_antisymm (sup_le ?_ ?_) ?_
  · rintro _ ⟨a, rfl⟩
    exact ⟨upperSL2 (Multiplicative.toAdd a),
      (minusFrame n b c).longSL2_upperSL2 (succ_ne_of_lt n hk) true false _⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨lowerSL2 (Multiplicative.toAdd a),
      (minusFrame n b c).longSL2_lowerSL2 (succ_ne_of_lt n hk) true false _⟩
  · rintro _ ⟨M, rfl⟩
    refine (Subgroup.closure_le _).mpr ?_
      (mem_closure_upperSL2_lowerSL2 ((minusFrame n b c).longSL2 (succ_ne_of_lt n hk) true false) M)
    rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact Subgroup.mem_sup_left ⟨.ofAdd a,
        ((minusFrame n b c).longSL2_upperSL2 (succ_ne_of_lt n hk) true false a).symm⟩
    · exact Subgroup.mem_sup_right ⟨.ofAdd a,
        ((minusFrame n b c).longSL2_lowerSL2 (succ_ne_of_lt n hk) true false a).symm⟩

theorem rankOne_minusRootGroup_of_not_lt {k : Fin (n - 1)} (hk : ¬k.val + 1 < n - 1) :
    rankOne (minusRootGroup n hirr) k =
      (shortPosHom n hirr k).range ⊔ (shortNegHom n hirr k).range := by
  rw [rankOne, minusRootGroup_single_of_not_lt n hirr hk,
    minusRootGroup_neg_single_of_not_lt n hirr hk]

@[expose] noncomputable def minusWeyl (k : Fin (n - 1)) : spinGroup (quadMinus n K b c) :=
  if h : k.val + 1 < n - 1 then (minusFrame n b c).longWeyl (succ_ne_of_lt n h) true false
  else shortWeyl n hirr k

@[expose] noncomputable def minusTorus (k : Fin (n - 1)) :
    Subgroup (spinGroup (quadMinus n K b c)) :=
  if h : k.val + 1 < n - 1 then ((minusFrame n b c).longTorus (succ_ne_of_lt n h) true false).range
  else shortTorus n hirr k

theorem minusWeyl_of_lt {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    minusWeyl n hirr k = (minusFrame n b c).longWeyl (succ_ne_of_lt n hk) true false := by
  rw [minusWeyl, dite_eq_left hk]

theorem minusWeyl_of_not_lt {k : Fin (n - 1)} (hk : ¬k.val + 1 < n - 1) :
    minusWeyl n hirr k = shortWeyl n hirr k := by
  rw [minusWeyl, dite_eq_right hk]

theorem minusTorus_of_lt {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    minusTorus n hirr k = ((minusFrame n b c).longTorus (succ_ne_of_lt n hk) true false).range := by
  rw [minusTorus, dite_eq_left hk]

theorem minusTorus_of_not_lt {k : Fin (n - 1)} (hk : ¬k.val + 1 < n - 1) :
    minusTorus n hirr k = shortTorus n hirr k := by
  rw [minusTorus, dite_eq_right hk]

end CFSG.LieType.Universal.Spin.Twisted
