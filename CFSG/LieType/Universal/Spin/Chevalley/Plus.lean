module

public import CFSG.LieType.Universal.Spin.Chevalley.Braid
public import CFSG.LieType.Universal.Spin.Forms
import CFSG.LieType.Universal.SpinCenter

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap

variable (n : ℕ) (K : Type*) [Field K]

theorem exists_ne_and_ne {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) : ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have key : ∀ m : ℕ, m < n → m = i.val ∨ m = j.val := fun m hm => by
    by_cases hmi : (⟨m, hm⟩ : Fin n) = i
    · left
      rw [← hmi]
    · right
      rw [← h _ hmi]
  have := key 0 (by omega)
  have := key 1 (by omega)
  have := key 2 (by omega)
  omega

@[expose] def plusVec (i : Fin n) : Bool → Fin n ⊕ Fin n → K
  | true => Pi.single (.inl i) 1
  | false => Pi.single (.inr i) 1

@[simp] theorem plusVec_true (i : Fin n) : plusVec n K i true = Pi.single (.inl i) 1 := rfl

@[simp] theorem plusVec_false (i : Fin n) : plusVec n K i false = Pi.single (.inr i) 1 := rfl

theorem quadPlus_plusVec (i : Fin n) (s : Bool) : quadPlus n K (plusVec n K i s) = 0 := by
  cases s <;> simp [quadPlus_apply, Pi.single_apply]

theorem polar_quadPlus_plusVec (i j : Fin n) (s t : Bool) :
    polar (quadPlus n K) (plusVec n K i s) (plusVec n K j t) =
      if i = j ∧ s = !t then 1 else 0 := by
  cases s <;> cases t <;>
    simp [polar_quadPlus_single_inl, polar_quadPlus_single_inr, Pi.single_apply, eq_comm]

@[expose] noncomputable def plusFrame (hn : 3 ≤ n) : HypFrame (quadPlus n K) n where
  vec := plusVec n K
  map_vec := quadPlus_plusVec n K
  polar_vec_of_ne i j hij s t := by rw [polar_quadPlus_plusVec, ite_eq_right fun h => hij h.1]
  polar_vec_not i s := by rw [polar_quadPlus_plusVec, ite_eq_left ⟨rfl, by rw [Bool.not_not]⟩]
  exists_aux i j := by
    obtain ⟨k, hki, hkj⟩ := exists_ne_and_ne hn i j
    refine ⟨Pi.single (.inl k) 1 + Pi.single (.inr k) 1, ?_, fun s => ⟨?_, ?_⟩⟩
    · rw [quadPlus_apply]
      simp [Pi.single_apply]
    · rw [polar_add_right, ← plusVec_true, ← plusVec_false, polar_quadPlus_plusVec,
        polar_quadPlus_plusVec]
      simp [Ne.symm hki]
    · rw [polar_add_right, ← plusVec_true, ← plusVec_false, polar_quadPlus_plusVec,
        polar_quadPlus_plusVec]
      simp [Ne.symm hkj]

@[simp] theorem plusFrame_vec (hn : 3 ≤ n) : (plusFrame n K hn).vec = plusVec n K := rfl

theorem eq_one_or_eq_neg_one_of_spinAction_eq_one (g : spinGroup (quadPlus n K))
    (hg : spinAction (quadPlus n K) g = 1) :
    (g : CliffordAlgebra (quadPlus n K)) = 1 ∨ (g : CliffordAlgebra (quadPlus n K)) = -1 := by
  have := isCentral_cliffordAlgebra_quadPlus K n
  exact eq_one_or_eq_neg_one_of_commute fun v =>
    commute_of_mem_ker_spinAction _ (MonoidHom.mem_ker.mpr hg) _

@[expose] def rootIdxD (k : Fin n) : Fin n :=
  if k.val + 1 < n then k else ⟨n - 2, by have := k.isLt; omega⟩

@[expose] def rootIdxD' (k : Fin n) : Fin n :=
  if h : k.val + 1 < n then ⟨k.val + 1, h⟩ else ⟨n - 1, by have := k.isLt; omega⟩

@[expose] def rootSignD (k : Fin n) : Bool := decide (n ≤ k.val + 1)

theorem rootIdxD_of_lt {k : Fin n} (h : k.val + 1 < n) : rootIdxD n k = k := by
  simp [rootIdxD, h]

theorem rootIdxD'_of_lt {k : Fin n} (h : k.val + 1 < n) :
    rootIdxD' n k = ⟨k.val + 1, h⟩ := by
  simp [rootIdxD', h]

theorem rootSignD_of_lt {k : Fin n} (h : k.val + 1 < n) : rootSignD n k = false := by
  simp [rootSignD]
  omega

theorem val_rootIdxD_of_not_lt {k : Fin n} (h : ¬k.val + 1 < n) : (rootIdxD n k).val = n - 2 := by
  simp [rootIdxD, h]

theorem val_rootIdxD'_of_not_lt {k : Fin n} (h : ¬k.val + 1 < n) :
    (rootIdxD' n k).val = n - 1 := by
  simp [rootIdxD', h]

theorem rootSignD_of_not_lt {k : Fin n} (h : ¬k.val + 1 < n) : rootSignD n k = true := by
  simp [rootSignD]
  omega

theorem val_rootIdxD' (hn : 2 ≤ n) (k : Fin n) : (rootIdxD' n k).val = (rootIdxD n k).val + 1 := by
  by_cases h : k.val + 1 < n
  · simp [rootIdxD, rootIdxD', h]
  · simp [rootIdxD, rootIdxD', h]
    omega

theorem rootIdxD_ne (hn : 2 ≤ n) (k : Fin n) : rootIdxD n k ≠ rootIdxD' n k := fun h => by
  have := val_rootIdxD' n hn k
  rw [h] at this
  omega

variable {n} (hn : 3 ≤ n)

@[expose] noncomputable def rootD (k : Fin n) : Multiplicative K →* spinGroup (quadPlus n K) :=
  (plusFrame n K hn).longRoot (rootIdxD_ne n (by omega) k) true (rootSignD n k)

@[expose] noncomputable def negRootD (k : Fin n) : Multiplicative K →* spinGroup (quadPlus n K) :=
  (plusFrame n K hn).longRoot (rootIdxD_ne n (by omega) k).symm (!rootSignD n k) false

@[expose] noncomputable def rankOneD (k : Fin n) :
    Matrix.SpecialLinearGroup (Fin 2) K →* spinGroup (quadPlus n K) :=
  (plusFrame n K hn).longSL2 (rootIdxD_ne n (by omega) k) true (rootSignD n k)

@[expose] noncomputable def weylD (k : Fin n) : spinGroup (quadPlus n K) :=
  (plusFrame n K hn).longWeyl (rootIdxD_ne n (by omega) k) true (rootSignD n k)

@[expose] noncomputable def torusD (k : Fin n) : Kˣ →* spinGroup (quadPlus n K) :=
  (plusFrame n K hn).longTorus (rootIdxD_ne n (by omega) k) true (rootSignD n k)

theorem rankOneD_upperSL2 (k : Fin n) (c : K) :
    rankOneD K hn k (upperSL2 c) = rootD K hn k (.ofAdd c) :=
  HypFrame.longSL2_upperSL2 _ _ _ _ c

theorem rankOneD_lowerSL2 (k : Fin n) (c : K) :
    rankOneD K hn k (lowerSL2 c) = negRootD K hn k (.ofAdd c) :=
  HypFrame.longSL2_lowerSL2 _ _ _ _ c

theorem weylD_eq (k : Fin n) :
    weylD K hn k = rootD K hn k (.ofAdd 1) * negRootD K hn k (.ofAdd (-1)) *
      rootD K hn k (.ofAdd 1) :=
  HypFrame.longWeyl_eq _ _ _ _

theorem weylD_eq_rankOneD (k : Fin n) : weylD K hn k = rankOneD K hn k (weylSL2 1) := rfl

theorem torusD_apply (k : Fin n) (τ : Kˣ) : torusD K hn k τ = rankOneD K hn k (diagSL2 τ) := rfl

theorem weylD_mul_self (k : Fin n) : weylD K hn k * weylD K hn k = torusD K hn k (-1) :=
  HypFrame.longWeyl_mul_self _ _ _ _

theorem spinAction_weylD (k : Fin n) (m : Fin n) (r : Bool) :
    spinAction (quadPlus n K) (weylD K hn k) (plusVec n K m r) =
      (longWeylSign (rootIdxD n k) m : K) •
        plusVec n K (Equiv.swap (rootIdxD n k) (rootIdxD' n k) m)
          (longWeylBool (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) m r) :=
  HypFrame.spinAction_longWeyl_vec _ _ _ _ m r

theorem weylD_conj_longRoot (k : Fin n) {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K) :
    weylD K hn k * (plusFrame n K hn).longRoot hij s t (.ofAdd c) * (weylD K hn k)⁻¹ =
      (plusFrame n K hn).longRoot ((Equiv.swap (rootIdxD n k) (rootIdxD' n k)).injective.ne hij)
        (longWeylBool (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) i s)
        (longWeylBool (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) j t)
        (.ofAdd ((longWeylSign (rootIdxD n k) i : K) * longWeylSign (rootIdxD n k) j * c)) :=
  HypFrame.longWeyl_conj_longRoot _ _ _ _ hij s t c

theorem weylD_mul_torusD_mul_inv (k : Fin n) (τ : Kˣ) :
    weylD K hn k * torusD K hn k τ * (weylD K hn k)⁻¹ = torusD K hn k τ⁻¹ :=
  HypFrame.longWeyl_mul_longTorus_mul_inv _ _ _ _ τ

theorem spinAction_torusD (k : Fin n) (τ : Kˣ) (m : Fin n) (r : Bool) :
    spinAction (quadPlus n K) (torusD K hn k τ) (plusVec n K m r) =
      ((τ ^ longCoroot (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) m r : Kˣ) : K) •
        plusVec n K m r :=
  HypFrame.spinAction_longTorus_vec _ _ _ _ τ m r

theorem torusD_conj_longRoot (k : Fin n) (τ : Kˣ) {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    (c : K) :
    torusD K hn k τ * (plusFrame n K hn).longRoot hij s t (.ofAdd c) * (torusD K hn k τ)⁻¹ =
      (plusFrame n K hn).longRoot hij s t
        (.ofAdd (((τ ^ (longCoroot (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) i s +
          longCoroot (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) j t) : Kˣ) : K) * c)) :=
  HypFrame.longTorus_conj_longRoot _ _ _ _ τ hij s t c

theorem commute_torusD (k l : Fin n) (τ σ : Kˣ) : Commute (torusD K hn k τ) (torusD K hn l σ) :=
  HypFrame.commute_longTorus_longTorus _ _ _ _ τ _ _ _ σ

theorem rankOneD_mem_closure (k : Fin n) (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    rankOneD K hn k M ∈ Subgroup.closure (Set.range (rootD K hn k) ∪ Set.range (negRootD K hn k)) := by
  refine Subgroup.closure_mono ?_ (mem_closure_upperSL2_lowerSL2 (rankOneD K hn k) M)
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact Or.inl ⟨.ofAdd c, (rankOneD_upperSL2 K hn k c).symm⟩
  · exact Or.inr ⟨.ofAdd c, (rankOneD_lowerSL2 K hn k c).symm⟩

theorem weylD_conj_torusD (j k : Fin n) (τ : Kˣ) :
    weylD K hn j * torusD K hn k τ * (weylD K hn j)⁻¹ =
      torusD K hn j (τ ^ (-(longCoroot (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k)
          (rootIdxD n j) true +
        longCoroot (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) (rootIdxD' n j)
          (rootSignD n j)))) * torusD K hn k τ := by
  set e := longCoroot (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) (rootIdxD n j) true +
    longCoroot (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) (rootIdxD' n j) (rootSignD n j)
  have h := weylSL2_conj_of_conj (rankOneD K hn j) (torusD K hn k τ) (τ ^ e) (fun c => by
      rw [rankOneD_upperSL2, rankOneD_upperSL2, rootD, torusD_conj_longRoot])
    (fun c => by
      rw [rankOneD_lowerSL2, rankOneD_lowerSL2, negRootD, torusD_conj_longRoot]
      congr 3
      have h1 := longCoroot_not (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k)
        (rootIdxD n j) true
      simp only [Bool.not_true] at h1
      rw [longCoroot_not, h1, ← zpow_neg]
      congr 2
      simp only [e]
      ring)
  rw [weylD_eq_rankOneD, h, zpow_neg]
  rfl

theorem weylD_conj_torusD_mem (j k : Fin n) (τ : Kˣ) :
    weylD K hn j * torusD K hn k τ * (weylD K hn j)⁻¹ ∈
      (torusD K hn j).range ⊔ (torusD K hn k).range := by
  rw [weylD_conj_torusD]
  exact mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right ⟨_, rfl⟩)

theorem weylD_eq_of_lt {k : Fin n} (hk : k.val + 1 < n) {i j : Fin n} (hi : i = k)
    (hj : j.val = k.val + 1) (hij : i ≠ j) :
    weylD K hn k = (plusFrame n K hn).longWeyl hij true false :=
  HypFrame.longWeyl_congr _ _ _ (by rw [rootIdxD_of_lt n hk, hi])
    (by rw [rootIdxD'_of_lt n hk]; exact Fin.ext hj.symm) rfl (rootSignD_of_lt n hk)

theorem weylD_eq_of_not_lt {k : Fin n} (hk : ¬k.val + 1 < n) {i j : Fin n} (hi : i.val = n - 2)
    (hj : j.val = n - 1) (hij : i ≠ j) :
    weylD K hn k = (plusFrame n K hn).longWeyl hij true true :=
  HypFrame.longWeyl_congr _ _ _ (Fin.ext (by rw [val_rootIdxD_of_not_lt n hk, hi]))
    (Fin.ext (by rw [val_rootIdxD'_of_not_lt n hk, hj])) rfl (rootSignD_of_not_lt n hk)

theorem weylD_braid_of_succ {k l : Fin n} (hkl : k.val + 1 = l.val) (hl : l.val + 1 < n) :
    weylD K hn k * weylD K hn l * weylD K hn k = weylD K hn l * weylD K hn k * weylD K hn l := by
  have hk : k.val + 1 < n := by omega
  have h1 : k ≠ l := Fin.ne_of_val_ne (by omega)
  have h2 : l ≠ (⟨l.val + 1, hl⟩ : Fin n) := Fin.ne_of_val_ne (by simp)
  have h3 : k ≠ (⟨l.val + 1, hl⟩ : Fin n) := Fin.ne_of_val_ne (by simp; omega)
  rw [weylD_eq_of_lt K hn hk rfl hkl.symm h1, weylD_eq_of_lt K hn hl rfl rfl h2]
  exact (plusFrame n K hn).longWeyl_braid h1 h2 h3 true false false
    (eq_one_or_eq_neg_one_of_spinAction_eq_one n K)

theorem weylD_braid_last {k l : Fin n} (hk : k.val + 3 = n) (hl : l.val + 1 = n) :
    weylD K hn k * weylD K hn l * weylD K hn k = weylD K hn l * weylD K hn k * weylD K hn l := by
  have hk' : k.val + 1 < n := by omega
  set j : Fin n := ⟨k.val + 1, hk'⟩
  have h1 : k ≠ j := Fin.ne_of_val_ne (by simp [j])
  have h2 : j ≠ l := Fin.ne_of_val_ne (by simp [j]; omega)
  have h3 : k ≠ l := Fin.ne_of_val_ne (by omega)
  rw [weylD_eq_of_lt K hn hk' rfl rfl h1,
    weylD_eq_of_not_lt K hn (k := l) (by omega) (i := j) (j := l) (by simp [j]; omega)
      (by omega) h2]
  exact (plusFrame n K hn).longWeyl_braid h1 h2 h3 true false true
    (eq_one_or_eq_neg_one_of_spinAction_eq_one n K)

theorem weylD_commute {k l : Fin n} (hkl : k ≠ l) (h₁ : ¬(k.val + 1 = l.val ∧ l.val + 1 < n))
    (h₂ : ¬(l.val + 1 = k.val ∧ k.val + 1 < n)) (h₃ : ¬(k.val + 3 = n ∧ l.val + 1 = n))
    (h₄ : ¬(l.val + 3 = n ∧ k.val + 1 = n)) :
    Commute (weylD K hn k) (weylD K hn l) := by
  have hkl' : k.val ≠ l.val := fun h => hkl (Fin.ext h)
  have last : ∀ {a b : Fin n} (ha : a.val + 1 < n) (hb : ¬b.val + 1 < n),
      ¬(a.val + 3 = n ∧ b.val + 1 = n) → Commute (weylD K hn a) (weylD K hn b) := by
    intro a b ha hb hab
    have hb' : b.val + 1 = n := by omega
    have ha1 : a ≠ (⟨a.val + 1, ha⟩ : Fin n) := Fin.ne_of_val_ne (by simp)
    by_cases hlast : a.val + 2 = n
    ·
      rw [weylD_eq_of_lt K hn ha rfl rfl ha1,
        weylD_eq_of_not_lt K hn hb (i := a) (j := ⟨a.val + 1, ha⟩) (by omega) (by simp; omega)
          ha1]
      exact (plusFrame n K hn).commute_longWeyl_longWeyl_flip ha1 true false
    ·
      have hn1 : n - 2 < n := by omega
      have hn2 : n - 1 < n := by omega
      have hb1 : (⟨n - 2, hn1⟩ : Fin n) ≠ ⟨n - 1, hn2⟩ := Fin.ne_of_val_ne (by simp; omega)
      rw [weylD_eq_of_lt K hn ha rfl rfl ha1, weylD_eq_of_not_lt K hn hb rfl rfl hb1]
      exact (plusFrame n K hn).commute_longWeyl_longWeyl_of_disjoint ha1 hb1
        (Fin.ne_of_val_ne (by simp; omega)) (Fin.ne_of_val_ne (by simp; omega))
        (Fin.ne_of_val_ne (by simp; omega)) (Fin.ne_of_val_ne (by simp; omega)) true false true
        true
  by_cases hk : k.val + 1 < n
  · by_cases hl : l.val + 1 < n
    · have hk1 : k ≠ (⟨k.val + 1, hk⟩ : Fin n) := Fin.ne_of_val_ne (by simp)
      have hl1 : l ≠ (⟨l.val + 1, hl⟩ : Fin n) := Fin.ne_of_val_ne (by simp)
      rw [weylD_eq_of_lt K hn hk rfl rfl hk1, weylD_eq_of_lt K hn hl rfl rfl hl1]
      exact (plusFrame n K hn).commute_longWeyl_longWeyl_of_disjoint hk1 hl1 hkl
        (Fin.ne_of_val_ne (by simp; omega)) (Fin.ne_of_val_ne (by simp; omega))
        (Fin.ne_of_val_ne (by simp; omega)) true false true false
    · exact last hk hl h₃
  · by_cases hl : l.val + 1 < n
    · exact (last hl hk h₄).symm
    · exact absurd (Fin.ext (by omega)) hkl

end CFSG.LieType.Universal.Spin
