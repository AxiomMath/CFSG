module

public import CFSG.LieType.Universal.Spin.Chevalley.Transfer

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap

variable (n : ℕ) (K : Type*) [Field K]

@[expose] def oddVec (i : Fin n) : Bool → Fin n ⊕ Fin n ⊕ Unit → K
  | true => Pi.single (.inl i) 1
  | false => Pi.single (.inr (.inl i)) 1

@[expose] def oddZ : Fin n ⊕ Fin n ⊕ Unit → K := Pi.single (.inr (.inr ())) 1

@[simp] theorem oddVec_true (i : Fin n) : oddVec n K i true = Pi.single (.inl i) 1 := rfl

@[simp] theorem oddVec_false (i : Fin n) : oddVec n K i false = Pi.single (.inr (.inl i)) 1 := rfl

theorem quadOdd_oddVec (i : Fin n) (s : Bool) : quadOdd n K (oddVec n K i s) = 0 := by
  cases s <;> simp [quadOdd_apply, Pi.single_apply]

theorem polar_quadOdd_oddVec (i j : Fin n) (s t : Bool) :
    polar (quadOdd n K) (oddVec n K i s) (oddVec n K j t) = if i = j ∧ s = !t then 1 else 0 := by
  cases s <;> cases t <;>
    simp [polar_quadOdd_single_inl, polar_quadOdd_single_inr_inl, Pi.single_apply, eq_comm]

theorem quadOdd_oddZ : quadOdd n K (oddZ n K) = 1 := by
  simp [quadOdd_apply, oddZ]

theorem polar_quadOdd_oddVec_oddZ (i : Fin n) (s : Bool) :
    polar (quadOdd n K) (oddVec n K i s) (oddZ n K) = 0 := by
  cases s <;> simp [oddZ, polar_quadOdd_single_inr_inr]

@[expose] noncomputable def oddFrame : OddFrame (quadOdd n K) n :=
  OddFrame.ofZ (oddVec n K) (quadOdd_oddVec n K)
    (fun i j hij s t => by rw [polar_quadOdd_oddVec, ite_eq_right fun h => hij h.1])
    (fun i s => by rw [polar_quadOdd_oddVec, ite_eq_left ⟨rfl, by rw [Bool.not_not]⟩])
    (oddZ n K) (quadOdd_oddZ n K) (polar_quadOdd_oddVec_oddZ n K)

@[simp] theorem oddFrame_vec : (oddFrame n K).vec = oddVec n K := rfl

@[simp] theorem oddFrame_z : (oddFrame n K).z = oddZ n K := rfl

theorem eq_one_or_eq_neg_one_of_spinAction_eq_one_odd (h2 : (2 : K) ≠ 0)
    (g : spinGroup (quadOdd n K)) (hg : spinAction (quadOdd n K) g = 1) :
    (g : CliffordAlgebra (quadOdd n K)) = 1 ∨ (g : CliffordAlgebra (quadOdd n K)) = -1 := by
  let : Invertible (2 : K) := invertibleOfNonzero h2
  rcases (mem_ker_spinAction_iff (quadOdd n K) (nondegenerate_quadOdd n K) g).mp
    (MonoidHom.mem_ker.mpr hg) with h | h
  · left
    rw [h]
    rfl
  · right
    rw [h, spinGroup.coe_negOne]

variable {n}

@[expose] noncomputable def rootB (k : Fin n) : Multiplicative K →* spinGroup (quadOdd n K) :=
  if h : k.val + 1 < n then
    (oddFrame n K).longRoot (i := k) (j := ⟨k.val + 1, h⟩) (Fin.ne_of_val_ne (by simp)) true false
  else (oddFrame n K).shortRoot k true

@[expose] noncomputable def negRootB (k : Fin n) : Multiplicative K →* spinGroup (quadOdd n K) :=
  if h : k.val + 1 < n then
    (oddFrame n K).longRoot (i := ⟨k.val + 1, h⟩) (j := k) (Fin.ne_of_val_ne (by simp)) true false
  else ((oddFrame n K).shortRoot k false).comp (AddMonoidHom.toMultiplicative (-AddMonoidHom.id K))

@[expose] noncomputable def rankOneB (k : Fin n) :
    Matrix.SpecialLinearGroup (Fin 2) K →* spinGroup (quadOdd n K) :=
  if h : k.val + 1 < n then
    (oddFrame n K).longSL2 (i := k) (j := ⟨k.val + 1, h⟩) (Fin.ne_of_val_ne (by simp)) true false
  else (oddFrame n K).shortSL2 k true

@[expose] noncomputable def weylB (k : Fin n) : spinGroup (quadOdd n K) :=
  rankOneB K k (weylSL2 1)

@[expose] noncomputable def torusB (k : Fin n) : Kˣ →* spinGroup (quadOdd n K) :=
  (rankOneB K k).comp diagSL2

theorem rootB_of_lt {k : Fin n} (hk : k.val + 1 < n) {j : Fin n} (hj : j.val = k.val + 1)
    (hkj : k ≠ j) : rootB K k = (oddFrame n K).longRoot hkj true false := by
  obtain rfl : j = ⟨k.val + 1, hk⟩ := Fin.ext hj
  rw [rootB, dite_eq_left hk]

theorem rootB_of_not_lt {k : Fin n} (hk : ¬k.val + 1 < n) :
    rootB K k = (oddFrame n K).shortRoot k true := by
  rw [rootB, dite_eq_right hk]

theorem negRootB_of_lt {k : Fin n} (hk : k.val + 1 < n) {j : Fin n} (hj : j.val = k.val + 1)
    (hkj : j ≠ k) : negRootB K k = (oddFrame n K).longRoot hkj true false := by
  obtain rfl : j = ⟨k.val + 1, hk⟩ := Fin.ext hj
  rw [negRootB, dite_eq_left hk]

theorem negRootB_of_not_lt {k : Fin n} (hk : ¬k.val + 1 < n) (c : K) :
    negRootB K k (.ofAdd c) = (oddFrame n K).shortRoot k false (.ofAdd (-c)) := by
  rw [negRootB, dite_eq_right hk]
  rfl

theorem rankOneB_upperSL2 (k : Fin n) (c : K) :
    rankOneB K k (upperSL2 c) = rootB K k (.ofAdd c) := by
  unfold rankOneB rootB
  split_ifs
  · exact HypFrame.longSL2_upperSL2 _ _ _ _ c
  · exact OddFrame.shortSL2_upperSL2 _ _ _ c

theorem rankOneB_lowerSL2 (k : Fin n) (c : K) :
    rankOneB K k (lowerSL2 c) = negRootB K k (.ofAdd c) := by
  unfold rankOneB negRootB
  split_ifs
  · exact HypFrame.longSL2_lowerSL2 _ _ _ _ c
  · rw [OddFrame.shortSL2_lowerSL2]
    rfl

theorem weylB_eq (k : Fin n) :
    weylB K k = rootB K k (.ofAdd 1) * negRootB K k (.ofAdd (-1)) * rootB K k (.ofAdd 1) := by
  rw [weylB, weylSL2_eq, map_mul, map_mul, rankOneB_upperSL2, rankOneB_lowerSL2]
  simp

theorem torusB_apply (k : Fin n) (τ : Kˣ) : torusB K k τ = rankOneB K k (diagSL2 τ) := rfl

theorem weylB_mul_self (k : Fin n) : weylB K k * weylB K k = torusB K k (-1) := by
  rw [weylB, ← map_mul, weylSL2_one_mul_self, torusB_apply]

theorem weylB_of_lt {k : Fin n} (hk : k.val + 1 < n) {j : Fin n} (hj : j.val = k.val + 1)
    (hkj : k ≠ j) : weylB K k = (oddFrame n K).longWeyl hkj true false := by
  obtain rfl : j = ⟨k.val + 1, hk⟩ := Fin.ext hj
  rw [weylB, rankOneB, dite_eq_left hk]
  rfl

theorem weylB_of_not_lt {k : Fin n} (hk : ¬k.val + 1 < n) :
    weylB K k = (oddFrame n K).shortWeyl k true := by
  rw [weylB, rankOneB, dite_eq_right hk]
  rfl

theorem spinAction_weylB_vec_of_lt {k : Fin n} (hk : k.val + 1 < n) (m : Fin n) (r : Bool) :
    spinAction (quadOdd n K) (weylB K k) (oddVec n K m r) =
      (longWeylSign k m : K) • oddVec n K (Equiv.swap k ⟨k.val + 1, hk⟩ m)
        (longWeylBool k ⟨k.val + 1, hk⟩ true false m r) := by
  rw [weylB_of_lt K hk (j := ⟨k.val + 1, hk⟩) rfl (Fin.ne_of_val_ne (by simp))]
  exact HypFrame.spinAction_longWeyl_vec _ _ _ _ m r

theorem spinAction_weylB_vec_of_not_lt {k : Fin n} (hk : ¬k.val + 1 < n) (m : Fin n) (r : Bool) :
    spinAction (quadOdd n K) (weylB K k) (oddVec n K m r) =
      (longWeylSign k m : K) • oddVec n K m (shortWeylBool k m r) := by
  rw [weylB_of_not_lt K hk]
  exact OddFrame.spinAction_shortWeyl_vec _ _ _ m r

theorem spinAction_weylB_z (k : Fin n) :
    spinAction (quadOdd n K) (weylB K k) (oddZ n K) =
      if k.val + 1 < n then oddZ n K else -oddZ n K := by
  by_cases hk : k.val + 1 < n
  · rw [weylB_of_lt K hk (j := ⟨k.val + 1, hk⟩) rfl (Fin.ne_of_val_ne (by simp)),
      ite_eq_left hk]
    exact (oddFrame n K).spinAction_longWeyl_of_polar _ _ _
      (fun r => (oddFrame n K).polar_z_vec _ r) (fun r => (oddFrame n K).polar_z_vec _ r)
  · rw [weylB_of_not_lt K hk, ite_eq_right hk]
    exact (oddFrame n K).spinAction_shortWeyl_z k true

theorem torusB_of_lt {k : Fin n} (hk : k.val + 1 < n) {j : Fin n} (hj : j.val = k.val + 1)
    (hkj : k ≠ j) : torusB K k = (oddFrame n K).longTorus hkj true false := by
  obtain rfl : j = ⟨k.val + 1, hk⟩ := Fin.ext hj
  rw [torusB, rankOneB, dite_eq_left hk]
  rfl

theorem torusB_of_not_lt {k : Fin n} (hk : ¬k.val + 1 < n) :
    torusB K k = (oddFrame n K).shortTorus k true := by
  rw [torusB, rankOneB, dite_eq_right hk]
  rfl

theorem weylB_mul_torusB_mul_inv (k : Fin n) (τ : Kˣ) :
    weylB K k * torusB K k τ * (weylB K k)⁻¹ = torusB K k τ⁻¹ := by
  rw [weylB, torusB_apply, torusB_apply, ← map_inv, ← map_mul, ← map_mul,
    weylSL2_mul_diagSL2_mul_inv]

theorem commute_torusB (k l : Fin n) (τ σ : Kˣ) : Commute (torusB K k τ) (torusB K l σ) := by
  by_cases hk : k.val + 1 < n
  · rw [torusB_of_lt K hk (j := ⟨k.val + 1, hk⟩) rfl (Fin.ne_of_val_ne (by simp))]
    by_cases hl : l.val + 1 < n
    · rw [torusB_of_lt K hl (j := ⟨l.val + 1, hl⟩) rfl (Fin.ne_of_val_ne (by simp))]
      exact HypFrame.commute_longTorus_longTorus _ _ _ _ τ _ _ _ σ
    · rw [torusB_of_not_lt K hl]
      exact OddFrame.commute_longTorus_shortTorus _ _ _ _ τ _ _ σ
  · rw [torusB_of_not_lt K hk]
    by_cases hl : l.val + 1 < n
    · rw [torusB_of_lt K hl (j := ⟨l.val + 1, hl⟩) rfl (Fin.ne_of_val_ne (by simp))]
      exact (OddFrame.commute_longTorus_shortTorus _ _ _ _ σ _ _ τ).symm
    · rw [torusB_of_not_lt K hl]
      exact OddFrame.commute_shortTorus_shortTorus _ _ _ τ _ _ σ

theorem rankOneB_of_lt {k : Fin n} (hk : k.val + 1 < n) {j : Fin n} (hj : j.val = k.val + 1)
    (hkj : k ≠ j) : rankOneB K k = (oddFrame n K).longSL2 hkj true false := by
  obtain rfl : j = ⟨k.val + 1, hk⟩ := Fin.ext hj
  rw [rankOneB, dite_eq_left hk]

theorem rankOneB_of_not_lt {k : Fin n} (hk : ¬k.val + 1 < n) :
    rankOneB K k = (oddFrame n K).shortSL2 k true := by
  rw [rankOneB, dite_eq_right hk]

theorem rankOneB_mem_closure (k : Fin n) (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    rankOneB K k M ∈ Subgroup.closure (Set.range (rootB K k) ∪ Set.range (negRootB K k)) := by
  refine Subgroup.closure_mono ?_ (mem_closure_upperSL2_lowerSL2 (rankOneB K k) M)
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact Or.inl ⟨.ofAdd c, (rankOneB_upperSL2 K k c).symm⟩
  · exact Or.inr ⟨.ofAdd c, (rankOneB_lowerSL2 K k c).symm⟩

theorem exists_torusB_conj (k j : Fin n) (τ : Kˣ) : ∃ e : ℤ,
    (∀ c : K, torusB K k τ * rankOneB K j (upperSL2 c) * (torusB K k τ)⁻¹ =
      rankOneB K j (upperSL2 (((τ ^ e : Kˣ) : K) * c))) ∧
    (∀ c : K, torusB K k τ * rankOneB K j (lowerSL2 c) * (torusB K k τ)⁻¹ =
      rankOneB K j (lowerSL2 ((((τ ^ e)⁻¹ : Kˣ) : K) * c))) := by
  by_cases hk : k.val + 1 < n
  · have hk1 : k ≠ (⟨k.val + 1, hk⟩ : Fin n) := Fin.ne_of_val_ne (by simp)
    rw [torusB_of_lt K hk rfl hk1]
    by_cases hj : j.val + 1 < n
    · have hj1 : j ≠ (⟨j.val + 1, hj⟩ : Fin n) := Fin.ne_of_val_ne (by simp)
      rw [rankOneB_of_lt K hj rfl hj1]
      refine ⟨longCoroot k ⟨k.val + 1, hk⟩ true false j true +
        longCoroot k ⟨k.val + 1, hk⟩ true false ⟨j.val + 1, hj⟩ false, fun c => ?_, fun c => ?_⟩
      · rw [HypFrame.longSL2_upperSL2, HypFrame.longSL2_upperSL2,
          HypFrame.longTorus_conj_longRoot]
      · rw [HypFrame.longSL2_lowerSL2, HypFrame.longSL2_lowerSL2,
          HypFrame.longTorus_conj_longRoot, ← zpow_neg, longCoroot_not, longCoroot_not]
        congr 5
        ring
    · rw [rankOneB_of_not_lt K hj]
      refine ⟨longCoroot k ⟨k.val + 1, hk⟩ true false j true, fun c => ?_, fun c => ?_⟩
      · rw [OddFrame.shortSL2_upperSL2, OddFrame.shortSL2_upperSL2,
          OddFrame.longTorus_conj_shortRoot]
      · rw [OddFrame.shortSL2_lowerSL2, OddFrame.shortSL2_lowerSL2,
          OddFrame.longTorus_conj_shortRoot, longCoroot_not, zpow_neg, mul_neg]
  · rw [torusB_of_not_lt K hk]
    by_cases hj : j.val + 1 < n
    · have hj1 : j ≠ (⟨j.val + 1, hj⟩ : Fin n) := Fin.ne_of_val_ne (by simp)
      rw [rankOneB_of_lt K hj rfl hj1]
      refine ⟨shortCoroot k true j true + shortCoroot k true ⟨j.val + 1, hj⟩ false,
        fun c => ?_, fun c => ?_⟩
      · rw [HypFrame.longSL2_upperSL2, HypFrame.longSL2_upperSL2,
          OddFrame.shortTorus_conj_longRoot]
      · rw [HypFrame.longSL2_lowerSL2, HypFrame.longSL2_lowerSL2,
          OddFrame.shortTorus_conj_longRoot, ← zpow_neg, shortCoroot_not, shortCoroot_not]
        congr 5
        ring
    · rw [rankOneB_of_not_lt K hj]
      refine ⟨shortCoroot k true j true, fun c => ?_, fun c => ?_⟩
      · rw [OddFrame.shortSL2_upperSL2, OddFrame.shortSL2_upperSL2,
          OddFrame.shortTorus_conj_shortRoot]
      · rw [OddFrame.shortSL2_lowerSL2, OddFrame.shortSL2_lowerSL2,
          OddFrame.shortTorus_conj_shortRoot, shortCoroot_not, zpow_neg, mul_neg]

theorem weylB_conj_torusB (j k : Fin n) (τ : Kˣ) :
    ∃ e : ℤ, weylB K j * torusB K k τ * (weylB K j)⁻¹ = torusB K j (τ ^ e) * torusB K k τ := by
  obtain ⟨e, hU, hL⟩ := exists_torusB_conj K k j τ
  refine ⟨-e, ?_⟩
  rw [weylB, weylSL2_conj_of_conj (rankOneB K j) _ (τ ^ e) hU hL, zpow_neg]
  rfl

theorem weylB_conj_torusB_mem (j k : Fin n) (τ : Kˣ) :
    weylB K j * torusB K k τ * (weylB K j)⁻¹ ∈ (torusB K j).range ⊔ (torusB K k).range := by
  obtain ⟨e, he⟩ := weylB_conj_torusB K j k τ
  rw [he]
  exact mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right ⟨_, rfl⟩)

theorem weylB_conj_longRoot_of_lt {k : Fin n} (hk : k.val + 1 < n) {i j : Fin n} (hij : i ≠ j)
    (s t : Bool) (c : K) :
    weylB K k * (oddFrame n K).longRoot hij s t (.ofAdd c) * (weylB K k)⁻¹ =
      (oddFrame n K).longRoot ((Equiv.swap k ⟨k.val + 1, hk⟩).injective.ne hij)
        (longWeylBool k ⟨k.val + 1, hk⟩ true false i s)
        (longWeylBool k ⟨k.val + 1, hk⟩ true false j t)
        (.ofAdd ((longWeylSign k i : K) * longWeylSign k j * c)) := by
  rw [weylB_of_lt K hk (j := ⟨k.val + 1, hk⟩) rfl (Fin.ne_of_val_ne (by simp))]
  exact HypFrame.longWeyl_conj_longRoot _ _ _ _ hij s t c

theorem weylB_conj_shortRoot_of_lt {k : Fin n} (hk : k.val + 1 < n) (i : Fin n) (s : Bool)
    (c : K) :
    weylB K k * (oddFrame n K).shortRoot i s (.ofAdd c) * (weylB K k)⁻¹ =
      (oddFrame n K).shortRoot (Equiv.swap k ⟨k.val + 1, hk⟩ i)
        (longWeylBool k ⟨k.val + 1, hk⟩ true false i s) (.ofAdd ((longWeylSign k i : K) * c)) := by
  rw [weylB_of_lt K hk (j := ⟨k.val + 1, hk⟩) rfl (Fin.ne_of_val_ne (by simp))]
  exact OddFrame.longWeyl_conj_shortRoot _ _ _ _ i s c

theorem weylB_conj_longRoot_of_not_lt {k : Fin n} (hk : ¬k.val + 1 < n) {i j : Fin n}
    (hij : i ≠ j) (s t : Bool) (c : K) :
    weylB K k * (oddFrame n K).longRoot hij s t (.ofAdd c) * (weylB K k)⁻¹ =
      (oddFrame n K).longRoot hij (shortWeylBool k i s) (shortWeylBool k j t)
        (.ofAdd ((longWeylSign k i : K) * longWeylSign k j * c)) := by
  rw [weylB_of_not_lt K hk]
  exact OddFrame.shortWeyl_conj_longRoot _ _ _ hij s t c

theorem weylB_conj_shortRoot_of_not_lt {k : Fin n} (hk : ¬k.val + 1 < n) (i : Fin n) (s : Bool)
    (c : K) :
    weylB K k * (oddFrame n K).shortRoot i s (.ofAdd c) * (weylB K k)⁻¹ =
      (oddFrame n K).shortRoot i (shortWeylBool k i s) (.ofAdd (-(longWeylSign k i : K) * c)) := by
  rw [weylB_of_not_lt K hk]
  exact OddFrame.shortWeyl_conj_shortRoot _ _ _ i s c

theorem weylB_braid_of_succ {k l : Fin n} (hkl : k.val + 1 = l.val) (hl : l.val + 1 < n) :
    weylB K k * weylB K l * weylB K k = weylB K l * weylB K k * weylB K l := by
  have hk : k.val + 1 < n := by omega
  have h1 : k ≠ l := Fin.ne_of_val_ne (by omega)
  have h2 : l ≠ (⟨l.val + 1, hl⟩ : Fin n) := Fin.ne_of_val_ne (by simp)
  have h3 : k ≠ (⟨l.val + 1, hl⟩ : Fin n) := Fin.ne_of_val_ne (by simp; omega)
  rw [weylB_of_lt K hk hkl.symm h1, weylB_of_lt K hl rfl h2]
  exact (oddFrame n K).longWeyl_braid' h1 h2 h3 true false false

theorem weylB_braid_last {k l : Fin n} (hk : k.val + 2 = n) (hl : l.val + 1 = n) :
    weylB K k * weylB K l * weylB K k * weylB K l =
      weylB K l * weylB K k * weylB K l * weylB K k := by
  have hk' : k.val + 1 < n := by omega
  have h1 : k ≠ l := Fin.ne_of_val_ne (by omega)
  rw [weylB_of_lt K hk' (j := l) (by omega) h1, weylB_of_not_lt K (k := l) (by omega)]
  exact (oddFrame n K).longWeyl_shortWeyl_braid h1 true false

theorem weylB_commute {k l : Fin n} (hkl : k ≠ l) (h₁ : k.val + 1 ≠ l.val)
    (h₂ : l.val + 1 ≠ k.val) : Commute (weylB K k) (weylB K l) := by
  have hkl' : k.val ≠ l.val := fun h => hkl (Fin.ext h)
  have mixed : ∀ {a b : Fin n} (ha : a.val + 1 < n) (hb : ¬b.val + 1 < n), a.val + 1 ≠ b.val →
      Commute (weylB K a) (weylB K b) := by
    intro a b ha hb hab
    have ha1 : a ≠ (⟨a.val + 1, ha⟩ : Fin n) := Fin.ne_of_val_ne (by simp)
    rw [weylB_of_lt K ha rfl ha1, weylB_of_not_lt K hb]
    exact (oddFrame n K).commute_longWeyl_shortWeyl_of_ne ha1 (Fin.ne_of_val_ne (by omega))
      (Fin.ne_of_val_ne (by simp; omega)) true false true
  by_cases hk : k.val + 1 < n
  · by_cases hl : l.val + 1 < n
    · have hk1 : k ≠ (⟨k.val + 1, hk⟩ : Fin n) := Fin.ne_of_val_ne (by simp)
      have hl1 : l ≠ (⟨l.val + 1, hl⟩ : Fin n) := Fin.ne_of_val_ne (by simp)
      rw [weylB_of_lt K hk rfl hk1, weylB_of_lt K hl rfl hl1]
      exact (oddFrame n K).commute_longWeyl_longWeyl_of_disjoint hk1 hl1 hkl
        (Fin.ne_of_val_ne (by simp; omega)) (Fin.ne_of_val_ne (by simp; omega))
        (Fin.ne_of_val_ne (by simp; omega)) true false true false
    · exact mixed hk hl h₁
  · by_cases hl : l.val + 1 < n
    · exact (mixed hl hk h₂).symm
    · exact absurd (Fin.ext (by omega)) hkl

end CFSG.LieType.Universal.Spin
