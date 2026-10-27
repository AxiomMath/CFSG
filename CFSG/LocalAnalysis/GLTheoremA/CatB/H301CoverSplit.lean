module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open

open scoped commutatorElement

section Products

variable {G : Type*} [Monoid G]

theorem ofFn_pow_prod_mul_ofFn_pow_prod : ∀ {n : ℕ} (c : Fin n → G),
    (∀ i j, Commute (c i) (c j)) → ∀ e f : Fin n → ℕ,
    (List.ofFn fun i => c i ^ e i).prod * (List.ofFn fun i => c i ^ f i).prod =
      (List.ofFn fun i => c i ^ (e i + f i)).prod
  | 0, _, _, _, _ => by simp
  | n + 1, c, hc, e, f => by
    have ih := ofFn_pow_prod_mul_ofFn_pow_prod (fun i => c i.succ) (fun i j => hc _ _)
      (fun i => e i.succ) (fun i => f i.succ)
    have hP : Commute (List.ofFn fun i : Fin n => c i.succ ^ e i.succ).prod (c 0 ^ f 0) :=
      Commute.list_prod_left _ _ fun x hx => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
        exact (hc _ _).pow_pow _ _
    simp only [List.ofFn_succ, List.prod_cons]
    rw [← ih, pow_add, mul_assoc, ← mul_assoc _ (c 0 ^ f 0), hP.eq]
    simp only [mul_assoc]

theorem ofFn_prod_eq_apply_of_eq_one : ∀ {n : ℕ} (f : Fin n → G) (i : Fin n),
    (∀ j, j ≠ i → f j = 1) → (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | n + 1, f, i, hf => by
    rw [List.ofFn_succ, List.prod_cons]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact hf _ (Fin.succ_ne_zero j)
    · rw [hf 0 (Fin.succ_ne_zero i).symm, one_mul]
      exact ofFn_prod_eq_apply_of_eq_one (fun j => f j.succ) i fun j hj =>
        hf _ fun h => hj (Fin.succ_injective _ h)

end Products

section Closure

variable {G : Type*} [Group G]

theorem exists_ofFn_pow_eq_of_mem_closure_range {n : ℕ} {c : Fin n → G}
    (hc : ∀ i j, Commute (c i) (c j)) (h3 : ∀ i, c i ^ 3 = 1) {x : G}
    (hx : x ∈ Subgroup.closure (Set.range c)) :
    ∃ e : Fin n → ℕ, (∀ i, e i < 3) ∧ (List.ofFn fun i => c i ^ e i).prod = x := by
  classical
  have hmul := ofFn_pow_prod_mul_ofFn_pow_prod c hc
  have key : ∃ e : Fin n → ℕ, (List.ofFn fun i => c i ^ e i).prod = x := by
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      refine ⟨fun j => if j = i then 1 else 0, ?_⟩
      rw [ofFn_prod_eq_apply_of_eq_one _ i]
      · simp
      · intro j hj
        simp [hj]
    | one =>
      refine ⟨0, List.prod_eq_one fun y hy => ?_⟩
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
      simp
    | mul x y _ _ hx hy =>
      obtain ⟨e, rfl⟩ := hx
      obtain ⟨f, rfl⟩ := hy
      exact ⟨fun i => e i + f i, (hmul e f).symm⟩
    | inv x _ hx =>
      obtain ⟨e, rfl⟩ := hx
      refine ⟨fun i => 2 * e i, (inv_eq_of_mul_eq_one_right ?_).symm⟩
      rw [hmul]
      refine List.prod_eq_one fun y hy => ?_
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
      rw [show e j + 2 * e j = 3 * e j by ring, pow_mul, h3, one_pow]
  obtain ⟨e, rfl⟩ := key
  refine ⟨fun i => e i % 3, fun i => Nat.mod_lt _ (by norm_num), ?_⟩
  exact congrArg List.prod (congrArg List.ofFn (funext fun i => (pow_eq_pow_mod (e i) (h3 i)).symm))

theorem isElemAbelian_three_closure_range {n : ℕ} {c : Fin n → G}
    (hc : ∀ i j, Commute (c i) (c j)) (h3 : ∀ i, c i ^ 3 = 1) :
    IsElemAbelian 3 (Subgroup.closure (Set.range c)) := by
  refine ⟨Subgroup.isMulCommutative_closure ?_, fun x hx => ?_⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hc i j
  · obtain ⟨e, -, rfl⟩ := exists_ofFn_pow_eq_of_mem_closure_range hc h3 hx
    rw [pow_three, ofFn_pow_prod_mul_ofFn_pow_prod c hc, ofFn_pow_prod_mul_ofFn_pow_prod c hc]
    refine List.prod_eq_one fun y hy => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
    rw [show e j + (e j + e j) = 3 * e j by ring, pow_mul, h3, one_pow]

private theorem commute_of_mem_closure_range {ι : Type*} {c : ι → G}
    (hc : ∀ i j, Commute (c i) (c j)) {x y : G} (hx : x ∈ Subgroup.closure (Set.range c))
    (hy : y ∈ Subgroup.closure (Set.range c)) : Commute x y := by
  have := Subgroup.isMulCommutative_closure (k := Set.range c) (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hc i j)
  exact congrArg Subtype.val (isMulCommutative_iff.1 this ⟨x, hx⟩ ⟨y, hy⟩)

end Closure

section Lifts

variable {E J : Type*} [Group E] [Group J]

private theorem commutatorElement_mul_left_of_central {x y w : E}
    (h : ⁅y, w⁆ ∈ Subgroup.center E) : ⁅x * y, w⁆ = ⁅y, w⁆ * ⁅x, w⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, Subgroup.mem_center_iff.1 h x, mul_inv_cancel_right]

private theorem commutatorElement_mul_center_left {x z w : E} (hz : z ∈ Subgroup.center E) :
    ⁅x * z, w⁆ = ⁅x, w⁆ := by
  have h1 : ⁅z, w⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.2 (Subgroup.mem_center_iff.1 hz w).symm
  have h1c : ⁅z, w⁆ ∈ Subgroup.center E := by
    rw [h1]
    exact Subgroup.one_mem _
  rw [commutatorElement_mul_left_of_central h1c, h1, one_mul]

private theorem commutatorElement_eq_of_map_eq_of_central (π : E →* J)
    (hker : π.ker ≤ Subgroup.center E) {x x' y y' : E} (hx : π x = π x') (hy : π y = π y') :
    ⁅x, y⁆ = ⁅x', y'⁆ := by
  have hzx : x⁻¹ * x' ∈ Subgroup.center E :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hx, inv_mul_cancel])
  have hzy : y⁻¹ * y' ∈ Subgroup.center E :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hy, inv_mul_cancel])
  have e1 : x' = x * (x⁻¹ * x') := by group
  have e2 : y' = y * (y⁻¹ * y') := by group
  rw [e1, e2, commutatorElement_mul_center_left hzx,
    ← commutatorElement_inv (y * (y⁻¹ * y')) x, commutatorElement_mul_center_left hzy,
    commutatorElement_inv]

private theorem pow_three_eq_of_map_eq_of_central (π : E →* J)
    (hker : π.ker ≤ Subgroup.center E) (hk3 : Nat.card π.ker = 3) {x x' : E}
    (hx : π x = π x') : x ^ 3 = x' ^ 3 := by
  have hz : x⁻¹ * x' ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hx, inv_mul_cancel]
  have hz3 : (x⁻¹ * x') ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := (⟨x⁻¹ * x', hz⟩ : π.ker))
    rw [hk3] at h
    simpa using congrArg Subtype.val h
  have hc : Commute x (x⁻¹ * x') := Subgroup.mem_center_iff.1 (hker hz) x
  calc x ^ 3 = x ^ 3 * (x⁻¹ * x') ^ 3 := by rw [hz3, mul_one]
    _ = (x * (x⁻¹ * x')) ^ 3 := (hc.mul_pow 3).symm
    _ = x' ^ 3 := by rw [mul_inv_cancel_left]

private theorem exists_log_of_card_eq_three {Z : Subgroup E} (hZ : Nat.card Z = 3) :
    ∃ ℓ : E → ZMod 3, (∀ x ∈ Z, ∀ y ∈ Z, ℓ (x * y) = ℓ x + ℓ y) ∧
      (∀ x ∈ Z, ℓ x = 0 → x = 1) := by
  classical
  let e : Z ≃* Multiplicative (ZMod 3) := mulEquivOfPrimeCardEq hZ (by simp)
  refine ⟨fun x => if hx : x ∈ Z then (e ⟨x, hx⟩).toAdd else 0, ?_, ?_⟩
  · intro x hx y hy
    simp only [dif_pos hx, dif_pos hy, dif_pos (Z.mul_mem hx hy)]
    rw [← toAdd_mul, ← map_mul]
    rfl
  · intro x hx h
    simp only [dif_pos hx] at h
    have h1 : e ⟨x, hx⟩ = 1 := by
      rw [← ofAdd_toAdd (e ⟨x, hx⟩), h]
      rfl
    exact congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))

end Lifts

theorem exists_commuting_lifts_of_noForms {E J : Type*} [Group E] [Group J] {n m : ℕ}
    (π : E →* J) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center E)
    (hk3 : Nat.card π.ker = 3)
    (b : Fin n → J) (hbc : ∀ i j, Commute (b i) (b j)) (hb3 : ∀ i, b i ^ 3 = 1)
    (g : Fin m → J) (M : Fin m → Matrix (Fin n) (Fin n) (ZMod 3))
    (hM : ∀ k i, g k * b i * (g k)⁻¹ = (List.ofFn fun j => b j ^ (M k i j).val).prod)
    (halt : ∀ C : Matrix (Fin n) (Fin n) (ZMod 3), (∀ i, C i i = 0) → (∀ i j, C j i = -C i j) →
      (∀ k, M k * C * (M k).transpose = C) → C = 0)
    (hlin : ∀ q : Fin n → ZMod 3, (∀ k, (M k).mulVec q = q) → q = 0) :
    ∃ bh : Fin n → E, (∀ i, π (bh i) = b i) ∧ (∀ i j, Commute (bh i) (bh j)) ∧
      (∀ i, bh i ^ 3 = 1) := by
  classical
  obtain ⟨ℓ, hℓmul, hℓinj⟩ := exists_log_of_card_eq_three hk3
  have hℓ1 : ℓ 1 = 0 := by
    have h := hℓmul 1 π.ker.one_mem 1 π.ker.one_mem
    rw [mul_one] at h
    linear_combination -h
  have hℓpow : ∀ x ∈ π.ker, ∀ k : ℕ, ℓ (x ^ k) = k * ℓ x := fun x hx k => by
    induction k with
    | zero => simp [hℓ1]
    | succ k ih =>
      rw [pow_succ, hℓmul _ (π.ker.pow_mem hx k) _ hx, ih]
      push_cast
      ring
  choose a ha using fun i => hπ (b i)
  choose h hh using fun k => hπ (g k)
  set P := (Subgroup.closure (Set.range b)).comap π with hP
  have haP : ∀ j, a j ∈ P := fun j => by
    rw [hP, Subgroup.mem_comap, ha j]
    exact Subgroup.subset_closure ⟨j, rfl⟩
  have hPZ : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ π.ker := fun x hx y hy => by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact commute_of_mem_closure_range hbc hx hy
  have hPc : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ Subgroup.center E := fun x hx y hy =>
    hker (hPZ x hx y hy)
  obtain ⟨X, hX⟩ : ∃ X : (Fin n → ℕ) → E, ∀ e, X e = (List.ofFn fun j => a j ^ e j).prod :=
    ⟨_, fun _ => rfl⟩
  have hXP : ∀ e, X e ∈ P := fun e => by
    rw [hX]
    refine P.list_prod_mem fun x hx => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    exact P.pow_mem (haP j) _
  have hπX : ∀ e, π (X e) = (List.ofFn fun j => b j ^ e j).prod := fun e => by
    rw [hX, map_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun j => ?_))
    simp [ha]
  have hconj : ∀ k i, π (h k * a i * (h k)⁻¹) = π (X fun j => (M k i j).val) := fun k i => by
    rw [map_mul, map_mul, map_inv, hh, ha, hM, hπX]
  have hlist : ∀ L : List E, (∀ x ∈ L, x ∈ P) → ∀ w ∈ P,
      ℓ ⁅L.prod, w⁆ = (L.map fun x => ℓ ⁅x, w⁆).sum := by
    intro L hL w hw
    induction L with
    | nil => simp [hℓ1]
    | cons x L ih =>
      have hx : x ∈ P := hL x List.mem_cons_self
      have hL' : ∀ y ∈ L, y ∈ P := fun y hy => hL y (List.mem_cons_of_mem _ hy)
      have hLP : L.prod ∈ P := P.list_prod_mem hL'
      rw [List.prod_cons, commutatorElement_mul_left_of_central (hPc _ hLP _ hw),
        hℓmul _ (hPZ _ hLP _ hw) _ (hPZ _ hx _ hw), ih hL', List.map_cons, List.sum_cons,
        add_comm]
  have hpow : ∀ x ∈ P, ∀ w ∈ P, ∀ k : ℕ, ℓ ⁅x ^ k, w⁆ = k * ℓ ⁅x, w⁆ := by
    intro x hx w hw k
    induction k with
    | zero => simp [hℓ1]
    | succ k ih =>
      rw [pow_succ, commutatorElement_mul_left_of_central (hPc _ hx _ hw),
        hℓmul _ (hPZ _ hx _ hw) _ (hPZ _ (P.pow_mem hx k) _ hw), ih]
      push_cast
      ring
  have hanti : ∀ x ∈ P, ∀ w ∈ P, ℓ ⁅x, w⁆ + ℓ ⁅w, x⁆ = 0 := fun x hx w hw => by
    rw [← hℓmul _ (hPZ _ hx _ hw) _ (hPZ _ hw _ hx), ← commutatorElement_inv x w,
      mul_inv_cancel, hℓ1]
  have hleft : ∀ e : Fin n → ℕ, ∀ w ∈ P, ℓ ⁅X e, w⁆ = ∑ j, (e j : ZMod 3) * ℓ ⁅a j, w⁆ := by
    intro e w hw
    rw [hX, hlist _ (fun x hx => ?_) w hw, List.map_ofFn, List.sum_ofFn]
    · exact Finset.sum_congr rfl fun j _ => hpow _ (haP j) _ hw _
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact P.pow_mem (haP j) _
  have hright : ∀ e : Fin n → ℕ, ∀ w ∈ P, ℓ ⁅w, X e⁆ = ∑ j, (e j : ZMod 3) * ℓ ⁅w, a j⁆ := by
    intro e w hw
    refine add_right_cancel ((hanti _ hw _ (hXP e)).trans ?_)
    rw [hleft e w hw, ← Finset.sum_add_distrib]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    rw [← mul_add, hanti _ hw _ (haP j), mul_zero]
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin n) (Fin n) (ZMod 3), ∀ i l, C i l = ℓ ⁅a i, a l⁆ :=
    ⟨fun i l => ℓ ⁅a i, a l⁆, fun _ _ => rfl⟩
  have hC0 : C = 0 := by
    refine halt C (fun i => by rw [hC, commutatorElement_self, hℓ1])
      (fun i j => by
        rw [hC, hC]
        exact eq_neg_of_add_eq_zero_left (hanti _ (haP j) _ (haP i))) fun k => ?_
    ext i l
    have key : ⁅a i, a l⁆ = ⁅X fun j => (M k i j).val, X fun j => (M k l j).val⁆ := by
      have hc : ⁅a i, a l⁆ ∈ Subgroup.center E := hPc _ (haP i) _ (haP l)
      calc ⁅a i, a l⁆ = h k * ⁅a i, a l⁆ * (h k)⁻¹ := by
            rw [Subgroup.mem_center_iff.1 hc, mul_inv_cancel_right]
        _ = ⁅h k * a i * (h k)⁻¹, h k * a l * (h k)⁻¹⁆ := conjugate_commutatorElement _ _ _
        _ = _ := commutatorElement_eq_of_map_eq_of_central π hker (hconj k i) (hconj k l)
    rw [hC i l, key, hleft _ _ (hXP _)]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hC]
    simp only [hright _ _ (haP _), ZMod.natCast_zmod_val, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
  have hcomm : ∀ i l, Commute (a i) (a l) := fun i l => by
    have h0 : ℓ ⁅a i, a l⁆ = 0 := by rw [← hC, hC0]; rfl
    exact commutatorElement_eq_one_iff_commute.1 (hℓinj _ (hPZ _ (haP i) _ (haP l)) h0)
  have ha3 : ∀ i, a i ^ 3 ∈ π.ker := fun i => by
    rw [MonoidHom.mem_ker, map_pow, ha, hb3]
  have hcubeL : ∀ L : List E, (∀ x ∈ L, ∀ y ∈ L, Commute x y) → (∀ x ∈ L, x ^ 3 ∈ π.ker) →
      L.prod ^ 3 ∈ π.ker ∧ ℓ (L.prod ^ 3) = (L.map fun x => ℓ (x ^ 3)).sum := by
    intro L
    induction L with
    | nil => intro _ _; simp [hℓ1]
    | cons x L ih =>
      intro hc h3
      obtain ⟨hm, hℓL⟩ := ih
        (fun y hy z hz => hc y (List.mem_cons_of_mem _ hy) z (List.mem_cons_of_mem _ hz))
        (fun y hy => h3 y (List.mem_cons_of_mem _ hy))
      have hxL : Commute x L.prod := Commute.list_prod_right _ _ fun y hy =>
        hc x List.mem_cons_self y (List.mem_cons_of_mem _ hy)
      have hx3 := h3 x List.mem_cons_self
      rw [List.prod_cons, hxL.mul_pow, List.map_cons, List.sum_cons]
      exact ⟨π.ker.mul_mem hx3 hm, by rw [hℓmul _ hx3 _ hm, hℓL]⟩
  have hcube : ∀ e : Fin n → ℕ, ℓ (X e ^ 3) = ∑ j, (e j : ZMod 3) * ℓ (a j ^ 3) := by
    intro e
    obtain ⟨-, hL⟩ := hcubeL (List.ofFn fun j => a j ^ e j)
      (fun x hx y hy => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
        obtain ⟨j', rfl⟩ := List.mem_ofFn.1 hy
        exact (hcomm j j').pow_pow _ _)
      (fun x hx => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
        rw [← pow_mul, mul_comm, pow_mul]
        exact π.ker.pow_mem (ha3 j) _)
    rw [hX, hL, List.map_ofFn, List.sum_ofFn]
    refine Finset.sum_congr rfl fun j _ => ?_
    change ℓ ((a j ^ e j) ^ 3) = _
    rw [← pow_mul, mul_comm, pow_mul, hℓpow _ (ha3 j)]
  have hq0 : (fun i => ℓ (a i ^ 3)) = 0 := by
    refine hlin _ fun k => funext fun i => ?_
    have key : a i ^ 3 = (X fun j => (M k i j).val) ^ 3 := by
      have hc : a i ^ 3 ∈ Subgroup.center E := hker (ha3 i)
      calc a i ^ 3 = h k * a i ^ 3 * (h k)⁻¹ := by
            rw [Subgroup.mem_center_iff.1 hc, mul_inv_cancel_right]
        _ = (h k * a i * (h k)⁻¹) ^ 3 := conj_pow.symm
        _ = _ := pow_three_eq_of_map_eq_of_central π hker hk3 (hconj k i)
    change ∑ j, M k i j * ℓ (a j ^ 3) = ℓ (a i ^ 3)
    rw [key, hcube]
    simp only [ZMod.natCast_zmod_val]
  exact ⟨a, ha, hcomm, fun i => hℓinj _ (ha3 i) (congrFun hq0 i)⟩

theorem exists_elemAbelian_complement_of_noForms {E J : Type*} [Group E] [Group J] {n m : ℕ}
    (π : E →* J) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center E)
    (hk3 : Nat.card π.ker = 3)
    (b : Fin n → J) (hbc : ∀ i j, Commute (b i) (b j)) (hb3 : ∀ i, b i ^ 3 = 1)
    (g : Fin m → J) (M : Fin m → Matrix (Fin n) (Fin n) (ZMod 3))
    (hM : ∀ k i, g k * b i * (g k)⁻¹ = (List.ofFn fun j => b j ^ (M k i j).val).prod)
    (halt : ∀ C : Matrix (Fin n) (Fin n) (ZMod 3), (∀ i, C i i = 0) → (∀ i j, C j i = -C i j) →
      (∀ k, M k * C * (M k).transpose = C) → C = 0)
    (hlin : ∀ q : Fin n → ZMod 3, (∀ k, (M k).mulVec q = q) → q = 0)
    (hind : ∀ e : Fin n → ℕ, (∀ i, e i < 3) → (List.ofFn fun i => b i ^ e i).prod = 1 →
      ∀ i, e i = 0) :
    ∃ Bh : Subgroup E, CFSG.Open.IsElemAbelian 3 Bh ∧ Bh ⊓ π.ker = ⊥ ∧
      Bh.map π = Subgroup.closure (Set.range b) ∧ ∀ i, ∃ y ∈ Bh, π y = b i := by
  obtain ⟨bh, hbh, hc, h3⟩ :=
    exists_commuting_lifts_of_noForms π hπ hker hk3 b hbc hb3 g M hM halt hlin
  refine ⟨Subgroup.closure (Set.range bh), isElemAbelian_three_closure_range hc h3, ?_, ?_,
    fun i => ⟨bh i, Subgroup.subset_closure ⟨i, rfl⟩, hbh i⟩⟩
  · rw [eq_bot_iff]
    rintro x ⟨hx, hxk⟩
    obtain ⟨e, he3, rfl⟩ := exists_ofFn_pow_eq_of_mem_closure_range hc h3 hx
    have h1 : (List.ofFn fun i => b i ^ e i).prod = 1 := by
      have h := MonoidHom.mem_ker.1 hxk
      rwa [map_list_prod, List.map_ofFn,
        show (⇑π ∘ fun i => bh i ^ e i) = fun i => b i ^ e i from
          funext fun i => by simp [hbh]] at h
    have h0 := hind e he3 h1
    rw [Subgroup.mem_bot]
    refine List.prod_eq_one fun y hy => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
    simp [h0 j]
  · rw [MonoidHom.map_closure, ← Set.range_comp, show ⇑π ∘ bh = b from funext hbh]

end CFSG.LocalAnalysis.GLTheoremA.H301
