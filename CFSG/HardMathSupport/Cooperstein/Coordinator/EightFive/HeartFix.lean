module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Lift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open Equiv Equiv.Perm CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {m : ℕ}

theorem sum_evenWeight (x : evenWeight m) : ∑ i, (x : Fin m → ZMod 2) i = 0 := by
  have h := x.2
  simpa [evenWeight] using h

theorem const_off_of_fix (S : Finset (Fin m)) (hS : S.card + 3 ≤ m) (x : Fin m → ZMod 2)
    (hx : ∀ σ : alternatingGroup (Fin m), (∀ p ∈ S, (σ : Perm (Fin m)) p = p) →
      ∀ i, x ((σ : Perm (Fin m))⁻¹ i) = x i) {i j : Fin m} (hi : i ∉ S) (hj : j ∉ S) :
    x i = x j := by
  classical
  by_cases hij : i = j
  · rw [hij]
  obtain ⟨k, hk⟩ := exists_notMem_of_card_lt (insert i (insert j S)) (by
    have h1 := Finset.card_insert_le i (insert j S)
    have h2 := Finset.card_insert_le j S
    omega)
  simp only [Finset.mem_insert, not_or] at hk
  obtain ⟨hki, hkj, hkS⟩ := hk
  let σ : alternatingGroup (Fin m) := ⟨swap i j * swap j k, swap_mul_swap_mem _ hij (Ne.symm hkj)⟩
  have hfix : ∀ p ∈ S, (σ : Perm (Fin m)) p = p := fun p hp => by
    have hpi : p ≠ i := fun h => hi (h ▸ hp)
    have hpj : p ≠ j := fun h => hj (h ▸ hp)
    have hpk : p ≠ k := fun h => hkS (h ▸ hp)
    change (swap i j * swap j k) p = p
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hpj hpk, swap_apply_of_ne_of_ne hpi hpj]
  have h := hx σ hfix j
  have hσj : (σ : Perm (Fin m))⁻¹ j = i := by
    rw [Perm.inv_eq_iff_eq]
    exact (swap_mul_swap_apply_left hij (Ne.symm hki)).symm
  rw [hσj] at h
  exact h

theorem sum_eq_add_card_mul (x : Fin m → ZMod 2) (S : Finset (Fin m)) (c : ZMod 2)
    (hc : ∀ i ∉ S, x i = c) : ∑ i, x i = ∑ i ∈ S, x i + ((m - S.card : ℕ) : ZMod 2) * c := by
  classical
  rw [← Finset.sum_add_sum_compl S x]
  congr 1
  rw [Finset.sum_congr rfl (fun i hi => hc i (Finset.mem_compl.1 hi)), Finset.sum_const,
    Finset.card_compl, Fintype.card_fin, nsmul_eq_mul]

theorem lift_fix {S : Finset (Fin m)} {a : Fin m} (ha : a ∈ S) {z : altHeart m}
    (hz : ∀ σ : alternatingGroup (Fin m), (∀ p ∈ S, (σ : Perm (Fin m)) p = p) →
      altAct (σ : Perm (Fin m)) z = z) {x : evenWeight m} (hx : (x : altHeart m) = z) :
    ∀ σ : alternatingGroup (Fin m), (∀ p ∈ S, (σ : Perm (Fin m)) p = p) →
      ∀ i, (x : Fin m → ZMod 2) ((σ : Perm (Fin m))⁻¹ i) = (x : Fin m → ZMod 2) i := by
  intro σ hσ i
  refine apply_inv_eq_of_mk_eq (hσ a ha) ?_ i
  rw [← altAct_mk, hx, hz σ hσ]

theorem mk_eq_mk_of_forall_eq_add {x y : evenWeight m} {c : ZMod 2}
    (h : ∀ i, (x : Fin m → ZMod 2) i = (y : Fin m → ZMod 2) i + c) :
    (x : altHeart m) = (y : altHeart m) := by
  refine QuotientAddGroup.eq.2 (mem_evenWeightOnes_of_forall_eq (c := -c) fun i => ?_)
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply, h i]
  abel

theorem mk_eq_zero_of_forall_eq {x : evenWeight m} {c : ZMod 2}
    (h : ∀ i, (x : Fin m → ZMod 2) i = c) : (x : altHeart m) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).2 (mem_evenWeightOnes_of_forall_eq h)

theorem heart_fix_one_lift (hm : Odd m) (hm4 : 4 ≤ m) (b : Fin m) {z : altHeart m} (hz0 : z ≠ 0)
    (hz : ∀ σ : alternatingGroup (Fin m), (σ : Perm (Fin m)) b = b →
      altAct (σ : Perm (Fin m)) z = z) {x : evenWeight m} (hx : (x : altHeart m) = z) :
    (x : Fin m → ZMod 2) b = 0 ∧ ∀ i, i ≠ b → (x : Fin m → ZMod 2) i = 1 := by
  have hfix := lift_fix (S := {b}) (Finset.mem_singleton_self b)
    (fun σ hσ => hz σ (hσ b (Finset.mem_singleton_self b))) hx
  have hconst : ∀ i j, i ≠ b → j ≠ b → (x : Fin m → ZMod 2) i = (x : Fin m → ZMod 2) j :=
    fun i j hi hj => const_off_of_fix {b} (by simp; omega) _ hfix (by simpa using hi)
      (by simpa using hj)
  obtain ⟨j₀, hj₀⟩ := exists_notMem_of_card_lt ({b} : Finset (Fin m)) (by simp; omega)
  rw [Finset.mem_singleton] at hj₀
  have hsum := sum_evenWeight x
  rw [sum_eq_add_card_mul _ {b} ((x : Fin m → ZMod 2) j₀) (fun i hi =>
    hconst i j₀ (by simpa using hi) hj₀)] at hsum
  have hm1 : ((m - ({b} : Finset (Fin m)).card : ℕ) : ZMod 2) = 0 := by
    rw [Finset.card_singleton, ZMod.natCast_eq_zero_iff_even]
    obtain ⟨k, hk⟩ := hm
    exact ⟨k, by omega⟩
  rw [hm1, zero_mul, add_zero, Finset.sum_singleton] at hsum
  refine ⟨hsum, fun i hi => ?_⟩
  rcases zmod_two_cases ((x : Fin m → ZMod 2) j₀) with h0 | h1
  · exfalso
    apply hz0
    rw [← hx]
    refine mk_eq_zero_of_forall_eq (c := 0) fun p => ?_
    by_cases hp : p = b
    · rw [hp, hsum]
    · rw [hconst p j₀ hp hj₀, h0]
  · rw [hconst i j₀ hi hj₀, h1]

theorem heart_eq_of_fix_one (hm : Odd m) (hm4 : 4 ≤ m) (b : Fin m) {z₁ z₂ : altHeart m}
    (h₁ : z₁ ≠ 0) (h₂ : z₂ ≠ 0)
    (hz₁ : ∀ σ : alternatingGroup (Fin m), (σ : Perm (Fin m)) b = b →
      altAct (σ : Perm (Fin m)) z₁ = z₁)
    (hz₂ : ∀ σ : alternatingGroup (Fin m), (σ : Perm (Fin m)) b = b →
      altAct (σ : Perm (Fin m)) z₂ = z₂) : z₁ = z₂ := by
  obtain ⟨x₁, rfl⟩ := QuotientAddGroup.mk_surjective z₁
  obtain ⟨x₂, rfl⟩ := QuotientAddGroup.mk_surjective z₂
  obtain ⟨hb₁, h1⟩ := heart_fix_one_lift hm hm4 b h₁ hz₁ rfl
  obtain ⟨hb₂, h2⟩ := heart_fix_one_lift hm hm4 b h₂ hz₂ rfl
  refine congrArg _ (Subtype.ext (funext fun i => ?_))
  by_cases hi : i = b
  · rw [hi, hb₁, hb₂]
  · rw [h1 i hi, h2 i hi]

theorem heart_eq_pair_of_fix_two_swap (hm : Odd m) (hm5 : 5 ≤ m) {c d e f : Fin m}
    (hcd : c ≠ d) (hec : e ≠ c) (hed : e ≠ d) (hfc : f ≠ c) (hfd : f ≠ d)
    {z : altHeart m} (hz0 : z ≠ 0)
    (hz : ∀ σ : alternatingGroup (Fin m), (σ : Perm (Fin m)) c = c → (σ : Perm (Fin m)) d = d →
      altAct (σ : Perm (Fin m)) z = z)
    (hτ : altAct (swap c d * swap e f) z = z) : z = (pairEW c d : altHeart m) := by
  classical
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  have hfix := lift_fix (S := {c, d}) (a := c) (by simp)
    (fun σ hσ => hz σ (hσ c (by simp)) (hσ d (by simp))) rfl
  have hScard : ({c, d} : Finset (Fin m)).card = 2 := Finset.card_pair hcd
  have hconst : ∀ i j, i ∉ ({c, d} : Finset (Fin m)) → j ∉ ({c, d} : Finset (Fin m)) →
      (x : Fin m → ZMod 2) i = (x : Fin m → ZMod 2) j :=
    fun i j hi hj => const_off_of_fix {c, d} (by omega) _ hfix hi hj
  obtain ⟨p, hpc, hpd, hpe, hpf⟩ := exists_ne_four hm5 c d e f
  have hτp : (swap c d * swap e f) p = p := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hpe hpf, swap_apply_of_ne_of_ne hpc hpd]
  have hτx := apply_inv_eq_of_mk_eq hτp (x := x) (by rw [← altAct_mk]; exact hτ) d
  have hτd : (swap c d * swap e f)⁻¹ d = c := by
    rw [Perm.inv_eq_iff_eq, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hec) (Ne.symm hfc),
      swap_apply_left]
  rw [hτd] at hτx
  obtain ⟨j₀, hj₀⟩ := exists_notMem_of_card_lt ({c, d} : Finset (Fin m)) (by omega)
  have hsum := sum_evenWeight x
  rw [sum_eq_add_card_mul _ {c, d} ((x : Fin m → ZMod 2) j₀) (fun i hi => hconst i j₀ hi hj₀),
    Finset.sum_pair hcd, hScard, ← hτx] at hsum
  have hm2 : ((m - 2 : ℕ) : ZMod 2) = 1 := by
    rw [ZMod.natCast_eq_one_iff_odd]
    obtain ⟨k, hk⟩ := hm
    exact ⟨k - 1, by omega⟩
  rw [hm2, one_mul, zmod2_add_self, zero_add] at hsum
  have hoff : ∀ i, i ∉ ({c, d} : Finset (Fin m)) → (x : Fin m → ZMod 2) i = 0 :=
    fun i hi => (hconst i j₀ hi hj₀).trans hsum
  rcases zmod_two_cases ((x : Fin m → ZMod 2) c) with h0 | h1
  · exfalso
    apply hz0
    refine mk_eq_zero_of_forall_eq (c := 0) fun i => ?_
    by_cases hi : i ∈ ({c, d} : Finset (Fin m))
    · rcases (by simpa using hi : i = c ∨ i = d) with rfl | rfl
      · exact h0
      · rw [← hτx, h0]
    · exact hoff i hi
  · refine mk_eq_mk_of_forall_eq_add (c := 0) fun i => ?_
    rw [add_zero, pairEW_apply]
    by_cases hi : i ∈ ({c, d} : Finset (Fin m))
    · rcases (by simpa using hi : i = c ∨ i = d) with rfl | rfl
      · simp [hcd, h1]
      · simp [hcd.symm, ← hτx, h1]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      simp [hoff i (by simp [hi.1, hi.2]), hi.1, hi.2]

private theorem zmod2_eq_of_add_eq_zero' : ∀ p q : ZMod 2, p + q = 0 → q = p := by decide

private theorem zmod2_cases_add (p r : ZMod 2) : p = r ∨ p = 1 + r := by
  revert p r; decide

theorem heart_eq_pair_of_fix_two (hm : Even m) (hm5 : 5 ≤ m) {c d : Fin m} (hcd : c ≠ d)
    {z : altHeart m} (hz0 : z ≠ 0)
    (hz : ∀ σ : alternatingGroup (Fin m), (σ : Perm (Fin m)) c = c → (σ : Perm (Fin m)) d = d →
      altAct (σ : Perm (Fin m)) z = z) : z = (pairEW c d : altHeart m) := by
  classical
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  have hfix := lift_fix (S := {c, d}) (a := c) (by simp)
    (fun σ hσ => hz σ (hσ c (by simp)) (hσ d (by simp))) rfl
  have hScard : ({c, d} : Finset (Fin m)).card = 2 := Finset.card_pair hcd
  have hconst : ∀ i j, i ∉ ({c, d} : Finset (Fin m)) → j ∉ ({c, d} : Finset (Fin m)) →
      (x : Fin m → ZMod 2) i = (x : Fin m → ZMod 2) j :=
    fun i j hi hj => const_off_of_fix {c, d} (by omega) _ hfix hi hj
  obtain ⟨j₀, hj₀⟩ := exists_notMem_of_card_lt ({c, d} : Finset (Fin m)) (by omega)
  have hsum := sum_evenWeight x
  rw [sum_eq_add_card_mul _ {c, d} ((x : Fin m → ZMod 2) j₀) (fun i hi => hconst i j₀ hi hj₀),
    Finset.sum_pair hcd, hScard] at hsum
  have hm2 : ((m - 2 : ℕ) : ZMod 2) = 0 := by
    rw [ZMod.natCast_eq_zero_iff_even]
    obtain ⟨k, hk⟩ := hm
    exact ⟨k - 1, by omega⟩
  rw [hm2, zero_mul, add_zero] at hsum
  have hdc := zmod2_eq_of_add_eq_zero' _ _ hsum
  set r := (x : Fin m → ZMod 2) j₀ with hr
  have hoff : ∀ i, i ∉ ({c, d} : Finset (Fin m)) → (x : Fin m → ZMod 2) i = r :=
    fun i hi => hconst i j₀ hi hj₀
  rcases zmod2_cases_add ((x : Fin m → ZMod 2) c) r with h0 | h1
  · exfalso
    apply hz0
    refine mk_eq_zero_of_forall_eq (c := r) fun i => ?_
    by_cases hi : i ∈ ({c, d} : Finset (Fin m))
    · rcases (by simpa using hi : i = c ∨ i = d) with rfl | rfl
      · exact h0
      · rw [hdc, h0]
    · exact hoff i hi
  · refine mk_eq_mk_of_forall_eq_add (c := r) fun i => ?_
    rw [pairEW_apply]
    by_cases hi : i ∈ ({c, d} : Finset (Fin m))
    · rcases (by simpa using hi : i = c ∨ i = d) with rfl | rfl
      · simp [hcd, h1]
      · simp [hcd.symm, hdc, h1]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      simp [hoff i (by simp [hi.1, hi.2]), hi.1, hi.2]

private theorem zmod2_three (p q s t : ZMod 2) (h : p + q + s + t = 0) :
    (p = t ∧ q = t ∧ s = t) ∨ (p = 1 + t ∧ q = 1 + t ∧ s = t) ∨
      (p = 1 + t ∧ q = t ∧ s = 1 + t) ∨ (p = t ∧ q = 1 + t ∧ s = 1 + t) := by
  revert p q s t; decide

theorem heart_fix_three (hm : Even m) (hm6 : 6 ≤ m) {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) {z : altHeart m}
    (hz : ∀ σ : alternatingGroup (Fin m), (σ : Perm (Fin m)) a = a → (σ : Perm (Fin m)) b = b →
      (σ : Perm (Fin m)) c = c → altAct (σ : Perm (Fin m)) z = z) :
    z = 0 ∨ z = (pairEW a b : altHeart m) ∨ z = (pairEW a c : altHeart m) ∨
      z = (pairEW b c : altHeart m) := by
  classical
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  have hfix := lift_fix (S := {a, b, c}) (a := a) (by simp)
    (fun σ hσ => hz σ (hσ a (by simp)) (hσ b (by simp)) (hσ c (by simp))) rfl
  have hScard : ({a, b, c} : Finset (Fin m)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
  have hconst : ∀ i j, i ∉ ({a, b, c} : Finset (Fin m)) → j ∉ ({a, b, c} : Finset (Fin m)) →
      (x : Fin m → ZMod 2) i = (x : Fin m → ZMod 2) j :=
    fun i j hi hj => const_off_of_fix {a, b, c} (by omega) _ hfix hi hj
  obtain ⟨j₀, hj₀⟩ := exists_notMem_of_card_lt ({a, b, c} : Finset (Fin m)) (by omega)
  set r := (x : Fin m → ZMod 2) j₀ with hr
  have hsum := sum_evenWeight x
  rw [sum_eq_add_card_mul _ {a, b, c} r (fun i hi => hconst i j₀ hi hj₀), hScard,
    Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc] at hsum
  have hm3 : ((m - 3 : ℕ) : ZMod 2) = 1 := by
    rw [ZMod.natCast_eq_one_iff_odd]
    obtain ⟨k, hk⟩ := hm
    exact ⟨k - 2, by omega⟩
  rw [hm3, one_mul, ← add_assoc] at hsum
  have hoff : ∀ i, i ≠ a → i ≠ b → i ≠ c → (x : Fin m → ZMod 2) i = r :=
    fun i hia hib hic => hconst i j₀ (by simp [hia, hib, hic]) hj₀
  have key : ∀ (y : evenWeight m) (α β γ : ZMod 2),
      (∀ i, (y : Fin m → ZMod 2) i = (if i = a then α else 0) + (if i = b then β else 0) +
        (if i = c then γ else 0)) → (x : Fin m → ZMod 2) a = α + r →
        (x : Fin m → ZMod 2) b = β + r → (x : Fin m → ZMod 2) c = γ + r →
      (x : altHeart m) = (y : altHeart m) := by
    intro y α β γ hy ha hb hc
    refine mk_eq_mk_of_forall_eq_add (c := r) fun i => ?_
    rw [hy i]
    by_cases hia : i = a
    · subst hia; simp [hab, hac, ha]
    by_cases hib : i = b
    · subst hib; simp [hab.symm, hbc, hb]
    by_cases hic : i = c
    · subst hic; simp [hac.symm, hbc.symm, hc]
    simp [hia, hib, hic, hoff i hia hib hic]
  have hpair : ∀ p q : Fin m, ∀ i, ((pairEW p q : evenWeight m) : Fin m → ZMod 2) i =
      (if i = p then 1 else 0) + (if i = q then 1 else 0) := fun p q i => pairEW_apply p q i
  rcases zmod2_three _ _ _ _ hsum with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
  · left
    refine mk_eq_zero_of_forall_eq (c := r) fun i => ?_
    by_cases hia : i = a
    · rw [hia, ha]
    by_cases hib : i = b
    · rw [hib, hb]
    by_cases hic : i = c
    · rw [hic, hc]
    exact hoff i hia hib hic
  · right; left
    refine key _ 1 1 0 (fun i => ?_) ha hb (by rw [hc, zero_add])
    rw [hpair]
    by_cases hic : i = c
    · subst hic; simp [hac.symm, hbc.symm]
    · simp [hic]
  · right; right; left
    refine key _ 1 0 1 (fun i => ?_) ha (by rw [hb, zero_add]) hc
    rw [hpair]
    by_cases hib : i = b
    · subst hib; simp [hab.symm, hbc]
    · simp [hib]
  · right; right; right
    refine key _ 0 1 1 (fun i => ?_) (by rw [ha, zero_add]) hb hc
    rw [hpair]
    by_cases hia : i = a
    · subst hia; simp [hab, hac]
    · simp [hia]

theorem mk_pairEW_ne_mk_pairEW {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (pairEW a b : altHeart m) ≠ (pairEW b c : altHeart m) := by
  intro h
  have h' : ((pairEW a c : evenWeight m) : altHeart m) = 0 := by
    have : (pairEW a c : evenWeight m) = pairEW a b - pairEW b c := by
      refine Subtype.ext (funext fun p => ?_)
      simp only [AddSubgroup.coe_sub, Pi.sub_apply, pairEW_apply]
      by_cases hpa : p = a
      · subst hpa; simp [hab, hac]
      by_cases hpb : p = b
      · subst hpb; simp [hab.symm, hbc]
      by_cases hpc : p = c
      · subst hpc; simp [hac.symm, hbc.symm]
      simp [hpa, hpb, hpc]
    rw [this, QuotientAddGroup.mk_sub, h, sub_self]
  exact mk_pairEW_ne_zero hac hab.symm hbc h'

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
