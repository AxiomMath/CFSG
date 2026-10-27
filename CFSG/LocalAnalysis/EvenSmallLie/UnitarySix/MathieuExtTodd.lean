module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignWittAut

public section

namespace CFSG.EvenSmallLie.UnitarySix.MathieuExt

open CFSG.ComponentClassification.WittDesign CFSG.Sporadic.Mathieu Module

@[expose] def W22 : Type := Fin 22 → ZMod 2

instance : AddCommGroup W22 := Pi.addCommGroup

instance : Module (ZMod 2) W22 := Pi.module _ _ _

instance : Fintype W22 := Pi.instFintype

instance : DecidableEq W22 := fun a b => decEq (α := Fin 22 → ZMod 2) a b

@[ext] theorem W22.ext {v w : W22} (h : ∀ i, v i = w i) : v = w := funext h

theorem W22.add_apply (v w : W22) (i : Fin 22) : (v + w) i = v i + w i := rfl

theorem W22.smul_apply (c : ZMod 2) (v : W22) (i : Fin 22) : (c • v) i = c * v i := rfl

theorem W22.zero_apply (i : Fin 22) : (0 : W22) i = 0 := rfl

theorem W22.sum_apply {ι : Type*} (s : Finset ι) (f : ι → W22) (i : Fin 22) :
    (∑ k ∈ s, f k) i = ∑ k ∈ s, f k i := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, W22.add_apply, ih, Finset.sum_insert ha]

@[expose] def permW (g : Equiv.Perm (Fin 22)) : W22 →ₗ[ZMod 2] W22 :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑g⁻¹

theorem permW_apply (g : Equiv.Perm (Fin 22)) (v : W22) (i : Fin 22) :
    permW g v i = v (g⁻¹ i) := rfl

theorem permW_mul (g h : Equiv.Perm (Fin 22)) (v : W22) :
    permW (g * h) v = permW g (permW h v) := by
  funext i
  simp [permW_apply, mul_inv_rev, Equiv.Perm.mul_apply]

theorem permW_pow (g : Equiv.Perm (Fin 22)) (n : ℕ) (v : W22) :
    permW (g ^ n) v = (permW g)^[n] v := by
  induction n generalizing v with
  | zero =>
    funext i
    simp [permW_apply]
  | succ n ih => rw [pow_succ, permW_mul, ih, Function.iterate_succ_apply]

@[expose] def bvec (m : ℕ) (i : Fin 22) : ZMod 2 := if m.testBit i then 1 else 0

@[expose] def vecOfMask (m : ℕ) : W22 := bvec m

theorem vecOfMask_apply (m : ℕ) (i : Fin 22) : vecOfMask m i = bvec m i := rfl

theorem vecOfMask_xor (m m' : ℕ) : vecOfMask (m ^^^ m') = vecOfMask m + vecOfMask m' := by
  ext i
  simp only [vecOfMask_apply, bvec, Nat.testBit_xor, W22.add_apply]
  cases m.testBit i <;> cases m'.testBit i <;> decide

theorem finrank_W22 : finrank (ZMod 2) W22 = 22 := by
  change finrank (ZMod 2) (Fin 22 → ZMod 2) = 22
  simp

@[expose] def fixedW (z : Equiv.Perm (Fin 22)) : Submodule (ZMod 2) W22 :=
  LinearMap.eqLocus (permW z) LinearMap.id

theorem mem_fixedW {z : Equiv.Perm (Fin 22)} {v : W22} : v ∈ fixedW z ↔ permW z v = v :=
  LinearMap.mem_eqLocus

theorem apply_eq_of_mem_fixedW {z : Equiv.Perm (Fin 22)} {v : W22} (hv : v ∈ fixedW z)
    (n : ℕ) (j : Fin 22) : v ((⇑z)^[n] j) = v j := by
  have h1 : ∀ j, v (z j) = v j := fun j => by
    have := congrFun (mem_fixedW.1 hv) (z j)
    rw [permW_apply, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply] at this
    exact this.symm
  induction n generalizing j with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', h1, ih]

theorem finrank_fixedW_le {z : Equiv.Perm (Fin 22)} {i₀ i₁ : Fin 22} {m : ℕ}
    (hcyc : ∀ j : Fin 22, ∃ n : Fin 11,
      ((⇑z)^[n] i₀ = j ∧ m.testBit j = true) ∨ ((⇑z)^[n] i₁ = j ∧ m.testBit j = false)) :
    finrank (ZMod 2) (fixedW z) ≤ 2 := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective fun v : fixedW z => ((v : W22) i₀, (v : W22) i₁) := by
    intro v w hvw
    simp only [Prod.mk.injEq] at hvw
    refine Subtype.ext (funext fun j => ?_)
    obtain ⟨n, (⟨hn, -⟩ | ⟨hn, -⟩)⟩ := hcyc j
    · rw [← hn, apply_eq_of_mem_fixedW v.2, apply_eq_of_mem_fixedW w.2]
      exact hvw.1
    · rw [← hn, apply_eq_of_mem_fixedW v.2, apply_eq_of_mem_fixedW w.2]
      exact hvw.2
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [← FiniteField.pow_finrank_eq_natCard 2 (fixedW z), Nat.card_prod, Nat.card_zmod] at hle
  by_contra hc
  have : 2 ^ 3 ≤ 2 ^ finrank (ZMod 2) (fixedW z) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem card_fixed_mod_eleven {z : Equiv.Perm (Fin 22)} (hz : z ^ 11 = 1)
    {K : Submodule (ZMod 2) W22} (hK : ∀ v ∈ K, permW z v ∈ K) :
    Nat.card K % 11 = Nat.card (K ⊓ fixedW z : Submodule (ZMod 2) W22) % 11 := by
  classical
  have hp : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let f : Function.End K := fun v => ⟨permW z v, hK v v.2⟩
  have hit : ∀ (n : ℕ) (v : K), ((f^[n] v : K) : W22) = (permW z)^[n] (v : W22) := by
    intro n
    induction n with
    | zero => exact fun v => rfl
    | succ n ih =>
      intro v
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
  have hf : f ^ 11 ^ 1 = 1 := by
    change f^[11 ^ 1] = id
    funext v
    refine Subtype.ext ?_
    rw [hit, ← permW_pow, pow_one, hz]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 11) (n := 1) hf
  have hfix : Fintype.card (Function.fixedPoints f) =
      Nat.card (K ⊓ fixedW z : Submodule (ZMod 2) W22) := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun v => ⟨v.1.1, v.1.2, mem_fixedW.2 (congrArg Subtype.val v.2)⟩
        invFun := fun v => ⟨⟨v.1, v.2.1⟩, Subtype.ext (mem_fixedW.1 v.2.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [← hfix, Nat.card_eq_fintype_card]
  exact hmod

theorem card_inf_fixedW {z : Equiv.Perm (Fin 22)} {i₀ i₁ : Fin 22} {m : ℕ}
    (hcyc : ∀ j : Fin 22, ∃ n : Fin 11,
      ((⇑z)^[n] i₀ = j ∧ m.testBit j = true) ∨ ((⇑z)^[n] i₁ = j ∧ m.testBit j = false))
    (K : Submodule (ZMod 2) W22) :
    Nat.card (K ⊓ fixedW z : Submodule (ZMod 2) W22) =
        2 ^ finrank (ZMod 2) (K ⊓ fixedW z : Submodule (ZMod 2) W22) ∧
      finrank (ZMod 2) (K ⊓ fixedW z : Submodule (ZMod 2) W22) ≤ 2 := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨(FiniteField.pow_finrank_eq_natCard 2 (K ⊓ fixedW z : Submodule (ZMod 2) W22)).symm,
    ?_⟩
  exact (Submodule.finrank_mono inf_le_right).trans (finrank_fixedW_le hcyc)

theorem pow_mod_eleven_of_invariant {z : Equiv.Perm (Fin 22)} (hz : z ^ 11 = 1)
    {i₀ i₁ : Fin 22} {m : ℕ}
    (hcyc : ∀ j : Fin 22, ∃ n : Fin 11,
      ((⇑z)^[n] i₀ = j ∧ m.testBit j = true) ∨ ((⇑z)^[n] i₁ = j ∧ m.testBit j = false))
    {K : Submodule (ZMod 2) W22} (hK : ∀ v ∈ K, permW z v ∈ K) :
    2 ^ finrank (ZMod 2) K % 11 = 1 ∨ 2 ^ finrank (ZMod 2) K % 11 = 2 ∨
      (2 ^ finrank (ZMod 2) K % 11 = 4 ∧ ∀ v, v ∈ fixedW z → v ∈ K) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := card_fixed_mod_eleven hz hK
  rw [← FiniteField.pow_finrank_eq_natCard 2 K] at h
  obtain ⟨hc, hle⟩ := card_inf_fixedW hcyc K
  rw [hc] at h
  set f := finrank (ZMod 2) (K ⊓ fixedW z : Submodule (ZMod 2) W22) with hf
  rcases (show f = 0 ∨ f = 1 ∨ f = 2 by omega) with h0 | h1 | h2
  · rw [h0] at h
    exact Or.inl h
  · rw [h1] at h
    exact Or.inr (Or.inl h)
  · rw [h2] at h
    refine Or.inr (Or.inr ⟨h, ?_⟩)
    have heq : K ⊓ fixedW z = fixedW z :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right (le_antisymm
        (Submodule.finrank_mono inf_le_right) (by rw [← hf, h2]; exact finrank_fixedW_le hcyc))
    intro v hv
    rw [← heq] at hv
    exact hv.1

@[expose] def toddWords : Fin 11 → List Bool :=
  ![[], [false], [true, false], [false, true, false], [true, true, false],
    [false, true, true, false], [true, false, true, false], [true, false, true, true, false],
    [true, true, false, true, false], [false, true, false, true, true, false],
    [true, true, false, true, true, false]]

@[expose] def wordPerm : List Bool → Equiv.Perm (Fin 22)
  | [] => 1
  | c :: l => (if c then m22gB else m22gA) * wordPerm l

theorem wordPerm_mem
    (l : List Bool) : wordPerm l ∈ M22 := by
  induction l with
  | nil => exact one_mem _
  | cons c l ih =>
    refine mul_mem ?_ ih
    cases c
    · exact m22a.2
    · exact m22b.2

@[expose] def toddZ (k : Fin 11) : Equiv.Perm (Fin 22) :=
  wordPerm (toddWords k) * (m22gA * m22gB) * (wordPerm (toddWords k))⁻¹

theorem toddZ_mem
    (k : Fin 11) : toddZ k ∈ M22 :=
  mul_mem (mul_mem (wordPerm_mem _) (mul_mem m22a.2 m22b.2)) (inv_mem (wordPerm_mem _))

@[expose] def toddTab : Fin 11 → List ℕ :=
  ![[5, 17, 20, 0, 3, 13, 14, 10, 9, 1, 16, 4, 7, 19, 21, 2, 18, 11, 6, 8, 12, 15],
    [1, 13, 15, 4, 11, 2, 18, 17, 7, 8, 19, 12, 21, 6, 5, 20, 14, 3, 16, 9, 0, 10],
    [21, 2, 6, 12, 1, 10, 9, 8, 13, 7, 20, 4, 11, 3, 16, 0, 18, 19, 5, 14, 15, 17],
    [3, 9, 12, 4, 7, 17, 18, 15, 1, 10, 11, 0, 5, 20, 6, 16, 8, 19, 21, 14, 2, 13],
    [15, 4, 3, 9, 11, 18, 0, 13, 19, 5, 6, 17, 1, 8, 7, 21, 10, 20, 16, 12, 14, 2],
    [7, 10, 5, 17, 3, 15, 13, 4, 21, 19, 9, 8, 2, 16, 1, 11, 12, 20, 6, 0, 14, 18],
    [20, 10, 19, 9, 21, 14, 4, 6, 17, 5, 3, 13, 11, 15, 16, 18, 2, 7, 8, 0, 1, 12],
    [5, 20, 16, 0, 8, 17, 7, 9, 2, 21, 15, 12, 3, 11, 19, 4, 14, 6, 1, 18, 10, 13],
    [17, 4, 1, 13, 19, 18, 12, 10, 3, 21, 5, 2, 7, 14, 11, 16, 8, 6, 20, 15, 9, 0],
    [11, 8, 4, 0, 9, 10, 14, 20, 5, 15, 3, 12, 21, 2, 19, 6, 1, 16, 7, 18, 13, 17],
    [6, 12, 19, 14, 1, 9, 15, 2, 20, 16, 3, 8, 21, 7, 13, 11, 17, 0, 5, 4, 18, 10]]

@[expose] def tabFun (k : Fin 11) (i : Fin 22) : Fin 22 :=
  ⟨(toddTab k).getD i 0 % 22, Nat.mod_lt _ (by norm_num)⟩

@[expose] def toddM1 : Fin 11 → ℕ :=
  ![666427, 1433703, 4178977, 102299, 2459245, 1722011, 1656367, 2243305, 3544801, 2301227,
    1543009]

@[expose] def toddM2 : Fin 11 → ℕ :=
  ![3527876, 2760600, 15326, 4092004, 1735058, 2472292, 2537936, 1950998, 649502, 1893076,
    2651294]

@[expose] def toddI1 : Fin 11 → Fin 22 := ![2, 3, 1, 2, 1, 2, 4, 1, 1, 2, 1]

@[expose] def orbitIdx (i : Fin 22) : Fin 11 := ⟨i.val / 2, by omega⟩

@[expose] def orbitMask (i : Fin 22) : ℕ :=
  if i.val % 2 = 0 then toddM1 (orbitIdx i) else toddM2 (orbitIdx i)

@[expose] def toddBM : Fin 12 → ℕ :=
  ![1239, 2899, 4834, 8815, 17396, 33125, 65914, 131534, 262748, 525257, 1049535, 2097401]

@[expose] def toddCombo : Fin 12 → ℕ :=
  ![1296, 1380688, 267285, 1115478, 81988, 21574, 1392710, 1397830, 1093, 1130561, 349523,
    1381461]

@[expose] def toddPivot (l : Fin 12) : Fin 22 := ⟨l.val + 10, by omega⟩

@[expose] def toddBasis (l : Fin 12) : W22 := vecOfMask (toddBM l)

@[expose] def toddKernel : Submodule (ZMod 2) W22 := Submodule.span (ZMod 2) (Set.range toddBasis)

theorem toddZ_eq_tabFun : ∀ k : Fin 11, ∀ i : Fin 22, toddZ k i = tabFun k i := by
  decide +kernel

theorem tab_facts : ∀ k : Fin 11, (∀ j : Fin 22, (tabFun k)^[11] j = j) ∧
    (∀ j : Fin 22, ∃ n : Fin 11, ((tabFun k)^[n] 0 = j ∧ (toddM1 k).testBit j = true) ∨
      ((tabFun k)^[n] (toddI1 k) = j ∧ (toddM1 k).testBit j = false)) ∧
    ∀ j : Fin 22, (toddM1 k).testBit (tabFun k j) = (toddM1 k).testBit j := by
  decide +kernel

theorem toddM2_spec : ∀ k : Fin 11, ∀ j : Fin 22,
    (toddM2 k).testBit j = !(toddM1 k).testBit j := by
  decide +kernel

theorem toddBasis_eq_sum : ∀ l : Fin 12, ∀ j : Fin 22, bvec (toddBM l) j =
    ∑ i : Fin 22, (if (toddCombo l).testBit i then (1 : ZMod 2) else 0) * bvec (orbitMask i) j := by
  decide +kernel

theorem bvec_pivot : ∀ l l' : Fin 12,
    bvec (toddBM l) (toddPivot l') = if l = l' then 1 else 0 := by
  decide +kernel

theorem toddBasis_pivot (l l' : Fin 12) :
    toddBasis l (toddPivot l') = if l = l' then 1 else 0 := bvec_pivot l l'

theorem coe_toddZ (k : Fin 11) : ⇑(toddZ k) = tabFun k := funext (toddZ_eq_tabFun k)

theorem toddZ_pow (k : Fin 11) : toddZ k ^ 11 = 1 :=
  Equiv.ext fun j => by rw [Equiv.Perm.coe_pow, coe_toddZ]; exact (tab_facts k).1 j

theorem toddZ_cyc (k : Fin 11) : ∀ j : Fin 22, ∃ n : Fin 11,
    ((⇑(toddZ k))^[n] 0 = j ∧ (toddM1 k).testBit j = true) ∨
      ((⇑(toddZ k))^[n] (toddI1 k) = j ∧ (toddM1 k).testBit j = false) := by
  rw [coe_toddZ]
  exact (tab_facts k).2.1

theorem testBit_toddM1_apply (k : Fin 11) (j : Fin 22) :
    (toddM1 k).testBit (toddZ k j) = (toddM1 k).testBit j :=
  (congrArg (fun y : Fin 22 => (toddM1 k).testBit y) (toddZ_eq_tabFun k j)).trans
    ((tab_facts k).2.2 j)

theorem testBit_toddM1_inv (k : Fin 11) (j : Fin 22) :
    (toddM1 k).testBit ((toddZ k)⁻¹ j) = (toddM1 k).testBit j := by
  have e : toddZ k ((toddZ k)⁻¹ j) = j := by
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
  exact (testBit_toddM1_apply k ((toddZ k)⁻¹ j)).symm.trans
    (congrArg (fun y : Fin 22 => (toddM1 k).testBit y) e)

theorem orbitMask_mem_fixedW (i : Fin 22) :
    vecOfMask (orbitMask i) ∈ fixedW (toddZ (orbitIdx i)) := by
  rw [mem_fixedW]
  ext j
  rw [permW_apply, vecOfMask_apply, vecOfMask_apply]
  have hb : (orbitMask i).testBit ((toddZ (orbitIdx i))⁻¹ j) = (orbitMask i).testBit j := by
    unfold orbitMask
    split_ifs
    · exact testBit_toddM1_inv (orbitIdx i) j
    · exact (toddM2_spec (orbitIdx i) _).trans ((congrArg Bool.not
        (testBit_toddM1_inv (orbitIdx i) j)).trans (toddM2_spec (orbitIdx i) j).symm)
  unfold bvec
  rw [hb]

theorem finrank_toddKernel : finrank (ZMod 2) toddKernel = 12 := by
  have hli : LinearIndependent (ZMod 2) toddBasis := by
    rw [Fintype.linearIndependent_iff]
    intro g hg l'
    have := congrArg (fun v : W22 => v (toddPivot l')) hg
    simp only [W22.sum_apply, W22.smul_apply, toddBasis_pivot, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, W22.zero_apply] at this
    exact this
  rw [toddKernel, finrank_span_eq_card hli, Fintype.card_fin]

theorem card_toddKernel : Nat.card toddKernel = 2 ^ 12 := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← FiniteField.pow_finrank_eq_natCard 2, finrank_toddKernel]

theorem mem_toddKernel_iff {v : W22} :
    v ∈ toddKernel ↔ v = ∑ l : Fin 12, v (toddPivot l) • toddBasis l := by
  constructor
  · intro hv
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hv
    congr 1
    funext l
    congr 1
    simp only [W22.sum_apply, W22.smul_apply, toddBasis_pivot, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · intro hv
    rw [hv]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

instance (v : W22) : Decidable (v ∈ toddKernel) := decidable_of_iff _ mem_toddKernel_iff.symm

@[expose] def combMask (g : Fin 12 → Bool) : ℕ :=
  (List.finRange 12).foldl (fun acc l => if g l then acc ^^^ toddBM l else acc) 0

@[expose] def wt22 (m : ℕ) : ℕ := (Finset.univ.filter fun i : Fin 22 => m.testBit i = true).card

theorem combMask_weight : ∀ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : Bool,
    (b₀ || b₁ || b₂ || b₃ || b₄ || b₅ || b₆ || b₇ || b₈ || b₉ || b₁₀ || b₁₁) = true →
    6 ≤ wt22 (combMask ![b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈, b₉, b₁₀, b₁₁]) := by
  decide +kernel

theorem vecOfMask_zero : vecOfMask 0 = 0 := by
  ext i
  simp [vecOfMask_apply, bvec, W22.zero_apply]

@[expose] def supp (c : W22) : Finset (Fin 22) :=
  Finset.univ.filter fun i => decide (c i ≠ 0) = true

theorem mem_supp {c : W22} {i : Fin 22} : i ∈ supp c ↔ c i ≠ 0 := by
  simp [supp]

theorem vecOfMask_foldl (g : Fin 12 → Bool) (L : List (Fin 12)) (acc : ℕ) :
    vecOfMask (L.foldl (fun acc l => if g l then acc ^^^ toddBM l else acc) acc) =
      vecOfMask acc + (L.map fun l => if g l then toddBasis l else 0).sum := by
  induction L generalizing acc with
  | nil => simp
  | cons l L ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, ← add_assoc]
    congr 1
    split_ifs
    · exact vecOfMask_xor _ _
    · rw [add_zero]

theorem vecOfMask_combMask (g : Fin 12 → Bool) :
    vecOfMask (combMask g) = ∑ l : Fin 12, if g l then toddBasis l else 0 := by
  rw [combMask, vecOfMask_foldl, vecOfMask_zero, zero_add, Fin.sum_univ_def]

theorem card_supp_vecOfMask (m : ℕ) : (supp (vecOfMask m)).card = wt22 m := by
  rw [wt22]
  congr 1
  ext i
  rw [mem_supp, Finset.mem_filter, vecOfMask_apply, bvec]
  cases m.testBit i <;> simp

theorem zmod_two_eq (a : ZMod 2) : a = if decide (a = 1) then 1 else 0 := by
  revert a
  decide

theorem six_le_card_supp {c : W22} (hc : c ∈ toddKernel) (h0 : c ≠ 0) : 6 ≤ (supp c).card := by
  set g : Fin 12 → Bool := fun l => decide (c (toddPivot l) = 1)
  have hcg : c = vecOfMask (combMask g) := by
    rw [vecOfMask_combMask]
    conv_lhs => rw [mem_toddKernel_iff.1 hc]
    refine Finset.sum_congr rfl fun l _ => ?_
    conv_lhs => rw [zmod_two_eq (c (toddPivot l))]
    split_ifs <;> simp
  have hg : (g 0 || g 1 || g 2 || g 3 || g 4 || g 5 || g 6 || g 7 || g 8 || g 9 || g 10 ||
      g 11) = true := by
    by_contra hf
    apply h0
    rw [hcg, vecOfMask_combMask]
    refine Finset.sum_eq_zero fun l _ => ?_
    have : g l = false := by
      simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hf
      fin_cases l <;> simp_all
    rw [this]
    rfl
  have hw := combMask_weight _ _ _ _ _ _ _ _ _ _ _ _ hg
  have he : (![g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7, g 8, g 9, g 10, g 11] : Fin 12 → Bool) =
      g := by
    funext l
    fin_cases l <;> rfl
  rw [he, ← card_supp_vecOfMask, ← hcg] at hw
  exact hw

theorem vecOfMask_mem_toddKernel {m : ℕ}
    (h : combMask (fun l => m.testBit (l.val + 10)) = m) : vecOfMask m ∈ toddKernel := by
  rw [mem_toddKernel_iff]
  conv_lhs => rw [← h, vecOfMask_combMask]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [vecOfMask_apply, bvec, toddPivot]
  split_ifs <;> simp

theorem hexadMasks_check :
    hexadMasks.all (fun m => combMask (fun l => m.testBit (l.val + 10)) == m) = true := by
  decide +kernel

@[expose] def indW (B : Finset (Fin 22)) : W22 := fun i => if i ∈ B then 1 else 0

theorem hexad_mem_toddKernel {B : Finset (Fin 22)} (hB : B ∈ hexads) : indW B ∈ toddKernel := by
  have hm : CFSG.Monster.B.Classical.Plane.mask B ∈ hexadMasks :=
    List.mem_map_of_mem (mem_hexads.1 hB)
  have h := List.all_eq_true.1 hexadMasks_check _ hm
  rw [beq_iff_eq] at h
  have heq : indW B = vecOfMask (CFSG.Monster.B.Classical.Plane.mask B) := by
    ext i
    rw [vecOfMask_apply, bvec, indW]
    simp [CFSG.Monster.B.Classical.Plane.testBit_mask]
  rw [heq]
  exact vecOfMask_mem_toddKernel h

theorem eq_toddKernel_of_invariant {K : Submodule (ZMod 2) W22}
    (hK : ∀ k : Fin 11, ∀ v ∈ K, permW (toddZ k) v ∈ K) (h12 : finrank (ZMod 2) K = 12) :
    K = toddKernel := by
  have horb : ∀ i : Fin 22, vecOfMask (orbitMask i) ∈ K := by
    intro i
    rcases pow_mod_eleven_of_invariant (toddZ_pow (orbitIdx i)) (toddZ_cyc (orbitIdx i))
      (hK (orbitIdx i)) with h | h | ⟨-, h⟩
    · rw [h12] at h
      norm_num at h
    · rw [h12] at h
      norm_num at h
    · exact h _ (orbitMask_mem_fixedW i)
  have hle : toddKernel ≤ K := by
    rw [toddKernel, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    have he : toddBasis l = ∑ i : Fin 22,
        (if (toddCombo l).testBit i then (1 : ZMod 2) else 0) • vecOfMask (orbitMask i) := by
      ext j
      rw [toddBasis, vecOfMask_apply, toddBasis_eq_sum, W22.sum_apply]
      rfl
    rw [SetLike.mem_coe, he]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (horb i)
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_toddKernel, h12])).symm

@[expose] def toddGen
    : Fin 3 → Equiv.Perm (Fin 22) := ![m22gA, m22gB, sigmaPerm]

theorem toddGen_check : ∀ t : Fin 3, ∀ l : Fin 12, ∀ j : Fin 22,
    bvec (toddBM l) ((toddGen t)⁻¹ j) = ∑ l' : Fin 12,
      bvec (toddBM l) ((toddGen t)⁻¹ (toddPivot l')) * bvec (toddBM l') j := by
  have hinv : ∀ t : Fin 3, ⇑((toddGen t)⁻¹) = ![⇑(m22gA⁻¹), ⇑(m22gB⁻¹), sigmaFun] t := by
    intro t
    fin_cases t <;> rfl
  have h' : ∀ t : Fin 3, ∀ l : Fin 12, ∀ j : Fin 22,
      bvec (toddBM l) (![⇑(m22gA⁻¹), ⇑(m22gB⁻¹), sigmaFun] t j) = ∑ l' : Fin 12,
        bvec (toddBM l) (![⇑(m22gA⁻¹), ⇑(m22gB⁻¹), sigmaFun] t (toddPivot l')) *
          bvec (toddBM l') j := by
    decide +kernel
  intro t l j
  rw [hinv t]
  exact h' t l j

theorem permW_one (v : W22) : permW 1 v = v := rfl

theorem permW_mem_of_gen
    (t : Fin 3) {c : W22} (hc : c ∈ toddKernel) :
    permW (toddGen t) c ∈ toddKernel := by
  have hb : ∀ l, permW (toddGen t) (toddBasis l) ∈ toddKernel := fun l => by
    rw [mem_toddKernel_iff]
    ext j
    rw [W22.sum_apply, permW_apply, toddBasis, vecOfMask_apply, toddGen_check t l j]
    rfl
  rw [toddKernel] at hc ⊢
  refine Submodule.span_induction (fun v hv => ?_) ?_ (fun u v _ _ hu hv => ?_)
    (fun a v _ hv => ?_) hc
  · obtain ⟨l, rfl⟩ := hv
    exact hb l
  · rw [map_zero]
    exact zero_mem _
  · rw [map_add]
    exact add_mem hu hv
  · rw [map_smul]
    exact Submodule.smul_mem _ _ hv

@[expose] def toddStab : Subgroup (Equiv.Perm (Fin 22)) where
  carrier := {g | ∀ c ∈ toddKernel, permW g c ∈ toddKernel}
  mul_mem' {g h} hg hh c hc := by
    rw [permW_mul]
    exact hg _ (hh c hc)
  one_mem' c hc := by
    rw [permW_one]
    exact hc
  inv_mem' {g} hg := by
    change ∀ c ∈ toddKernel, permW g c ∈ toddKernel at hg
    change ∀ c ∈ toddKernel, permW g⁻¹ c ∈ toddKernel
    have hpow : ∀ n : ℕ, ∀ c ∈ toddKernel, permW (g ^ n) c ∈ toddKernel := by
      intro n
      induction n with
      | zero => exact fun c hc => hc
      | succ n ih =>
        intro c hc
        rw [pow_succ, permW_mul]
        exact ih _ (hg c hc)
    have hinv : g⁻¹ = g ^ (orderOf g - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one]
    rw [hinv]
    exact hpow _

theorem permW_mem_toddKernel
    {g : Equiv.Perm (Fin 22)} (hg : g ∈ hexadAut) {c : W22}
    (hc : c ∈ toddKernel) : permW g c ∈ toddKernel := by
  have hgen : ∀ t : Fin 3, toddGen t ∈ toddStab := fun t c hc => permW_mem_of_gen t hc
  have hM : M22 ≤ toddStab := by
    change CFSG.Blueprint.NativeSporadic.M22 ≤ toddStab
    rw [CFSG.Sporadic.Mathieu.m22_eq, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hgen 0
    · exact hgen 1
  set H := M22 ⊔ Subgroup.closure {sigmaPerm}
  have hH : H ≤ hexadAut :=
    sup_le M22_le_hexadAut ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 sigmaPerm_mem))
  have hMH : M22 ≤ H := le_sup_left
  have hσ : sigmaPerm ∈ H := Subgroup.mem_sup_right (Subgroup.subset_closure rfl)
  have hHeq : H = hexadAut := by
    obtain ⟨hA, hidx⟩ := card_hexadAut
    have hdvd := Subgroup.card_dvd_of_le hH
    have hdvd' := Subgroup.card_dvd_of_le hMH
    rw [hA] at hdvd
    rw [card_M22'] at hdvd'
    have hne : Nat.card H ≠ 443520 := by
      intro h
      have : M22 = H := Subgroup.eq_of_le_of_card_ge hMH (by rw [h, card_M22'])
      exact sigmaPerm_not_mem (this ▸ hσ)
    obtain ⟨k, hk⟩ := hdvd'
    obtain ⟨k', hk'⟩ := hdvd
    have hk2 : k = 2 := by
      have hpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h, mul_zero] at hk
          exact absurd hk (Nat.card_pos (α := H)).ne'
        · exact h
      have : k * k' = 2 := by nlinarith
      have hk1 : k ≠ 1 := fun h => hne (by rw [hk, h, mul_one])
      rcases (Nat.dvd_prime Nat.prime_two).1 (Dvd.intro _ this) with h | h
      · exact absurd h hk1
      · exact h
    exact Subgroup.eq_of_le_of_card_ge hH (by rw [hA, hk, hk2])
  have hσS : sigmaPerm ∈ toddStab := hgen 2
  have hHS : H ≤ toddStab := sup_le hM ((Subgroup.closure_le _).2
    (Set.singleton_subset_iff.2 hσS))
  rw [← hHeq] at hg
  exact hHS hg c hc

section Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def evalW (x : Fin 22 → V) : W22 →ₗ[ZMod 2] V := Fintype.linearCombination (ZMod 2) x

theorem evalW_apply (x : Fin 22 → V) (c : W22) : evalW x c = ∑ i, c i • x i :=
  Fintype.linearCombination_apply _ _ _

theorem range_evalW (x : Fin 22 → V) :
    LinearMap.range (evalW x) = Submodule.span (ZMod 2) (Set.range x) :=
  Fintype.range_linearCombination _ _

theorem evalW_permW {x : Fin 22 → V} {g : Equiv.Perm (Fin 22)} {ρ : V →+ V}
    (hρ : ∀ i, ρ (x i) = x (g i)) (c : W22) : evalW x (permW g c) = ρ (evalW x c) := by
  rw [evalW_apply, evalW_apply, map_sum]
  simp only [permW_apply]
  rw [← Equiv.sum_comp g]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply, ← hρ]
  exact ((ρ.toZModLinearMap 2).map_smul _ _).symm

theorem todd_module_unique
    [Finite V] (hV : Nat.card V = 2 ^ 10) {x : Fin 22 → V}
    (hx : Function.Injective x) (hρ : ∀ g ∈ M22, ∃ ρ : V →+ V, ∀ i, ρ (x i) = x (g i)) :
    Submodule.span (ZMod 2) (Set.range x) = ⊤ ∧ ∀ c : W22, evalW x c = 0 ↔ c ∈ toddKernel := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := LinearMap.ker (evalW x)
  have hK : ∀ k : Fin 11, ∀ v ∈ K, permW (toddZ k) v ∈ K := by
    intro k v hv
    obtain ⟨ρ, hρk⟩ := hρ _ (toddZ_mem k)
    rw [LinearMap.mem_ker] at hv ⊢
    rw [evalW_permW hρk, hv, map_zero]
  have hW : finrank (ZMod 2) W22 = 22 := finrank_W22
  have hVd : finrank (ZMod 2) V = 10 := by
    have := FiniteField.pow_finrank_eq_natCard 2 V
    rw [hV] at this
    exact Nat.pow_right_injective (le_refl 2) this
  have hrk : finrank (ZMod 2) (LinearMap.range (evalW x)) + finrank (ZMod 2) K = 22 := by
    have := LinearMap.finrank_range_add_finrank_ker (evalW x)
    rw [hW] at this
    exact this
  have hU10 : finrank (ZMod 2) (LinearMap.range (evalW x)) ≤ 10 :=
    hVd ▸ Submodule.finrank_le _
  have hU5 : 5 ≤ finrank (ZMod 2) (LinearMap.range (evalW x)) := by
    have hcard := FiniteField.pow_finrank_eq_natCard 2 (LinearMap.range (evalW x))
    have h22 : 22 ≤ Nat.card (LinearMap.range (evalW x)) := by
      have := Nat.card_le_card_of_injective
        (fun i : Fin 22 => (⟨x i, by
          rw [range_evalW]
          exact Submodule.subset_span ⟨i, rfl⟩⟩ : LinearMap.range (evalW x)))
        (fun i j h => hx (congrArg Subtype.val h))
      simpa using this
    by_contra hc
    have : 2 ^ finrank (ZMod 2) (LinearMap.range (evalW x)) ≤ 2 ^ 4 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h12 : finrank (ZMod 2) K = 12 := by
    have hmod := pow_mod_eleven_of_invariant (toddZ_pow 0) (toddZ_cyc 0) (hK 0)
    have hlo : 12 ≤ finrank (ZMod 2) K := by omega
    have hhi : finrank (ZMod 2) K ≤ 17 := by omega
    interval_cases hk : finrank (ZMod 2) K <;> simp_all
  have hKeq := eq_toddKernel_of_invariant hK h12
  refine ⟨?_, fun c => by rw [← LinearMap.mem_ker, ← hKeq]⟩
  rw [← range_evalW]
  refine Submodule.eq_top_of_finrank_eq ?_
  omega


@[expose] def basisW (i : Fin 22) : W22 := Pi.single i 1

theorem basisW_apply (i j : Fin 22) : basisW i j = if j = i then 1 else 0 := by
  simp only [basisW, Pi.single_apply]

theorem evalW_basisW (x : Fin 22 → V) (i : Fin 22) : evalW x (basisW i) = x i := by
  rw [evalW_apply, Finset.sum_eq_single i]
  · simp [basisW_apply]
  · intro j _ hj
    simp [basisW_apply, hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem two_smul_eq_zero (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem card_supp_le {c : W22} {S : Finset (Fin 22)} (h : ∀ i, c i ≠ 0 → i ∈ S) :
    (supp c).card ≤ S.card :=
  Finset.card_le_card fun i hi => h i (mem_supp.1 hi)

theorem pair_aux {i j k l : Fin 22} (hij : i ≠ j) (hkl : k ≠ l)
    (h : ∀ m, basisW i m + basisW j m + basisW k m + basisW l m = 0) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  have hi := h i
  have hj := h j
  simp only [basisW_apply] at hi hj
  by_cases hik : i = k
  · subst hik
    by_cases hjl : j = l
    · exact Or.inl ⟨rfl, hjl⟩
    · exfalso
      simp [Ne.symm hij, hjl] at hj
  · by_cases hil : i = l
    · subst hil
      by_cases hjk : j = k
      · exact Or.inr ⟨rfl, hjk⟩
      · exfalso
        simp [Ne.symm hij, hjk] at hj
    · exfalso
      simp [hij, hik, hil] at hi

theorem triple_aux {i j k : Fin 22} (hij : i ≠ j)
    (h : ∀ m, basisW i m + basisW j m + basisW k m = 0) : False := by
  have hi := h i
  have hj := h j
  simp only [basisW_apply] at hi hj
  by_cases hik : i = k
  · subst hik
    simp [Ne.symm hij] at hj
  · simp [hij, hik] at hi

theorem evalW_indW (x : Fin 22 → V) (B : Finset (Fin 22)) : evalW x (indW B) = ∑ i ∈ B, x i := by
  rw [evalW_apply]
  simp only [indW, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem todd_relations
    [Finite V] (hV : Nat.card V = 2 ^ 10) {x : Fin 22 → V}
    (hx : Function.Injective x) (hρ : ∀ g ∈ M22, ∃ ρ : V →+ V, ∀ i, ρ (x i) = x (g i)) :
    (∀ B ∈ hexads, ∑ i ∈ B, x i = 0) ∧
    (∀ c : W22, evalW x c = 0 → c = 0 ∨ 6 ≤ (supp c).card) ∧
    (∀ i j k l : Fin 22, i ≠ j → k ≠ l → x i + x j = x k + x l →
      (i = k ∧ j = l) ∨ (i = l ∧ j = k)) ∧
    (∀ i j k : Fin 22, i ≠ j → x i + x j ≠ x k) := by
  have hrel := (todd_module_unique hV hx hρ).2
  have hmin : ∀ c : W22, evalW x c = 0 → c = 0 ∨ 6 ≤ (supp c).card := fun c hc => by
    by_cases h0 : c = 0
    · exact Or.inl h0
    · exact Or.inr (six_le_card_supp ((hrel c).1 hc) h0)
  refine ⟨fun B hB => ?_, hmin, fun i j k l hij hkl he => ?_, fun i j k hij he => ?_⟩
  · rw [← evalW_indW]
    exact (hrel _).2 (hexad_mem_toddKernel hB)
  · set c : W22 := basisW i + basisW j + basisW k + basisW l
    have hc : evalW x c = 0 := by
      simp only [c, map_add, evalW_basisW, he]
      rw [show x k + x l + x k + x l = (x k + x l) + (x k + x l) by abel, two_smul_eq_zero]
    have hcv : ∀ m, c m = basisW i m + basisW j m + basisW k m + basisW l m := fun m => rfl
    have hc0 : c = 0 := by
      rcases hmin c hc with h | h
      · exact h
      · have := card_supp_le (S := {i, j, k, l}) (c := c) fun m hm => by
          rw [hcv] at hm
          simp only [basisW_apply] at hm
          simp only [Finset.mem_insert, Finset.mem_singleton]
          by_contra hn
          push Not at hn
          simp [hn.1, hn.2.1, hn.2.2.1, hn.2.2.2] at hm
        have h4 := Finset.card_le_four (a := i) (b := j) (c := k) (d := l)
        omega
    exact pair_aux hij hkl fun m => by rw [← hcv, hc0]; rfl
  · set c : W22 := basisW i + basisW j + basisW k
    have hc : evalW x c = 0 := by
      simp only [c, map_add, evalW_basisW, he, two_smul_eq_zero]
    have hcv : ∀ m, c m = basisW i m + basisW j m + basisW k m := fun m => rfl
    have hc0 : c = 0 := by
      rcases hmin c hc with h | h
      · exact h
      · have := card_supp_le (S := {i, j, k}) (c := c) fun m hm => by
          rw [hcv] at hm
          simp only [basisW_apply] at hm
          simp only [Finset.mem_insert, Finset.mem_singleton]
          by_contra hn
          push Not at hn
          simp [hn.1, hn.2.1, hn.2.2] at hm
        have h3 := Finset.card_le_three (a := i) (b := j) (c := k)
        omega
    exact triple_aux hij fun m => by rw [← hcv, hc0]; rfl

theorem todd_fixedPointFree
    [Finite V] (hV : Nat.card V = 2 ^ 10) {x : Fin 22 → V}
    (hx : Function.Injective x) (hρ : ∀ g ∈ M22, ∃ ρ : V →+ V, ∀ i, ρ (x i) = x (g i))
    {g : Equiv.Perm (Fin 22)} (hg11 : orderOf g = 11) {ρ : V →+ V}
    (hρg : ∀ i, ρ (x i) = x (g i)) {v : V} (hv : ρ v = v) : v = 0 := by
  classical
  have hp : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hft : Fintype V := Fintype.ofFinite V
  have hspan := (todd_module_unique hV hx hρ).1
  let r : V →ₗ[ZMod 2] V := ρ.toZModLinearMap 2
  have hr : ∀ w, r w = ρ w := fun _ => rfl
  have hpow : ∀ (n : ℕ) (i : Fin 22), (r ^ n) (x i) = x ((g ^ n) i) := by
    intro n
    induction n with
    | zero => exact fun i => rfl
    | succ n ih =>
      intro i
      rw [pow_succ, Module.End.mul_apply, hr, hρg, ih, pow_succ, Equiv.Perm.mul_apply]
  have h11 : r ^ 11 = 1 := by
    have heq : ∀ w ∈ Submodule.span (ZMod 2) (Set.range x), (r ^ 11) w = w := by
      intro w hw
      refine Submodule.span_induction (fun u hu => ?_) (by simp) (fun a b _ _ ha hb => ?_)
        (fun c a _ ha => ?_) hw
      · obtain ⟨i, rfl⟩ := hu
        rw [hpow, ← hg11, pow_orderOf_eq_one, Equiv.Perm.one_apply]
      · rw [map_add, ha, hb]
      · rw [map_smul, ha]
    exact LinearMap.ext fun w => heq w (hspan ▸ Submodule.mem_top)
  set F := LinearMap.eqLocus r LinearMap.id
  have hfix : ∀ w, w ∈ F ↔ r w = w := fun w => LinearMap.mem_eqLocus
  let f : Function.End V := fun w => r w
  have hf : f ^ 11 ^ 1 = 1 := by
    change f^[11 ^ 1] = id
    funext w
    have : ∀ n : ℕ, f^[n] w = (r ^ n) w := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', Module.End.mul_apply]
    rw [this, pow_one, h11]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 11) (n := 1) hf
  have hcardF : Fintype.card (Function.fixedPoints f) = Nat.card F := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      { toFun := fun w => ⟨w.1, (hfix w.1).2 w.2⟩
        invFun := fun w => ⟨w.1, (hfix w.1).1 w.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hcardF, ← Nat.card_eq_fintype_card, hV, ← FiniteField.pow_finrank_eq_natCard 2 F] at hmod
  have hle : finrank (ZMod 2) F ≤ 10 := by
    have := Submodule.finrank_le F
    have hVd : finrank (ZMod 2) V = 10 := by
      have h := FiniteField.pow_finrank_eq_natCard 2 V
      rw [hV] at h
      exact Nat.pow_right_injective (le_refl 2) h
    omega
  have hd : finrank (ZMod 2) F = 0 ∨ finrank (ZMod 2) F = 10 := by
    have key : ∀ d ≤ 10, 2 ^ 10 % 11 = 2 ^ d % 11 → d = 0 ∨ d = 10 := by decide
    exact key _ hle hmod
  rcases hd with h0 | h10
  · have hF : F = ⊥ := Submodule.finrank_eq_zero.1 h0
    have hvF : v ∈ F := (hfix v).2 hv
    rw [hF, Submodule.mem_bot] at hvF
    exact hvF
  · exfalso
    have hVd : finrank (ZMod 2) V = 10 := by
      have h := FiniteField.pow_finrank_eq_natCard 2 V
      rw [hV] at h
      exact Nat.pow_right_injective (le_refl 2) h
    have hF : F = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h10, hVd])
    have hg1 : g = 1 := by
      refine Equiv.ext fun i => hx ?_
      have : x i ∈ F := hF ▸ Submodule.mem_top
      rw [hfix, hr, hρg] at this
      exact this
    rw [hg1, orderOf_one] at hg11
    exact absurd hg11 (by norm_num)

abbrev toddModule : Type := W22 ⧸ toddKernel

@[expose] def toddPoint (i : Fin 22) : toddModule := Submodule.Quotient.mk (basisW i)

theorem finrank_toddModule : finrank (ZMod 2) toddModule = 10 := by
  have h := Submodule.finrank_quotient_add_finrank toddKernel
  rw [finrank_toddKernel, finrank_W22] at h
  change finrank (ZMod 2) (W22 ⧸ toddKernel) = 10
  omega

theorem card_toddModule : Nat.card toddModule = 2 ^ 10 := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← FiniteField.pow_finrank_eq_natCard 2, finrank_toddModule]

theorem toddPoint_injective : Function.Injective toddPoint := by
  intro i j h
  by_contra hij
  rw [toddPoint, toddPoint, Submodule.Quotient.eq] at h
  have hne : basisW i - basisW j ≠ 0 := by
    intro h0
    have := congrFun h0 i
    change basisW i i - basisW j i = 0 at this
    rw [basisW_apply, basisW_apply, ite_eq_left rfl, ite_eq_right hij] at this
    exact absurd this (by decide)
  have h6 := six_le_card_supp h hne
  have h2 : (supp (basisW i - basisW j)).card ≤ ({i, j} : Finset (Fin 22)).card :=
    card_supp_le fun m hm => by
      change basisW i m - basisW j m ≠ 0 at hm
      simp only [basisW_apply] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_contra hn
      push Not at hn
      simp [hn.1, hn.2] at hm
  have := Finset.card_le_two (a := i) (b := j)
  omega

theorem permW_basisW (g : Equiv.Perm (Fin 22)) (i : Fin 22) :
    permW g (basisW i) = basisW (g i) := by
  ext j
  rw [permW_apply, basisW_apply, basisW_apply]
  simp only [Equiv.Perm.inv_eq_iff_eq]

@[expose] def toddAct
    {g : Equiv.Perm (Fin 22)} (hg : g ∈ hexadAut) :
    toddModule →ₗ[ZMod 2] toddModule :=
  toddKernel.mapQ toddKernel (permW g) fun _ hc => permW_mem_toddKernel hg hc

theorem toddAct_point
    {g : Equiv.Perm (Fin 22)} (hg : g ∈ hexadAut) (i : Fin 22) :
    toddAct hg (toddPoint i) = toddPoint (g i) := by
  rw [toddAct, toddPoint, Submodule.mapQ_apply, permW_basisW]
  rfl

theorem todd_module_equiv
    [Finite V] (hV : Nat.card V = 2 ^ 10) {x : Fin 22 → V}
    (hx : Function.Injective x) (hρ : ∀ g ∈ M22, ∃ ρ : V →+ V, ∀ i, ρ (x i) = x (g i)) :
    ∃ e : V ≃ₗ[ZMod 2] toddModule, ∀ i, e (x i) = toddPoint i := by
  obtain ⟨hspan, hrel⟩ := todd_module_unique hV hx hρ
  have hsurj : Function.Surjective (evalW x) := by
    rw [← LinearMap.range_eq_top, range_evalW, hspan]
  have hker : LinearMap.ker (evalW x) = toddKernel := by
    ext c
    rw [LinearMap.mem_ker, hrel]
  let e₁ := (evalW x).quotKerEquivOfSurjective hsurj
  let e₂ : toddModule ≃ₗ[ZMod 2] (W22 ⧸ LinearMap.ker (evalW x)) :=
    Submodule.quotEquivOfEq _ _ hker.symm
  refine ⟨(e₂.trans e₁).symm, fun i => ?_⟩
  rw [LinearEquiv.symm_apply_eq]
  change x i = e₁ (e₂ (Submodule.Quotient.mk (basisW i)))
  rw [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk, evalW_basisW]

end Module

end CFSG.EvenSmallLie.UnitarySix.MathieuExt
