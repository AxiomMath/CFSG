module

public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverPresentation
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public noncomputable section

namespace CFSG.ComponentClassification.PresentationLocal

open Equiv Equiv.Perm CFSG.LocalAnalysis.ComponentInitial

theorem finite_closure_and_card_le_of_carmichael {G : Type*} [Group G] :
    ∀ (m : ℕ) (a : Fin m → G), (∀ i, a i ^ 3 = 1) → (∀ i j, i ≠ j → (a i * a j) ^ 2 = 1) →
      Finite (Subgroup.closure (Set.range a)) ∧
        Nat.card (Subgroup.closure (Set.range a)) ≤ (m + 2).factorial / 2 := by
  intro m
  induction m with
  | zero =>
    intro a _ _
    rw [Set.range_eq_empty, Subgroup.closure_empty, Subgroup.card_bot]
    exact ⟨inferInstance, by simp⟩
  | succ m ih =>
    intro a ha haa
    set b := a (Fin.last m)
    set a' : Fin m → G := fun i => a i.castSucc
    set H := Subgroup.closure (Set.range a')
    obtain ⟨hHfin, hH⟩ := ih a' (fun i => ha _) fun i j hij =>
      haa _ _ (fun h => hij (Fin.castSucc_injective _ h))
    have hHle : H ≤ Subgroup.closure (Set.range a) :=
      Subgroup.closure_mono (Set.range_subset_iff.mpr fun i => ⟨i.castSucc, rfl⟩)
    have hrep : ∀ k, carmichaelRep a' b k ∈ Subgroup.closure (Set.range a) := by
      have hb : b ∈ Subgroup.closure (Set.range a) := Subgroup.subset_closure ⟨_, rfl⟩
      rintro (k | i)
      · fin_cases k
        · exact Subgroup.one_mem _
        · exact hb
        · exact Subgroup.pow_mem _ hb _
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, rfl⟩) (Subgroup.pow_mem _ hb _)
    have hcov : ∀ g ∈ Subgroup.closure (Set.range a),
        ∃ k, ∃ h ∈ H, g = carmichaelRep a' b k * h := by
      have hstep : ∀ x ∈ Set.range a, ∀ g, (∃ k, ∃ h ∈ H, g = carmichaelRep a' b k * h) →
          ∃ k, ∃ h ∈ H, x * g = carmichaelRep a' b k * h := by
        rintro x ⟨j, rfl⟩ g ⟨k, h, hh, rfl⟩
        have hx : a j = b ∨ ∃ i, a j = a' i := by
          cases j using Fin.lastCases with
          | last => exact Or.inl rfl
          | cast i => exact Or.inr ⟨i, rfl⟩
        obtain ⟨k', h', hh', he⟩ := exists_mul_carmichaelRep_eq a' b (fun i => ha _) (ha _)
          (fun i => haa _ _ (Fin.castSucc_ne_last i)) (fun i j hij => haa _ _
            (fun h => hij (Fin.castSucc_injective _ h))) (a j) hx k
        exact ⟨k', h' * h, H.mul_mem hh' hh, by rw [← mul_assoc, he, mul_assoc]⟩
      intro g hg
      induction hg using Subgroup.closure_induction_left with
      | one => exact ⟨.inl 0, 1, H.one_mem, by simp [carmichaelRep]⟩
      | mul_left x hx g _ ih => exact hstep x hx g ih
      | inv_mul_cancel x hx g _ ih =>
        obtain ⟨j, rfl⟩ := hx
        rw [inv_eq_sq_of_pow_three (ha j), sq, mul_assoc]
        exact hstep _ ⟨j, rfl⟩ _ (hstep _ ⟨j, rfl⟩ g ih)
    let f : (Fin 3 ⊕ Fin m) × H → Subgroup.closure (Set.range a) := fun p =>
      ⟨carmichaelRep a' b p.1 * p.2, Subgroup.mul_mem _ (hrep _) (hHle p.2.2)⟩
    have hf : Function.Surjective f := by
      rintro ⟨g, hg⟩
      obtain ⟨k, h, hh, rfl⟩ := hcov g hg
      exact ⟨(k, ⟨h, hh⟩), rfl⟩
    have hcard := Nat.card_le_card_of_surjective f hf
    refine ⟨Finite.of_surjective f hf, ?_⟩
    rw [Nat.card_prod, Nat.card_sum, Nat.card_eq_fintype_card (α := Fin 3),
      Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin, Fintype.card_fin] at hcard
    have h2 : 2 ∣ (m + 2).factorial := Nat.dvd_factorial (by norm_num) (by omega)
    calc Nat.card (Subgroup.closure (Set.range a)) ≤ (3 + m) * Nat.card H := hcard
      _ ≤ (3 + m) * ((m + 2).factorial / 2) := Nat.mul_le_mul_left _ hH
      _ = (m + 1 + 2).factorial / 2 := by
        have : (m + 1 + 2).factorial = (m + 3) * (m + 2).factorial := Nat.factorial_succ (m + 2)
        rw [this, Nat.mul_div_assoc _ h2, Nat.add_comm 3 m]

variable {n : ℕ}

variable (n) in
abbrev CarmichaelIndex : Type := {k : Fin n // 2 ≤ (k : ℕ)}

theorem CarmichaelIndex.two_lt (k : CarmichaelIndex n) : 2 < n :=
  lt_of_le_of_lt k.2 k.1.isLt

@[expose] def carmichaelPerm (k : CarmichaelIndex n) : Perm (Fin n) :=
  swap ⟨0, by have := k.two_lt; omega⟩ k.1 * swap ⟨0, by have := k.two_lt; omega⟩
    ⟨1, by have := k.two_lt; omega⟩

theorem carmichaelPerm_apply (k : CarmichaelIndex n) (x : Fin n) :
    carmichaelPerm k x =
      if (x : ℕ) = 0 then ⟨1, by have := k.two_lt; omega⟩
      else if (x : ℕ) = 1 then k.1 else if x = k.1 then ⟨0, by have := k.two_lt; omega⟩
      else x := by
  have hk := k.2
  rw [carmichaelPerm, Perm.mul_apply]
  by_cases h0 : (x : ℕ) = 0
  · have hx : x = ⟨0, by have := k.two_lt; omega⟩ := Fin.ext h0
    rw [ite_eq_left h0, hx, swap_apply_left, swap_apply_of_ne_of_ne (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff]; omega)]
  by_cases h1 : (x : ℕ) = 1
  · have hx : x = ⟨1, by have := k.two_lt; omega⟩ := Fin.ext h1
    rw [ite_eq_right h0, ite_eq_left h1, hx, swap_apply_right, swap_apply_left]
  have hin : swap (⟨0, by have := k.two_lt; omega⟩ : Fin n) ⟨1, by have := k.two_lt; omega⟩ x =
      x := swap_apply_of_ne_of_ne (fun h => h0 (by rw [h])) (fun h => h1 (by rw [h]))
  rw [ite_eq_right h0, ite_eq_right h1, hin]
  by_cases hxk : x = k.1
  · rw [ite_eq_left hxk, hxk, swap_apply_right]
  · rw [ite_eq_right hxk, swap_apply_of_ne_of_ne (fun h => h0 (by rw [h])) hxk]

theorem carmichaelPerm_isThreeCycle (k : CarmichaelIndex n) : (carmichaelPerm k).IsThreeCycle := by
  have hk := k.2
  exact isThreeCycle_swap_mul_swap_same (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff])
    (by simp [Fin.ext_iff]; omega)

theorem carmichaelPerm_mem (k : CarmichaelIndex n) : carmichaelPerm k ∈ alternatingGroup (Fin n) :=
  mem_alternatingGroup.2 (carmichaelPerm_isThreeCycle k).sign

@[expose] def carmichaelCycle (k : CarmichaelIndex n) : alternatingGroup (Fin n) :=
  ⟨carmichaelPerm k, carmichaelPerm_mem k⟩

theorem carmichaelCycle_pow_three (k : CarmichaelIndex n) : carmichaelCycle k ^ 3 = 1 :=
  Subtype.ext (by
    rw [Subgroup.coe_pow, ← (carmichaelPerm_isThreeCycle k).orderOf]
    exact pow_orderOf_eq_one _)

theorem carmichaelPerm_mul (i j : CarmichaelIndex n) :
    carmichaelPerm i * carmichaelPerm j =
      swap ⟨0, by have := i.two_lt; omega⟩ i.1 * swap ⟨1, by have := i.two_lt; omega⟩ j.1 := by
  have hi := i.2
  have hj := j.2
  have h01 : (⟨0, by have := i.two_lt; omega⟩ : Fin n) ≠ ⟨1, by have := i.two_lt; omega⟩ := by
    simp
  have hconj : swap (⟨0, by have := i.two_lt; omega⟩ : Fin n) ⟨1, by have := i.two_lt; omega⟩ *
      swap ⟨0, by have := i.two_lt; omega⟩ j.1 *
        swap ⟨0, by have := i.two_lt; omega⟩ ⟨1, by have := i.two_lt; omega⟩ =
      swap ⟨1, by have := i.two_lt; omega⟩ j.1 := by
    have h := swap_apply_apply (swap (⟨0, by have := i.two_lt; omega⟩ : Fin n)
      ⟨1, by have := i.two_lt; omega⟩) ⟨0, by have := i.two_lt; omega⟩ j.1
    rw [swap_apply_left, swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; omega)
      (by simp [Fin.ext_iff]; omega), swap_inv] at h
    exact h.symm
  rw [carmichaelPerm, carmichaelPerm, ← hconj]
  simp only [mul_assoc]

theorem swap_mul_swap_sq_eq_one {a b c d : Fin n} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : (swap a b * swap c d) ^ 2 = 1 := by
  have hcomm : swap a b * swap c d = swap c d * swap a b := by
    have h := swap_apply_apply (swap a b) c d
    rw [swap_apply_of_ne_of_ne hac.symm hbc.symm, swap_apply_of_ne_of_ne had.symm hbd.symm,
      swap_inv] at h
    conv_rhs => rw [h]
    exact (mul_swap_mul_self _ _ _).symm
  rw [sq, mul_assoc, ← mul_assoc (swap c d), ← hcomm, mul_assoc, swap_mul_self, mul_one,
    swap_mul_self]

theorem carmichaelCycle_mul_sq (i j : CarmichaelIndex n) (hij : i ≠ j) :
    (carmichaelCycle i * carmichaelCycle j) ^ 2 = 1 := by
  have hi := i.2
  have hj := j.2
  have hij' : (i.1 : ℕ) ≠ j.1 := fun h => hij (Subtype.ext (Fin.ext h))
  refine Subtype.ext ?_
  rw [Subgroup.coe_pow, Subgroup.coe_mul]
  change (carmichaelPerm i * carmichaelPerm j) ^ 2 = 1
  rw [carmichaelPerm_mul i j]
  exact swap_mul_swap_sq_eq_one (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]; omega)
    (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)

theorem alternatingGroup_le_of_swap_mul_swap_mem (h : 1 < n) {H : Subgroup (Perm (Fin n))}
    (hH : ∀ a b : Fin n, (a : ℕ) ≠ 0 → (b : ℕ) ≠ 0 →
      swap ⟨0, Nat.zero_lt_of_lt h⟩ a * swap ⟨0, Nat.zero_lt_of_lt h⟩ b ∈ H)
    (hHA : H ≤ alternatingGroup (Fin n)) : alternatingGroup (Fin n) ≤ H := by
  set z : Fin n := ⟨0, Nat.zero_lt_of_lt h⟩ with hz
  set o : Fin n := ⟨1, h⟩ with ho
  have hoz : (o : ℕ) ≠ 0 := by simp [ho]
  have hzo : z ≠ o := by simp [hz, ho]
  have hconj : ∀ x y : Fin n, (y : ℕ) ≠ 0 → x ≠ y →
      swap x y = swap z x * swap z y * swap z x := by
    intro x y hy hxy
    have := swap_apply_apply (swap z x) z y
    rw [swap_apply_left, swap_apply_of_ne_of_ne (fun h' => hy (by rw [h'])) hxy.symm,
      swap_inv] at this
    exact this
  have hstep : ∀ y : Fin n, (y : ℕ) ≠ 0 → ∀ f : Perm (Fin n), (f ∈ H ∨ swap z o * f ∈ H) →
      (swap z y * f ∈ H ∨ swap z o * (swap z y * f) ∈ H) := by
    intro y hy f hf
    rcases hf with hf | hf
    · right
      rw [← mul_assoc]
      exact H.mul_mem (hH o y hoz hy) hf
    · left
      have : swap z y * f = (swap z y * swap z o) * (swap z o * f) := by
        simp only [mul_assoc, swap_mul_self_mul]
      rw [this]
      exact H.mul_mem (hH y o hy hoz) hf
  have key : ∀ σ : Perm (Fin n), σ ∈ H ∨ swap z o * σ ∈ H := by
    intro σ
    induction σ using Equiv.Perm.swap_induction_on with
    | one => exact Or.inl H.one_mem
    | swap_mul f x y hxy ih =>
      by_cases hx : (x : ℕ) = 0
      · have hx' : x = z := Fin.ext hx
        rw [hx']
        exact hstep y (fun hy => hxy (Fin.ext (by rw [hx, hy]))) f ih
      by_cases hy : (y : ℕ) = 0
      · have hy' : y = z := Fin.ext hy
        rw [hy', swap_comm]
        exact hstep x hx f ih
      rw [hconj x y hy hxy]
      rcases ih with hf | hf
      · right
        have : swap z o * (swap z x * swap z y * swap z x * f) =
            (swap z o * swap z x) * (swap z y * swap z x) * f := by
          simp only [mul_assoc]
        rw [this]
        exact H.mul_mem (H.mul_mem (hH o x hoz hx) (hH y x hy hx)) hf
      · left
        have : swap z x * swap z y * swap z x * f =
            (swap z x * swap z y) * (swap z x * swap z o) * (swap z o * f) := by
          simp only [mul_assoc, swap_mul_self_mul]
        rw [this]
        exact H.mul_mem (H.mul_mem (hH x y hx hy) (hH x o hx hoz)) hf
  intro σ hσ
  rcases key σ with h1 | h2
  · exact h1
  · exfalso
    have := mem_alternatingGroup.1 (hHA h2)
    rw [map_mul, sign_swap hzo, mem_alternatingGroup.1 hσ, mul_one] at this
    exact absurd this (by decide)

theorem closure_range_carmichaelCycle (hn : 3 ≤ n) :
    Subgroup.closure (Set.range (carmichaelCycle (n := n))) = ⊤ := by
  have h : 1 < n := by omega
  set z : Fin n := ⟨0, Nat.zero_lt_of_lt h⟩ with hz
  set o : Fin n := ⟨1, h⟩ with ho
  set H := Subgroup.closure (Set.range fun k : CarmichaelIndex n => carmichaelPerm k) with hH
  have hmemH : ∀ k, carmichaelPerm k ∈ H := fun k => Subgroup.subset_closure ⟨k, rfl⟩
  have hstar : ∀ a : Fin n, (a : ℕ) ≠ 0 → swap z a * swap z o ∈ H := by
    intro a ha
    by_cases ha1 : (a : ℕ) = 1
    · have : a = o := Fin.ext ha1
      rw [this, swap_mul_self]
      exact H.one_mem
    · exact hmemH ⟨a, by omega⟩
  have hpair : ∀ a b : Fin n, (a : ℕ) ≠ 0 → (b : ℕ) ≠ 0 → swap z a * swap z b ∈ H := by
    intro a b ha hb
    have : swap z a * swap z b = (swap z a * swap z o) * (swap z b * swap z o)⁻¹ := by
      rw [mul_inv_rev, swap_inv, swap_inv]
      simp only [mul_assoc, swap_mul_self_mul]
    rw [this]
    exact H.mul_mem (hstar a ha) (H.inv_mem (hstar b hb))
  have hHA : H ≤ alternatingGroup (Fin n) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact carmichaelPerm_mem k
  have hle := alternatingGroup_le_of_swap_mul_swap_mem h hpair hHA
  have hmap : (Subgroup.closure (Set.range (carmichaelCycle (n := n)))).map
      (alternatingGroup (Fin n)).subtype = H := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  rw [eq_top_iff]
  intro σ _
  have hσ : (σ : Perm (Fin n)) ∈ H := hle σ.2
  rw [← hmap] at hσ
  obtain ⟨g, hg, hgσ⟩ := hσ
  rwa [show g = σ from Subtype.ext hgσ] at hg

@[expose] def carmichaelIndexEquiv (n : ℕ) : Fin (n - 2) ≃ CarmichaelIndex n where
  toFun i := ⟨⟨i + 2, by omega⟩, by simp⟩
  invFun k := ⟨k.1 - 2, by have := k.1.isLt; have := k.2; omega⟩
  left_inv i := Fin.ext (by simp)
  right_inv k := Subtype.ext (Fin.ext (by have := k.2; simp; omega))

theorem exists_hom_carmichaelCycle (hn : 3 ≤ n) {J : Type*} [Group J]
    (x : CarmichaelIndex n → J) (hx : ∀ i, x i ^ 3 = 1)
    (hxx : ∀ i j, i ≠ j → (x i * x j) ^ 2 = 1) :
    ∃ φ : alternatingGroup (Fin n) →* J, ∀ i, φ (carmichaelCycle i) = x i := by
  let y : CarmichaelIndex n → alternatingGroup (Fin n) × J := fun i => (carmichaelCycle i, x i)
  set K := Subgroup.closure (Set.range y) with hK
  have hy3 : ∀ i, y i ^ 3 = 1 := fun i =>
    Prod.ext (by simp [y, carmichaelCycle_pow_three]) (by simp [y, hx])
  have hyy : ∀ i j, i ≠ j → (y i * y j) ^ 2 = 1 := fun i j hij =>
    Prod.ext (by simp [y, carmichaelCycle_mul_sq i j hij]) (by simp [y, hxx i j hij])
  obtain ⟨hKfin, hKcard⟩ : Finite K ∧ Nat.card K ≤ (n - 2 + 2).factorial / 2 := by
    have := finite_closure_and_card_le_of_carmichael (n - 2) (y ∘ carmichaelIndexEquiv n)
      (fun i => hy3 _) (fun i j hij => hyy _ _ ((carmichaelIndexEquiv n).injective.ne hij))
    rwa [Set.range_comp, (carmichaelIndexEquiv n).range_eq_univ, Set.image_univ] at this
  let p : K →* alternatingGroup (Fin n) := (MonoidHom.fst _ _).comp K.subtype
  have hp : Function.Surjective p := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_range_carmichaelCycle hn,
      Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨y i, Subgroup.subset_closure ⟨i, rfl⟩⟩, rfl⟩
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hbij : Function.Bijective p := hp.bijective_of_nat_card_le (by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rwa [show n - 2 + 2 = n by omega] at hKcard)
  let E := MulEquiv.ofBijective p hbij
  refine ⟨((MonoidHom.snd _ _).comp K.subtype).comp E.symm.toMonoidHom, fun i => ?_⟩
  have hE : E.symm (carmichaelCycle i) = ⟨y i, Subgroup.subset_closure ⟨i, rfl⟩⟩ :=
    E.symm_apply_eq.2 rfl
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hE]
  rfl

theorem hom_ext_carmichaelCycle (hn : 3 ≤ n) {L : Type*} [Group L]
    {φ ψ : alternatingGroup (Fin n) →* L}
    (h : ∀ i, φ (carmichaelCycle i) = ψ (carmichaelCycle i)) : φ = ψ := by
  refine MonoidHom.eq_of_eqOn_dense (closure_range_carmichaelCycle hn) ?_
  rintro _ ⟨i, rfl⟩
  exact h i

variable (n) in
@[expose] def carmichaelRels : Set (FreeGroup (CarmichaelIndex n)) :=
  Set.range (fun i => FreeGroup.of i ^ 3) ∪
    {r | ∃ i j, i ≠ j ∧ r = (FreeGroup.of i * FreeGroup.of j) ^ 2}

theorem alternating_carmichael_presentation_universal_map (hn : 3 ≤ n) {J : Type*} [Group J]
    (x : CarmichaelIndex n → J) (hx : ∀ i, x i ^ 3 = 1)
    (hxx : ∀ i j, i ≠ j → (x i * x j) ^ 2 = 1) :
    (∃ e : PresentedGroup (carmichaelRels n) ≃* alternatingGroup (Fin n),
      ∀ i, e (PresentedGroup.of i) = carmichaelCycle i) ∧
    (∃! φ : alternatingGroup (Fin n) →* J, ∀ i, φ (carmichaelCycle i) = x i) ∧
    ∀ φ : alternatingGroup (Fin n) →* J, (∀ i, φ (carmichaelCycle i) = x i) →
      φ.range = Subgroup.closure (Set.range x) := by
  refine ⟨?_, ?_, fun φ hφ => ?_⟩
  ·
    have hrel : ∀ r ∈ carmichaelRels n, FreeGroup.lift carmichaelCycle r = 1 := by
      rintro r (⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩)
      · simp [carmichaelCycle_pow_three]
      · simp [carmichaelCycle_mul_sq i j hij]
    have hof3 : ∀ i, (PresentedGroup.of i : PresentedGroup (carmichaelRels n)) ^ 3 = 1 :=
      fun i => PresentedGroup.one_of_mem (Or.inl ⟨i, rfl⟩)
    have hofof : ∀ i j, i ≠ j →
        ((PresentedGroup.of i : PresentedGroup (carmichaelRels n)) * PresentedGroup.of j) ^ 2 =
          1 :=
      fun i j hij => PresentedGroup.one_of_mem (Or.inr ⟨i, j, hij, rfl⟩)
    obtain ⟨ψ, hψ⟩ := exists_hom_carmichaelCycle hn _ hof3 hofof
    let f := PresentedGroup.toGroup hrel
    have hf : ∀ i, f (PresentedGroup.of i) = carmichaelCycle i := fun i =>
      PresentedGroup.toGroup.of hrel
    refine ⟨MonoidHom.toMulEquiv f ψ ?_ ?_, hf⟩
    · refine PresentedGroup.ext fun i => ?_
      rw [MonoidHom.comp_apply, hf, hψ, MonoidHom.id_apply]
    · refine hom_ext_carmichaelCycle hn fun i => ?_
      rw [MonoidHom.comp_apply, hψ, hf, MonoidHom.id_apply]
  · obtain ⟨φ, hφ⟩ := exists_hom_carmichaelCycle hn x hx hxx
    exact ⟨φ, hφ, fun ψ hψ => hom_ext_carmichaelCycle hn fun i => by rw [hψ, hφ]⟩
  · rw [MonoidHom.range_eq_map, ← closure_range_carmichaelCycle hn, MonoidHom.map_closure,
      ← Set.range_comp]
    congr 1
    ext y
    simp [hφ]

end CFSG.ComponentClassification.PresentationLocal
