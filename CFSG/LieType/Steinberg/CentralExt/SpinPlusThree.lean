module

public import CFSG.LieType.Steinberg.CentralExt.POmegaPlusMultiplier
public import CFSG.LieType.Steinberg.CentralExt.WeylLift

public section

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.SpinFrame CFSG.LieType.RootSystem CFSG.LieType.Steinberg.CentralExt.SpinTorus
  CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed

variable {n : ℕ} {K : Type} [Field K]

theorem exists_ne_four (hn5 : 5 ≤ n) (a b c d : Fin n) :
    ∃ m : Fin n, m ≠ a ∧ m ≠ b ∧ m ≠ c ∧ m ≠ d := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, b, c, d} := fun m _ => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hm
    push Not at hm
    exact hm.2.2.2 (h m hm.1 hm.2.1 hm.2.2.1)
  have h1 := Finset.card_le_card hsub
  have h2 : ({a, b, c, d} : Finset (Fin n)).card ≤ 4 :=
    (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
      (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))))
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem exists_ne_three (hn4 : 4 ≤ n) (a b c : Fin n) : ∃ m : Fin n, m ≠ a ∧ m ≠ b ∧ m ≠ c := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, b, c} := fun m _ => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hm
    push Not at hm
    exact hm.2.2 (h m hm.1 hm.2.1)
  have h1 := Finset.card_le_card hsub
  have h2 : ({a, b, c} : Finset (Fin n)).card ≤ 3 :=
    (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
      (by simp)))
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem not_isLong_add_disjoint {i j k l : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (s t u v : Bool) :
    ¬IsLong ((Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin n → ℤ) +
      (Pi.single k (boolSign u) + Pi.single l (boolSign v))) := by
  refine not_isLong_of_apply_ne_zero hij hik hjk ?_ ?_ ?_ <;>
    simp [Pi.single_apply, hij, hik, hil, hjk, hjl, hkl, hij.symm, hik.symm, hil.symm, hjk.symm,
      hjl.symm, hkl.symm, boolSign] <;> split_ifs <;> norm_num

theorem single_add_single_apply_of_ne' {i j m : Fin n} (hmi : m ≠ i) (hmj : m ≠ j) (a b : ℤ) :
    (Pi.single i a + Pi.single j b : Fin n → ℤ) m = 0 := by
  simp [hmi, hmj]

theorem neg_one_zpow_boolSign (u : Bool) : ((-1 : Kˣ) ^ boolSign u : Kˣ) = -1 := by
  cases u <;> simp [boolSign]

theorem not_isLong_single_two {i : Fin n} {z : ℤ} (hz : z = 2 ∨ z = -2) :
    ¬IsLong (Pi.single i z : Fin n → ℤ) := by
  intro h
  rcases h.apply_mem i with h1 | h1 | h1 <;> rw [Pi.single_eq_same] at h1 <;> omega

variable (hn : 3 ≤ n)

section Swap

@[expose] def negBool (j m : Fin n) (x : Fin n) (r : Bool) : Bool :=
  if x = j ∨ x = m then !r else r

@[expose] def negSign (j m : Fin n) (x : Fin n) (_r : Bool) : ℤ :=
  if x = j ∨ x = m then -1 else 1

variable {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} (F : HypFrame Q n)

@[expose] noncomputable def negPair {j m : Fin n} (hjm : j ≠ m) : spinGroup Q :=
  F.longWeyl hjm true true * F.longWeyl hjm true false

theorem spinAction_negPair {j m : Fin n} (hjm : j ≠ m) (x : Fin n) (r : Bool) :
    spinAction Q (negPair F hjm) (F.vec x r) =
      ((negSign j m x r : ℤ) : K) • F.vec x (negBool j m x r) := by
  have a1 : spinAction Q (F.longWeyl hjm true false) (F.vec j true) =
      -F.vec m true := by
    have := F.spinAction_longWeyl_vec_left hjm true false
    simpa only [Bool.not_false] using this
  have a2 : spinAction Q (F.longWeyl hjm true false) (F.vec j false) =
      -F.vec m false := by
    have := F.spinAction_longWeyl_vec_left_not hjm true false
    simpa only [Bool.not_true] using this
  have a3 : spinAction Q (F.longWeyl hjm true false) (F.vec m false) =
      F.vec j false := by
    have := F.spinAction_longWeyl_vec_right hjm true false
    simpa only [Bool.not_true] using this
  have a4 : spinAction Q (F.longWeyl hjm true false) (F.vec m true) =
      F.vec j true := by
    have := F.spinAction_longWeyl_vec_right_not hjm true false
    simpa only [Bool.not_false] using this
  have b1 : spinAction Q (F.longWeyl hjm true true) (F.vec j true) =
      -F.vec m false := by
    have := F.spinAction_longWeyl_vec_left hjm true true
    simpa only [Bool.not_true] using this
  have b2 : spinAction Q (F.longWeyl hjm true true) (F.vec j false) =
      -F.vec m true := by
    have := F.spinAction_longWeyl_vec_left_not hjm true true
    simpa only [Bool.not_true] using this
  have b3 : spinAction Q (F.longWeyl hjm true true) (F.vec m true) =
      F.vec j false := by
    have := F.spinAction_longWeyl_vec_right hjm true true
    simpa only [Bool.not_true] using this
  have b4 : spinAction Q (F.longWeyl hjm true true) (F.vec m false) =
      F.vec j true := by
    have := F.spinAction_longWeyl_vec_right_not hjm true true
    simpa only [Bool.not_true] using this
  rw [negPair, map_mul, LinearEquiv.mul_apply]
  by_cases hxj : x = j
  · subst hxj
    cases r
    · rw [a2, map_neg, b4]
      simp [negSign, negBool]
    · rw [a1, map_neg, b3]
      simp [negSign, negBool]
  · by_cases hxm : x = m
    · subst hxm
      cases r
      · rw [a3, b2]
        simp [negSign, negBool, hxj]
      · rw [a4, b1]
        simp [negSign, negBool, hxj]
    · rw [F.spinAction_longWeyl_vec_of_ne hjm true false hxj hxm,
        F.spinAction_longWeyl_vec_of_ne hjm true true hxj hxm]
      simp [negSign, negBool, hxj, hxm]

theorem negBool_negBool (j m x : Fin n) (r : Bool) : negBool j m x (negBool j m x r) = r := by
  unfold negBool
  split_ifs <;> simp

theorem negPair_swap {i j m : Fin n} (hij : i ≠ j) (hmi : m ≠ i) (hmj : m ≠ j) (s t : Bool) :
    ∃ a : K, a * a = 1 ∧
      (∀ c, negPair F hmj.symm * rootElt F (Pi.single i (boolSign s) + Pi.single j (boolSign t)) c *
        (negPair F hmj.symm)⁻¹ = rootElt F (Pi.single i (boolSign s) + Pi.single j (boolSign (!t)))
          (a * c)) ∧
      ∀ c, negPair F hmj.symm * rootElt F (Pi.single i (boolSign s) + Pi.single j (boolSign (!t))) c *
        (negPair F hmj.symm)⁻¹ = rootElt F (Pi.single i (boolSign s) + Pi.single j (boolSign t))
          (a * c) := by
  have hw : ∀ x r, negSign j m x r = 1 ∨ negSign j m x r = -1 := fun x r => by
    unfold negSign
    split_ifs <;> simp
  have hg := spinAction_negPair F hmj.symm
  have hβi : ∀ r, negBool j m i r = r := fun r => by simp [negBool, hij, hmi.symm]
  have hβj : ∀ r, negBool j m j r = !r := fun r => by simp [negBool]
  obtain ⟨ε₁, hε₁, h1⟩ := conj_rootElt_of_signedPerm F (negPair F hmj.symm) (Equiv.refl _)
    (negBool j m) (negSign j m) hw hg hij (u := s) (v := t) rfl
  obtain ⟨ε₂, hε₂, h2⟩ := conj_rootElt_of_signedPerm F (negPair F hmj.symm) (Equiv.refl _)
    (negBool j m) (negSign j m) hw hg hij (u := s) (v := !t) rfl
  simp only [Equiv.refl_apply, hβi, hβj, Bool.not_not] at h1 h2
  have hg2 : ∀ x r, spinAction Q (negPair F hmj.symm * negPair F hmj.symm)
      (F.vec x r) = (1 : K) • F.vec x r := fun x r => by
    rw [map_mul, LinearEquiv.mul_apply, hg, map_smul, hg, negBool_negBool, smul_smul]
    unfold negSign
    split_ifs <;> simp
  have hd := conj_rootElt_of_diag F _ (fun _ _ => (1 : K)) hg2 hij
    (e := Pi.single i (boolSign s) + Pi.single j (boolSign t)) (u := s) (v := t) rfl 1
  have he : IsLong (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin n → ℤ) :=
    isLong_single_add_single hij s t
  have hεε : (ε₂ : K) * ε₁ = 1 := by
    have e : negPair F hmj.symm * negPair F hmj.symm *
        rootElt F (Pi.single i (boolSign s) + Pi.single j (boolSign t)) 1 *
          (negPair F hmj.symm * negPair F hmj.symm)⁻¹ =
        negPair F hmj.symm * (negPair F hmj.symm *
          rootElt F (Pi.single i (boolSign s) + Pi.single j (boolSign t)) 1 *
            (negPair F hmj.symm)⁻¹) * (negPair F hmj.symm)⁻¹ := by group
    rw [e, h1, h2] at hd
    have := rootElt_injective F he hd
    linear_combination this
  have hε₁' : (ε₁ : K) * ε₁ = 1 := intCast_mul_self_of_sq hε₁
  have heq : (ε₂ : K) = ε₁ := by linear_combination (-(ε₂ : K)) * hε₁' + (ε₁ : K) * hεε
  refine ⟨ε₁, hε₁', h1, fun c => ?_⟩
  rw [h2, heq]

theorem spinAction_longWeyl_true {i k : Fin n} (hik : i ≠ k) (τ : Bool) (m : Fin n) (r : Bool) :
    spinAction Q (F.longWeyl hik true τ) (F.vec m r) =
      ((if m = i then -1 else 1 : ℤ) : K) •
        F.vec (Equiv.swap i k m) (if m = i ∨ m = k then xor r τ else r) := by
  rw [F.spinAction_longWeyl_vec hik true τ m r]
  by_cases hmi : m = i
  · subst hmi
    simp only [longWeylSign, longWeylBool, ite_true, true_or, Bool.true_xor, Bool.not_not]
    norm_num
  · by_cases hmk : m = k
    · subst hmk
      simp only [longWeylSign, longWeylBool, hmi, ite_false, or_true, ite_true, Bool.true_xor,
        Bool.not_not]
      norm_num
    · simp only [longWeylSign, longWeylBool, hmi, hmk, or_self, ite_false]
      norm_num

@[expose] noncomputable def swapPair {i j k l : Fin n} (hik : i ≠ k) (hjl : j ≠ l) (τ₁ τ₂ : Bool) :
    spinGroup Q :=
  F.longWeyl hik true τ₁ * F.longWeyl hjl true τ₂

@[expose] def swapPerm (i j k l : Fin n) : Equiv.Perm (Fin n) := Equiv.swap i k * Equiv.swap j l

@[expose] def swapBool (i j k l : Fin n) (τ₁ τ₂ : Bool) (m : Fin n) (r : Bool) : Bool :=
  if m = i ∨ m = k then xor r τ₁ else if m = j ∨ m = l then xor r τ₂ else r

@[expose] def swapSign (i j : Fin n) (m : Fin n) (_r : Bool) : ℤ :=
  if m = i ∨ m = j then -1 else 1

theorem spinAction_swapPair {i j k l : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (τ₁ τ₂ : Bool) (m : Fin n) (r : Bool) :
    spinAction Q (swapPair F hik hjl τ₁ τ₂) (F.vec m r) =
      ((swapSign i j m r : ℤ) : K) • F.vec (swapPerm i j k l m) (swapBool i j k l τ₁ τ₂ m r) := by
  simp only [swapPair, map_mul, LinearEquiv.mul_apply, swapPerm, Equiv.Perm.mul_apply, swapSign,
    swapBool]
  rw [spinAction_longWeyl_true F hjl τ₂ m r, map_smul, spinAction_longWeyl_true F hik τ₁, smul_smul]
  by_cases hmi : m = i
  · rw [hmi]
    simp [Equiv.swap_apply_def, hij, hik, hil, hjk, hjl, hkl, hij.symm, hik.symm, hil.symm,
      hjk.symm, hjl.symm, hkl.symm]
  · by_cases hmk : m = k
    · rw [hmk]
      simp [Equiv.swap_apply_def, hij, hik, hil, hjk, hjl, hkl, hij.symm, hik.symm, hil.symm,
        hjk.symm, hjl.symm, hkl.symm]
    · by_cases hmj : m = j
      · rw [hmj]
        simp [Equiv.swap_apply_def, hij, hik, hil, hjk, hjl, hkl, hij.symm, hik.symm, hil.symm,
          hjk.symm, hjl.symm, hkl.symm]
      · by_cases hml : m = l
        · rw [hml]
          simp [Equiv.swap_apply_def, hij, hik, hil, hjk, hjl, hkl, hij.symm, hik.symm, hil.symm,
            hjk.symm, hjl.symm, hkl.symm]
        · simp [Equiv.swap_apply_def, hmi, hmk, hmj, hml]

theorem swapPair_swap {i j k l : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (s t u v : Bool) :
    ∃ a : K, a * a = 1 ∧
      (∀ c, swapPair F hik hjl (xor s u) (xor t v) *
        rootElt F (Pi.single i (boolSign s) + Pi.single j (boolSign t)) c *
          (swapPair F hik hjl (xor s u) (xor t v))⁻¹ =
        rootElt F (Pi.single k (boolSign u) + Pi.single l (boolSign v)) (a * c)) ∧
      ∀ c, swapPair F hik hjl (xor s u) (xor t v) *
        rootElt F (Pi.single k (boolSign u) + Pi.single l (boolSign v)) c *
          (swapPair F hik hjl (xor s u) (xor t v))⁻¹ =
        rootElt F (Pi.single i (boolSign s) + Pi.single j (boolSign t)) (a * c) := by
  set g := swapPair F hik hjl (xor s u) (xor t v) with hgdef
  have hw : ∀ x r, swapSign i j x r = 1 ∨ swapSign i j x r = -1 := fun x r => by
    unfold swapSign
    split_ifs <;> simp
  have hg := spinAction_swapPair F hij hik hil hjk hjl hkl (xor s u) (xor t v)
  obtain ⟨ε₁, hε₁, h1⟩ := conj_rootElt_of_signedPerm F g (swapPerm i j k l)
    (swapBool i j k l (xor s u) (xor t v)) (swapSign i j) hw hg hij (u := s) (v := t) rfl
  obtain ⟨ε₂, hε₂, h2⟩ := conj_rootElt_of_signedPerm F g (swapPerm i j k l)
    (swapBool i j k l (xor s u) (xor t v)) (swapSign i j) hw hg hkl (u := u) (v := v) rfl
  have hπi : swapPerm i j k l i = k := by
    simp [swapPerm, Equiv.swap_apply_def, hij, hik, hil, hjk, hjl, hkl, hij.symm, hik.symm, hil.symm, hjk.symm, hjl.symm, hkl.symm]
  have hπj : swapPerm i j k l j = l := by
    simp [swapPerm, Equiv.swap_apply_def, hij, hik, hil, hjk, hjl, hkl, hij.symm, hik.symm, hil.symm, hjk.symm, hjl.symm, hkl.symm]
  have hπk : swapPerm i j k l k = i := by
    simp [swapPerm, Equiv.swap_apply_def, hij, hik, hil, hjk, hjl, hkl, hij.symm, hik.symm, hil.symm, hjk.symm, hjl.symm, hkl.symm]
  have hπl : swapPerm i j k l l = j := by
    simp [swapPerm, Equiv.swap_apply_def, hij, hik, hil, hjk, hjl, hkl, hij.symm, hik.symm, hil.symm, hjk.symm, hjl.symm, hkl.symm]
  have hβi : swapBool i j k l (xor s u) (xor t v) i s = u := by
    simp [swapBool, hij, hik, hil, hjk, hjl, hkl, hij.symm, hik.symm, hil.symm, hjk.symm, hjl.symm, hkl.symm]
  have hβj : swapBool i j k l (xor s u) (xor t v) j t = v := by
    simp [swapBool, hij, hik, hil, hjk, hjl, hkl, hij.symm, hik.symm, hil.symm, hjk.symm, hjl.symm, hkl.symm]
  have hβk : swapBool i j k l (xor s u) (xor t v) k u = s := by
    simp only [swapBool, hij, hik, hil, hjk, hjl, hkl, hij.symm, hik.symm, hil.symm, hjk.symm, hjl.symm, hkl.symm, or_true, ite_true]
    cases s <;> cases u <;> rfl
  have hβl : swapBool i j k l (xor s u) (xor t v) l v = t := by
    simp only [swapBool, hij, hik, hil, hjk, hjl, hkl, hij.symm, hik.symm, hil.symm, hjk.symm, hjl.symm, hkl.symm, or_true, or_false, ite_true, ite_false]
    cases t <;> cases v <;> rfl
  rw [hπi, hπj, hβi, hβj] at h1
  rw [hπk, hπl, hβk, hβl] at h2
  have hg2 : ∀ x r, spinAction Q (g * g) (F.vec x r) =
      ((if x = i ∨ x = j ∨ x = k ∨ x = l then -1 else 1 : K)) • F.vec x r := fun x r => by
    rw [map_mul, LinearEquiv.mul_apply, hg, map_smul, hg, smul_smul]
    by_cases hxi : x = i
    · rw [hxi]
      simp [swapPerm, swapBool, swapSign, Equiv.swap_apply_def, hij, hik, hil, hjk, hjl, hkl, hij.symm, hik.symm, hil.symm, hjk.symm, hjl.symm, hkl.symm]
    · by_cases hxk : x = k
      · rw [hxk]
        simp [swapPerm, swapBool, swapSign, Equiv.swap_apply_def, hij, hik, hil, hjk, hjl, hkl, hij.symm, hik.symm, hil.symm, hjk.symm, hjl.symm, hkl.symm]
      · by_cases hxj : x = j
        · rw [hxj]
          simp [swapPerm, swapBool, swapSign, Equiv.swap_apply_def, hij, hik, hil, hjk, hjl, hkl, hij.symm, hik.symm, hil.symm, hjk.symm, hjl.symm, hkl.symm]
        · by_cases hxl : x = l
          · rw [hxl]
            simp [swapPerm, swapBool, swapSign, Equiv.swap_apply_def, hij, hik, hil, hjk, hjl, hkl, hij.symm, hik.symm, hil.symm, hjk.symm, hjl.symm, hkl.symm]
          · simp [swapPerm, swapBool, swapSign, Equiv.swap_apply_def, hxi, hxk, hxj, hxl]
  have hd := conj_rootElt_of_diag F _ _ hg2 hij
    (e := Pi.single i (boolSign s) + Pi.single j (boolSign t)) (u := s) (v := t) rfl 1
  have he : IsLong (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin n → ℤ) :=
    isLong_single_add_single hij s t
  have hεε : (ε₂ : K) * ε₁ = 1 := by
    have e : g * g * rootElt F (Pi.single i (boolSign s) + Pi.single j (boolSign t)) 1 *
          (g * g)⁻¹ =
        g * (g * rootElt F (Pi.single i (boolSign s) + Pi.single j (boolSign t)) 1 * g⁻¹) *
          g⁻¹ := by group
    rw [e, h1, h2] at hd
    have := rootElt_injective F he hd
    simp only [true_or, ite_true, or_true] at this
    linear_combination this
  have hε₁' : (ε₁ : K) * ε₁ = 1 := intCast_mul_self_of_sq hε₁
  have heq : (ε₂ : K) = ε₁ := by linear_combination (-(ε₂ : K)) * hε₁' + (ε₁ : K) * hεε
  refine ⟨ε₁, hε₁', h1, fun c => ?_⟩
  rw [h2, heq]

end Swap

theorem exists_sep_three (h2 : (2 : K) ≠ 0) {i j k l : Fin n} (hkl : k ≠ l)
    (s t u v : Bool) (hki : k ≠ i) (hkj : k ≠ j) {γ δ : Fin n → ℤ}
    (he : toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    (he' : toStdD n δ = Pi.single k (boolSign u) + Pi.single l (boolSign v))
    (hm : ∃ m : Fin n, m ≠ i ∧ m ≠ j ∧ m ≠ k ∧ m ≠ l) :
    ∃ p : TorIdx n K, chi p γ = 1 ∧ chi p δ ≠ 1 := by
  obtain ⟨m, hmi, hmj, hmk, hml⟩ := hm
  refine ⟨⟨k, m, hmk.symm, true, true, -1⟩, ?_, ?_⟩
  · apply chi_eq_one
    rw [he, TorIdx.vec, single_add_single_dotProduct]
    simp only
    rw [single_add_single_apply_of_ne' hki.symm hmi.symm, single_add_single_apply_of_ne' hkj.symm
      hmj.symm]
    ring
  · rw [chi, he', TorIdx.vec, single_add_single_dotProduct]
    simp only
    rw [single_add_single_apply_left hmk.symm, single_add_single_apply_of_ne' hkl.symm hml.symm,
      boolSign_true, mul_one, mul_zero, add_zero, neg_one_zpow_boolSign, Units.val_neg,
      Units.val_one]
    intro h
    apply h2
    linear_combination -h

theorem single_add_single_add_not {i j : Fin n} (s t : Bool) :
    (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin n → ℤ) +
        (Pi.single i (boolSign s) + Pi.single j (boolSign (!t))) =
      Pi.single i (2 * boolSign s) := by
  have h := boolSign_add_boolSign_not t
  funext x
  simp only [Pi.add_apply, Pi.single_apply]
  split_ifs <;> omega

theorem two_mul_boolSign (s : Bool) : 2 * boolSign s = 2 ∨ 2 * boolSign s = -2 := by
  cases s <;> simp [boolSign]

include hn in
theorem commute_X_of_swap [Finite K] (hK : Nat.card K = 3) {E : Type*} [Group E]
    {π : E →* spinGroup (quadPlus n K)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) {γ δ : Fin n → ℤ}
    (hγ : IsRootLift hn π γ (X hn π γ)) (hδ : IsRootLift hn π δ (X hn π δ))
    (hl : ¬IsLong (toStdD n γ + toStdD n δ)) (h0 : toStdD n γ + toStdD n δ ≠ 0)
    (hγl : IsLong (toStdD n γ)) (hδl : IsLong (toStdD n δ)) {g : spinGroup (quadPlus n K)} {a : K}
    (ha : a * a = 1)
    (h1 : ∀ c, g * rootElt (plusFrame n K hn) (toStdD n γ) c * g⁻¹ =
      rootElt (plusFrame n K hn) (toStdD n δ) (a * c))
    (h2 : ∀ c, g * rootElt (plusFrame n K hn) (toStdD n δ) c * g⁻¹ =
      rootElt (plusFrame n K hn) (toStdD n γ) (a * c)) (s t : K) :
    X hn π γ s * X hn π δ t = X hn π δ t * X hn π γ s :=
  WeylLift.commute_of_swap_lift hK hcen hπ hγ.1 hδ.1 hγ.2.1 hδ.2.1
    (fun s t => (commute_rootElt (plusFrame n K hn) hγl hδl h0 hl s t).eq) ha h1 h2 s t

include hn in
theorem spinPlus_three_exists_section_of_central [Finite K] (hK : Nat.card K = 3) (hn4 : 4 ≤ n)
    {E : Type*} [Group E] {π : E →* spinGroup (quadPlus n K)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : spinGroup (quadPlus n K) →* E, ∀ g, π (σ g) = g := by
  have h2 : (2 : K) ≠ 0 := FieldThree.two_ne_zero_of_card_three hK
  have hspec : ∀ γ ∈ roots (isFiniteType_cartanD n) ∅, IsRootLift hn π γ (X hn π γ) :=
    fun γ hγ => by
      obtain ⟨i, j, hij, s, t, he⟩ := isLong_of_mem hn hγ
      obtain ⟨m, hmi, hmj⟩ := exists_ne_and_ne hn i j
      refine X_isRootLift hn (exists_isRootLift hn hcen hπ hγ
        (p := ⟨i, m, hmi.symm, true, true, -1⟩) ?_)
      rw [chi, he, TorIdx.vec, single_add_single_dotProduct]
      simp only
      rw [single_add_single_apply_left hmi.symm, single_add_single_apply_of_ne' hij.symm hmj.symm,
        boolSign_true, mul_one, mul_zero, add_zero, neg_one_zpow_boolSign, Units.val_neg,
        Units.val_one]
      intro h
      apply h2
      linear_combination -h
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (plusDatum n K hn).isFiniteType
    (Dv := (plusDatum n K hn).divisible) rfl
  refine HalfSpaceLift.exists_section_of_lift' hcen rfl
    (SpinPlus.chevalleyExtras hn O SpinPlus.commC (SpinPlus.commutatorFormula hn O))
    (SpinPlus.presentationB hn) (X := X hn π)
    (tor := fun p : TorIdx n K => TorusLift.lift hπ (tor K hn p))
    (χ := fun p γ => chi p γ) (fun γ hγ => (hspec γ hγ).1)
    (fun γ hγ => (hspec γ hγ).2.1)
    (fun p γ hγ c => (hspec γ hγ).2.2 p _ (TorusLift.map_lift hπ _) c)
    fun γ hγ δ hδ hli => ?_
  obtain ⟨hne, hne'⟩ := toStdD_ne_of_linIndepPair hli
  change toStdD n δ ≠ toStdD n γ at hne
  change toStdD n δ ≠ -toStdD n γ at hne'
  have hγl := isLong_of_mem hn hγ
  have hδl := isLong_of_mem hn hδ
  obtain ⟨i, j, hij, s, t, he⟩ := hγl
  obtain ⟨k, l, hkl, u, v, he'⟩ := hδl
  by_cases hk : k ≠ i ∧ k ≠ j
  · by_cases hl : l ≠ i ∧ l ≠ j
    ·
      right
      obtain ⟨a, ha, h1, h2'⟩ := swapPair_swap (plusFrame n K hn) hij hk.1.symm hl.1.symm
        hk.2.symm hl.2.symm hkl s t u v
      rw [← he, ← he'] at h1 h2'
      have hnl : ¬IsLong (toStdD n γ + toStdD n δ) := by
        rw [he, he']
        exact not_isLong_add_disjoint hij hk.1.symm hl.1.symm hk.2.symm hl.2.symm hkl s t u v
      have hn0 : toStdD n γ + toStdD n δ ≠ 0 := by
        rw [he, he']
        intro h0
        have := congrFun h0 i
        simp [Pi.single_apply, hij, hk.1.symm, hl.1.symm, boolSign] at this
        cases s <;> simp at this
      have hcomm := commute_X_of_swap hn hK hπ hcen (hspec γ hγ) (hspec δ hδ) hnl hn0
        (isLong_of_mem hn hγ) (isLong_of_mem hn hδ) ha h1 h2'
      intro a' b
      rw [hcomm, mul_inv_cancel_right]
      exact Subgroup.mem_iSup_of_mem δ (Subgroup.mem_iSup_of_mem ⟨hδ, Or.inl rfl⟩
        (CFSG.LieType.Steinberg.xh_mem_chevRoot δ b))
    · have hl' : l = i ∨ l = j := by tauto
      obtain ⟨m, hmi, hmj, hmk⟩ := exists_ne_three hn4 i j k
      refine Or.inl (exists_sep_three h2 hkl s t u v hk.1 hk.2 he he'
        ⟨m, hmi, hmj, hmk, ?_⟩)
      rcases hl' with rfl | rfl
      · exact hmi
      · exact hmj
  by_cases hl : l ≠ i ∧ l ≠ j
  · have hk' : k = i ∨ k = j := by tauto
    obtain ⟨m, hmi, hmj, hml⟩ := exists_ne_three hn4 i j l
    refine Or.inl (exists_sep_three h2 hkl.symm s t v u hl.1 hl.2 he
      (by rw [he', add_comm]) ⟨m, hmi, hmj, hml, ?_⟩)
    rcases hk' with rfl | rfl
    · exact hmi
    · exact hmj
  right
  obtain ⟨u', v', he''⟩ : ∃ u' v' : Bool,
      toStdD n δ = Pi.single i (boolSign u') + Pi.single j (boolSign v') := by
    have hk' : k = i ∨ k = j := by tauto
    have hl' : l = i ∨ l = j := by tauto
    rcases hk' with rfl | rfl <;> rcases hl' with rfl | rfl
    · exact absurd rfl hkl
    · exact ⟨u, v, he'⟩
    · exact ⟨v, u, by rw [he', add_comm]⟩
    · exact absurd rfl hkl
  obtain ⟨m, hmi, hmj⟩ := exists_ne_and_ne hn i j
  have hcomm : ∀ a b, X hn π γ a * X hn π δ b = X hn π δ b * X hn π γ a := by
    have hcase : (u' = s ∧ v' = !t) ∨ (u' = !s ∧ v' = t) := by
      have hnot : ∀ b c : Bool, b ≠ c → b = !c := fun b c h => by
        cases b <;> cases c <;> simp_all
      by_cases hu : u' = s <;> by_cases hv : v' = t
      · exact absurd (by rw [he'', he, hu, hv]) hne
      · exact Or.inl ⟨hu, hnot _ _ hv⟩
      · exact Or.inr ⟨hnot _ _ hu, hv⟩
      · exfalso
        apply hne'
        rw [he'', he, neg_single_add_single, hnot _ _ hu, hnot _ _ hv, boolSign_not, boolSign_not]
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨a, ha, h1, h2'⟩ := negPair_swap (plusFrame n K hn) hij hmi hmj u' t
      rw [← he, ← he''] at h1 h2'
      refine commute_X_of_swap hn hK hπ hcen (hspec γ hγ) (hspec δ hδ) ?_ ?_
        (isLong_of_mem hn hγ) (isLong_of_mem hn hδ) ha h1 h2'
      · rw [he, he'', single_add_single_add_not]
        exact not_isLong_single_two (two_mul_boolSign u')
      · rw [he, he'', single_add_single_add_not]
        intro h0
        have := congrFun h0 i
        rw [Pi.single_eq_same, Pi.zero_apply] at this
        rcases two_mul_boolSign u' with h' | h' <;> omega
    · obtain ⟨a, ha, h1, h2'⟩ := negPair_swap (plusFrame n K hn) hij.symm hmj hmi v' s
      have ehe : toStdD n γ = Pi.single j (boolSign v') + Pi.single i (boolSign s) := by
        rw [he, add_comm]
      have ehe' : toStdD n δ = Pi.single j (boolSign v') + Pi.single i (boolSign (!s)) := by
        rw [he'', add_comm]
      rw [← ehe, ← ehe'] at h1 h2'
      refine commute_X_of_swap hn hK hπ hcen (hspec γ hγ) (hspec δ hδ) ?_ ?_
        (isLong_of_mem hn hγ) (isLong_of_mem hn hδ) ha h1 h2'
      · rw [ehe, ehe', single_add_single_add_not]
        exact not_isLong_single_two (two_mul_boolSign v')
      · rw [ehe, ehe', single_add_single_add_not]
        intro h0
        have := congrFun h0 j
        rw [Pi.single_eq_same, Pi.zero_apply] at this
        rcases two_mul_boolSign v' with h' | h' <;> omega
  intro a b
  rw [hcomm, mul_inv_cancel_right]
  exact Subgroup.mem_iSup_of_mem δ (Subgroup.mem_iSup_of_mem ⟨hδ, Or.inl rfl⟩
    (CFSG.LieType.Steinberg.xh_mem_chevRoot δ b))

theorem pomegaPlus_three_hopfMultiplier [Finite K] {p f : ℕ} (hn4 : 4 ≤ n)
    (hK : Nat.card K = p ^ f) (hK3 : Nat.card K = 3) :
    commutator (StatedProj (StatedOmega (StatedQuadPlus n K))) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (StatedProj (StatedOmega (StatedQuadPlus n K))) ≃*
        generic .POmegaPlus n p f) := by
  have hn : 3 ≤ n := by omega
  set q := spinToStatedProj (quadPlus n K) (range_spinMatrix_quadPlus hn)
  obtain ⟨hq, hkerZ, hker⟩ := spinToStatedProj_quadPlus (K := K) hn
  have : Group.IsPerfect (spinGroup (quadPlus n K)) := isPerfect_spinGroup_quadPlus hn
  have hperf : Group.IsPerfect (StatedProj (StatedOmega (StatedQuadPlus n K))) :=
    Group.IsPerfect.ofSurjective hq
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  have e1 : CFSG.RankThree.PerfectCover.hopfMultiplier
      (StatedProj (StatedOmega (StatedQuadPlus n K))) ≃* q.ker :=
    MulEquiv.ofBijective _ (SL2Closed.hopfMultiplierToKer_bijective q hq hker.le
      fun π hπ hcen => spinPlus_three_exists_section_of_central hn hK3 hn4 hπ hcen)
  obtain ⟨e3⟩ := nonempty_scalarSpin_mulEquiv_generic (K := K) hn hK
  exact ⟨(CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).trans
    (e1.trans ((MulEquiv.subgroupCongr hkerZ).trans e3))⟩

end CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed
