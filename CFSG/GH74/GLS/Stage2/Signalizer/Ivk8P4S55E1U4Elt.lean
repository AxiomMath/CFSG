module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1U4Alg
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1UnCore
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1UnGen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

abbrev FlagCond (r ε d : ℕ) (a b : HypIndex r ε) : Prop :=
  d ≤ fullPos b ∧ (fullPos b < 2 * r + ε - d → fullPos a < d) ∧ fullPos a < 2 * r + ε - d

theorem flagCond_single {r ε d : ℕ} {a b : HypIndex r ε} (c : K) (hab : FlagCond r ε d a b)
    (i j : HypIndex r ε) (hne : single a b c i j ≠ 0) : FlagCond r ε d i j := by
  have : i = a ∧ j = b := by
    by_contra hnot
    exact hne (single_apply_of_ne a b c i j fun hh => hnot ⟨hh.1.symm, hh.2.symm⟩)
  obtain ⟨rfl, rfl⟩ := this
  exact hab

theorem flagCond_sub {r ε d : ℕ} {a b a' b' : HypIndex r ε} (c c' : K) (hab : FlagCond r ε d a b)
    (hab' : FlagCond r ε d a' b') (i j : HypIndex r ε)
    (hne : (single a b c - single a' b' c') i j ≠ 0) : FlagCond r ε d i j := by
  rw [Matrix.sub_apply] at hne
  by_cases h1 : single a b c i j = 0
  · by_cases h2 : single a' b' c' i j = 0
    · exact absurd (by rw [h1, h2, sub_self]) hne
    · exact flagCond_single c' hab' i j h2
  · exact flagCond_single c hab i j h1

theorem mem_dom_inl_inr (c : K) (hc : c ∈ h.traceZero) (i : Fin 2) :
    c ∈ uRootDom h (Sum.inl i : Fin 2 ⊕ Fin 2) (Sum.inr i) := by
  rw [show (Sum.inr i : Fin 2 ⊕ Fin 2) = (Sum.inl i).swap from rfl, uRootDom_swap]
  exact hc

theorem mem_dom_top (c : K) {a b : Fin 2 ⊕ Fin 2} (hb : b ≠ a.swap) : c ∈ uRootDom h a b := by
  rw [uRootDom_of_ne h hb]
  trivial

@[expose] noncomputable def uEltA (c : K) (hc : c ∈ h.traceZero) : hypSU h 2 0 :=
  uRootElt h (a := Sum.inl 0) (b := Sum.inr 0) (by simp) ⟨c, mem_dom_inl_inr h c hc 0⟩

@[expose] noncomputable def uEltB (c : K) (hc : c ∈ h.traceZero) : hypSU h 2 0 :=
  uRootElt h (a := Sum.inl 1) (b := Sum.inr 1) (by simp) ⟨c, mem_dom_inl_inr h c hc 1⟩

@[expose] noncomputable def uEltC (t : K) : hypSU h 2 0 :=
  uRootElt h (a := Sum.inl 1) (b := Sum.inr 0) (by simp)
    ⟨t, mem_dom_top h t (by simp)⟩

@[expose] noncomputable def uEltD (t : K) : hypSU h 2 0 :=
  uRootElt h (a := Sum.inl 0) (b := Sum.inl 1) (by simp)
    ⟨t, mem_dom_top h t (by simp)⟩

theorem coe_uEltA (c : K) (hc : c ∈ h.traceZero) :
    (((uEltA h c hc : hypSU h 2 0) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
      = 1 + single ue1 uf1 c :=
  uRootMat_inl_inr_self h 0 c

theorem coe_uEltB (c : K) (hc : c ∈ h.traceZero) :
    (((uEltB h c hc : hypSU h 2 0) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)
      = 1 + single ue2 uf2 c :=
  uRootMat_inl_inr_self h 1 c

theorem coe_uEltC (t : K) :
    (((uEltC h t : hypSU h 2 0) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      1 + (single ue2 uf1 t - single ue1 uf2 (h.bar t)) := by
  rw [← add_sub_assoc]
  exact uRootMat_inl_inr h (by decide) t

theorem coe_uEltD (t : K) :
    (((uEltD h t : hypSU h 2 0) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      1 + (single ue1 ue2 t - single uf2 uf1 (h.bar t)) := by
  rw [← add_sub_assoc]
  exact uRootMat_inl_inl h t

theorem uEltA_mem {d : ℕ} (hd : d ≤ 2) (hd1 : 1 ≤ d) (c : K) (hc : c ∈ h.traceZero) :
    uEltA h c hc ∈ unRad h (by norm_num : (0 : ℕ) ≤ 1) hd :=
  mem_unRad_of_nil h _ hd _ _ (coe_uEltA h c hc) (flagCond_single c (by
    obtain rfl | rfl : d = 1 ∨ d = 2 := by omega
    all_goals decide))

theorem uEltB_mem (c : K) (hc : c ∈ h.traceZero) :
    uEltB h c hc ∈ unRad h (by norm_num : (0 : ℕ) ≤ 1) (by norm_num : (2 : ℕ) ≤ 2) :=
  mem_unRad_of_nil h _ _ _ _ (coe_uEltB h c hc) (flagCond_single c (by decide))

theorem uEltC_mem {d : ℕ} (hd : d ≤ 2) (hd1 : 1 ≤ d) (t : K) :
    uEltC h t ∈ unRad h (by norm_num : (0 : ℕ) ≤ 1) hd :=
  mem_unRad_of_nil h _ hd _ _ (coe_uEltC h t) (flagCond_sub t (h.bar t) (by
    obtain rfl | rfl : d = 1 ∨ d = 2 := by omega
    all_goals decide) (by
    obtain rfl | rfl : d = 1 ∨ d = 2 := by omega
    all_goals decide))

theorem uEltD_mem (t : K) :
    uEltD h t ∈ unRad h (by norm_num : (0 : ℕ) ≤ 1) (by norm_num : (1 : ℕ) ≤ 2) :=
  mem_unRad_of_nil h _ _ _ _ (coe_uEltD h t) (flagCond_sub t (h.bar t) (by decide) (by decide))


section Final

variable [Fact p.Prime] [CharP K p]

theorem two_ne_zero_of_ne_two (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  intro h0
  have h1 : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h0)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h1)

theorem scalar_eq_one_u4 (hp2 : p ≠ 2) :
    ∀ c : K, c ^ (2 * 2 + 0) = 1 → ((2 * 2 + 0 : ℕ) : K) * (1 - c) = 0 → c = 1 := by
  intro c _ hmul
  have h4 : ((2 * 2 + 0 : ℕ) : K) ≠ 0 := by
    have : ((2 * 2 + 0 : ℕ) : K) = 2 * 2 := by push_cast; ring
    rw [this]
    exact mul_ne_zero (two_ne_zero_of_ne_two hp2) (two_ne_zero_of_ne_two hp2)
  have := (mul_eq_zero.mp hmul).resolve_left h4
  linear_combination -this

theorem pow_eq_one_of_shape_u4 (x : semilinearSimilitudes h 2 0)
    (hσ : ∀ c, (x : SemiGL (HypIndex 2 0) K).right c = c) {a : K} (ha : a ≠ 0)
    (hM : (((x : SemiGL (HypIndex 2 0) K).left : Matrix (HypIndex 2 0) (HypIndex 2 0) K) - a • 1) *
      (((x : SemiGL (HypIndex 2 0) K).left : Matrix (HypIndex 2 0) (HypIndex 2 0) K) - a • 1) =
        0) :
    semilinearAutHom h (by norm_num : 1 ≤ 2) (by norm_num : 0 ≤ 1) x ^ p = 1 := by
  have : Nonempty (HypIndex 2 0) := ⟨ue1⟩
  refine semilinearAutHom_pow_eq_one h (by norm_num) (by norm_num) (by norm_num) x p
    (RingEquiv.ext hσ) (a ^ p) (pow_ne_zero p ha) ?_
  rw [Units.val_pow_eq_pow_val]
  exact pow_eq_smul_one_of_sq_zero _ _ a (by abel) hM

theorem radFixPow_u4_one (hp2 : p ≠ 2) :
    RadFixPow (r := 2) (ε := 0) (d := 1) h (by norm_num) (by norm_num) := by
  intro b hb
  obtain ⟨x, rfl⟩ := semilinearAutHom_surjective h (by norm_num : 1 ≤ 2) (by norm_num : 0 ≤ 1)
    hp2 (by norm_num : 3 ≤ 2 * 2 + 0) b
  obtain ⟨c0, hc0t, hc0⟩ := exists_mem_traceZero_ne_zero' h
  have hc0b : h.bar c0 = -c0 := eq_neg_of_add_eq_zero_left (mem_traceZero_add hc0t)
  have key : ∀ g : hypSU h 2 0, g ∈ unRad h (by norm_num : (0 : ℕ) ≤ 1)
      (by norm_num : (1 : ℕ) ≤ 2) →
      ∀ N : Matrix (HypIndex 2 0) (HypIndex 2 0) K,
        ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = 1 + N →
          ((x : SemiGL (HypIndex 2 0) K).left : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
              N.map (x : SemiGL (HypIndex 2 0) K).right =
            N * ((x : SemiGL (HypIndex 2 0) K).left : Matrix (HypIndex 2 0) (HypIndex 2 0) K) :=
    fun g hg N hgN => by
      have := comm_of_fix h (by norm_num) (by norm_num) (by norm_num) (scalar_eq_one_u4 hp2) x hg
        (hb g hg)
      rwa [hgN, add_sub_cancel_left] at this
  obtain ⟨hσ, a, ha, hM⟩ := shape_u4_one h (two_ne_zero_of_ne_two hp2) _
    (((x : SemiGL (HypIndex 2 0) K).left⁻¹ : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) (Units.inv_mul _)
    (x : SemiGL (HypIndex 2 0) K).right hc0 hc0b
    (key _ (uEltA_mem h (by norm_num) (by norm_num) c0 hc0t) _ (coe_uEltA h c0 hc0t))
    (fun t => key _ (uEltC_mem h (by norm_num) (by norm_num) t) _ (coe_uEltC h t))
    (fun t => key _ (uEltD_mem h t) _ (coe_uEltD h t))
  exact pow_eq_one_of_shape_u4 h x hσ ha hM

theorem radFixPow_u4_two (hp2 : p ≠ 2) :
    RadFixPow (r := 2) (ε := 0) (d := 2) h (by norm_num) (by norm_num) := by
  intro b hb
  obtain ⟨x, rfl⟩ := semilinearAutHom_surjective h (by norm_num : 1 ≤ 2) (by norm_num : 0 ≤ 1)
    hp2 (by norm_num : 3 ≤ 2 * 2 + 0) b
  obtain ⟨c0, hc0t, hc0⟩ := exists_mem_traceZero_ne_zero' h
  have key : ∀ g : hypSU h 2 0, g ∈ unRad h (by norm_num : (0 : ℕ) ≤ 1)
      (by norm_num : (2 : ℕ) ≤ 2) →
      ∀ N : Matrix (HypIndex 2 0) (HypIndex 2 0) K,
        ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = 1 + N →
          ((x : SemiGL (HypIndex 2 0) K).left : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
              N.map (x : SemiGL (HypIndex 2 0) K).right =
            N * ((x : SemiGL (HypIndex 2 0) K).left : Matrix (HypIndex 2 0) (HypIndex 2 0) K) :=
    fun g hg N hgN => by
      have := comm_of_fix h (by norm_num) (by norm_num) (by norm_num) (scalar_eq_one_u4 hp2) x hg
        (hb g hg)
      rwa [hgN, add_sub_cancel_left] at this
  obtain ⟨hσ, a, ha, hM⟩ := shape_u4_two h _
    (((x : SemiGL (HypIndex 2 0) K).left⁻¹ : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) (Units.inv_mul _)
    (x : SemiGL (HypIndex 2 0) K).right hc0
    (key _ (uEltA_mem h (by norm_num) (by norm_num) c0 hc0t) _ (coe_uEltA h c0 hc0t))
    (key _ (uEltB_mem h c0 hc0t) _ (coe_uEltB h c0 hc0t))
    (fun t => key _ (uEltC_mem h (by norm_num) (by norm_num) t) _ (coe_uEltC h t))
  exact pow_eq_one_of_shape_u4 h x hσ ha hM

end Final

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
