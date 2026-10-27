module

public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.LieType.Universal.Spin.PlusCT.Basic

public section

namespace CFSG.LieType.Universal.Spin.Twisted

open CliffordAlgebra QuadraticMap CFSG.LieType.RootSystem CFSG.LieType.Steinberg
open CFSG.LieType.Universal.Spin.PlusCT
open scoped commutatorElement

variable (n : ℕ) {K : Type*} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

theorem minusDatum_ne_bot (γ : Fin (n - 1) → ℤ) (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) :
    minusRootGroup n hirr γ ≠ ⊥ := by
  intro hbot
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, t, hγ'⟩ | ⟨i, s, hγ'⟩
  · have h1 := longRoot_mem_minusRootGroup n hirr hij s t hγ' (1 : K)
    rw [hbot, Subgroup.mem_bot, ← map_one ((minusFrame n b c).longRoot hij s t)] at h1
    have h2 := congrArg Multiplicative.toAdd ((minusFrame n b c).longRoot_injective hij s t h1)
    simp at h2
  · have h1 := twShortRoot_mem_minusRootGroup n hirr i s hγ' planeOne
    rw [hbot, Subgroup.mem_bot, ← map_one (twShortRoot n hirr i s)] at h1
    have h2 := congrArg Multiplicative.toAdd (twShortRoot_injective n hirr i s h1)
    exact planeOne_ne_zero h2

theorem toStdB_apply_mem_of_mem_roots {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) (x : Fin (n - 1)) :
    toStdB (n - 1) γ x = 0 ∨ toStdB (n - 1) γ x = 1 ∨ toStdB (n - 1) γ x = -1 := by
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, t, hγ'⟩ | ⟨i, s, hγ'⟩
  · rw [hγ']
    exact single_add_single_apply_mem hij s t x
  · rw [hγ', Pi.single_apply]
    split_ifs
    · rcases boolSign_eq_one_or_eq_neg_one s with h | h <;> simp [h]
    · simp

theorem exists_toStdB_apply_ne_zero {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) :
    ∃ x, toStdB (n - 1) γ x = 1 ∨ toStdB (n - 1) γ x = -1 := by
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, t, hγ'⟩ | ⟨i, s, hγ'⟩
  · refine ⟨i, ?_⟩
    rw [hγ', single_add_single_apply_left hij]
    exact boolSign_eq_one_or_eq_neg_one s
  · refine ⟨i, ?_⟩
    rw [hγ', Pi.single_eq_same]
    exact boolSign_eq_one_or_eq_neg_one s

theorem add_self_notMem_roots {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) :
    γ + γ ∉ roots (isFiniteType_cartanB (n - 1)) ∅ := by
  intro h2
  obtain ⟨x, hx⟩ := exists_toStdB_apply_ne_zero n hγ
  have hmem := toStdB_apply_mem_of_mem_roots n h2 x
  rw [toStdB_add, Pi.add_apply] at hmem
  rcases hx with hx | hx <;> rw [hx] at hmem <;> omega

theorem minusDatum_two_smul_le (γ : Fin (n - 1) → ℤ)
    (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅)
    (h2 : 2 • γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) :
    minusRootGroup n hirr (2 • γ) ≤ minusRootGroup n hirr γ := by
  rw [two_nsmul] at h2
  exact absurd h2 (add_self_notMem_roots n hγ)

theorem openCone_comm (Φ : Set (Fin (n - 1) → ℤ)) (γ δ : Fin (n - 1) → ℤ) :
    openCone Φ γ δ = openCone Φ δ γ := by
  ext ε
  constructor <;> rintro ⟨hε, a, b, ha, hb, rfl⟩ <;> exact ⟨hε, b, a, hb, ha, add_comm _ _⟩

private theorem mem_openCone {γ δ ε : Fin (n - 1) → ℤ}
    (hε : ε ∈ roots (isFiniteType_cartanB (n - 1)) ∅)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ε = a • γ + b • δ) :
    ε ∈ openCone (roots (isFiniteType_cartanB (n - 1)) ∅) γ δ :=
  ⟨hε, a, b, ha, hb, h⟩

private theorem mem_iSup_openCone {γ δ ε : Fin (n - 1) → ℤ}
    (hε : ε ∈ openCone (roots (isFiniteType_cartanB (n - 1)) ∅) γ δ)
    {x : spinGroup (quadMinus n K b c)} (hx : x ∈ minusRootGroup n hirr ε) :
    x ∈ ⨆ ε ∈ openCone (roots (isFiniteType_cartanB (n - 1)) ∅) γ δ, minusRootGroup n hirr ε :=
  (le_iSup₂ (f := fun ε (_ : ε ∈ openCone (roots (isFiniteType_cartanB (n - 1)) ∅) γ δ) =>
    minusRootGroup n hirr ε) ε hε) hx

private theorem commutator_mem_of_commute {γ δ : Fin (n - 1) → ℤ}
    {x y : spinGroup (quadMinus n K b c)} (h : Commute x y) :
    ⁅x, y⁆ ∈
      ⨆ ε ∈ openCone (roots (isFiniteType_cartanB (n - 1)) ∅) γ δ, minusRootGroup n hirr ε := by
  rw [commutatorElement_eq_one_iff_commute.mpr h]
  exact one_mem _

private theorem ne_of_linIndepPair {γ δ : Fin (n - 1) → ℤ} (hind : LinIndepPair γ δ) :
    δ ≠ γ ∧ δ ≠ -γ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := hind 1 (-1) (by rw [h]; simp)
    simp at this
  · have := hind 1 1 (by rw [h]; simp)
    simp at this

private theorem commutator_mem_long_of_shared {γ δ : Fin (n - 1) → ℤ} (hind : LinIndepPair γ δ)
    {i j l : Fin (n - 1)} (hij : i ≠ j) (hjl : j ≠ l) (s t u v : Bool)
    (hγ : toStdB (n - 1) γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    (hδ : toStdB (n - 1) δ = Pi.single j (boolSign u) + Pi.single l (boolSign v)) (a d : K) :
    ⁅(minusFrame n b c).longRoot hij s t (.ofAdd a),
        (minusFrame n b c).longRoot hjl u v (.ofAdd d)⁆ ∈
      ⨆ ε ∈ openCone (roots (isFiniteType_cartanB (n - 1)) ∅) γ δ, minusRootGroup n hirr ε := by
  by_cases hsum : i ≠ l ∧ u = !t
  · obtain ⟨hil, hu⟩ := hsum
    rw [hu] at hδ ⊢
    rw [(minusFrame n b c).commutator_longRoot_longRoot hij hjl hil s t v a d]
    have h' : toStdB (n - 1) (γ + δ) = Pi.single i (boolSign s) + Pi.single l (boolSign v) := by
      rw [toStdB_add, hγ, hδ, boolSign_not, Pi.single_neg]
      abel
    exact mem_iSup_openCone n hirr
      (mem_openCone n (mem_roots_of_toStdB_eq_long n hil s v h') 1 1 one_pos one_pos (by simp))
      (longRoot_mem_minusRootGroup n hirr hil s v h' (a * d))
  · refine commutator_mem_of_commute n hirr ?_
    rcases Bool.eq_or_eq_not u t with hu | hu
    · rw [hu, (minusFrame n b c).longRoot_swap hjl]
      exact (minusFrame n b c).commute_longRoot_longRoot_right hij hjl.symm s t v a (-d)
    · have hil : i = l := by
        by_contra hil
        exact hsum ⟨hil, hu⟩
      cases hil
      rw [hu] at hδ ⊢
      rcases Bool.eq_or_eq_not v s with hv | hv
      · rw [hv, (minusFrame n b c).longRoot_swap hjl]
        exact (minusFrame n b c).commute_longRoot_longRoot_left hij hjl.symm s t (!t) a (-d)
      · exfalso
        rw [hv] at hδ
        refine (ne_of_linIndepPair n hind).2 (toStdB_injective (n - 1) ?_)
        rw [toStdB_neg, hγ, hδ, boolSign_not, boolSign_not, Pi.single_neg, Pi.single_neg]
        abel

private theorem commutator_mem_long_long {γ δ : Fin (n - 1) → ℤ} (hind : LinIndepPair γ δ)
    {i j k l : Fin (n - 1)} (hij : i ≠ j) (hkl : k ≠ l) (s t u v : Bool)
    (hγ : toStdB (n - 1) γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    (hδ : toStdB (n - 1) δ = Pi.single k (boolSign u) + Pi.single l (boolSign v)) (a d : K) :
    ⁅(minusFrame n b c).longRoot hij s t (.ofAdd a),
        (minusFrame n b c).longRoot hkl u v (.ofAdd d)⁆ ∈
      ⨆ ε ∈ openCone (roots (isFiniteType_cartanB (n - 1)) ∅) γ δ, minusRootGroup n hirr ε := by
  by_cases hjk : j = k
  · cases hjk
    exact commutator_mem_long_of_shared n hirr hind hij hkl s t u v hγ hδ a d
  by_cases hjl : j = l
  · cases hjl
    rw [(minusFrame n b c).longRoot_swap hkl]
    exact commutator_mem_long_of_shared n hirr hind hij hkl.symm s t v u hγ
      (by rw [hδ, add_comm]) a (-d)
  by_cases hik : i = k
  · cases hik
    rw [(minusFrame n b c).longRoot_swap hij]
    exact commutator_mem_long_of_shared n hirr hind hij.symm hkl t s u v
      (by rw [hγ, add_comm]) hδ (-a) d
  by_cases hil : i = l
  · cases hil
    rw [(minusFrame n b c).longRoot_swap hij, (minusFrame n b c).longRoot_swap hkl]
    exact commutator_mem_long_of_shared n hirr hind hij.symm hkl.symm t s v u
      (by rw [hγ, add_comm]) (by rw [hδ, add_comm]) (-a) (-d)
  exact commutator_mem_of_commute n hirr
    ((minusFrame n b c).commute_longRoot_longRoot_of_disjoint hij hkl hik hil hjk hjl s t u v a d)

private theorem commutator_mem_long_short_of_eq {γ δ : Fin (n - 1) → ℤ} {i j : Fin (n - 1)}
    (hij : i ≠ j) (s t u : Bool)
    (hγ : toStdB (n - 1) γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    (hδ : toStdB (n - 1) δ = Pi.single j (boolSign u)) (a : K) (q : Fin 2 → K) :
    ⁅(minusFrame n b c).longRoot hij s t (.ofAdd a), twShortRoot n hirr j u (.ofAdd q)⁆ ∈
      ⨆ ε ∈ openCone (roots (isFiniteType_cartanB (n - 1)) ∅) γ δ, minusRootGroup n hirr ε := by
  rcases Bool.eq_or_eq_not u t with hu | hu
  · rw [hu]
    exact commutator_mem_of_commute n hirr
      (commute_longRoot_twShortRoot_right n hirr hij s t a q)
  · rw [hu] at hδ ⊢
    rw [commutator_longRoot_twShortRoot n hirr hij s t a q]
    have h1 : toStdB (n - 1) (γ + δ) = Pi.single i (boolSign s) := by
      rw [toStdB_add, hγ, hδ, boolSign_not, Pi.single_neg]
      abel
    have h2 : toStdB (n - 1) (γ + (δ + δ)) =
        Pi.single i (boolSign s) + Pi.single j (boolSign (!t)) := by
      rw [toStdB_add, toStdB_add, hγ, hδ, boolSign_not, Pi.single_neg]
      abel
    refine mul_mem (mem_iSup_openCone n hirr
      (mem_openCone n (mem_roots_of_toStdB_eq_short n i s h1) 1 1 one_pos one_pos (by simp))
      (twShortRoot_mem_minusRootGroup n hirr i s h1 _))
      (mem_iSup_openCone n hirr
        (mem_openCone n (mem_roots_of_toStdB_eq_long n hij s (!t) h2) 1 2 one_pos two_pos
          (by rw [one_nsmul, two_nsmul]))
        (longRoot_mem_minusRootGroup n hirr hij s (!t) h2 _))

private theorem commutator_mem_long_short {γ δ : Fin (n - 1) → ℤ} {i j k : Fin (n - 1)}
    (hij : i ≠ j) (s t u : Bool)
    (hγ : toStdB (n - 1) γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    (hδ : toStdB (n - 1) δ = Pi.single k (boolSign u)) (a : K) (q : Fin 2 → K) :
    ⁅(minusFrame n b c).longRoot hij s t (.ofAdd a), twShortRoot n hirr k u (.ofAdd q)⁆ ∈
      ⨆ ε ∈ openCone (roots (isFiniteType_cartanB (n - 1)) ∅) γ δ, minusRootGroup n hirr ε := by
  by_cases hkj : k = j
  · cases hkj
    exact commutator_mem_long_short_of_eq n hirr hij s t u hγ hδ a q
  by_cases hki : k = i
  · cases hki
    rw [(minusFrame n b c).longRoot_swap hij]
    exact commutator_mem_long_short_of_eq n hirr hij.symm t s u (by rw [hγ, add_comm]) hδ (-a) q
  exact commutator_mem_of_commute n hirr
    (commute_longRoot_twShortRoot_of_ne n hirr hij hki hkj s t u a q)

private theorem commutator_mem_short_short {γ δ : Fin (n - 1) → ℤ} (hind : LinIndepPair γ δ)
    {i k : Fin (n - 1)} (s u : Bool) (hγ : toStdB (n - 1) γ = Pi.single i (boolSign s))
    (hδ : toStdB (n - 1) δ = Pi.single k (boolSign u)) (p q : Fin 2 → K) :
    ⁅twShortRoot n hirr i s (.ofAdd p), twShortRoot n hirr k u (.ofAdd q)⁆ ∈
      ⨆ ε ∈ openCone (roots (isFiniteType_cartanB (n - 1)) ∅) γ δ, minusRootGroup n hirr ε := by
  by_cases hik : i = k
  · exfalso
    cases hik
    rcases Bool.eq_or_eq_not u s with hu | hu
    · rw [hu] at hδ
      exact (ne_of_linIndepPair n hind).1 (toStdB_injective (n - 1) (hδ.trans hγ.symm))
    · rw [hu] at hδ
      refine (ne_of_linIndepPair n hind).2 (toStdB_injective (n - 1) ?_)
      rw [toStdB_neg, hγ, hδ, boolSign_not, Pi.single_neg]
  rw [commutator_twShortRoot_twShortRoot n hirr hik s u p q]
  have h' : toStdB (n - 1) (γ + δ) = Pi.single i (boolSign s) + Pi.single k (boolSign u) := by
    rw [toStdB_add, hγ, hδ]
  exact mem_iSup_openCone n hirr
    (mem_openCone n (mem_roots_of_toStdB_eq_long n hik s u h') 1 1 one_pos one_pos (by simp))
    (longRoot_mem_minusRootGroup n hirr hik s u h' _)

theorem minusDatum_commutator_mem (γ : Fin (n - 1) → ℤ)
    (hγ : γ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) (δ : Fin (n - 1) → ℤ)
    (hδ : δ ∈ roots (isFiniteType_cartanB (n - 1)) ∅) (hind : LinIndepPair γ δ)
    (x : spinGroup (quadMinus n K b c)) (hx : x ∈ minusRootGroup n hirr γ)
    (y : spinGroup (quadMinus n K b c)) (hy : y ∈ minusRootGroup n hirr δ) :
    ⁅x, y⁆ ∈
      ⨆ ε ∈ openCone (roots (isFiniteType_cartanB (n - 1)) ∅) γ δ, minusRootGroup n hirr ε := by
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, t, hγ'⟩ | ⟨i, s, hγ'⟩
  · obtain ⟨a, rfl⟩ := (mem_minusRootGroup_long_iff n hirr hij s t hγ').mp hx
    rcases exists_toStdB_eq_of_mem_roots n hδ with ⟨k, l, hkl, u, v, hδ'⟩ | ⟨k, u, hδ'⟩
    · obtain ⟨d, rfl⟩ := (mem_minusRootGroup_long_iff n hirr hkl u v hδ').mp hy
      exact commutator_mem_long_long n hirr hind hij hkl s t u v hγ' hδ' a d
    · obtain ⟨q, rfl⟩ := (mem_minusRootGroup_short_iff n hirr k u hδ').mp hy
      exact commutator_mem_long_short n hirr hij s t u hγ' hδ' a q
  · obtain ⟨p, rfl⟩ := (mem_minusRootGroup_short_iff n hirr i s hγ').mp hx
    rcases exists_toStdB_eq_of_mem_roots n hδ with ⟨k, l, hkl, u, v, hδ'⟩ | ⟨k, u, hδ'⟩
    · obtain ⟨d, rfl⟩ := (mem_minusRootGroup_long_iff n hirr hkl u v hδ').mp hy
      rw [← commutatorElement_inv, openCone_comm]
      exact inv_mem (commutator_mem_long_short n hirr hkl u v s hδ' hγ' d p)
    · obtain ⟨q, rfl⟩ := (mem_minusRootGroup_short_iff n hirr k u hδ').mp hy
      exact commutator_mem_short_short n hirr hind s u hγ' hδ' p q

end CFSG.LieType.Universal.Spin.Twisted
