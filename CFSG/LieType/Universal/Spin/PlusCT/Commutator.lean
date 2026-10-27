module

public import CFSG.LieType.Universal.Spin.PlusCT.Basic

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap CFSG.LieType.RootSystem CFSG.LieType.Steinberg
open CFSG.LieType.Universal.Spin.PlusCT
open scoped commutatorElement

variable {n : ℕ} {K : Type} [Field K]

theorem plusDatum_ne_bot (hn : 3 ≤ n) :
    ∀ γ ∈ (plusDatum n K hn).roots, (plusDatum n K hn).rootGroup γ ≠ ⊥ := by
  intro γ hγ hbot
  obtain ⟨i, j, hij, s, t, hγ', -⟩ := exists_plusRootGroup_eq (K := K) hn hγ
  have hbot' : plusRootGroup n K hn γ = ⊥ := hbot
  have h1 := longRoot_mem_plusRootGroup (K := K) hn hij s t hγ' 1
  rw [hbot', Subgroup.mem_bot, ← map_one ((plusFrame n K hn).longRoot hij s t)] at h1
  have h2 := congrArg Multiplicative.toAdd ((plusFrame n K hn).longRoot_injective hij s t h1)
  simp at h2

theorem PlusCT.add_self_notMem_rootsD (hn : n ≠ 1) {γ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanD n) ∅) :
    γ + γ ∉ roots (isFiniteType_cartanD n) ∅ := by
  intro h2
  obtain ⟨i, j, hij, s, t, hγ'⟩ := exists_toStdD_eq_of_mem_rootsD hn hγ
  obtain ⟨p, q, hpq, s', t', h2'⟩ := exists_toStdD_eq_of_mem_rootsD hn h2
  have hval := single_add_single_apply_mem hpq s' t' i
  rw [← h2', toStdD_add, hγ', Pi.add_apply, single_add_single_apply_left hij] at hval
  cases s <;> simp at hval

theorem plusDatum_two_smul_le (hn : 3 ≤ n) :
    ∀ γ ∈ (plusDatum n K hn).roots, 2 • γ ∈ (plusDatum n K hn).roots →
      (plusDatum n K hn).rootGroup (2 • γ) ≤ (plusDatum n K hn).rootGroup γ := by
  intro γ hγ h2
  rw [two_nsmul] at h2
  exact absurd h2 (add_self_notMem_rootsD (by omega) hγ)

private theorem add_mem_openCone {γ δ : Fin n → ℤ} {i l : Fin n} (hil : i ≠ l) (s v : Bool)
    (h : toStdD n (γ + δ) = Pi.single i (boolSign s) + Pi.single l (boolSign v)) :
    γ + δ ∈ openCone (roots (isFiniteType_cartanD n) ∅) γ δ :=
  ⟨mem_rootsD_of_toStdD_eq hil s v h, 1, 1, one_pos, one_pos, by simp⟩

private theorem commutator_mem_of_shared (hn : 3 ≤ n) {γ δ : Fin n → ℤ}
    (hind : LinIndepPair γ δ) {i j l : Fin n} (hij : i ≠ j) (hjl : j ≠ l) (s t u v : Bool)
    (hγ : toStdD n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    (hδ : toStdD n δ = Pi.single j (boolSign u) + Pi.single l (boolSign v)) (a b : K) :
    ⁅(plusFrame n K hn).longRoot hij s t (.ofAdd a),
        (plusFrame n K hn).longRoot hjl u v (.ofAdd b)⁆ ∈
      ⨆ ε ∈ openCone (roots (isFiniteType_cartanD n) ∅) γ δ, plusRootGroup n K hn ε := by
  by_cases hsum : i ≠ l ∧ u = !t
  ·
    obtain ⟨hil, hu⟩ := hsum
    rw [hu] at hδ ⊢
    rw [(plusFrame n K hn).commutator_longRoot_longRoot hij hjl hil s t v a b]
    have h' : toStdD n (γ + δ) = Pi.single i (boolSign s) + Pi.single l (boolSign v) := by
      rw [toStdD_add, hγ, hδ, boolSign_not, Pi.single_neg]
      abel
    exact (le_iSup₂ (f := fun ε (_ : ε ∈ openCone (roots (isFiniteType_cartanD n) ∅) γ δ) =>
      plusRootGroup n K hn ε) (γ + δ) (add_mem_openCone hil s v h'))
      (longRoot_mem_plusRootGroup hn hil s v h' (a * b))
  · rw [commutatorElement_eq_one_iff_commute.mpr ?_]
    · exact one_mem _
    rcases Bool.eq_or_eq_not u t with hu | hu
    ·
      rw [hu, (plusFrame n K hn).longRoot_swap hjl]
      exact (plusFrame n K hn).commute_longRoot_longRoot_right hij hjl.symm s t v a (-b)
    ·
      have hil : i = l := by
        by_contra hil
        exact hsum ⟨hil, hu⟩
      cases hil
      rw [hu] at hδ ⊢
      rcases Bool.eq_or_eq_not v s with hv | hv
      · rw [hv, (plusFrame n K hn).longRoot_swap hjl]
        exact (plusFrame n K hn).commute_longRoot_longRoot_left hij hjl.symm s t (!t) a (-b)
      · exfalso
        rw [hv] at hδ
        have hδγ : δ = -γ := toStdD_injective n (by
          rw [toStdD_neg, hγ, hδ, boolSign_not, boolSign_not, Pi.single_neg, Pi.single_neg]
          abel)
        have h1 := hind 1 1 (by rw [hδγ]; simp)
        simp at h1

theorem plusDatum_commutator_mem (hn : 3 ≤ n) :
    ∀ γ ∈ (plusDatum n K hn).roots, ∀ δ ∈ (plusDatum n K hn).roots, LinIndepPair γ δ →
      ∀ x ∈ (plusDatum n K hn).rootGroup γ, ∀ y ∈ (plusDatum n K hn).rootGroup δ,
        ⁅x, y⁆ ∈ ⨆ ε ∈ openCone (plusDatum n K hn).roots γ δ, (plusDatum n K hn).rootGroup ε := by
  intro γ hγ δ hδ hind x hx y hy
  obtain ⟨i, j, hij, s, t, hγ', -⟩ := exists_plusRootGroup_eq (K := K) hn hγ
  obtain ⟨k, l, hkl, u, v, hδ', -⟩ := exists_plusRootGroup_eq (K := K) hn hδ
  obtain ⟨a, rfl⟩ := (mem_plusRootGroup_iff hn hij s t hγ').mp hx
  obtain ⟨b, rfl⟩ := (mem_plusRootGroup_iff hn hkl u v hδ').mp hy
  change _ ∈ ⨆ ε ∈ openCone (roots (isFiniteType_cartanD n) ∅) γ δ, plusRootGroup n K hn ε
  by_cases hjk : j = k
  · cases hjk
    exact commutator_mem_of_shared hn hind hij hkl s t u v hγ' hδ' a b
  by_cases hjl : j = l
  · cases hjl
    rw [(plusFrame n K hn).longRoot_swap hkl]
    exact commutator_mem_of_shared hn hind hij hkl.symm s t v u hγ' (by rw [hδ', add_comm]) a (-b)
  by_cases hik : i = k
  · cases hik
    rw [(plusFrame n K hn).longRoot_swap hij]
    exact commutator_mem_of_shared hn hind hij.symm hkl t s u v (by rw [hγ', add_comm]) hδ' (-a) b
  by_cases hil : i = l
  · cases hil
    rw [(plusFrame n K hn).longRoot_swap hij, (plusFrame n K hn).longRoot_swap hkl]
    exact commutator_mem_of_shared hn hind hij.symm hkl.symm t s v u (by rw [hγ', add_comm])
      (by rw [hδ', add_comm]) (-a) (-b)
  rw [commutatorElement_eq_one_iff_commute.mpr
    ((plusFrame n K hn).commute_longRoot_longRoot_of_disjoint hij hkl hik hil hjk hjl s t u v a b)]
  exact one_mem _

end CFSG.LieType.Universal.Spin
