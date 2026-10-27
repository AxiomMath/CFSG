module

public import CFSG.LieType.Universal.Spin.OddCT.Weyl

public section

namespace CFSG.LieType.Universal.Spin

open CFSG.LieType.RootSystem CFSG.LieType.Steinberg
open scoped commutatorElement

namespace OddCT

variable {n : ℕ} {K : Type} [Field K]

theorem toStdB_nsmul (a : ℕ) (v : Fin n → ℤ) : toStdB n (a • v) = a • toStdB n v := by
  induction a with
  | zero => rw [zero_smul, zero_smul, toStdB_zero]
  | succ a ih => rw [succ_nsmul, succ_nsmul, toStdB_add, ih]

theorem openCone_comm (Φ : Set (Fin n → ℤ)) (γ δ : Fin n → ℤ) :
    openCone Φ γ δ = openCone Φ δ γ := by
  ext ε
  constructor <;> rintro ⟨hε, a, b, ha, hb, rfl⟩ <;> exact ⟨hε, b, a, hb, ha, add_comm _ _⟩

theorem ofStdB_mem_openCone {γ δ e : Fin n → ℤ} (he : ofStdB n e ∈ roots (isFiniteType_cartanB n) ∅)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : e = a • toStdB n γ + b • toStdB n δ) :
    ofStdB n e ∈ openCone (roots (isFiniteType_cartanB n) ∅) γ δ := by
  refine ⟨he, a, b, ha, hb, toStdB_injective n ?_⟩
  rw [toStdB_ofStdB, toStdB_add, toStdB_nsmul, toStdB_nsmul, h]

theorem longRoot_mem_cone {γ δ : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j) (s t : Bool) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (h : Pi.single i (boolSign s) + Pi.single j (boolSign t) = a • toStdB n γ + b • toStdB n δ)
    (c : Multiplicative K) :
    (oddFrame n K).longRoot hij s t c ∈
      ⨆ ε ∈ openCone (roots (isFiniteType_cartanB n) ∅) γ δ, oddRootGroup n K ε := by
  refine (le_iSup₂ (f := fun ε (_ : ε ∈ openCone (roots (isFiniteType_cartanB n) ∅) γ δ) =>
    oddRootGroup n K ε) _ (ofStdB_mem_openCone (ofStdB_add_mem hij s t) ha hb h)) ?_
  exact longRoot_mem_oddRootGroup hij (toStdB_ofStdB n _) c

theorem shortRoot_mem_cone {γ δ : Fin n → ℤ} (i : Fin n) (s : Bool) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (h : Pi.single i (boolSign s) = a • toStdB n γ + b • toStdB n δ)
    (c : Multiplicative K) :
    (oddFrame n K).shortRoot i s c ∈
      ⨆ ε ∈ openCone (roots (isFiniteType_cartanB n) ∅) γ δ, oddRootGroup n K ε := by
  refine (le_iSup₂ (f := fun ε (_ : ε ∈ openCone (roots (isFiniteType_cartanB n) ∅) γ δ) =>
    oddRootGroup n K ε) _ (ofStdB_mem_openCone (ofStdB_single_mem i s) ha hb h)) ?_
  exact shortRoot_mem_oddRootGroup (toStdB_ofStdB n _) c

theorem commutatorElement_mem_of_commute {G : Type*} [Group G] {S : Subgroup G} {x y : G}
    (h : Commute x y) : ⁅x, y⁆ ∈ S := by
  rw [commutatorElement_eq_one_iff_commute.mpr h]
  exact one_mem S

theorem not_linIndepPair_of_toStdB_eq {γ δ : Fin n → ℤ} (h : toStdB n δ = toStdB n γ) :
    ¬ LinIndepPair γ δ := by
  intro hind
  have hδ : δ = γ := toStdB_injective n h
  have := hind 1 (-1) (by rw [hδ]; simp)
  simp at this

theorem not_linIndepPair_of_toStdB_eq_neg {γ δ : Fin n → ℤ} (h : toStdB n δ = -toStdB n γ) :
    ¬ LinIndepPair γ δ := by
  intro hind
  have hδ : δ = -γ := toStdB_injective n (by rw [h, toStdB_neg])
  have := hind 1 1 (by rw [hδ]; simp)
  simp at this

theorem commutator_longRoot_longRoot_mem_of_eq {γ δ : Fin n → ℤ} (hind : LinIndepPair γ δ)
    {i j l : Fin n} (hij : i ≠ j) (hjl : j ≠ l) (s t u v : Bool)
    (hγ : toStdB n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    (hδ : toStdB n δ = Pi.single j (boolSign u) + Pi.single l (boolSign v)) (a b : K) :
    ⁅(oddFrame n K).longRoot hij s t (.ofAdd a), (oddFrame n K).longRoot hjl u v (.ofAdd b)⁆ ∈
      ⨆ ε ∈ openCone (roots (isFiniteType_cartanB n) ∅) γ δ, oddRootGroup n K ε := by
  rcases Bool.eq_or_eq_not u t with rfl | rfl
  ·
    refine commutatorElement_mem_of_commute ?_
    rw [(oddFrame n K).longRoot_swap hjl _ _ b]
    exact (oddFrame n K).commute_longRoot_longRoot_right hij hjl.symm _ _ _ a (-b)
  · rcases eq_or_ne i l with rfl | hil
    · rcases Bool.eq_or_eq_not v s with rfl | rfl
      ·
        refine commutatorElement_mem_of_commute ?_
        rw [(oddFrame n K).longRoot_swap hjl _ _ b]
        exact (oddFrame n K).commute_longRoot_longRoot_left hij hjl.symm _ _ _ a (-b)
      ·
        exact absurd hind (not_linIndepPair_of_toStdB_eq_neg (by
          rw [hγ, hδ, boolSign_not, boolSign_not, Pi.single_neg, Pi.single_neg]
          abel))
    ·
      rw [(oddFrame n K).commutator_longRoot_longRoot hij hjl hil s t v a b]
      exact longRoot_mem_cone hil s v one_pos one_pos (by
        rw [hγ, hδ, boolSign_not, Pi.single_neg, one_smul, one_smul]
        abel) _

theorem commutator_longRoot_longRoot_mem {γ δ : Fin n → ℤ} (hind : LinIndepPair γ δ)
    {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) (s t u v : Bool)
    (hγ : toStdB n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    (hδ : toStdB n δ = Pi.single k (boolSign u) + Pi.single l (boolSign v)) (a b : K) :
    ⁅(oddFrame n K).longRoot hij s t (.ofAdd a), (oddFrame n K).longRoot hkl u v (.ofAdd b)⁆ ∈
      ⨆ ε ∈ openCone (roots (isFiniteType_cartanB n) ∅) γ δ, oddRootGroup n K ε := by
  rcases eq_or_ne j k with rfl | hjk
  · exact commutator_longRoot_longRoot_mem_of_eq hind hij hkl s t u v hγ hδ a b
  rcases eq_or_ne j l with rfl | hjl
  · rw [(oddFrame n K).longRoot_swap hkl u v b]
    exact commutator_longRoot_longRoot_mem_of_eq hind hij hkl.symm s t v u hγ
      (by rw [hδ, add_comm]) a (-b)
  rcases eq_or_ne i k with rfl | hik
  · rw [(oddFrame n K).longRoot_swap hij s t a]
    exact commutator_longRoot_longRoot_mem_of_eq hind hij.symm hkl t s u v
      (by rw [hγ, add_comm]) hδ (-a) b
  rcases eq_or_ne i l with rfl | hil
  · rw [(oddFrame n K).longRoot_swap hij s t a, (oddFrame n K).longRoot_swap hkl u v b]
    exact commutator_longRoot_longRoot_mem_of_eq hind hij.symm hkl.symm t s v u
      (by rw [hγ, add_comm]) (by rw [hδ, add_comm]) (-a) (-b)
  exact commutatorElement_mem_of_commute
    ((oddFrame n K).commute_longRoot_longRoot_of_disjoint hij hkl hik hil hjk hjl s t u v a b)

theorem commutator_longRoot_shortRoot_mem_of_eq {γ δ : Fin n → ℤ} {i j : Fin n} (hij : i ≠ j)
    (s t u : Bool) (hγ : toStdB n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    (hδ : toStdB n δ = Pi.single j (boolSign u)) (a b : K) :
    ⁅(oddFrame n K).longRoot hij s t (.ofAdd a), (oddFrame n K).shortRoot j u (.ofAdd b)⁆ ∈
      ⨆ ε ∈ openCone (roots (isFiniteType_cartanB n) ∅) γ δ, oddRootGroup n K ε := by
  rcases Bool.eq_or_eq_not u t with rfl | rfl
  · exact commutatorElement_mem_of_commute
      ((oddFrame n K).commute_longRoot_shortRoot_right hij _ _ a b)
  · rw [(oddFrame n K).commutator_longRoot_shortRoot hij s t a b]
    refine mul_mem (shortRoot_mem_cone i s one_pos one_pos ?_ _)
      (longRoot_mem_cone hij s (!t) one_pos two_pos ?_ _)
    · rw [hγ, hδ, boolSign_not, Pi.single_neg, one_smul, one_smul]
      abel
    · rw [hγ, hδ, boolSign_not, Pi.single_neg, one_smul, two_nsmul]
      abel

theorem commutator_longRoot_shortRoot_mem {γ δ : Fin n → ℤ} {i j k : Fin n} (hij : i ≠ j)
    (s t u : Bool) (hγ : toStdB n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    (hδ : toStdB n δ = Pi.single k (boolSign u)) (a b : K) :
    ⁅(oddFrame n K).longRoot hij s t (.ofAdd a), (oddFrame n K).shortRoot k u (.ofAdd b)⁆ ∈
      ⨆ ε ∈ openCone (roots (isFiniteType_cartanB n) ∅) γ δ, oddRootGroup n K ε := by
  rcases eq_or_ne k j with rfl | hkj
  · exact commutator_longRoot_shortRoot_mem_of_eq hij s t u hγ hδ a b
  rcases eq_or_ne k i with rfl | hki
  · rw [(oddFrame n K).longRoot_swap hij s t a]
    exact commutator_longRoot_shortRoot_mem_of_eq hij.symm t s u (by rw [hγ, add_comm]) hδ (-a) b
  exact commutatorElement_mem_of_commute
    ((oddFrame n K).commute_longRoot_shortRoot_of_ne hij hki hkj s t u a b)

theorem commutator_shortRoot_shortRoot_mem {γ δ : Fin n → ℤ} (hind : LinIndepPair γ δ)
    {i k : Fin n} (s u : Bool) (hγ : toStdB n γ = Pi.single i (boolSign s))
    (hδ : toStdB n δ = Pi.single k (boolSign u)) (a b : K) :
    ⁅(oddFrame n K).shortRoot i s (.ofAdd a), (oddFrame n K).shortRoot k u (.ofAdd b)⁆ ∈
      ⨆ ε ∈ openCone (roots (isFiniteType_cartanB n) ∅) γ δ, oddRootGroup n K ε := by
  rcases eq_or_ne i k with rfl | hik
  · exfalso
    rcases Bool.eq_or_eq_not u s with rfl | rfl
    · exact not_linIndepPair_of_toStdB_eq (by rw [hγ, hδ]) hind
    · exact not_linIndepPair_of_toStdB_eq_neg (by rw [hγ, hδ, boolSign_not, Pi.single_neg]) hind
  · rw [(oddFrame n K).commutator_shortRoot_shortRoot hik s u a b]
    exact longRoot_mem_cone hik s u one_pos one_pos (by rw [hγ, hδ, one_smul, one_smul]) _

theorem commutator_mem {γ δ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanB n) ∅)
    (hδ : δ ∈ roots (isFiniteType_cartanB n) ∅) (hind : LinIndepPair γ δ)
    {x y : spinGroup (quadOdd n K)} (hx : x ∈ oddRootGroup n K γ) (hy : y ∈ oddRootGroup n K δ) :
    ⁅x, y⁆ ∈ ⨆ ε ∈ openCone (roots (isFiniteType_cartanB n) ∅) γ δ, oddRootGroup n K ε := by
  rcases exists_oddRootGroup_eq (K := K) hγ with
    ⟨i, j, hij, s, t, hγs, hγX⟩ | ⟨i, s, hγs, hγX⟩ <;>
  rcases exists_oddRootGroup_eq (K := K) hδ with
    ⟨k, l, hkl, u, v, hδs, hδX⟩ | ⟨k, u, hδs, hδX⟩ <;>
  rw [hγX] at hx <;> rw [hδX] at hy <;>
  obtain ⟨a, rfl⟩ := hx <;> obtain ⟨b, rfl⟩ := hy <;>
  obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective a <;>
  obtain ⟨b, rfl⟩ := Multiplicative.ofAdd.surjective b
  · exact commutator_longRoot_longRoot_mem hind hij hkl s t u v hγs hδs a b
  · exact commutator_longRoot_shortRoot_mem hij s t u hγs hδs a b
  · rw [← commutatorElement_inv, openCone_comm]
    exact inv_mem (commutator_longRoot_shortRoot_mem hkl u v s hδs hγs b a)
  · exact commutator_shortRoot_shortRoot_mem hind s u hγs hδs a b

end OddCT

open OddCT

variable (n : ℕ) (K : Type) [Field K]

theorem oddDatum_commutator_mem : ∀ γ ∈ (oddDatum n K).roots, ∀ δ ∈ (oddDatum n K).roots,
    LinIndepPair γ δ → ∀ x ∈ (oddDatum n K).rootGroup γ, ∀ y ∈ (oddDatum n K).rootGroup δ,
      ⁅x, y⁆ ∈ ⨆ ε ∈ openCone (oddDatum n K).roots γ δ, (oddDatum n K).rootGroup ε := by
  show ∀ γ ∈ roots (isFiniteType_cartanB n) ∅, ∀ δ ∈ roots (isFiniteType_cartanB n) ∅,
    LinIndepPair γ δ → ∀ x ∈ oddRootGroup n K γ, ∀ y ∈ oddRootGroup n K δ,
      ⁅x, y⁆ ∈ ⨆ ε ∈ openCone (roots (isFiniteType_cartanB n) ∅) γ δ, oddRootGroup n K ε
  intro γ hγ δ hδ hind x hx y hy
  exact commutator_mem hγ hδ hind hx hy

end CFSG.LieType.Universal.Spin
