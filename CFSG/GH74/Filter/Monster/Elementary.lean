module

public import CFSG.GH74.Filter.Monster.Products
public import CFSG.LocalAnalysis.SectionRank.Monster
public import CFSG.GH74.Uniqueness.SU.KI1r3FamSp2

public section

namespace CFSG.GH74.Filter.Monster

open CFSG.SectionRank CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

def vI : Fin 6 → Fin 12 := ![0, 2, 4, 6, 8, 10]

theorem vI_indep : ∀ i j : Fin 6, i ≠ j → y443AdjB (vI i) (vI j) = false := by decide +kernel

theorem exists_private_neighbour : ∀ b : Fin 6 → Fin 2, b ≠ 0 →
    ∃ w : Fin 12, ∃ i : Fin 6, b i = 1 ∧ y443AdjB w (vI i) = true ∧
      ∀ j, j ≠ i → b j = 1 → y443AdjB w (vI j) = false := by decide +kernel

theorem commute_y443Gen_of_adjB_eq_false {i j : Fin 12} (h : y443AdjB i j = false) :
    Commute (y443Gen i) (y443Gen j) := by
  by_cases hij : i = j
  · subst hij
    exact Commute.refl _
  · refine y443Gen_commute i j hij fun h' => ?_
    have := (y443Adjacent_iff i j).1 h'
    rw [h] at this
    exact absurd this (by decide)

theorem y443Gen_mul_mem_commutator_of_adj {u w : Fin 12} (h : y443Graph.Adj u w) :
    y443Gen u * y443Gen w ∈ commutator Y443 := by
  have h3 := y443Gen_edge u w h
  have hc : y443Gen u * y443Gen w = ⁅y443Gen u, y443Gen w⁆⁻¹ := by
    rw [commutatorElement_eq_sq (y443Gen_sq u) (y443Gen_sq w)]
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← pow_succ]
    exact h3
  rw [hc]
  exact Subgroup.inv_mem _
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

theorem y443Gen_mul_mem_commutator {u w : Fin 12} (h : y443Graph.Reachable u w) :
    y443Gen u * y443Gen w ∈ commutator Y443 := by
  obtain ⟨p⟩ := h
  induction p with
  | nil =>
    rw [← sq, y443Gen_sq]
    exact Subgroup.one_mem _
  | @cons a b c hadj p ih =>
    have e : y443Gen a * y443Gen c = (y443Gen a * y443Gen b) * (y443Gen b * y443Gen c) := by
      rw [mul_assoc, ← mul_assoc (y443Gen b), ← sq, y443Gen_sq, one_mul]
    rw [e]
    exact Subgroup.mul_mem _ (y443Gen_mul_mem_commutator_of_adj hadj) ih

theorem prod_vI_ne_one (hG : commutator Y443 ≠ ⊥) (b : Fin 6 → Fin 2) (hb : b ≠ 0) :
    (List.ofFn fun j => y443Gen (vI j) ^ (b j : ℕ)).prod ≠ 1 := by
  obtain ⟨w, i, hbi, hadj, hnon⟩ := exists_private_neighbour b hb
  intro h1
  set c : Y443 := y443Gen w with hc
  set f : Fin 6 → Y443 := fun j => y443Gen (vI j) ^ (b j : ℕ) with hf
  have hconj : ∀ j, j ≠ i → f j = MulAut.conj c (f j) := by
    intro j hj
    rcases Fin.exists_fin_two.mp (⟨b j, rfl⟩ : ∃ x : Fin 2, b j = x) with h0 | h0
    · have : f j = 1 := by simp [hf, h0]
      rw [this, map_one]
    · have hfj : f j = y443Gen (vI j) := by simp [hf, h0]
      have hcomm : Commute c (y443Gen (vI j)) :=
        commute_y443Gen_of_adjB_eq_false (hnon j hj h0)
      rw [hfj, MulAut.conj_apply, hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hp : (List.ofFn f).prod = (List.ofFn fun j => MulAut.conj c (f j)).prod := by
    have := map_list_prod (MulAut.conj c) (List.ofFn f)
    rw [List.map_ofFn] at this
    rw [h1] at this ⊢
    rw [map_one] at this
    exact this
  have hi := eq_of_prod_ofFn_eq f (fun j => MulAut.conj c (f j)) i hconj hp
  have hfi : f i = y443Gen (vI i) := by
    have : (b i : ℕ) = 1 := by rw [hbi]; rfl
    simp [hf, this]
  rw [hfi, MulAut.conj_apply] at hi
  have hcomm : Commute c (y443Gen (vI i)) := mul_inv_eq_iff_eq_mul.1 hi.symm
  have hadj' : y443Graph.Adj w (vI i) := y443Graph_adj _ _ hadj
  have h2 : (c * y443Gen (vI i)) ^ 2 = 1 := by
    rw [hcomm.mul_pow, hc, y443Gen_sq, y443Gen_sq, one_mul]
  have h3 : (c * y443Gen (vI i)) ^ 3 = 1 := y443Gen_edge _ _ hadj'
  have h4 : c * y443Gen (vI i) = 1 := by
    have : (c * y443Gen (vI i)) ^ 3 = (c * y443Gen (vI i)) ^ 2 * (c * y443Gen (vI i)) :=
      pow_succ _ 2
    rw [h3, h2, one_mul] at this
    exact this.symm
  have h5 := orderOf_mul_eq_three_of_adj y443Graph y443Graph_connected y443Graph_cliqueFree
    y443Gen y443_closure y443Gen_sq y443Gen_edge y443Gen_commute hG hadj'
  rw [← hc, h4, orderOf_one] at h5
  exact absurd h5 (by norm_num)

theorem exists_E32_M (hG : commutator Y443 ≠ ⊥) :
    ∃ E : Subgroup M, CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 32 := by
  let z : Fin 6 → Y443 := fun j => y443Gen (vI j)
  have hz2 : ∀ j, z j ^ 2 = 1 := fun j => y443Gen_sq _
  have hzc : ∀ i j, Commute (z i) (z j) := fun i j => by
    by_cases hij : i = j
    · subst hij
      exact Commute.refl _
    · exact commute_y443Gen_of_adjB_eq_false (vI_indep i j hij)
  have hmem : ∀ j k, z j * z k ∈ commutator Y443 := fun j k =>
    y443Gen_mul_mem_commutator (y443Graph_connected.preconnected _ _)
  let g : Fin 5 → M := fun i => ⟨z i.succ * z 0, hmem _ _⟩
  have hsq : ∀ i, g i ^ 2 = 1 := fun i => by
    apply Subtype.ext
    show (z i.succ * z 0) ^ 2 = 1
    rw [(hzc _ _).mul_pow, hz2, hz2, one_mul]
  have hcomm : ∀ i j, g i * g j = g j * g i := fun i j => by
    apply Subtype.ext
    show (z i.succ * z 0) * (z j.succ * z 0) = (z j.succ * z 0) * (z i.succ * z 0)
    exact (((hzc _ _).mul_right (hzc _ _)).mul_left ((hzc _ _).mul_right (hzc _ _))).eq
  have hker : ∀ a : Fin 5 → Fin 2, a ≠ 0 →
      (List.ofFn fun i => g i ^ (a i : ℕ)).prod ≠ 1 := by
    intro a ha h1
    have h2 : (List.ofFn fun i : Fin 5 => (z i.succ * z 0) ^ (a i : ℕ)).prod = 1 := by
      have := congrArg (commutator Y443).subtype h1
      rw [map_list_prod, List.map_ofFn, map_one] at this
      simpa [Function.comp_def, g] using this
    rw [prod_ofFn_cons_parity z hz2 hzc a] at h2
    refine prod_vI_ne_one hG _ ?_ h2
    intro h0
    apply ha
    funext i
    have := congrFun h0 i.succ
    simpa using this
  obtain ⟨E, hE, hc⟩ :=
    CFSG.GH74.Uniqueness.SU.K.R3.exists_isElemAbelian_of_commuting_involutions g
      (fun i => by simpa [sq] using hsq i) hcomm hker
  refine ⟨E, hE, ?_⟩
  rw [hc]
  norm_num

theorem not_gen4_M (hG : commutator Y443 ≠ ⊥) : ¬ Gen4 M := by
  obtain ⟨E, hE, hc⟩ := exists_E32_M hG
  exact not_gen4_of_elemAbelian E hE (by rw [hc]; norm_num)

end CFSG.GH74.Filter.Monster
