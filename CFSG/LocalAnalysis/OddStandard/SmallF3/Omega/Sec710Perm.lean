module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

@[expose] def wt4 (i : Fin 5) : Fin 5 → ZMod 2 :=
  fun j => if j = i then 0 else 1

theorem isEvenVec_wt4 (i : Fin 5) : IsEvenVec (wt4 i) := by
  revert i
  unfold IsEvenVec
  decide +kernel

theorem vecWeight_wt4 (i : Fin 5) : vecWeight (wt4 i) = 4 := by
  revert i
  decide +kernel

theorem permVec_wt4 (σ : Equiv.Perm (Fin 5)) (i : Fin 5) : permVec σ (wt4 i) = wt4 (σ i) := by
  funext j
  simp [permVec, wt4, Equiv.symm_apply_eq]

theorem wt4_injective : Function.Injective wt4 := by
  intro i j hij
  by_contra hne
  have h1 := congrFun hij i
  have hi : wt4 i i = 0 := by simp [wt4]
  have hj : wt4 j i = 1 := by simp [wt4, hne]
  rw [hi, hj] at h1
  exact zero_ne_one h1

theorem eq_wt4_of_weight_four {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) (h4 : vecWeight v = 4) :
    ∃ i, v = wt4 i := by
  revert v
  unfold IsEvenVec
  decide +kernel

theorem sec710_weight_cases {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    v = 0 ∨ vecWeight v = 2 ∨ vecWeight v = 4 := by
  revert v
  unfold IsEvenVec
  decide +kernel

private theorem exists_wt4_add_of_weight_two {v : Fin 5 → ZMod 2} (hv : IsEvenVec v)
    (h2 : vecWeight v = 2) : ∃ i j : Fin 5, v = wt4 i + wt4 j := by
  revert v
  unfold IsEvenVec
  decide +kernel

theorem sec710_evenVec_mem_closure_wt4 {w : Fin 5 → ZMod 2} (hw : IsEvenVec w) :
    w ∈ AddSubgroup.closure (Set.range wt4) := by
  let W : AddSubgroup (Fin 5 → ZMod 2) := AddSubgroup.closure (Set.range wt4)
  change w ∈ W
  have hgen : ∀ i : Fin 5, wt4 i ∈ W := fun i => AddSubgroup.subset_closure ⟨i, rfl⟩
  rcases sec710_weight_cases hw with rfl | h2 | h4
  · exact W.zero_mem
  · obtain ⟨i, j, rfl⟩ := exists_wt4_add_of_weight_two hw h2
    exact W.add_mem (hgen i) (hgen j)
  · obtain ⟨i, rfl⟩ := eq_wt4_of_weight_four hw h4
    exact hgen i

private theorem pow_eight_eq_one_of_mem {T : Subgroup (Equiv.Perm (Fin 5))}
    (h2 : IsPGroup 2 T) {u : Equiv.Perm (Fin 5)} (hu : u ∈ T) : u ^ 8 = 1 := by
  obtain ⟨k, hk⟩ := (isPGroup_iff_orderOf_dvd_pow.mp h2) (⟨u, hu⟩ : T)
  simp only [Subgroup.orderOf_mk] at hk
  have hord120 : orderOf u ∣ 120 := by
    have h := orderOf_dvd_natCard (G := Equiv.Perm (Fin 5)) u
    rw [Nat.card_perm] at h
    norm_num at h
    exact h
  have hcop : Nat.Coprime (orderOf u) 15 :=
    Nat.Coprime.coprime_dvd_left hk (Nat.Coprime.pow_left k (by norm_num))
  have h8 : orderOf u ∣ 8 := by
    have hmul : orderOf u ∣ 15 * 2 ^ 3 := by
      rw [show (15 : ℕ) * 2 ^ 3 = 120 by norm_num]
      exact hord120
    exact hcop.dvd_of_dvd_mul_left hmul
  exact orderOf_dvd_iff_pow_eq_one.mp h8

theorem sec710_perm5_normal_two_eq_bot (P : Subgroup (Equiv.Perm (Fin 5))) [P.Normal]
    (hP : IsPGroup 2 P) : P = ⊥ := by
  rw [eq_bot_iff]
  intro t ht
  by_contra hne
  have hcheck : ∀ t : Equiv.Perm (Fin 5), t ≠ 1 →
      t ^ 8 ≠ 1 ∨ ∃ g : Equiv.Perm (Fin 5), (g * t * g⁻¹ * t⁻¹) ^ 8 ≠ 1 := by
    decide +kernel
  rcases hcheck t hne with h | ⟨g, hg⟩
  · exact h (pow_eight_eq_one_of_mem hP ht)
  · have hmem : g * t * g⁻¹ * t⁻¹ ∈ P :=
      P.mul_mem ((inferInstance : P.Normal).conj_mem t ht g) (P.inv_mem ht)
    exact hg (pow_eight_eq_one_of_mem hP hmem)

@[expose] def toE16 (v : Fin 5 → ZMod 2) : E16 :=
  fun i => Multiplicative.ofAdd (v i.castSucc)

theorem toE16_add (v w : Fin 5 → ZMod 2) : toE16 (v + w) = toE16 v * toE16 w := by
  funext i
  simp only [toE16, Pi.add_apply, Pi.mul_apply]
  rfl

theorem toE16_injOn_even {v w : Fin 5 → ZMod 2} (hv : IsEvenVec v) (hw : IsEvenVec w)
    (h : toE16 v = toE16 w) : v = w := by
  have hcoord : ∀ i : Fin 4, v i.castSucc = w i.castSucc :=
    fun i => Multiplicative.ofAdd.injective (by simpa only [toE16] using congrFun h i)
  funext j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · exact hcoord i
  · have ha : (∑ i : Fin 4, v i.castSucc) = ∑ i : Fin 4, w i.castSucc :=
      Finset.sum_congr rfl fun i _ => hcoord i
    have hv' : (∑ i : Fin 4, v i.castSucc) + v (Fin.last 4) = 0 := by
      unfold IsEvenVec at hv
      rw [Fin.sum_univ_castSucc] at hv
      exact hv
    have hw' : (∑ i : Fin 4, w i.castSucc) + w (Fin.last 4) = 0 := by
      unfold IsEvenVec at hw
      rw [Fin.sum_univ_castSucc] at hw
      exact hw
    have hgoal : (∑ i : Fin 4, v i.castSucc) + v (Fin.last 4) =
        (∑ i : Fin 4, v i.castSucc) + w (Fin.last 4) := by
      rw [hv', ← hw', ha]
    exact add_left_cancel hgoal

theorem exists_even_toE16 (u : E16) : ∃ v : Fin 5 → ZMod 2, IsEvenVec v ∧ toE16 v = u := by
  let v : Fin 5 → ZMod 2 :=
    fun j => if h : j.val < 4 then (u ⟨j.val, h⟩).toAdd else ∑ i : Fin 4, (u i).toAdd
  refine ⟨v, ?_, ?_⟩
  · unfold IsEvenVec
    have hcast : (∑ i : Fin 4, v i.castSucc) = ∑ i : Fin 4, (u i).toAdd := by
      apply Finset.sum_congr rfl
      intro i _
      simp [v, i.isLt]
    have hlast : v (Fin.last 4) = ∑ i : Fin 4, (u i).toAdd := by
      simp [v]
    rw [Fin.sum_univ_castSucc, hcast, hlast]
    exact CharTwo.add_self_eq_zero _
  · funext i
    simp only [toE16]
    simp [v, i.isLt]

end CFSG.OddStandard.SmallF3.Omega