module

public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.KS.SylowCount

open Finset

variable {G : Type*} [Group G]

theorem conj_pow_of_orderOf [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hdvd : ¬p ^ 2 ∣ Nat.card G) {z₀ z : G} (h₀ : orderOf z₀ = p) (h : orderOf z = p) :
    ∃ i < p, IsConj (z₀ ^ i) z := by
  have hpos : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hf : (Nat.card G).factorization p = 1 := by
    have h1 : p ^ 1 ∣ Nat.card G := by
      rw [pow_one, ← h₀]
      exact orderOf_dvd_natCard z₀
    have hle := (hp.out.pow_dvd_iff_le_factorization hpos).1 h1
    have hlt : ¬2 ≤ (Nat.card G).factorization p := fun h2 =>
      hdvd ((hp.out.pow_dvd_iff_le_factorization hpos).2 h2)
    omega
  have hc : ∀ x : G, orderOf x = p →
      Nat.card (Subgroup.zpowers x) = p ^ (Nat.card G).factorization p := fun x hx => by
    rw [Nat.card_zpowers, hx, hf, pow_one]
  let P : Sylow p G := Sylow.ofCard (Subgroup.zpowers z₀) (hc z₀ h₀)
  let Q : Sylow p G := Sylow.ofCard (Subgroup.zpowers z) (hc z h)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hz : z ∈ ((g • P : Sylow p G) : Subgroup G) := by
    rw [hg]
    exact Subgroup.mem_zpowers z
  rw [Sylow.coe_subgroup_smul] at hz
  obtain ⟨w, hw, hwz⟩ := (Subgroup.mem_smul_pointwise_iff_exists z (MulAut.conj g) _).1 hz
  obtain ⟨m, rfl⟩ := mem_powers_iff_mem_zpowers.2 hw
  refine ⟨m % p, Nat.mod_lt _ hp.out.pos, ?_⟩
  rw [← h₀, pow_mod_orderOf]
  exact isConj_iff.2 ⟨g, by rw [← hwz]; rfl⟩

open scoped Classical in
theorem card_conj_mul_card_comm [Fintype G] (j : G) :
    #(univ.filter (IsConj j)) * #(univ.filter fun g => g * j = j * g) = Fintype.card G := by
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) j
  rw [ConjAct.card] at h
  rw [← h]
  congr 1
  · rw [← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun x => by
      simp only [mem_filter, mem_univ, true_and]
      rw [ConjAct.mem_orbit_conjAct]
      exact isConj_comm)
  · rw [← Fintype.card_coe]
    refine Fintype.card_congr (ConjAct.toConjAct.toEquiv.subtypeEquiv fun x => ?_)
    simp only [mem_filter, mem_univ, true_and, MulAction.mem_stabilizer_iff,
      MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ConjAct.toConjAct_smul]
    exact (mul_inv_eq_iff_eq_mul).symm

variable [Fintype G]

open scoped Classical

variable (a : G) (Q : G → G → Prop)
  (hQ : ∀ g x y, Q (g * x * g⁻¹) (g * y * g⁻¹) ↔ Q x y)
  (Zr : G → Prop) (hZr : ∀ g z, Zr (g * z * g⁻¹) ↔ Zr z)

include hQ hZr in
theorem card_partners_conj {x : G} (hx : IsConj a x) :
    #(univ.filter fun y => Zr (x * y) ∧ Q x y) = #(univ.filter fun y => Zr (a * y) ∧ Q a y) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hx
  refine card_nbij' (fun y => c⁻¹ * y * c) (fun y => c * y * c⁻¹) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hy ⊢
    have e1 : c * a * c⁻¹ * y = c * (a * (c⁻¹ * y * c)) * c⁻¹ := by group
    have e2 : y = c * (c⁻¹ * y * c) * c⁻¹ := by group
    obtain ⟨h1, h2⟩ := hy
    rw [e1, hZr] at h1
    rw [e2, hQ] at h2
    exact ⟨h1, h2⟩
  · intro y hy
    simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hy ⊢
    have e1 : c * a * c⁻¹ * (c * y * c⁻¹) = c * (a * y) * c⁻¹ := by group
    rw [e1, hZr, hQ]
    exact hy
  · intro y _
    group
  · intro y _
    group

include hQ in
theorem card_conjugates_conj {z w : G} (hzw : IsConj z w) :
    #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * w)) =
      #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * z)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hzw
  refine card_nbij' (fun x => c⁻¹ * x * c) (fun x => c * x * c⁻¹) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hx ⊢
    obtain ⟨h1, h2⟩ := hx
    refine ⟨h1.trans (isConj_iff.2 ⟨c⁻¹, by group⟩), ?_⟩
    rw [← hQ c]
    have e1 : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
    have e2 : c * ((c⁻¹ * x * c)⁻¹ * z) * c⁻¹ = x⁻¹ * (c * z * c⁻¹) := by group
    rw [e1, e2]
    exact h2
  · intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hx ⊢
    obtain ⟨h1, h2⟩ := hx
    refine ⟨h1.trans (isConj_iff.2 ⟨c, rfl⟩), ?_⟩
    have e2 : (c * x * c⁻¹)⁻¹ * (c * z * c⁻¹) = c * (x⁻¹ * z) * c⁻¹ := by group
    rw [e2, hQ]
    exact h2
  · intro x _
    group
  · intro x _
    group

include hQ hZr in
theorem pair_count (Z : List G)
    (hZ : ∀ z, Zr z ↔ ∃ j ∈ Z, IsConj j z) (hZd : Z.Pairwise fun i j => ¬IsConj i j) :
    #(univ.filter (IsConj a)) * #(univ.filter fun y => Zr (a * y) ∧ Q a y) =
      (Z.map fun j => #(univ.filter fun z => IsConj j z) *
        #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * j))).sum := by
  have hS : #(univ.filter (IsConj a)) * #(univ.filter fun y => Zr (a * y) ∧ Q a y) =
      ∑ x, ∑ y, if IsConj a x ∧ Zr (x * y) ∧ Q x y then 1 else 0 := by
    rw [← smul_eq_mul, ← sum_const, sum_filter]
    refine sum_congr rfl fun x _ => ?_
    split_ifs with hx
    · rw [← card_partners_conj a Q hQ Zr hZr hx, card_filter]
      refine sum_congr rfl fun y _ => ?_
      simp only [hx, true_and]
    · exact (sum_eq_zero fun y _ => ite_eq_right fun h => hx h.1).symm
  have hT : (∑ x, ∑ y, if IsConj a x ∧ Zr (x * y) ∧ Q x y then 1 else 0) =
      ∑ z, if Zr z then #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * z)) else 0 := by
    have : ∀ x : G, (∑ y, if IsConj a x ∧ Zr (x * y) ∧ Q x y then 1 else 0) =
        ∑ z, if IsConj a x ∧ Zr z ∧ Q x (x⁻¹ * z) then 1 else 0 := fun x => by
      refine Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun y => ?_
      simp [Equiv.coe_mulLeft]
    rw [Fintype.sum_congr _ _ this, sum_comm]
    refine sum_congr rfl fun z _ => ?_
    split_ifs with hz
    · rw [card_filter]
      refine sum_congr rfl fun x _ => ?_
      simp [hz]
    · exact sum_eq_zero fun x _ => by simp [hz]
  have hU : ∀ L : List G, L.Pairwise (fun i j => ¬IsConj i j) →
      (∑ z, if ∃ j ∈ L, IsConj j z then #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * z))
        else 0) =
      (L.map fun j => #(univ.filter fun z => IsConj j z) *
        #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * j))).sum := by
    intro L
    induction L with
    | nil => intro _; simp
    | cons j L ih =>
      intro hL
      rw [List.pairwise_cons] at hL
      rw [List.map_cons, List.sum_cons, ← ih hL.2, ← smul_eq_mul, ← sum_const, sum_filter]
      have hsplit : ∀ z : G, (if ∃ i ∈ j :: L, IsConj i z then
          #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * z)) else 0) =
          (if IsConj j z then #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * j)) else 0) +
          (if ∃ i ∈ L, IsConj i z then
            #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * z)) else 0) := fun z => by
        by_cases hj : IsConj j z
        · have hn : ¬∃ i ∈ L, IsConj i z := fun ⟨i, hi, hiz⟩ =>
            hL.1 i hi (hj.trans (isConj_comm.1 hiz))
          rw [ite_eq_left ⟨j, List.mem_cons_self, hj⟩, ite_eq_left hj, ite_eq_right hn, add_zero,
            card_conjugates_conj a Q hQ hj]
        · rw [ite_eq_right hj, zero_add]
          simp only [List.mem_cons, exists_eq_or_imp, hj, false_or]
      rw [Fintype.sum_congr _ _ hsplit, sum_add_distrib]
  rw [hS, hT, ← hU Z hZd]
  exact sum_congr rfl fun z _ => by simp only [hZ]

omit [Fintype G] in
theorem orderOf_conj' (c x : G) : orderOf (c * x * c⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq c (by rw [SemiconjBy]; group : SemiconjBy c x (c * x * c⁻¹))).symm

omit [Fintype G] in
theorem cover_eleven {z g x : G} (hz : orderOf z = 11) (hg : g * z * g⁻¹ = z ^ 3)
    (hx : ∃ i < 11, IsConj (z ^ i) x) (hx1 : orderOf x = 11) : IsConj z x ∨ IsConj z⁻¹ x := by
  obtain ⟨i, hi, hc⟩ := hx
  have st : ∀ k, IsConj (z ^ k) (z ^ (3 * k % 11)) := fun k => by
    refine isConj_iff.2 ⟨g, ?_⟩
    rw [← conj_pow, hg, ← pow_mul, ← hz, pow_mod_orderOf]
  have h11 : z ^ 11 = 1 := by
    rw [← hz]
    exact pow_orderOf_eq_one z
  have zi : z⁻¹ = z ^ 10 := (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h11)).symm
  have c1 := st 1
  have c2 := st 2
  have c3 := st 3
  have c5 := st 5
  have c6 := st 6
  have c8 := st 8
  have c9 := st 9
  have c10 := st 10
  simp only [Nat.reduceMul, Nat.reduceMod, pow_one] at c1 c2 c3 c5 c6 c8 c9 c10
  rw [zi]
  interval_cases i
  · rw [pow_zero, isConj_one_right] at hc
    rw [hc, orderOf_one] at hx1
    omega
  · rw [pow_one] at hc
    exact Or.inl hc
  · exact Or.inr ((c10.trans c8).trans hc)
  · exact Or.inl (c1.trans hc)
  · exact Or.inl ((((c1.trans c3).trans c9).trans c5).trans hc)
  · exact Or.inl (((c1.trans c3).trans c9).trans hc)
  · exact Or.inr (((c10.trans c8).trans c2).trans hc)
  · exact Or.inr ((((c10.trans c8).trans c2).trans c6).trans hc)
  · exact Or.inr (c10.trans hc)
  · exact Or.inl ((c1.trans c3).trans hc)
  · exact Or.inr hc

theorem not_isConj_of_card {z w : G} (h : #(univ.filter fun c => c * z = w * c) = 0) :
    ¬IsConj z w := fun hc => by
  obtain ⟨c, hc⟩ := isConj_iff.1 hc
  have hm : c ∈ univ.filter fun c => c * z = w * c := by
    rw [mem_filter]
    exact ⟨mem_univ c, by rw [← hc]; group⟩
  rw [card_eq_zero] at h
  rw [h] at hm
  exact absurd hm (Finset.notMem_empty c)

theorem card_conj_inv (z : G) :
    #(univ.filter (IsConj z⁻¹)) = #(univ.filter (IsConj z)) := by
  refine card_nbij' (fun y => y⁻¹) (fun y => y⁻¹) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hy ⊢
    obtain ⟨c, rfl⟩ := isConj_iff.1 hy
    exact isConj_iff.2 ⟨c, by group⟩
  · intro y hy
    simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hy ⊢
    obtain ⟨c, rfl⟩ := isConj_iff.1 hy
    exact isConj_iff.2 ⟨c, by group⟩
  · intro y _
    exact inv_inv y
  · intro y _
    exact inv_inv y

include hQ in
theorem pair_total_eleven (hdvd : ¬11 ^ 2 ∣ Nat.card G) {z g : G} (hz : orderOf z = 11)
    (hg : g * z * g⁻¹ = z ^ 3) (hzi : ¬IsConj z z⁻¹) :
    #(univ.filter (IsConj a)) * #(univ.filter fun y => orderOf (a * y) = 11 ∧ Q a y) *
        #(univ.filter fun c => c * z = z * c) =
      Fintype.card G * (#(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * z)) +
        #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * z⁻¹))) := by
  have hp : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hZr : ∀ g z : G, orderOf (g * z * g⁻¹) = 11 ↔ orderOf z = 11 := fun g z => by
    rw [orderOf_conj']
  have hZ : ∀ x : G, orderOf x = 11 ↔ ∃ j ∈ [z, z⁻¹], IsConj j x := fun x => by
    constructor
    · intro hx
      rcases cover_eleven hz hg (conj_pow_of_orderOf hdvd hz hx) hx with h | h
      · exact ⟨z, List.mem_cons_self, h⟩
      · exact ⟨z⁻¹, by simp, h⟩
    · rintro ⟨j, hj, hc⟩
      obtain ⟨c, rfl⟩ := isConj_iff.1 hc
      rw [orderOf_conj']
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact hz
      · rw [orderOf_inv, hz]
  have hZd : [z, z⁻¹].Pairwise fun i j => ¬IsConj i j := by
    simpa using hzi
  have h := pair_count a Q hQ (fun x => orderOf x = 11) hZr [z, z⁻¹] hZ hZd
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    card_conj_inv] at h
  have e := congrArg (· * #(univ.filter fun c => c * z = z * c)) h
  have e' : #(univ.filter (IsConj a)) * #(univ.filter fun y => orderOf (a * y) = 11 ∧ Q a y) *
        #(univ.filter fun c => c * z = z * c) =
      (#(univ.filter (IsConj z)) * #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * z)) +
        #(univ.filter (IsConj z)) * #(univ.filter fun x => IsConj a x ∧ Q x (x⁻¹ * z⁻¹))) *
        #(univ.filter fun c => c * z = z * c) := by
    convert e
  rw [e', ← card_conj_mul_card_comm z]
  ring

end CFSG.KS.SylowCount

end
