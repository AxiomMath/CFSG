module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4CombSpan

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped CharTwo

private instance instDecidableIsEvenVec6 (v : Fin 6 → ZMod 2) : Decidable (IsEvenVec v) := by
  unfold IsEvenVec
  infer_instance

private lemma sec5b6_exists_perm_permVec {v w : Fin 6 → ZMod 2} (h : vecWeight v = vecWeight w) :
    ∃ σ : Equiv.Perm (Fin 6), permVec σ v = w := by
  classical
  have hvs : Fintype.card {i : Fin 6 // v i ≠ 0} = vecWeight v := by
    rw [Fintype.card_subtype]; rfl
  have hws : Fintype.card {i : Fin 6 // w i ≠ 0} = vecWeight w := by
    rw [Fintype.card_subtype]; rfl
  have hv : Fintype.card {i : Fin 6 // v i ≠ 0} = Fintype.card {i : Fin 6 // w i ≠ 0} := by
    rw [hvs, hws, h]
  let e : {i : Fin 6 // v i ≠ 0} ≃ {i : Fin 6 // w i ≠ 0} := Fintype.equivOfCardEq hv
  have hc : Fintype.card {i : Fin 6 // ¬ v i ≠ 0} = Fintype.card {i : Fin 6 // ¬ w i ≠ 0} := by
    rw [Fintype.card_subtype_compl (fun i => v i ≠ 0),
      Fintype.card_subtype_compl (fun i => w i ≠ 0), hvs, hws, h]
  let e' : {i : Fin 6 // ¬ v i ≠ 0} ≃ {i : Fin 6 // ¬ w i ≠ 0} := Fintype.equivOfCardEq hc
  let A : Set (Fin 6) := {i | v i ≠ 0}
  let B : Set (Fin 6) := {i | w i ≠ 0}
  let σ : Equiv.Perm (Fin 6) :=
    (Equiv.Set.sumCompl A).symm.trans ((e.sumCongr e').trans (Equiv.Set.sumCompl B))
  refine ⟨σ, ?_⟩
  have hσw : ∀ j, w (σ j) = v j := by
    intro j
    by_cases hj : v j ≠ 0
    · have h1 : σ j = (e ⟨j, hj⟩ : Fin 6) := by
        dsimp only [σ]
        rw [Equiv.trans_apply, Equiv.trans_apply,
          Equiv.Set.sumCompl_symm_apply_of_mem hj, Equiv.sumCongr_apply, Sum.map_inl,
          Equiv.Set.sumCompl_apply_inl]
      rw [h1, zmod2_eq_one_of_ne_zero (e ⟨j, hj⟩).2, zmod2_eq_one_of_ne_zero hj]
    · have h1 : σ j = (e' ⟨j, hj⟩ : Fin 6) := by
        dsimp only [σ]
        rw [Equiv.trans_apply, Equiv.trans_apply,
          Equiv.Set.sumCompl_symm_apply_of_notMem hj, Equiv.sumCongr_apply, Sum.map_inr,
          Equiv.Set.sumCompl_apply_inr]
      rw [h1, not_not.mp (e' ⟨j, hj⟩).2, not_not.mp hj]
  funext i
  have := hσw (σ.symm i)
  simp only [permVec, Function.comp_apply]
  rw [← this, Equiv.apply_symm_apply]

private lemma sec5b6_permVec_swap_eq_self {w : Fin 6 → ZMod 2} {a b : Fin 6} (hab : a ≠ b)
    (h : w a = w b) : permVec (Equiv.swap a b) w = w := by
  funext i
  simp only [permVec, Function.comp_apply]
  rw [Equiv.symm_swap, Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact h.symm
  · subst h2; exact h
  · rfl

private lemma sec5b6_permVec_mul (σ τ : Equiv.Perm (Fin 6)) (v : Fin 6 → ZMod 2) :
    permVec (σ * τ) v = permVec σ (permVec τ v) := by
  rfl

private lemma sec5b6_exists_ne_val (w : Fin 6 → ZMod 2) :
    ∃ a b : Fin 6, a ≠ b ∧ w a = w b := by
  obtain ⟨x, y, hxy, hwxy⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun t : Fin 3 => w ⟨t.1, by omega⟩) (by decide)
  exact ⟨⟨x.1, by omega⟩, ⟨y.1, by omega⟩,
    (fun h => hxy (Fin.ext (by simpa using congrArg Fin.val h))), hwxy⟩

theorem sec5b6_exists_alt {v w : Fin 6 → ZMod 2} (h : vecWeight v = vecWeight w) :
    ∃ σ ∈ alternatingGroup (Fin 6), permVec σ v = w := by
  obtain ⟨σ₀, hσ₀⟩ := sec5b6_exists_perm_permVec h
  by_cases hsign : Equiv.Perm.sign σ₀ = 1
  · exact ⟨σ₀, Equiv.Perm.mem_alternatingGroup.mpr hsign, hσ₀⟩
  · have hneg : Equiv.Perm.sign σ₀ = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ₀) with h1 | h1
      · exact absurd h1 hsign
      · exact h1
    obtain ⟨a, b, hab, hwab⟩ := sec5b6_exists_ne_val w
    refine ⟨Equiv.swap a b * σ₀, Equiv.Perm.mem_alternatingGroup.mpr ?_, ?_⟩
    · rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, hneg]
      decide
    · rw [sec5b6_permVec_mul, hσ₀, sec5b6_permVec_swap_eq_self hab hwab]

private lemma sec5b6_weight_le_six_aux (v : Fin 6 → ZMod 2) : vecWeight v ≤ 6 := by
  unfold vecWeight
  calc (Finset.univ.filter fun i => v i ≠ 0).card
      ≤ (Finset.univ : Finset (Fin 6)).card := Finset.card_filter_le _ _
    _ = 6 := by simp

private lemma sec5b6_eq_one_of_weight_six_aux {v : Fin 6 → ZMod 2} (h : vecWeight v = 6) :
    v = 1 := by
  revert v
  decide +kernel

theorem sec5b6_ncard_weight (k : ℕ) :
    Set.ncard {v : Fin 6 → ZMod 2 | vecWeight v = k} = Nat.choose 6 k := by
  have hcoe : {v : Fin 6 → ZMod 2 | vecWeight v = k} =
      ↑(Finset.univ.filter fun v : Fin 6 → ZMod 2 => vecWeight v = k) := by
    ext v; simp
  rw [hcoe, Set.ncard_coe_finset]
  by_cases hk : k ≤ 6
  · interval_cases k <;> decide +kernel
  · have hcard : (Finset.univ.filter fun v : Fin 6 → ZMod 2 => vecWeight v = k).card = 0 := by
      apply Finset.card_eq_zero.mpr
      rw [Finset.eq_empty_iff_forall_notMem]
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      have := sec5b6_weight_le_six_aux v
      omega
    rw [hcard, Nat.choose_eq_zero_of_lt (n := 6) (k := k) (by omega)]

theorem sec5b6_isEvenVec_iff (v : Fin 6 → ZMod 2) : IsEvenVec v ↔ Even (vecWeight v) := by
  revert v
  decide +kernel

theorem sec5b6_vecWeight_add_one (v : Fin 6 → ZMod 2) :
    vecWeight (v + 1) = 6 - vecWeight v := by
  revert v
  decide +kernel

theorem sec5b6_weight_le_six (v : Fin 6 → ZMod 2) : vecWeight v ≤ 6 :=
  sec5b6_weight_le_six_aux v

theorem sec5b6_vecWeight_zero : vecWeight (0 : Fin 6 → ZMod 2) = 0 := by
  decide +kernel

theorem sec5b6_vecWeight_one : vecWeight (1 : Fin 6 → ZMod 2) = 6 := by
  decide +kernel

theorem sec5b6_vecWeight_single (i : Fin 6) : vecWeight (Pi.single i (1 : ZMod 2)) = 1 := by
  revert i
  decide +kernel

theorem sec5b6_eq_one_of_weight_six {v : Fin 6 → ZMod 2} (h : vecWeight v = 6) : v = 1 :=
  sec5b6_eq_one_of_weight_six_aux h

end CFSG.OddStandard.SmallF3.Omega
