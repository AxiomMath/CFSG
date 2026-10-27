module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4CombSpan

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private instance instDecidableIsEvenVec8 (v : Fin 8 → ZMod 2) : Decidable (IsEvenVec v) := by
  unfold IsEvenVec
  infer_instance

theorem sec5b_permVec_add (σ : Equiv.Perm (Fin 8)) (v w : Fin 8 → ZMod 2) :
    permVec σ (v + w) = permVec σ v + permVec σ w := by
  rfl

theorem sec5b_permVec_mul (σ τ : Equiv.Perm (Fin 8)) (v : Fin 8 → ZMod 2) :
    permVec (σ * τ) v = permVec σ (permVec τ v) := by
  rfl

theorem sec5b_permVec_one (σ : Equiv.Perm (Fin 8)) : permVec σ (1 : Fin 8 → ZMod 2) = 1 := by
  rfl

theorem sec5b_isEvenVec_zero : IsEvenVec (0 : Fin 8 → ZMod 2) := by
  unfold IsEvenVec
  simp

theorem sec5b_isEvenVec_one : IsEvenVec (1 : Fin 8 → ZMod 2) := by
  unfold IsEvenVec
  decide +kernel

theorem sec5b_isEvenVec_add {v w : Fin 8 → ZMod 2} (hv : IsEvenVec v) (hw : IsEvenVec w) :
    IsEvenVec (v + w) :=
  isEvenVec_add hv hw

theorem sec5b_vecWeight_add_one (v : Fin 8 → ZMod 2) :
    vecWeight (v + 1) = 8 - vecWeight v := by
  revert v
  decide +kernel

theorem sec5b_weight_cases {v : Fin 8 → ZMod 2} (hv : IsEvenVec v) :
    vecWeight v = 0 ∨ vecWeight v = 2 ∨ vecWeight v = 4 ∨ vecWeight v = 6 ∨ vecWeight v = 8 := by
  revert hv
  revert v
  decide +kernel

theorem sec5b_eq_one_of_weight_eight {v : Fin 8 → ZMod 2} (h : vecWeight v = 8) :
    v = 1 := by
  revert v
  decide +kernel

private lemma sec5b_exists_perm_permVec {v w : Fin 8 → ZMod 2} (h : vecWeight v = vecWeight w) :
    ∃ σ : Equiv.Perm (Fin 8), permVec σ v = w := by
  classical
  have hvs : Fintype.card {i : Fin 8 // v i ≠ 0} = vecWeight v := by
    rw [Fintype.card_subtype]; rfl
  have hws : Fintype.card {i : Fin 8 // w i ≠ 0} = vecWeight w := by
    rw [Fintype.card_subtype]; rfl
  have hv : Fintype.card {i : Fin 8 // v i ≠ 0} = Fintype.card {i : Fin 8 // w i ≠ 0} := by
    rw [hvs, hws, h]
  let e : {i : Fin 8 // v i ≠ 0} ≃ {i : Fin 8 // w i ≠ 0} := Fintype.equivOfCardEq hv
  have hc : Fintype.card {i : Fin 8 // ¬ v i ≠ 0} = Fintype.card {i : Fin 8 // ¬ w i ≠ 0} := by
    rw [Fintype.card_subtype_compl (fun i => v i ≠ 0),
      Fintype.card_subtype_compl (fun i => w i ≠ 0), hvs, hws, h]
  let e' : {i : Fin 8 // ¬ v i ≠ 0} ≃ {i : Fin 8 // ¬ w i ≠ 0} := Fintype.equivOfCardEq hc
  let A : Set (Fin 8) := {i | v i ≠ 0}
  let B : Set (Fin 8) := {i | w i ≠ 0}
  let σ : Equiv.Perm (Fin 8) :=
    (Equiv.Set.sumCompl A).symm.trans ((e.sumCongr e').trans (Equiv.Set.sumCompl B))
  refine ⟨σ, ?_⟩
  have hσw : ∀ j, w (σ j) = v j := by
    intro j
    by_cases hj : v j ≠ 0
    · have h1 : σ j = (e ⟨j, hj⟩ : Fin 8) := by
        dsimp only [σ]
        rw [Equiv.trans_apply, Equiv.trans_apply,
          Equiv.Set.sumCompl_symm_apply_of_mem hj, Equiv.sumCongr_apply, Sum.map_inl,
          Equiv.Set.sumCompl_apply_inl]
      rw [h1, zmod2_eq_one_of_ne_zero (e ⟨j, hj⟩).2, zmod2_eq_one_of_ne_zero hj]
    · have h1 : σ j = (e' ⟨j, hj⟩ : Fin 8) := by
        dsimp only [σ]
        rw [Equiv.trans_apply, Equiv.trans_apply,
          Equiv.Set.sumCompl_symm_apply_of_notMem hj, Equiv.sumCongr_apply, Sum.map_inr,
          Equiv.Set.sumCompl_apply_inr]
      rw [h1, not_not.mp (e' ⟨j, hj⟩).2, not_not.mp hj]
  funext i
  have := hσw (σ.symm i)
  simp only [permVec, Function.comp_apply]
  rw [← this, Equiv.apply_symm_apply]

private lemma sec5b_permVec_swap_eq_self {w : Fin 8 → ZMod 2} {a b : Fin 8} (hab : a ≠ b)
    (h : w a = w b) : permVec (Equiv.swap a b) w = w := by
  funext i
  simp only [permVec, Function.comp_apply]
  rw [Equiv.symm_swap, Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact h.symm
  · subst h2; exact h
  · rfl

private lemma sec5b_exists_ne_val (w : Fin 8 → ZMod 2) :
    ∃ a b : Fin 8, a ≠ b ∧ w a = w b := by
  obtain ⟨x, y, hxy, hwxy⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun t : Fin 3 => w ⟨t.1, by omega⟩) (by decide)
  exact ⟨⟨x.1, by omega⟩, ⟨y.1, by omega⟩,
    (fun h => hxy (Fin.ext (by simpa using congrArg Fin.val h))), hwxy⟩

theorem sec5b_exists_alt {v w : Fin 8 → ZMod 2} (h : vecWeight v = vecWeight w) :
    ∃ σ ∈ alternatingGroup (Fin 8), permVec σ v = w := by
  obtain ⟨σ₀, hσ₀⟩ := sec5b_exists_perm_permVec h
  by_cases hsign : Equiv.Perm.sign σ₀ = 1
  · exact ⟨σ₀, Equiv.Perm.mem_alternatingGroup.mpr hsign, hσ₀⟩
  · have hneg : Equiv.Perm.sign σ₀ = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ₀) with h1 | h1
      · exact absurd h1 hsign
      · exact h1
    obtain ⟨a, b, hab, hwab⟩ := sec5b_exists_ne_val w
    refine ⟨Equiv.swap a b * σ₀, Equiv.Perm.mem_alternatingGroup.mpr ?_, ?_⟩
    · rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, hneg]
      decide
    · rw [sec5b_permVec_mul, hσ₀, sec5b_permVec_swap_eq_self hab hwab]

theorem sec5b_ncard_weight_four {G : Type} (φ : (Fin 8 → ZMod 2) → G)
    (h1 : ∀ v, IsEvenVec v → φ (v + 1) = φ v)
    (h2 : ∀ v w, IsEvenVec v → IsEvenVec w → φ v = φ w → w = v ∨ w = v + 1) :
    Set.ncard (φ '' {v | IsEvenVec v ∧ vecWeight v = 4}) = 35 := by
  let W : Set (Fin 8 → ZMod 2) := {v | IsEvenVec v ∧ vecWeight v = 4}
  let W' : Set (Fin 8 → ZMod 2) := {v | IsEvenVec v ∧ vecWeight v = 4 ∧ v 0 = 1}
  change Set.ncard (φ '' W) = 35
  have hmemW : ∀ v, v ∈ W ↔ IsEvenVec v ∧ vecWeight v = 4 := by
    intro v; simp [W]
  have hmemW' : ∀ v, v ∈ W' ↔ IsEvenVec v ∧ vecWeight v = 4 ∧ v 0 = 1 := by
    intro v; simp [W']
  have hsub : W' ⊆ W := by
    intro v hv
    rw [hmemW' v] at hv
    rw [hmemW v]
    exact ⟨hv.1, hv.2.1⟩
  have hset : φ '' W = φ '' W' := by
    apply Set.Subset.antisymm
    · rintro x ⟨v, hv, rfl⟩
      rw [hmemW v] at hv
      by_cases hv0 : v 0 = 0
      · refine ⟨v + 1, ?_, h1 v hv.1⟩
        rw [hmemW' (v + 1)]
        refine ⟨sec5b_isEvenVec_add hv.1 sec5b_isEvenVec_one, ?_, ?_⟩
        · rw [sec5b_vecWeight_add_one, hv.2]
        · simp [Pi.add_apply, hv0]
      · exact ⟨v, by rw [hmemW' v]; exact ⟨hv.1, hv.2, zmod2_eq_one_of_ne_zero hv0⟩, rfl⟩
    · rintro x ⟨v, hv, rfl⟩
      rw [hmemW' v] at hv
      exact ⟨v, by rw [hmemW v]; exact ⟨hv.1, hv.2.1⟩, rfl⟩
  have hinj : Set.InjOn φ W' := by
    intro v hv w hw hφ
    rw [hmemW' v] at hv
    rw [hmemW' w] at hw
    rcases h2 v w hv.1 hw.1 hφ with h | h
    · exact h.symm
    · exfalso
      have hw0 : w 0 = 0 := by
        rw [h]
        simp only [Pi.add_apply, Pi.one_apply, hv.2.2]
        decide
      rw [hw.2.2] at hw0
      exact one_ne_zero hw0
  rw [hset, hinj.ncard_image]
  have hW'coe : W' = ↑(Finset.univ.filter fun v : Fin 8 → ZMod 2 =>
      IsEvenVec v ∧ vecWeight v = 4 ∧ v 0 = 1) := by
    ext v
    rw [hmemW' v]
    simp
  rw [hW'coe, Set.ncard_coe_finset]
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega
