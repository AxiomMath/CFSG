module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4CombSpan

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped CharTwo

private instance instDecidableIsEvenVec {n : ℕ} (v : Fin n → ZMod 2) : Decidable (IsEvenVec v) := by
  unfold IsEvenVec
  infer_instance

private lemma exists_perm_permVec {v w : Fin 7 → ZMod 2} (h : vecWeight v = vecWeight w) :
    ∃ σ : Equiv.Perm (Fin 7), permVec σ v = w := by
  classical
  have hvs : Fintype.card {i : Fin 7 // v i ≠ 0} = vecWeight v := by
    rw [Fintype.card_subtype]; rfl
  have hws : Fintype.card {i : Fin 7 // w i ≠ 0} = vecWeight w := by
    rw [Fintype.card_subtype]; rfl
  have hv : Fintype.card {i : Fin 7 // v i ≠ 0} = Fintype.card {i : Fin 7 // w i ≠ 0} := by
    rw [hvs, hws, h]
  let e : {i : Fin 7 // v i ≠ 0} ≃ {i : Fin 7 // w i ≠ 0} := Fintype.equivOfCardEq hv
  have hc : Fintype.card {i : Fin 7 // ¬ v i ≠ 0} = Fintype.card {i : Fin 7 // ¬ w i ≠ 0} := by
    rw [Fintype.card_subtype_compl (fun i => v i ≠ 0),
      Fintype.card_subtype_compl (fun i => w i ≠ 0), hvs, hws, h]
  let e' : {i : Fin 7 // ¬ v i ≠ 0} ≃ {i : Fin 7 // ¬ w i ≠ 0} := Fintype.equivOfCardEq hc
  let A : Set (Fin 7) := {i | v i ≠ 0}
  let B : Set (Fin 7) := {i | w i ≠ 0}
  let σ : Equiv.Perm (Fin 7) :=
    (Equiv.Set.sumCompl A).symm.trans ((e.sumCongr e').trans (Equiv.Set.sumCompl B))
  refine ⟨σ, ?_⟩
  have hσw : ∀ j, w (σ j) = v j := by
    intro j
    by_cases hj : v j ≠ 0
    · have h1 : σ j = (e ⟨j, hj⟩ : Fin 7) := by
        dsimp only [σ]
        rw [Equiv.trans_apply, Equiv.trans_apply,
          Equiv.Set.sumCompl_symm_apply_of_mem hj, Equiv.sumCongr_apply, Sum.map_inl,
          Equiv.Set.sumCompl_apply_inl]
      rw [h1, zmod2_eq_one_of_ne_zero (e ⟨j, hj⟩).2, zmod2_eq_one_of_ne_zero hj]
    · have h1 : σ j = (e' ⟨j, hj⟩ : Fin 7) := by
        dsimp only [σ]
        rw [Equiv.trans_apply, Equiv.trans_apply,
          Equiv.Set.sumCompl_symm_apply_of_notMem hj, Equiv.sumCongr_apply, Sum.map_inr,
          Equiv.Set.sumCompl_apply_inr]
      rw [h1, not_not.mp (e' ⟨j, hj⟩).2, not_not.mp hj]
  funext i
  have := hσw (σ.symm i)
  simp only [permVec, Function.comp_apply]
  rw [← this, Equiv.apply_symm_apply]

private lemma permVec_swap_eq_self {w : Fin 7 → ZMod 2} {a b : Fin 7} (hab : a ≠ b)
    (h : w a = w b) : permVec (Equiv.swap a b) w = w := by
  funext i
  simp only [permVec, Function.comp_apply]
  rw [Equiv.symm_swap, Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact h.symm
  · subst h2; exact h
  · rfl

private lemma permVec_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (v : Fin n → ZMod 2) :
    permVec (τ * σ) v = permVec τ (permVec σ v) := by
  funext i
  simp only [permVec, Function.comp_apply]
  congr 1

private lemma exists_ne_val (w : Fin 7 → ZMod 2) :
    ∃ a b : Fin 7, a ≠ b ∧ w a = w b := by
  obtain ⟨x, y, hxy, hwxy⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun t : Fin 3 => w ⟨t.1, by omega⟩) (by decide)
  exact ⟨⟨x.1, by omega⟩, ⟨y.1, by omega⟩,
    (fun h => hxy (Fin.ext (by simpa using congrArg Fin.val h))), hwxy⟩

theorem isEvenVec_permVec {n : ℕ} (σ : Equiv.Perm (Fin n)) {v : Fin n → ZMod 2}
    (hv : IsEvenVec v) : IsEvenVec (permVec σ v) := by
  unfold IsEvenVec permVec at *
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp σ.symm v]
  exact hv

theorem vecWeight_permVec {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n → ZMod 2) :
    vecWeight (permVec σ v) = vecWeight v := by
  unfold vecWeight permVec
  simp only [Function.comp_apply]
  have h : (Finset.univ.filter fun i => v (σ.symm i) ≠ 0)
      = (Finset.univ.filter fun i => v i ≠ 0).image σ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      exact ⟨σ.symm i, by simpa using hi, by simp⟩
    · rintro ⟨j, hj, rfl⟩
      simpa [Equiv.symm_apply_apply] using hj
  rw [h, Finset.card_image_of_injective _ σ.injective]

theorem exists_alternating_permVec {v w : Fin 7 → ZMod 2} (hv : IsEvenVec v) (hw : IsEvenVec w)
    (h : vecWeight v = vecWeight w) : ∃ σ ∈ alternatingGroup (Fin 7), permVec σ v = w := by
  obtain ⟨σ₀, hσ₀⟩ := exists_perm_permVec h
  by_cases hsign : Equiv.Perm.sign σ₀ = 1
  · exact ⟨σ₀, Equiv.Perm.mem_alternatingGroup.mpr hsign, hσ₀⟩
  · have hneg : Equiv.Perm.sign σ₀ = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ₀) with h1 | h1
      · exact absurd h1 hsign
      · exact h1
    obtain ⟨a, b, hab, hwab⟩ := exists_ne_val w
    refine ⟨Equiv.swap a b * σ₀, Equiv.Perm.mem_alternatingGroup.mpr ?_, ?_⟩
    · rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, hneg]
      decide
    · rw [permVec_mul, hσ₀, permVec_swap_eq_self hab hwab]

theorem card_evenVec_weight_six :
    Nat.card {v : Fin 7 → ZMod 2 // IsEvenVec v ∧ vecWeight v = 6} = 7 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem vecWeight_cases_of_isEvenVec {v : Fin 7 → ZMod 2} (hv : IsEvenVec v) :
    vecWeight v = 0 ∨ vecWeight v = 2 ∨ vecWeight v = 4 ∨ vecWeight v = 6 := by
  revert hv
  revert v
  decide +kernel

theorem eq_zero_of_vecWeight_eq_zero {n : ℕ} {v : Fin n → ZMod 2} (h : vecWeight v = 0) :
    v = 0 := by
  unfold vecWeight at h
  have hempty : (Finset.univ.filter fun i => v i ≠ 0) = ∅ := Finset.card_eq_zero.mp h
  funext i
  have hmem : i ∉ (Finset.univ.filter fun i => v i ≠ 0) := by
    rw [hempty]
    simp
  simpa using hmem

variable {G : Type} [Group G]

theorem IsPermModuleVia.map_zero {φ : (Fin 7 → ZMod 2) → G} {E H : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 7))} (h : IsPermModuleVia IsEvenVec φ E H Alt) :
    φ 0 = 1 := by
  have hz : IsEvenVec (0 : Fin 7 → ZMod 2) := by unfold IsEvenVec; simp
  have hmul : φ 0 * φ 0 = φ 0 := by
    simpa using (h.1 0 0 hz hz).symm
  exact mul_eq_right.mp hmul

theorem IsPermModuleVia.orderOf_eq_two {φ : (Fin 7 → ZMod 2) → G} {E H : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 7))} (h : IsPermModuleVia IsEvenVec φ E H Alt)
    {v : Fin 7 → ZMod 2} (hv : IsEvenVec v) (hv0 : v ≠ 0) : orderOf (φ v) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : IsEvenVec (0 : Fin 7 → ZMod 2) := by unfold IsEvenVec; simp
  have hvv : v + v = 0 := by funext k; exact CharTwo.add_self_eq_zero (v k)
  have hone : φ v * φ v = 1 := by
    rw [← h.1 v v hv hv, hvv, IsPermModuleVia.map_zero h]
  have hne : φ v ≠ 1 := fun h1 =>
    hv0 (h.2.1 v 0 hv hz (by rw [h1, IsPermModuleVia.map_zero h]))
  exact orderOf_eq_prime (by rw [pow_two]; exact hone) hne

theorem IsPermModuleVia.mem {φ : (Fin 7 → ZMod 2) → G} {E H : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 7))} (h : IsPermModuleVia IsEvenVec φ E H Alt)
    {v : Fin 7 → ZMod 2} (hv : IsEvenVec v) : φ v ∈ E :=
  (h.2.2.1 (φ v)).mpr ⟨v, hv, rfl⟩

theorem IsPermModuleVia.conjClassIn_eq {φ : (Fin 7 → ZMod 2) → G} {B H : Subgroup G}
    (h : IsPermModuleVia IsEvenVec φ B H (alternatingGroup (Fin 7))) {v : Fin 7 → ZMod 2}
    (hv : IsEvenVec v) :
    conjClassIn H (φ v) = {x | ∃ w, IsEvenVec w ∧ vecWeight w = vecWeight v ∧ φ w = x} := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨σ, _hσ, hσv⟩ := h.2.2.2.1 k hk
    refine ⟨permVec σ v, ?_, ?_, ?_⟩
    · exact isEvenVec_permVec σ hv
    · exact vecWeight_permVec σ v
    · rw [hσv v hv]
  · rintro ⟨w, hw, hwt, rfl⟩
    obtain ⟨σ, hσ, hσv⟩ := exists_alternating_permVec hv hw hwt.symm
    obtain ⟨k, hk, hkσ⟩ := h.2.2.2.2 σ hσ
    exact ⟨k, hk, by rw [hkσ v hv, hσv]⟩

theorem IsPermModuleVia.closure_conjClassIn {φ : (Fin 7 → ZMod 2) → G} {B H : Subgroup G}
    (h : IsPermModuleVia IsEvenVec φ B H (alternatingGroup (Fin 7))) {v : Fin 7 → ZMod 2}
    (hv : IsEvenVec v) (hw : vecWeight v = 2 ∨ vecWeight v = 4 ∨ vecWeight v = 6) :
    Subgroup.closure (conjClassIn H (φ v)) = B := by
  let C : Set G := {x | ∃ w, IsEvenVec w ∧ vecWeight w = vecWeight v ∧ φ w = x}
  have hCeq : conjClassIn H (φ v) = C := h.conjClassIn_eq hv
  rw [hCeq]
  refine le_antisymm ?_ ?_
  · apply (Subgroup.closure_le B).mpr
    rintro x ⟨w, hw', _hwt, rfl⟩
    exact h.mem hw'
  · intro x hx
    rw [h.2.2.1 x] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hz : IsEvenVec (0 : Fin 7 → ZMod 2) := by unfold IsEvenVec; simp
    exact (AddSubgroup.closure_induction
      (p := fun w _ => IsEvenVec w ∧ φ w ∈ Subgroup.closure C)
      (fun w hwS => ⟨hwS.1, Subgroup.subset_closure ⟨w, hwS.1, hwS.2, rfl⟩⟩)
      ⟨hz, by rw [IsPermModuleVia.map_zero h]; exact Subgroup.one_mem _⟩
      (fun x y _ _ ihx ihy => ⟨isEvenVec_add ihx.1 ihy.1, by
        rw [h.1 x y ihx.1 ihy.1]; exact Subgroup.mul_mem _ ihx.2 ihy.2⟩)
      (fun x _ ihx => by rw [CharTwo.neg_eq x]; exact ihx)
      (isEvenVec_mem_closure_weight (k := vecWeight v) hw hu)).2

end CFSG.OddStandard.SmallF3.Omega
