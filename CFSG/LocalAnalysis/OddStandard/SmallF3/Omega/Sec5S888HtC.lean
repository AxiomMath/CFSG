module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888HtB

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private instance instDecidableIsEvenVecHtC (v : Fin 8 → ZMod 2) : Decidable (IsEvenVec v) := by
  unfold IsEvenVec
  infer_instance

private def combFst (v : Fin 8 → ZMod 2) : Prop :=
  (∀ i : Fin 8, 4 ≤ (i : ℕ) → v i = 0) ∨ (∀ i : Fin 8, 4 ≤ (i : ℕ) → v i = 1)

private def combSnd (v : Fin 8 → ZMod 2) : Prop :=
  (∀ i : Fin 8, (i : ℕ) < 4 → v i = 0) ∨ (∀ i : Fin 8, (i : ℕ) < 4 → v i = 1)

private instance instDecidableCombFst (v : Fin 8 → ZMod 2) : Decidable (combFst v) := by
  unfold combFst
  infer_instance

private instance instDecidableCombSnd (v : Fin 8 → ZMod 2) : Decidable (combSnd v) := by
  unfold combSnd
  infer_instance

private theorem comb_exc (v : Fin 8 → ZMod 2)
    (h : v = 0 ∨ v = 1 ∨ v = heartZVec ∨ v = heartZVec + 1) : combFst v ∧ combSnd v := by
  revert v
  decide +kernel

private theorem comb_exc_add (v : Fin 8 → ZMod 2)
    (h : v + heartZVec = 0 ∨ v + heartZVec = 1 ∨ v + heartZVec = heartZVec ∨
      v + heartZVec = heartZVec + 1) :
    v = 0 ∨ v = 1 ∨ v = heartZVec ∨ v = heartZVec + 1 := by
  revert v
  decide +kernel

private theorem comb_C1 : ∀ v : Fin 8 → ZMod 2, IsEvenVec v →
    (vecWeight v = 2 ∨ vecWeight v = 6) →
    (vecWeight (v + heartZVec) = 2 ∨ vecWeight (v + heartZVec) = 6) → combFst v ∨ combSnd v := by
  decide +kernel

private theorem comb_C2 : ∀ u v : Fin 8 → ZMod 2,
    (IsEvenVec u ∧ IsEvenVec v ∧ combFst u ∧ ¬ combSnd u ∧ combSnd v ∧ ¬ combFst v) →
    (u + v ≠ 0 ∧ u + v ≠ 1 ∧ u + v ≠ heartZVec ∧ u + v ≠ heartZVec + 1 ∧
      vecWeight (u + v) ≠ 2 ∧ vecWeight (u + v) ≠ 6) := by
  decide +kernel

private theorem comb_dichotomy (P : (Fin 8 → ZMod 2) → Prop) (hE : ∀ v, P v → IsEvenVec v)
    (hc : P heartZVec) (hadd : ∀ u v, P u → P v → P (u + v))
    (hw : ∀ v, P v → v ≠ 0 → v ≠ 1 → v ≠ heartZVec → v ≠ heartZVec + 1 →
      vecWeight v = 2 ∨ vecWeight v = 6) :
    (∀ v, P v → combFst v) ∨ (∀ v, P v → combSnd v) := by
  have hside : ∀ v, P v → ¬ (combFst v ∧ combSnd v) → combFst v ∨ combSnd v := by
    intro v hv hnot
    have hne : ¬ (v = 0 ∨ v = 1 ∨ v = heartZVec ∨ v = heartZVec + 1) := fun h =>
      hnot (comb_exc v h)
    have hw1 := hw v hv (fun h => hne (Or.inl h)) (fun h => hne (Or.inr (Or.inl h)))
      (fun h => hne (Or.inr (Or.inr (Or.inl h)))) (fun h => hne (Or.inr (Or.inr (Or.inr h))))
    have hvc : P (v + heartZVec) := hadd v _ hv hc
    have hne2 : ¬ (v + heartZVec = 0 ∨ v + heartZVec = 1 ∨ v + heartZVec = heartZVec ∨
        v + heartZVec = heartZVec + 1) := fun h => hne (comb_exc_add v h)
    have hw2 := hw (v + heartZVec) hvc (fun h => hne2 (Or.inl h))
      (fun h => hne2 (Or.inr (Or.inl h))) (fun h => hne2 (Or.inr (Or.inr (Or.inl h))))
      (fun h => hne2 (Or.inr (Or.inr (Or.inr h))))
    exact comb_C1 v (hE v hv) hw1 hw2
  by_cases hex : ∃ u, P u ∧ combFst u ∧ ¬ combSnd u
  · left
    obtain ⟨u, hu, hfu, hsu⟩ := hex
    intro v hv
    by_contra hfv
    have hsv : combSnd v := (hside v hv fun h => hfv h.1).resolve_left hfv
    have h2 := comb_C2 u v ⟨hE u hu, hE v hv, hfu, hsu, hsv, hfv⟩
    rcases hw (u + v) (hadd u v hu hv) h2.1 h2.2.1 h2.2.2.1 h2.2.2.2.1 with h | h
    · exact h2.2.2.2.2.1 h
    · exact h2.2.2.2.2.2 h
  · right
    push Not at hex
    intro v hv
    by_contra hsv
    rcases hside v hv fun h => hsv h.2 with hf | hs
    · exact hsv (hex v hv hf)
    · exact hsv hs

theorem heart_block_cases {φ : (Fin 8 → ZMod 2) → G} {A M : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 8))} (hd : HeartData φ A M Alt) {t : G}
    (hcls : ∀ x ∈ conjClassIn M t, ∃ w, IsEvenVec w ∧ φ w = x ∧ vecWeight w = 2)
    {A' : Subgroup G} (hA'A : A' ≤ A) (hz : φ heartZVec ∈ A')
    (hA't : ∀ x ∈ A', x ≠ 1 → x ≠ φ heartZVec → x ∈ conjClassIn M t)
    (h8 : 8 ≤ Nat.card A') :
    (A' : Set G) = φ '' {v | IsFirstBlockVec v} ∨
      (A' : Set G) = φ '' {v | IsSecondBlockVec v} := by
  have h0 : φ 0 = 1 := hd.map_zero
  have key : ∀ a : ZMod 2, 0 = a + 1 → a = 1 := by decide
  have key2 : ∀ a b : ZMod 2, b = a + 1 → a = b + 1 := by decide
  have key3 : ∀ a : ZMod 2, a + 1 + 1 = a := by decide
  let P : (Fin 8 → ZMod 2) → Prop := fun v => IsEvenVec v ∧ φ v ∈ A'
  have hPw : ∀ v, P v → v ≠ 0 → v ≠ 1 → v ≠ heartZVec → v ≠ heartZVec + 1 →
      vecWeight v = 2 ∨ vecWeight v = 6 := by
    intro v hv hv0 hv1 hvc hvc1
    have hx1 : φ v ≠ 1 := by
      intro h
      rcases hd.inj v 0 hv.1 sec5b_isEvenVec_zero (by rw [h, h0]) with h' | h'
      · exact hv0 h'.symm
      · exact hv1 (funext fun i => key (v i) (congrFun h' i))
    have hxz : φ v ≠ φ heartZVec := by
      intro h
      rcases hd.inj v heartZVec hv.1 isEvenVec_heartZVec h with h' | h'
      · exact hvc h'.symm
      · exact hvc1 (funext fun i => key2 (v i) (heartZVec i) (congrFun h' i))
    obtain ⟨w, hwE, hwφ, hw2⟩ := hcls _ (hA't _ hv.2 hx1 hxz)
    rcases hd.inj w v hwE hv.1 hwφ with h' | h'
    · exact Or.inl (by rw [h', hw2])
    · exact Or.inr (by rw [h', sec5b_vecWeight_add_one, hw2])
  have hdich := comb_dichotomy P (fun v hv => hv.1) ⟨isEvenVec_heartZVec, hz⟩
    (fun u v hu hv => ⟨sec5b_isEvenVec_add hu.1 hv.1, by
      rw [hd.add u v hu.1 hv.1]; exact A'.mul_mem hu.2 hv.2⟩) hPw
  have hsub : ∀ x ∈ A', ∃ v, P v ∧ φ v = x := fun x hx => by
    obtain ⟨v, hv, hvx⟩ := hd.surj x (hA'A hx)
    exact ⟨v, ⟨hv, hvx ▸ hx⟩, hvx⟩
  have hAcard : 8 ≤ (A' : Set G).ncard := by
    have h1 : Nat.card A' = (A' : Set G).ncard := Nat.card_coe_set_eq (A' : Set G)
    rw [← h1]
    exact h8
  rcases hdich with hF | hS
  · left
    refine Set.eq_of_subset_of_ncard_le ?_ (by rw [heart_ncard_firstBlock hd.inj]; exact hAcard)
      (Set.toFinite _)
    intro x hx
    obtain ⟨v, hv, rfl⟩ := hsub x hx
    rcases hF v hv with h | h
    · exact ⟨v, ⟨hv.1, h⟩, rfl⟩
    · refine ⟨v + 1, ⟨sec5b_isEvenVec_add hv.1 sec5b_isEvenVec_one, fun i hi => ?_⟩,
        hd.add_one v hv.1⟩
      show v i + 1 = 0
      rw [h i hi]
      decide
  · right
    refine Set.eq_of_subset_of_ncard_le ?_ (by rw [heart_ncard_secondBlock hd.inj]; exact hAcard)
      (Set.toFinite _)
    intro x hx
    obtain ⟨v, hv, rfl⟩ := hsub x hx
    rcases hS v hv with h | h
    · exact ⟨v, ⟨hv.1, h⟩, rfl⟩
    · refine ⟨v + 1, ⟨sec5b_isEvenVec_add hv.1 sec5b_isEvenVec_one, fun i hi => ?_⟩,
        hd.add_one v hv.1⟩
      show v i + 1 = 0
      rw [h i hi]
      decide

end CFSG.OddStandard.SmallF3.Omega
