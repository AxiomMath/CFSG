module

public import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.AltLeaf

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.QuasithinUnique CFSG.RankThree.PartTwo Equiv Equiv.Perm
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56

section Klein

def a7KleinA : Perm (Fin 7) := swap 0 1 * swap 2 3

def a7KleinB : Perm (Fin 7) := swap 0 2 * swap 1 3

def a7KleinC : Perm (Fin 7) := swap 0 3 * swap 1 2

def a7KleinList : List (Perm (Fin 7)) := [1, a7KleinA, a7KleinB, a7KleinC]

theorem a7_klein_check :
    (a7KleinList.all fun a => a7KleinList.all fun b => a7KleinList.contains (a * b)) &&
    a7KleinList.all (fun a => decide (sign a = 1)) &&
    a7KleinList.all (fun a => decide (a * a = 1)) &&
    a7KleinList.all (fun a => decide (a 6 = 6)) = true := by
  decide +kernel

theorem a7_klein_mul {a b : Perm (Fin 7)} (ha : a ∈ a7KleinList) (hb : b ∈ a7KleinList) :
    a * b ∈ a7KleinList := by
  have h := a7_klein_check
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact h.1.1.1 a ha b hb

theorem a7_klein_sign {a : Perm (Fin 7)} (ha : a ∈ a7KleinList) : sign a = 1 := by
  have h := a7_klein_check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2 a ha

theorem a7_klein_sq {a : Perm (Fin 7)} (ha : a ∈ a7KleinList) : a * a = 1 := by
  have h := a7_klein_check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.2 a ha

theorem a7_klein_fix {a : Perm (Fin 7)} (ha : a ∈ a7KleinList) : a 6 = 6 := by
  have h := a7_klein_check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.2 a ha

def a7KleinSub : Subgroup (alternatingGroup (Fin 7)) where
  carrier := {g | (g : Perm (Fin 7)) ∈ a7KleinList}
  mul_mem' ha hb := a7_klein_mul ha hb
  one_mem' := List.mem_cons_self
  inv_mem' {a} ha := by
    have hinv : (a : Perm (Fin 7))⁻¹ = a := inv_eq_of_mul_eq_one_right (a7_klein_sq ha)
    change (a : Perm (Fin 7))⁻¹ ∈ a7KleinList
    rw [hinv]
    exact ha

theorem isPGroup_a7KleinSub : IsPGroup 2 a7KleinSub := fun g => ⟨1, by
  refine Subtype.ext (Subtype.ext ?_)
  have h := a7_klein_sq g.2
  simpa [pow_two] using h⟩

theorem exists_conj_a7Klein_le (S : Subgroup (alternatingGroup (Fin 7))) (hS : IsPGroup 2 S)
    (hodd : ¬ 2 ∣ S.index) :
    ∃ g : alternatingGroup (Fin 7), ∀ p ∈ a7KleinSub, g⁻¹ * p * g ∈ S := by
  obtain ⟨Q, hPQ⟩ := isPGroup_a7KleinSub.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) (hS.toSylow hodd) Q
  refine ⟨g, fun p hp => ?_⟩
  have h1 : p ∈ (Q : Subgroup (alternatingGroup (Fin 7))) := hPQ hp
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
  have h2 : (MulAut.conj g)⁻¹ • p ∈ ((hS.toSylow hodd : Sylow 2 _) : Subgroup _) := h1
  rw [IsPGroup.toSylow_coe] at h2
  simpa [MulAut.conj_inv_apply] using h2

def a7KleinThree : Perm (Fin 7) := swap 0 1 * swap 0 2

theorem a7KleinThree_isThreeCycle : a7KleinThree.IsThreeCycle :=
  isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem a7KleinThree_mem : a7KleinThree ∈ alternatingGroup (Fin 7) :=
  mem_alternatingGroup.2 a7KleinThree_isThreeCycle.sign

theorem a7KleinThree_cases :
    ∀ q : Fin 7, a7KleinThree q = q ∨ (q.val < 3 ∧ (a7KleinThree q).val < 3) := by
  decide

end Klein

section Fixing

theorem exists_three_fixing (S : Subgroup (alternatingGroup (Fin 7))) (hS : IsPGroup 2 S)
    (hodd : ¬ 2 ∣ S.index) :
    ∃ x : alternatingGroup (Fin 7), orderOf x = 3 ∧ ∀ y : evenWeight 7,
      (∀ s ∈ S, (QuotientAddGroup.mk (evenWeightPerm (s : Perm (Fin 7)) y) : altHeart 7) =
        QuotientAddGroup.mk y) → evenWeightPerm (x : Perm (Fin 7)) y = y := by
  obtain ⟨g, hg⟩ := exists_conj_a7Klein_le S hS hodd
  set G : Perm (Fin 7) := (g : Perm (Fin 7)) with hG
  let t₀ : alternatingGroup (Fin 7) := ⟨a7KleinThree, a7KleinThree_mem⟩
  refine ⟨g⁻¹ * t₀ * g, ?_, ?_⟩
  · have h1 : orderOf t₀ = 3 := by
      rw [← Subgroup.orderOf_coe]
      exact a7KleinThree_isThreeCycle.orderOf
    have h2 : g⁻¹ * t₀ * g = (MulAut.conj g⁻¹).toMonoidHom t₀ := by
      simp
    rw [h2, orderOf_injective _ (MulAut.conj g⁻¹).injective t₀, h1]
  · intro y hy
    have hpt : ∀ (σ : Perm (Fin 7)) (z : evenWeight 7) (r : Fin 7),
        ((evenWeightPerm σ z : evenWeight 7) : Fin 7 → ZMod 2) r =
          (z : Fin 7 → ZMod 2) (σ⁻¹ r) := fun _ _ _ => rfl
    have hw : ∀ p ∈ a7KleinList, ∀ q : Fin 7, (y : Fin 7 → ZMod 2) (G⁻¹ (p q)) =
        (y : Fin 7 → ZMod 2) (G⁻¹ q) := by
      intro p hp q
      have hmem : (⟨p, mem_alternatingGroup.2 (a7_klein_sign hp)⟩ : alternatingGroup (Fin 7)) ∈
          a7KleinSub := hp
      have hs := hy _ (hg _ hmem)
      have hcoe : (((g⁻¹ * ⟨p, mem_alternatingGroup.2 (a7_klein_sign hp)⟩ * g :
          alternatingGroup (Fin 7))) : Perm (Fin 7)) = G⁻¹ * p * G := rfl
      rw [hcoe] at hs
      have hs' : evenWeightPerm (G⁻¹ * p * G) y = y := by
        refine evenWeightPerm_eq_of_fixed_point _ y hs (G⁻¹ 6) ?_
        show G⁻¹ (p (G (G⁻¹ 6))) = G⁻¹ 6
        rw [papply_inv_self, a7_klein_fix hp]
      have h1 := congrFun (congrArg Subtype.val hs') (G⁻¹ q)
      rw [hpt] at h1
      have hinv : p⁻¹ = p := inv_eq_of_mul_eq_one_right (a7_klein_sq hp)
      have h2 : (G⁻¹ * p * G)⁻¹ (G⁻¹ q) = G⁻¹ (p q) := by
        simp only [mul_inv_rev, inv_inv, Perm.mul_apply, papply_inv_self, hinv]
      rw [h2] at h1
      exact h1
    have h1 : (y : Fin 7 → ZMod 2) (G⁻¹ 1) = (y : Fin 7 → ZMod 2) (G⁻¹ 0) := by
      have := hw a7KleinA (by simp [a7KleinList]) 0
      have e : a7KleinA 0 = 1 := by decide
      rwa [e] at this
    have h2 : (y : Fin 7 → ZMod 2) (G⁻¹ 2) = (y : Fin 7 → ZMod 2) (G⁻¹ 0) := by
      have := hw a7KleinB (by simp [a7KleinList]) 0
      have e : a7KleinB 0 = 2 := by decide
      rwa [e] at this
    have hconst : ∀ q : Fin 7, q.val < 3 →
        (y : Fin 7 → ZMod 2) (G⁻¹ q) = (y : Fin 7 → ZMod 2) (G⁻¹ 0) := by
      intro q hq
      fin_cases q
      · rfl
      · exact h1
      · exact h2
      all_goals simp at hq
    have hthree : ∀ q : Fin 7, (y : Fin 7 → ZMod 2) (G⁻¹ (a7KleinThree q)) =
        (y : Fin 7 → ZMod 2) (G⁻¹ q) := by
      intro q
      rcases a7KleinThree_cases q with h | ⟨hq, hq'⟩
      · rw [h]
      · rw [hconst _ hq, hconst _ hq']
    show evenWeightPerm (G⁻¹ * a7KleinThree * G) y = y
    apply Subtype.ext
    funext r
    rw [hpt]
    have h3 : (G⁻¹ * a7KleinThree * G)⁻¹ r = G⁻¹ (a7KleinThree⁻¹ (G r)) := by
      simp only [mul_inv_rev, inv_inv, Perm.mul_apply]
    rw [h3]
    have h4 := hthree (a7KleinThree⁻¹ (G r))
    rw [papply_inv_self] at h4
    rw [← h4]
    simp

end Fixing

section Abstract

variable {G U : Type*} [Group G] [Group U]

theorem exists_three_fixing_of_natural (hU2 : ∀ u : U, u * u = 1)
    (e : G ≃* alternatingGroup (Fin 7)) (ρ : G →* MulAut U)
    (π : U →* Multiplicative (altHeart 7))
    (hker : ∀ u, π u = 1 → ∀ g, ρ g u = u)
    (hπ : ∀ (g : G) (u : U) (y : evenWeight 7),
      Multiplicative.toAdd (π u) = (QuotientAddGroup.mk y : altHeart 7) →
      Multiplicative.toAdd (π (ρ g u)) =
        (QuotientAddGroup.mk (evenWeightPerm (e g : Perm (Fin 7)) y) : altHeart 7))
    (S : Subgroup G) (hS : IsPGroup 2 S) (hodd : ¬ 2 ∣ S.index) :
    ∃ x : G, orderOf x = 3 ∧ ∀ u : U, (∀ s ∈ S, ρ s u = u) → ρ x u = u := by
  have hS' : IsPGroup 2 (S.map (e : G →* alternatingGroup (Fin 7))) :=
    hS.map (e : G →* alternatingGroup (Fin 7))
  have hodd' : ¬ 2 ∣ (S.map (e : G →* alternatingGroup (Fin 7))).index := by
    rw [Subgroup.index_map_equiv]
    exact hodd
  obtain ⟨x₀, hx₀, hfix⟩ := exists_three_fixing _ hS' hodd'
  obtain ⟨x, hx⟩ : ∃ x : G, e x = x₀ := ⟨e.symm x₀, e.apply_symm_apply x₀⟩
  have hxo : orderOf x = 3 := by rw [← MulEquiv.orderOf_eq e x, hx, hx₀]
  refine ⟨x, hxo, fun u hu => ?_⟩
  obtain ⟨y, hy⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (π u))
  have hSy : ∀ s' ∈ S.map (e : G →* alternatingGroup (Fin 7)),
      (QuotientAddGroup.mk (evenWeightPerm (s' : Perm (Fin 7)) y) : altHeart 7) =
        QuotientAddGroup.mk y := by
    rintro _ ⟨s, hs, rfl⟩
    have h1 := hπ s u y hy.symm
    rw [hu s hs] at h1
    show (QuotientAddGroup.mk (evenWeightPerm ((e s : alternatingGroup (Fin 7)) : Perm (Fin 7))
      y) : altHeart 7) = _
    rw [← h1, hy]
  have hxy : evenWeightPerm (x₀ : Perm (Fin 7)) y = y := hfix y hSy
  have hπx : π (ρ x u) = π u := by
    apply Multiplicative.toAdd.injective
    have h1 := hπ x u y hy.symm
    rw [hx, hxy, hy] at h1
    exact h1
  obtain ⟨c, hc⟩ : ∃ c : U, c = ρ x u * u⁻¹ := ⟨_, rfl⟩
  have hcker : π c = 1 := by rw [hc, map_mul, map_inv, hπx, mul_inv_cancel]
  have hcfix : ∀ g, ρ g c = c := hker c hcker
  have hcu : ρ x u = c * u := by rw [hc, inv_mul_cancel_right]
  have hpow : ∀ j : ℕ, ρ (x ^ j) u = c ^ j * u := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', map_mul, MulAut.mul_apply, ih, map_mul, map_pow, hcfix, hcu, pow_succ,
        mul_assoc]
  have h3 : ρ (x ^ 3) u = u := by
    rw [← hxo, pow_orderOf_eq_one, map_one, MulAut.one_apply]
  have hc3 : c ^ 3 = 1 := by
    have := hpow 3
    rw [h3] at this
    exact (mul_eq_right.1 this.symm)
  have hc2 : c ^ 2 = 1 := by rw [pow_two]; exact hU2 c
  have hc1 : c = 1 := by
    have : c ^ 3 = c := by rw [pow_succ, hc2, one_mul]
    rw [← this, hc3]
  rw [hc1, one_mul] at hcu
  exact hcu

end Abstract

end CFSG.AGLEmbeddingD2.GN
