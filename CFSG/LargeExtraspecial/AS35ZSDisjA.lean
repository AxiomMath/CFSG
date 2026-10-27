module

public import CFSG.LargeExtraspecial.AS35ZSHyp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35ZS

open Module CFSG.RankThree.OrthogonalInvolutions CFSG.Fischer.Classification.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary QuadraticMap
open CFSG.Blueprint.Fischer (K)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
theorem card_toFinset_submodule [Fintype V] (W : Submodule (ZMod 2) V)
    [Fintype (W : Set V)] : ((W : Set V).toFinset).card = 2 ^ finrank (ZMod 2) W := by
  rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
  exact (FiniteField.pow_finrank_eq_natCard 2 W).symm

theorem false_of_six_disjoint {U : Submodule (ZMod 2) V} (hU : finrank (ZMod 2) U ≤ 4)
    (L : Fin 6 → Submodule (ZMod 2) V) (hLU : ∀ i, L i ≤ U)
    (h2 : ∀ i, finrank (ZMod 2) (L i) = 2) (hdisj : ∀ i j, i ≠ j → L i ⊓ L j = ⊥) : False := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Fintype V := Fintype.ofFinite V
  set S : Fin 6 → Finset V := fun i => ((L i : Set V).toFinset).erase 0 with hS
  have hcardL : ∀ i, ((L i : Set V).toFinset).card = 4 := by
    intro i
    rw [card_toFinset_submodule, h2]
    norm_num
  have hcardS : ∀ i, (S i).card = 3 := by
    intro i
    rw [hS, Finset.card_erase_of_mem (by simp), hcardL]
  have hpd : (Set.univ : Set (Fin 6)).PairwiseDisjoint S := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro v hvi hvj
    rw [hS, Finset.mem_erase, Set.mem_toFinset] at hvi hvj
    have hv : v ∈ L i ⊓ L j := Submodule.mem_inf.2 ⟨hvi.2, hvj.2⟩
    rw [hdisj i j hij, Submodule.mem_bot] at hv
    exact hvi.1 hv
  have hsub : (Finset.univ.biUnion S) ⊆ ((U : Set V).toFinset).erase 0 := by
    intro v hv
    rw [Finset.mem_biUnion] at hv
    obtain ⟨i, -, hvi⟩ := hv
    rw [hS, Finset.mem_erase, Set.mem_toFinset] at hvi
    rw [Finset.mem_erase, Set.mem_toFinset]
    exact ⟨hvi.1, hLU i hvi.2⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_biUnion (fun i _ j _ hij => hpd (Set.mem_univ i) (Set.mem_univ j) hij),
    Finset.card_erase_of_mem (by simp), card_toFinset_submodule] at h1
  simp only [hcardS, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  have h2' : 2 ^ finrank (ZMod 2) U ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hU
  omega

variable {n : ℕ} {ρ : PG n →* (V ≃ₗ[ZMod 2] V)}

theorem tq_commute {x y : Fin n → K} (hx : herm frob x x = 0) (hy : herm frob y y = 0)
    (hxy : herm frob x y = 0) : tq x * tq y = tq y * tq x := by
  rw [← QuotientGroup.mk_mul, tvU_commute hx hy hxy, QuotientGroup.mk_mul]

theorem add_self_vec (w : Fin n → K) : w + w = 0 := by
  rw [← two_smul K w, two_eq_zero, zero_smul]

theorem tvU_tvU_smul {w w' : Fin n → K} (hw : herm frob w w = 0) (hw' : herm frob w' w' = 0)
    (hww' : herm frob w w' ≠ 0) : tvU w • (tvU w' • w) = herm frob w' w • w' := by
  rw [tvU_smul hw', tvU_smul hw, herm_add_right, herm_smul_right, hw, zero_add,
    mul_comm, herm_mul_herm_comm hww', one_smul, add_comm w, add_assoc, add_self_vec, add_zero]

namespace ZSHyp

variable {q : QuadraticForm (ZMod 2) V} (h : ZSHyp n q ρ)
include h

theorem inf_eq_bot_or_le {a b w : Fin n → K} (ha0 : a ≠ 0) (ha : herm frob a a = 0)
    (hb0 : b ≠ 0) (hb : herm frob b b = 0) (hab : herm frob a b ≠ 0) (hw0 : w ≠ 0)
    (hw : herm frob w w = 0) (haw : herm frob a w = 0) (hbw : herm frob b w = 0) :
    lineA ρ w ⊓ (lineA ρ a ⊔ lineA ρ b) = ⊥ ∨ lineA ρ w ≤ lineA ρ a ⊔ lineA ρ b := by
  set c := ρ (tq a * tq b) with hc
  have hcube := cube_apply (ρ := ρ) ha hb hab
  have hcomm : c * ρ (tq w) = ρ (tq w) * c := by
    rw [hc, ← map_mul, ← map_mul, mul_assoc, tq_commute hb hw hbw, ← mul_assoc,
      tq_commute ha hw haw, mul_assoc]
  rw [← h.commSpace_eq_sup ha0 ha hb0 hb hab]
  set S := lineA ρ w ⊓ commSpace c with hS
  have hSc : ∀ v ∈ S, c v ∈ S := fun v hv =>
    Submodule.mem_inf.2 ⟨apply_mem_commSpace_of_commute hcomm (Submodule.mem_inf.1 hv).1,
      apply_mem_commSpace_of_commute rfl (Submodule.mem_inf.1 hv).2⟩
  have hle : finrank (ZMod 2) S ≤ 2 := by
    have := Submodule.finrank_mono (inf_le_left : S ≤ lineA ρ w)
    rwa [h.finrank_lineA hw0 hw] at this
  have hne1 : finrank (ZMod 2) S ≠ 1 := by
    intro h1
    obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (Submodule.one_le_finrank_iff.1 h1.ge)
    have hspan := eq_span_singleton_of_mem_of_finrank_eq_one h1 hsS hs0
    have hcs := hSc s hsS
    rw [hspan, Submodule.mem_span_singleton] at hcs
    obtain ⟨t, ht⟩ := hcs
    have ht' : t = 0 ∨ t = 1 := (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) t
    rcases ht' with rfl | rfl
    · rw [zero_smul, eq_comm, LinearEquiv.map_eq_zero_iff] at ht
      exact hs0 ht
    · rw [one_smul] at ht
      exact hs0 (fixed_eq_zero_of_cube hcube (Submodule.mem_inf.1 hsS).2 ht.symm)
  rcases (by omega : finrank (ZMod 2) S = 0 ∨ finrank (ZMod 2) S = 2) with h0 | h2
  · exact Or.inl (Submodule.finrank_eq_zero.1 h0)
  · refine Or.inr ?_
    have := Submodule.eq_of_le_of_finrank_eq (inf_le_left : S ≤ lineA ρ w)
      (by rw [h2, h.finrank_lineA hw0 hw])
    rw [← this]
    exact inf_le_right

theorem apply_mem_vH {a b w : Fin n → K} (ha0 : a ≠ 0) (ha : herm frob a a = 0) (hb0 : b ≠ 0)
    (hb : herm frob b b = 0) (hab : herm frob a b ≠ 0) (hw : herm frob w w = 0)
    (haw : herm frob a w = 0) (hbw : herm frob b w = 0) {v : V}
    (hv : v ∈ lineA ρ a ⊔ lineA ρ b) : ρ (tq w) v ∈ lineA ρ a ⊔ lineA ρ b := by
  rw [← h.commSpace_eq_sup ha0 ha hb0 hb hab] at hv ⊢
  refine apply_mem_commSpace_of_commute ?_ hv
  rw [← map_mul, ← map_mul, ← mul_assoc, tq_commute hw ha (herm_eq_zero_comm frob frob_frob haw),
    mul_assoc, tq_commute hw hb (herm_eq_zero_comm frob frob_frob hbw), mul_assoc]

theorem le_of_le_of_herm_ne_zero {a b w w' : Fin n → K} (ha0 : a ≠ 0)
    (ha : herm frob a a = 0) (hb0 : b ≠ 0) (hb : herm frob b b = 0) (hab : herm frob a b ≠ 0)
    (hw : herm frob w w = 0) (haw : herm frob a w = 0) (hbw : herm frob b w = 0)
    (hw' : herm frob w' w' = 0) (haw' : herm frob a w' = 0) (hbw' : herm frob b w' = 0)
    (hww' : herm frob w w' ≠ 0) (hle : lineA ρ w ≤ lineA ρ a ⊔ lineA ρ b) :
    lineA ρ w' ≤ lineA ρ a ⊔ lineA ρ b := by
  have hc : herm frob w' w ≠ 0 := fun h0 => hww' (herm_eq_zero_comm frob frob_frob h0)
  rw [← lineA_smul hw' hc, ← tvU_tvU_smul hw hw' hww', ← mul_smul, ← map_lineA _ hw]
  rintro _ ⟨v, hv, rfl⟩
  rw [LinearEquiv.coe_coe, rs_apply, QuotientGroup.mk_mul, map_mul, LinearEquiv.mul_apply]
  exact h.apply_mem_vH ha0 ha hb0 hb hab hw haw hbw
    (h.apply_mem_vH ha0 ha hb0 hb hab hw' haw' hbw' (hle hv))

omit [FiniteDimensional (ZMod 2) V] h in
theorem map_vH (g : SUid frob n) {a b : Fin n → K} (ha : herm frob a a = 0)
    (hb : herm frob b b = 0) :
    (lineA ρ a ⊔ lineA ρ b).map (rs ρ g : V →ₗ[ZMod 2] V) = lineA ρ (g • a) ⊔ lineA ρ (g • b) := by
  rw [Submodule.map_sup, map_lineA g ha, map_lineA g hb]

end ZSHyp

end CFSG.LargeExtraspecial.AS35ZS
