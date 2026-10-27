module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.GroupTheory.ZPowersPGroup
public import CFSG.Quasithin.EmptyFaithful.S153NMcSimple

public section

namespace CFSG.GroupTheory.AlternatingFive

open scoped Pointwise

open Equiv Equiv.Perm

local notation "A₅" => alternatingGroup (Fin 5)

noncomputable section

private def d₁ (i : Fin 5) : A₅ :=
  ![(⟨swap 1 2 * swap 3 4, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ : A₅),
    (⟨swap 2 3 * swap 4 0, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ : A₅),
    (⟨swap 3 4 * swap 0 1, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ : A₅),
    (⟨swap 4 0 * swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ : A₅),
    (⟨swap 0 1 * swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ : A₅)] i

private def d₂ (i : Fin 5) : A₅ :=
  ![(⟨swap 1 3 * swap 2 4, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ : A₅),
    (⟨swap 2 4 * swap 3 0, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ : A₅),
    (⟨swap 3 0 * swap 4 1, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ : A₅),
    (⟨swap 4 1 * swap 0 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ : A₅),
    (⟨swap 0 2 * swap 1 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ : A₅)] i

private abbrev memV (i : Fin 5) (x : A₅) : Prop :=
  x = 1 ∨ x = d₁ i ∨ x = d₂ i ∨ x = d₁ i * d₂ i

private instance decidableMemV (i : Fin 5) : DecidablePred (memV i) := fun x => by
  change Decidable (x = 1 ∨ x = d₁ i ∨ x = d₂ i ∨ x = d₁ i * d₂ i)
  infer_instance

private def V (i : Fin 5) : Subgroup A₅ where
  carrier := {x | memV i x}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro x y hx hy
    fin_cases i <;>
      simp only [Set.mem_setOf_eq, memV] at hx hy ⊢ <;>
      rcases hx with rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl <;>
      decide
  inv_mem' := by
    intro x hx
    fin_cases i <;>
      simp only [Set.mem_setOf_eq, memV] at hx ⊢ <;>
      rcases hx with rfl | rfl | rfl | rfl <;>
      decide

private lemma memV_iff (i : Fin 5) (x : A₅) : x ∈ V i ↔ memV i x := Iff.rfl

private instance decidableMemV' (i : Fin 5) : DecidablePred (fun x : A₅ => x ∈ V i) := fun x =>
  decidable_of_iff (memV i x) (memV_iff i x).symm

private lemma mem_V_iff {i : Fin 5} {x : A₅} :
    x ∈ V i ↔ x = 1 ∨ (x * x = 1 ∧ x ≠ 1 ∧ x • i = i) := by
  revert i x
  decide

private lemma card_V (i : Fin 5) : Nat.card (V i) = 4 := by
  change Nat.card ((V i : Set A₅)) = 4
  rw [Nat.card_coe_set_eq]
  have h : (V i : Set A₅) = ({1, d₁ i, d₂ i, d₁ i * d₂ i} : Finset A₅) := by
    ext x
    simp only [SetLike.mem_coe, memV_iff, memV, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [h, Set.ncard_coe_finset]
  fin_cases i <;> decide

private lemma V_fixed {i : Fin 5} {x : A₅} (hx : x ∈ V i) : x • i = i := by
  rw [mem_V_iff] at hx
  rcases hx with rfl | hx
  · simp
  · exact hx.2.2

private lemma smul_V (g : A₅) (i : Fin 5) : MulAut.conj g • V i = V (g • i) := by
  ext x
  have h1 : ((MulAut.conj g)⁻¹ • x = 1) ↔ x = 1 := by
    rw [MulAut.smul_def, MulAut.conj_inv_apply]
    constructor
    · intro h
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = g * 1 * g⁻¹ := by rw [h]
        _ = 1 := by group
    · intro h
      rw [h]
      group
  have h2 : (((MulAut.conj g)⁻¹ • x) * ((MulAut.conj g)⁻¹ • x) = 1) ↔ x * x = 1 := by
    rw [MulAut.smul_def, MulAut.conj_inv_apply]
    constructor
    · intro h
      calc x * x =
          (g * (g⁻¹ * x * g) * g⁻¹) * (g * (g⁻¹ * x * g) * g⁻¹) := by group
        _ = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    · intro h
      calc (g⁻¹ * x * g) * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
        _ = 1 := by rw [h]; group
  have h3 : (((MulAut.conj g)⁻¹ • x) • i = i) ↔ x • (g • i) = g • i := by
    constructor
    · intro h
      have := congrArg (fun j : Fin 5 => g • j) h
      simpa [MulAut.smul_def, MulAut.conj_inv_apply, Subgroup.smul_def,
        Perm.smul_def, mul_assoc] using this
    · intro h
      have := congrArg (fun j : Fin 5 => g⁻¹ • j) h
      simpa [MulAut.smul_def, MulAut.conj_inv_apply, Subgroup.smul_def,
        Perm.smul_def, mul_assoc] using this
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_V_iff, mem_V_iff]
  simp only [h1, h2, h3]
  tauto

private lemma card_A5 : Nat.card A₅ = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

private noncomputable def sylowV (i : Fin 5) : Sylow 2 A₅ :=
  Sylow.ofCard (V i) (by
    rw [card_V, card_A5]
    have hfac : (Nat.factorization 60) 2 = 2 := by
      rw [show 60 = 2 ^ 2 * 15 by norm_num,
        Nat.factorization_mul_apply_of_coprime (by decide), Nat.factorization_pow,
        Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Nat.prime_two.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (by decide)]
    rw [hfac]
    norm_num)

@[simp]
private lemma coe_sylowV (i : Fin 5) : (sylowV i : Subgroup A₅) = V i := by
  rw [sylowV, Sylow.coe_ofCard]

private lemma sylowV_smul (g : A₅) (i : Fin 5) : g • sylowV i = sylowV (g • i) := by
  apply Sylow.ext
  simpa only [Sylow.coe_subgroup_smul, coe_sylowV] using smul_V g i

private lemma d₁_mem_V (i : Fin 5) : d₁ i ∈ V i := Or.inr (Or.inl rfl)

private lemma d₁_fixed_iff (i j : Fin 5) : d₁ i • j = j ↔ i = j := by
  fin_cases i <;> fin_cases j <;> decide

private lemma V_injective : Function.Injective V := by
  intro i j hij
  have hmem : d₁ i ∈ V j := by
    rw [← hij]
    exact d₁_mem_V i
  exact (d₁_fixed_iff i j).mp (V_fixed hmem)

private lemma sylowV_injective : Function.Injective sylowV := by
  intro i j hij
  apply V_injective
  have := congrArg (fun P : Sylow 2 A₅ => (P : Subgroup A₅)) hij
  simpa only [coe_sylowV] using this

private lemma finite_sylow_two : Finite (Sylow 2 A₅) := by
  obtain ⟨P⟩ := Sylow.nonempty (G := A₅)
  exact Sylow.finite_of_finiteIndex P

private lemma exists_sylowV_eq (P : Sylow 2 A₅) : ∃ i : Fin 5, sylowV i = P := by
  haveI : Finite (Sylow 2 A₅) := finite_sylow_two
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A₅ (sylowV (0 : Fin 5)) P
  refine ⟨g • (0 : Fin 5), ?_⟩
  rw [← hg, sylowV_smul]

theorem card_sylowTwo : Nat.card (Sylow 2 A₅) = 5 := by
  haveI : Finite (Sylow 2 A₅) := finite_sylow_two
  have hle : 5 ≤ Nat.card (Sylow 2 A₅) := by
    have := Nat.card_le_card_of_injective sylowV sylowV_injective
    simpa using this
  have hge : Nat.card (Sylow 2 A₅) ≤ 5 := by
    have := Nat.card_le_card_of_surjective sylowV exists_sylowV_eq
    simpa using this
  omega

theorem card_sylow_two_eq (P : Sylow 2 A₅) : Nat.card P = 4 := by
  obtain ⟨i, rfl⟩ := exists_sylowV_eq P
  change Nat.card ((sylowV i : Subgroup A₅)) = 4
  rw [coe_sylowV]
  exact card_V i

private lemma eq_of_fixed_of_involution_of_ne_one :
    ∀ (x : A₅) (i j : Fin 5), x * x = 1 → x ≠ 1 →
      x • i = i → x • j = j → i = j := by
  decide

theorem inf_eq_bot_of_ne {P P' : Sylow 2 A₅} (h : P ≠ P') :
    (P : Subgroup A₅) ⊓ P' = ⊥ := by
  obtain ⟨i, rfl⟩ := exists_sylowV_eq P
  obtain ⟨j, rfl⟩ := exists_sylowV_eq P'
  have hij : i ≠ j := by
    intro hij
    exact h (by rw [hij])
  simp only [coe_sylowV]
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_inf, mem_V_iff, mem_V_iff] at hx
  by_contra hx1
  have hx2 : x * x = 1 := by
    rcases hx.1 with h1 | h1
    · exact absurd h1 hx1
    · exact h1.1
  have hxi : x • i = i := by
    rcases hx.1 with h1 | h1
    · exact absurd h1 hx1
    · exact h1.2.2
  have hxj : x • j = j := by
    rcases hx.2 with h1 | h1
    · exact absurd h1 hx1
    · exact h1.2.2
  exact hij (eq_of_fixed_of_involution_of_ne_one x i j hx2 hx1 hxi hxj)

theorem card_normalizer_sylow_two (P : Sylow 2 A₅) :
    Nat.card (Subgroup.normalizer (P : Set A₅)) = 12 := by
  haveI : Finite (Sylow 2 A₅) := finite_sylow_two
  have hindex : (Subgroup.normalizer (P : Set A₅)).index = 5 := by
    rw [← Sylow.card_eq_index_normalizer P, card_sylowTwo]
  have hmul := Subgroup.card_mul_index (Subgroup.normalizer (P : Set A₅))
  rw [hindex, card_A5] at hmul
  omega

theorem card_ne_twenty (H : Subgroup A₅) : Nat.card H ≠ 20 := by
  intro hH
  have hindex : H.index = 3 := by
    have hmul := Subgroup.card_mul_index H
    rw [hH, card_A5] at hmul
    omega
  haveI : IsSimpleGroup A₅ := alternatingGroup.isSimpleGroup (by norm_num)
  exact CFSG.Quasithin.S153N.index_ne_three_of_isSimpleGroup
    (by rw [card_A5]; norm_num) H hindex

theorem commutator_eq_top : commutator A₅ = ⊤ :=
  commutator_alternatingGroup_eq_top (by norm_num)

private lemma card_fixed_filter_of_pow_three_eq_one :
    ∀ x : A₅, x ^ 3 = 1 → x ≠ 1 →
      (Finset.univ.filter (fun i : Fin 5 => x • i = i)).card = 2 := by
  decide +kernel

private lemma orderOf_eq_three_iff {x : A₅} : orderOf x = 3 ↔ x ^ 3 = 1 ∧ x ≠ 1 := by
  constructor
  · intro hx
    refine ⟨by rw [← hx, pow_orderOf_eq_one], ?_⟩
    intro hx1
    rw [hx1, orderOf_one] at hx
    norm_num at hx
  · rintro ⟨h3, h1⟩
    exact orderOf_eq_prime h3 h1

private lemma sylowV_smul_eq_iff (x : A₅) (i : Fin 5) :
    x • sylowV i = sylowV i ↔ x • i = i := by
  rw [sylowV_smul]
  exact ⟨fun h => sylowV_injective h, fun h => by rw [h]⟩

private noncomputable def fixedSylowEquiv (x : A₅) :
    {P : Sylow 2 A₅ // x • P = P} ≃ {i : Fin 5 // x • i = i} where
  toFun P := by
    let i := Classical.choose (exists_sylowV_eq P.1)
    have hi : sylowV i = P.1 := Classical.choose_spec (exists_sylowV_eq P.1)
    refine ⟨i, ?_⟩
    exact (sylowV_smul_eq_iff x i).mp (by simpa [hi] using P.2)
  invFun i := ⟨sylowV i.1, (sylowV_smul_eq_iff x i.1).mpr i.2⟩
  left_inv P := by
    apply Subtype.ext
    exact Classical.choose_spec (exists_sylowV_eq P.1)
  right_inv i := by
    apply Subtype.ext
    exact sylowV_injective (Classical.choose_spec (exists_sylowV_eq (sylowV i.1)))

private lemma exists_swap_of_pow_three_eq_one :
    ∀ (x : A₅) (i j : Fin 5), x ^ 3 = 1 → x ≠ 1 →
      x • i = i → x • j = j → i ≠ j →
      (Finset.univ.filter (fun u : A₅ =>
        u * u = 1 ∧ u ≠ 1 ∧
          (u * x * u⁻¹ = x ∨ u * x * u⁻¹ = x * x) ∧ u • i = j)).card ≠ 0 := by
  decide +kernel

theorem card_fixed_sylow_two_of_orderOf_eq_three {x : A₅} (hx : orderOf x = 3) :
    Nat.card {P : Sylow 2 A₅ // x • P = P} = 2 := by
  obtain ⟨hx3, hx1⟩ := orderOf_eq_three_iff.mp hx
  have hcard : Nat.card {i : Fin 5 // x • i = i} = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact card_fixed_filter_of_pow_three_eq_one x hx3 hx1
  rw [Nat.card_congr (fixedSylowEquiv x)]
  exact hcard

theorem exists_swap_of_orderOf_eq_three {x : A₅} (hx : orderOf x = 3)
    {P P' : Sylow 2 A₅} (hP : x • P = P) (hP' : x • P' = P') (hne : P ≠ P') :
    ∃ u : A₅, u * u = 1 ∧ u ≠ 1 ∧ u * x * u⁻¹ ∈ Subgroup.zpowers x ∧ u • P = P' := by
  obtain ⟨hx3, hx1⟩ := orderOf_eq_three_iff.mp hx
  obtain ⟨i, rfl⟩ := exists_sylowV_eq P
  obtain ⟨j, rfl⟩ := exists_sylowV_eq P'
  have hxi : x • i = i := (sylowV_smul_eq_iff x i).mp hP
  have hxj : x • j = j := (sylowV_smul_eq_iff x j).mp hP'
  have hij : i ≠ j := by
    intro hij
    exact hne (by rw [hij])
  have hnonempty := exists_swap_of_pow_three_eq_one x i j hx3 hx1 hxi hxj hij
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (Nat.pos_iff_ne_zero.mpr hnonempty)
  rw [Finset.mem_filter] at hu
  obtain ⟨-, hu2, hu1, hux, hui⟩ := hu
  refine ⟨u, hu2, hu1, ?_, ?_⟩
  · rcases hux with hux | hux
    · rw [hux]
      exact Subgroup.mem_zpowers x
    · rw [hux]
      exact Subgroup.mul_mem _ (Subgroup.mem_zpowers x) (Subgroup.mem_zpowers x)
  · rw [sylowV_smul, hui]

end

end CFSG.GroupTheory.AlternatingFive
