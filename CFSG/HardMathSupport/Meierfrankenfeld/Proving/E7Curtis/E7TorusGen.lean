module

public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.E7Neg
public import CFSG.Quasithin.Background.SmithCurtisChevType

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis

open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev

theorem prod_zpow_sum {ι G : Type*} [CommGroup G] (s : Finset ι) (g : G) (e : ι → ℤ) :
    ∏ i ∈ s, g ^ e i = g ^ ∑ i ∈ s, e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add, ih]

@[expose] def e7AdjCartan : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ :=
  ![![4, 4, 6, 8, 6, 4, 2], ![4, 7, 8, 12, 9, 6, 3], ![6, 8, 12, 16, 12, 8, 4],
    ![8, 12, 16, 24, 18, 12, 6], ![6, 9, 12, 18, 15, 10, 5], ![4, 6, 8, 12, 10, 8, 4],
    ![2, 3, 4, 6, 5, 4, 3]]

theorem e7AdjCartan_mul : ∀ i l : Fin Tag.E7.rank,
    ∑ j : Fin Tag.E7.rank, e7AdjCartan j i * Tag.E7.cartan j l = if i = l then 2 else 0 := by
  decide +kernel

section

variable {K : Type} [Field K] [Finite K]

theorem exists_cartanChar_eq
    (hodd : Odd (Nat.card Kˣ)) (l : Fin Tag.E7.rank → Kˣ) :
    ∃ c : Fin Tag.E7.rank → Kˣ, cartanChar (τ := .E7) c = l := by
  obtain ⟨r, hr⟩ := hodd
  refine ⟨fun j => ∏ i, l i ^ ((r + 1 : ℤ) * e7AdjCartan j i), funext fun l' => ?_⟩
  unfold cartanChar
  simp only [← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  simp only [prod_zpow_sum]
  have h1 : ∀ i : Fin Tag.E7.rank, ∑ j : Fin Tag.E7.rank, (r + 1 : ℤ) * e7AdjCartan j i * Tag.E7.cartan j l' =
      (r + 1 : ℤ) * (if i = l' then 2 else 0) := by
    intro i
    rw [← e7AdjCartan_mul i l', Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [h1]
  have h2 : ∀ i : Fin Tag.E7.rank, l i ^ ((r + 1 : ℤ) * (if i = l' then 2 else 0)) =
      if l' = i then l l' else 1 := by
    intro i
    by_cases hi : i = l'
    · subst hi
      simp only [ite_true]
      have : l i ^ (Nat.card Kˣ) = 1 := pow_card_eq_one'
      rw [hr] at this
      rw [show ((r + 1 : ℤ) * 2) = ((2 * r + 1 : ℕ) : ℤ) + 1 by push_cast; ring, zpow_add,
        zpow_natCast, this, one_mul, zpow_one]
    · simp [hi, Ne.symm hi]
  simp only [h2]
  rw [Finset.prod_ite_eq]
  simp

end

section H


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_dC_prod_of_mem_H (hodd : Odd (Nat.card Kˣ)) {h : ↥(adjointGroup .E7 K)}
    (hh : h ∈ (chevDatum .E7 K 2 exists_weyl_neg_E7).H) :
    ∃ c : Fin Tag.E7.rank → Kˣ,
      h = ((List.finRange Tag.E7.rank).map fun j => dC .E7 K j (c j)).prod := by
  have hT : (h : ModGL .E7 K) ∈ torusGroup .E7 K := Subgroup.mem_subgroupOf.1 hh
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  obtain ⟨c, hc⟩ := exists_cartanChar_eq hodd l
  refine ⟨c, Subtype.ext ?_⟩
  rw [hl, ← hc, ← list_prod_torusElt_eq_rootDiagUnit, Subgroup.val_list_prod, List.map_map]
  rfl

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem chi_mul_of_isChevType {ρ : Representation k ↥(adjointGroup .E7 K) V} {y : V}
    {χ : ↥(adjointGroup .E7 K) → k} {J : Finset (Fin Tag.E7.rank)}
    (ht : IsChevType .E7 K 2 exists_weyl_neg_E7 ρ y χ J) {h h' : ↥(adjointGroup .E7 K)}
    (hh : h ∈ (chevDatum .E7 K 2 exists_weyl_neg_E7).H)
    (hh' : h' ∈ (chevDatum .E7 K 2 exists_weyl_neg_E7).H) : χ (h * h') = χ h * χ h' := by
  have e := ht.2.2.1 _ (mul_mem hh hh')
  rw [map_mul, Module.End.mul_apply, ht.2.2.1 h' hh', map_smul, ht.2.2.1 h hh, smul_smul,
    mul_comm] at e
  exact (smul_left_injective k ht.2.1 e).symm

theorem chi_one_of_isChevType {ρ : Representation k ↥(adjointGroup .E7 K) V} {y : V}
    {χ : ↥(adjointGroup .E7 K) → k} {J : Finset (Fin Tag.E7.rank)}
    (ht : IsChevType .E7 K 2 exists_weyl_neg_E7 ρ y χ J) : χ 1 = 1 := by
  have e := ht.2.2.1 1 (one_mem _)
  rw [map_one, Module.End.one_apply] at e
  exact smul_left_injective k ht.2.1 (show χ 1 • y = (1 : k) • y by rw [one_smul]; exact e.symm)

theorem chi_eq_of_dC_eq (hodd : Odd (Nat.card Kˣ)) {k : Type*} [Field k]
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
    {ρ₁ : Representation k ↥(adjointGroup .E7 K) V₁} {ρ₂ : Representation k ↥(adjointGroup .E7 K) V₂}
    {y₁ : V₁} {y₂ : V₂} {χ₁ χ₂ : ↥(adjointGroup .E7 K) → k} {J₁ J₂ : Finset (Fin Tag.E7.rank)}
    (ht₁ : IsChevType .E7 K 2 exists_weyl_neg_E7 ρ₁ y₁ χ₁ J₁)
    (ht₂ : IsChevType .E7 K 2 exists_weyl_neg_E7 ρ₂ y₂ χ₂ J₂)
    (hd : ∀ (j : Fin Tag.E7.rank) (t : Kˣ), χ₁ (dC .E7 K j t) = χ₂ (dC .E7 K j t)) :
    ∀ h ∈ (chevDatum .E7 K 2 exists_weyl_neg_E7).H, χ₁ h = χ₂ h := by
  intro h hh
  obtain ⟨c, rfl⟩ := exists_dC_prod_of_mem_H hodd hh
  have key : ∀ (L : List (Fin Tag.E7.rank)),
      χ₁ ((L.map fun j => dC .E7 K j (c j)).prod) = χ₂ ((L.map fun j => dC .E7 K j (c j)).prod) := by
    intro L
    induction L with
    | nil => simp [chi_one_of_isChevType ht₁, chi_one_of_isChevType ht₂]
    | cons j L ih =>
      have hL : ((L.map fun j => dC .E7 K j (c j)).prod) ∈
          (chevDatum .E7 K 2 exists_weyl_neg_E7).H :=
        Subgroup.list_prod_mem _ fun g hg => by
          obtain ⟨j', -, rfl⟩ := List.mem_map.1 hg
          exact dC_mem_H j' (c j')
      rw [List.map_cons, List.prod_cons, chi_mul_of_isChevType ht₁ (dC_mem_H j (c j)) hL,
        chi_mul_of_isChevType ht₂ (dC_mem_H j (c j)) hL, ih, hd]
  exact key _

end H

end CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis
