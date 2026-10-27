module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

@[expose] def resNonid (A : Type*) [Group A] : MulAut A →* Equiv.Perm {a : A // a ≠ 1} where
  toFun f := Equiv.subtypeEquiv f.toEquiv (fun a => by simp)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem resNonid_injective (A : Type*) [Group A] : Function.Injective (resNonid A) := by
  rw [injective_iff_map_eq_one]
  intro f hf
  ext a
  by_cases ha : a = 1
  · subst ha
    simp
  · have := congrArg (fun σ : Equiv.Perm {a : A // a ≠ 1} => ((σ ⟨a, ha⟩ : {a : A // a ≠ 1}) : A)) hf
    simpa [resNonid] using this

theorem quotient_equiv_perm_of_hom_fin3 {H : Type*} [Group H] [Finite H]
    (f : H →* Equiv.Perm (Fin 3)) {t : H} (ht : f t ≠ 1) (ht2 : t * t = 1) :
    Nonempty (H ⧸ f.ker ≃* Equiv.Perm (Fin 2)) ∨ Nonempty (H ⧸ f.ker ≃* Equiv.Perm (Fin 3)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (f t) = 2 := by
    refine orderOf_eq_prime ?_ ht
    rw [pow_two, ← map_mul, ht2, map_one]
  have hmem : f t ∈ f.range := ⟨t, rfl⟩
  have hdvd2 : 2 ∣ Nat.card f.range := by
    have h1 : orderOf (⟨f t, hmem⟩ : f.range) = 2 := by
      rw [← hord]
      exact (Subgroup.orderOf_coe (⟨f t, hmem⟩ : f.range)).symm
    rw [← h1]
    exact orderOf_dvd_natCard _
  have hS3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hdvd6 : Nat.card f.range ∣ 6 := hS3 ▸ Subgroup.card_subgroup_dvd_card f.range
  have hle : Nat.card f.range ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have hcases : Nat.card f.range = 2 ∨ Nat.card f.range = 6 := by
    generalize Nat.card f.range = n at hdvd2 hdvd6 hle hpos
    interval_cases n <;> simp_all
  rcases hcases with h2 | h6
  · refine Or.inl ⟨(QuotientGroup.quotientKerEquivRange f).trans (mulEquivOfPrimeCardEq (p := 2) h2 ?_)⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  · have htop : f.range = ⊤ := (Subgroup.card_eq_iff_eq_top f.range).1 (by rw [h6, hS3])
    exact Or.inr ⟨(QuotientGroup.quotientKerEquivRange f).trans
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)⟩

theorem quotient_equiv_perm_of_mulAut {H : Type*} [Group H] [Finite H] {A : Type*} [Group A] [Finite A]
    (hA : Nat.card A = 4) (ρ : H →* MulAut A) {t : H}
    (ht : ρ t ≠ 1) (ht2 : t * t = 1) :
    Nonempty (H ⧸ ρ.ker ≃* Equiv.Perm (Fin 2)) ∨ Nonempty (H ⧸ ρ.ker ≃* Equiv.Perm (Fin 3)) := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  have hA' : Fintype.card A = 4 := by rw [← Nat.card_eq_fintype_card, hA]
  have hΩ : Fintype.card {a : A // a ≠ 1} = 3 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hA']
  let e : {a : A // a ≠ 1} ≃ Fin 3 := Fintype.equivFinOfCardEq hΩ
  let φ : MulAut A →* Equiv.Perm (Fin 3) :=
    (e.permCongrHom : Equiv.Perm {a : A // a ≠ 1} ≃* Equiv.Perm (Fin 3)).toMonoidHom.comp (resNonid A)
  have hφ : Function.Injective φ := e.permCongrHom.injective.comp (resNonid_injective A)
  have hker : (φ.comp ρ).ker = ρ.ker := by
    ext h
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, map_eq_one_iff φ hφ]
  have hne : (φ.comp ρ) t ≠ 1 := fun h => ht ((map_eq_one_iff φ hφ).1 h)
  rcases quotient_equiv_perm_of_hom_fin3 (φ.comp ρ) hne ht2 with ⟨⟨e'⟩⟩ | ⟨⟨e'⟩⟩
  · exact Or.inl ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans e'⟩
  · exact Or.inr ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans e'⟩

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
