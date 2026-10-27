module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuBadAux.Cyclic
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuBadAux.CoverLift

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.HardMathSupport.Dickson.Sec6.I923 (exceptionalOrders_psu_eq)

section Abstract

theorem exists_hom_to_cover_of_card {E P Y : Type} [Group E] [Finite E] [Group.IsPerfect E] [Group P]
    [Finite P] [Group Y] (π : E →* P) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hM : Nat.card (hopfMultiplier P) ≠ 0)
    (hcard : Nat.card (hopfMultiplier P) ≤ Nat.card π.ker) (q : Y →* P)
    (hq : Function.Surjective q) (hker : q.ker ≤ Subgroup.center Y) :
    ∃ ρ : E →* Y, ∀ g, q (ρ g) = π g := by
  classical
  haveI : Group.IsPerfect P := Group.IsPerfect.ofSurjective (f := π) hπ
  obtain ⟨-, h, hph, -, hhs, hmap, eM, -⟩ :=
    perfect_central_kernel_quotient_of_hopf_multiplier π hπ hC
  set M := hopfMultiplier P with hMdef
  set N := (h.comp M.subtype).ker with hN
  haveI : Finite M := Nat.finite_of_card_ne_zero hM
  haveI : Finite N := inferInstance
  have hsplit : Nat.card M = Nat.card (M ⧸ N) * Nat.card N :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hquot : Nat.card (M ⧸ N) = Nat.card π.ker := Nat.card_congr eM.toEquiv
  have hpos : 0 < Nat.card π.ker := Nat.card_pos
  have hN1 : Nat.card N = 1 := by
    have hNpos : 0 < Nat.card N := Nat.card_pos
    by_contra hne
    have hgt : 2 ≤ Nat.card N := by omega
    have h2 : Nat.card π.ker * 2 ≤ Nat.card M := by
      rw [hsplit, hquot]
      exact Nat.mul_le_mul_left _ hgt
    omega
  have hNbot : N = ⊥ := Subgroup.card_eq_one.1 hN1
  have hinj : Function.Injective h := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hu' : hopfCoverMap P u = 1 := by
      rw [← hph, MonoidHom.comp_apply, hu, map_one]
    have hmem : (⟨u, hu'⟩ : M) ∈ N := by
      show h (⟨u, hu'⟩ : M) = 1
      exact hu
    rw [hNbot, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  let eh : HopfCover P ≃* E := MulEquiv.ofBijective h ⟨hinj, hhs⟩
  refine ⟨(hopfLift q hq hker).comp eh.symm.toMonoidHom, fun g => ?_⟩
  have h1 : q (hopfLift q hq hker (eh.symm g)) = hopfCoverMap P (eh.symm g) :=
    DFunLike.congr_fun (comp_hopfLift q hq hker) (eh.symm g)
  have h2 : π (h (eh.symm g)) = hopfCoverMap P (eh.symm g) :=
    DFunLike.congr_fun hph (eh.symm g)
  have h3 : h (eh.symm g) = g := eh.apply_symm_apply g
  show q (hopfLift q hq hker (eh.symm g)) = π g
  rw [h1, ← h2, h3]

end Abstract

section Hopf

theorem hopfMultiplier_card_psu (hGA : GriessAllModelsStatement) {X : Type} [Group X] {n p f : ℕ}
    (hm : StatedClassicalModel X .PSU n p f) (h1 : ¬(n = 4 ∧ p = 2 ∧ f = 1))
    (h2 : ¬(n = 6 ∧ p = 2 ∧ f = 1)) (h3 : ¬(n = 4 ∧ p = 3 ∧ f = 1)) :
    Nat.card (hopfMultiplier X) = Nat.gcd n (p ^ f + 1) := by
  obtain ⟨-, ⟨e⟩⟩ := hGA X .PSU n p f ⟨hm.1, Or.inl hm⟩
  have hex := exceptionalOrders_psu_eq h1 h2 h3
  let e' : hopfMultiplier X ≃*
      Multiplier.generic .PSU n p f × Multiplier.exceptional .PSU n p f :=
    (hopfMultiplierEquivGriess X).symm.trans e
  rw [Nat.card_congr e'.toEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod]
  have hg1 : (Multiplier.genericOrders .PSU n p f).1 = Nat.gcd n (p ^ f + 1) := rfl
  have hg2 : (Multiplier.genericOrders .PSU n p f).2 = 1 := rfl
  have hc : ∀ m : ℕ, Nat.card (Multiplicative (ZMod m)) = m := fun m => by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  simp only [Multiplier.generic, Multiplier.exceptional, hc, hg1, hg2, hex]
  simp

variable {p f : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_suHom_to_cover (hGA : GriessAllModelsStatement) {n : ℕ} (h : UnitaryFieldData p f K)
    {X : Type} [Group X] [Finite X] (hm : StatedClassicalModel X .PSU n p f)
    (e0 : X ≃* primeFormP h (idGram K n)) (hn : 5 ≤ n) (h2 : ¬(n = 6 ∧ p = 2 ∧ f = 1)) {Y : Type}
    [Group Y] (q : Y →* X) (hq : Function.Surjective q) (hker : q.ker ≤ Subgroup.center Y) :
    ∃ ρ : gramSU h (idGram K n) →* Y,
      ∀ g, q (ρ g) = e0.symm (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n) g) := by
  classical
  haveI : Finite (GL (Fin n) K) :=
    Finite.of_injective (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) Units.val_injective
  haveI : Group.IsPerfect (gramSU h (idGram K n)) :=
    CFSG.RankThree.Classical.isPerfect_gramSU_one h (by omega) (fun hc => by omega)
  set S := gramSU h (idGram K n) with hS
  set Z := normOneScalars h S n with hZ
  let π : S →* X := e0.symm.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hπ : Function.Surjective π := e0.symm.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hkerπ : π.ker = Z := by
    ext g
    rw [MonoidHom.mem_ker]
    show e0.symm (QuotientGroup.mk' Z g) = 1 ↔ g ∈ Z
    rw [map_eq_one_iff _ e0.symm.injective]
    exact QuotientGroup.eq_one_iff g
  have hC : π.ker ≤ Subgroup.center S := by
    rw [hkerπ]
    exact normOneScalars_le_center h _ n
  have hMcard := hopfMultiplier_card_psu hGA hm (fun hc => by omega) h2 (fun hc => by omega)
  have hZcard : Nat.card Z = Nat.gcd n (p ^ f + 1) :=
    CFSG.RankThree.Classical.card_normOneScalars_one h (by omega)
  have hgpos : 0 < Nat.gcd n (p ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  obtain ⟨ρ, hρ⟩ := exists_hom_to_cover_of_card π hπ hC (by rw [hMcard]; exact hgpos.ne')
    (by rw [hMcard, hkerπ, hZcard]) q hq hker
  exact ⟨ρ, fun g => hρ g⟩

end Hopf

end CFSG.HardMathSupport.Dickson.Sec6.I1431
