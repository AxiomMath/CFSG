module

public import CFSG.RankThree.PartTwo.Census.LinearRank

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.LargeEvenClassification.Helpers CFSG.RankThree.PartTwo.Census

universe u v w

theorem three_le_finrank_of_dvd_card_linearEquiv {K : Type u} [Field K] [Finite K] {S : Type w}
    [AddCommGroup S] [Module K S] [FiniteDimensional K S] {p : ℕ} (hp : p.Prime)
    (hpK : ¬ p ∣ Nat.card K) (h1 : ¬ p ∣ Nat.card K - 1) (h2 : ¬ p ∣ Nat.card K ^ 2 - 1)
    (hdvd : p ∣ Nat.card (S ≃ₗ[K] S)) : 3 ≤ Module.finrank K S := by
  classical
  by_contra hlt
  push Not at hlt
  have hcard : Nat.card (S ≃ₗ[K] S) = Nat.card (Matrix.GeneralLinearGroup (Fin (Module.finrank K S)) K) := by
    let basis := Module.finBasis K S
    let equivalence := (Matrix.GeneralLinearGroup.toLin' basis).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K S)
    exact (Nat.card_congr equivalence.toEquiv).symm
  have : Fintype K := Fintype.ofFinite K
  rw [hcard, Matrix.card_GL_field, ← Nat.card_eq_fintype_card] at hdvd
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hdvd
  have hfac : Nat.card K ^ Module.finrank K S - Nat.card K ^ (i : ℕ) =
      Nat.card K ^ (i : ℕ) * (Nat.card K ^ (Module.finrank K S - i) - 1) := by
    have hle : (i : ℕ) ≤ Module.finrank K S := i.2.le
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hle]
  rw [hfac] at hi
  rcases hp.dvd_mul.1 hi with hi | hi
  · exact hpK (hp.dvd_of_dvd_pow hi)
  · have hd : Module.finrank K S - i < 3 := by omega
    have hpos : 0 < Module.finrank K S - i := by have := i.2; omega
    interval_cases hj : Module.finrank K S - i
    · exact h1 (by simpa using hi)
    · exact h2 hi

theorem card_le_pow_div_three_of_faithful_module {K : Type u} [Field K] [Finite K] {A : Type v}
    [CommGroup A] [Finite A] (V : Type w) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (MonoidAlgebra K A) V] [IsScalarTower K (MonoidAlgebra K A) V] {p : ℕ}
    (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K) (h1 : ¬ p ∣ Nat.card K - 1)
    (h2 : ¬ p ∣ Nat.card K ^ 2 - 1) (hexp : ∀ a : A, a ^ p = 1)
    (hinjective : Function.Injective
      (groupAlgebraModuleAction (ScalarField := K) (Acting := A) V)) :
    Nat.card A ≤ p ^ (Module.finrank K V / 3) := by
  classical
  have hpK' : (p : K) ≠ 0 := by
    intro h
    have hdvd : ringChar K ∣ p := (CharP.cast_eq_zero_iff K (ringChar K) p).1 h
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, hpr, hcard⟩ := FiniteField.card K (ringChar K)
    have hrp : ringChar K = p := (Nat.prime_dvd_prime_iff_eq hpr hp).1 hdvd
    exact hpK (by rw [Nat.card_eq_fintype_card, hcard, ← hrp]; exact dvd_pow_self _ n.ne_zero)
  obtain ⟨r, hr⟩ := exists_card_eq_pow_of_exponent hp hexp
  have : NeZero (Nat.card A : K) := ⟨by rw [hr, Nat.cast_pow]; exact pow_ne_zero r hpK'⟩
  obtain ⟨count, summands, equivalence, hsimple, hdimension⟩ :=
    maschke_decomposition (K := K) (A := A) V
  have : ∀ i, IsSimpleModule (MonoidAlgebra K A) (summands i) := hsimple
  let actions := fun i =>
    groupAlgebraModuleAction (ScalarField := K) (Acting := A) (summands i)
  have : ∀ i, Finite (actions i).range := fun i =>
    Finite.of_surjective (actions i).rangeRestrict (actions i).rangeRestrict_surjective
  have : ∀ i, Module.Finite K (summands i) := fun i =>
    Module.Finite.of_injective (((summands i).subtype).restrictScalars K) Subtype.val_injective
  have hbound : ∀ i, Nat.card (actions i).range ≤ p ^ (Module.finrank K (summands i) / 3) := by
    intro i
    have : IsCyclic (actions i).range := simple_groupAlgebra_action_cyclic (summands i)
    have hdvd := cyclic_action_card_dvd_exponent (actions i) hexp
    by_cases hone : Nat.card (actions i).range = 1
    · rw [hone]
      exact Nat.one_le_pow _ _ hp.pos
    · have hp' : Nat.card (actions i).range = p := by
        rcases (Nat.dvd_prime hp).1 hdvd with h | h
        · exact absurd h hone
        · exact h
      have hdvd2 : p ∣ Nat.card (summands i ≃ₗ[K] summands i) := by
        rw [← hp']
        exact card_dvd_of_injective_hom (actions i).range.subtype Subtype.val_injective
      have h3 := three_le_finrank_of_dvd_card_linearEquiv hp hpK h1 h2 hdvd2
      rw [hp']
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (Module.finrank K (summands i) / 3) :=
          Nat.pow_le_pow_right hp.pos (by omega)
  let embedding := MonoidHom.pi (fun i => (actions i).rangeRestrict)
  have hembedding : Function.Injective embedding := by
    intro first second heq
    apply hinjective
    ext x
    change (MonoidAlgebra.of K A) first • x = (MonoidAlgebra.of K A) second • x
    apply equivalence.injective
    rw [equivalence.map_smul, equivalence.map_smul]
    apply DFinsupp.ext
    intro i
    have hcomponent : actions i first = actions i second :=
      congrArg (fun tuple => (tuple i : summands i ≃ₗ[K] summands i)) heq
    exact congrArg (fun automorphism : summands i ≃ₗ[K] summands i =>
      automorphism (equivalence x i)) hcomponent
  have hsum : ∑ i, Module.finrank K (summands i) / 3 ≤ Module.finrank K V / 3 := by
    rw [Nat.le_div_iff_mul_le (by norm_num), hdimension, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => Nat.div_mul_le_self _ _
  calc Nat.card A ≤ Nat.card (∀ i, (actions i).range) :=
        Nat.card_le_card_of_injective embedding hembedding
    _ = ∏ i, Nat.card (actions i).range := Nat.card_pi
    _ ≤ ∏ i, p ^ (Module.finrank K (summands i) / 3) := Finset.prod_le_prod fun i _ => hbound i
    _ = p ^ ∑ i, Module.finrank K (summands i) / 3 := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ p ^ (Module.finrank K V / 3) := Nat.pow_le_pow_right hp.pos hsum

theorem card_le_pow_div_three_of_faithful {K : Type u} [Field K] [Finite K] {A : Type v}
    [CommGroup A] [Finite A] {V : Type w} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K) (h1 : ¬ p ∣ Nat.card K - 1)
    (h2 : ¬ p ∣ Nat.card K ^ 2 - 1) (hexp : ∀ a : A, a ^ p = 1)
    (ρ : A →* (V ≃ₗ[K] V)) (hρ : Function.Injective ρ) :
    Nat.card A ≤ p ^ (Module.finrank K V / 3) := by
  let representation := linearActionRepresentation ρ
  have : FiniteDimensional K representation.asModule :=
    LinearEquiv.finiteDimensional representation.asModuleEquiv.symm
  have hmoduleInjective : Function.Injective
      (groupAlgebraModuleAction (ScalarField := K) (Acting := A) representation.asModule) := by
    intro first second heq
    apply hρ
    ext x
    have hfixed := congrArg (fun automorphism : representation.asModule ≃ₗ[K]
        representation.asModule => representation.asModuleEquiv
          (automorphism (representation.asModuleEquiv.symm x))) heq
    change representation.asModuleEquiv ((MonoidAlgebra.of K A) first •
        representation.asModuleEquiv.symm x) =
      representation.asModuleEquiv ((MonoidAlgebra.of K A) second •
        representation.asModuleEquiv.symm x) at hfixed
    rw [representation.asModuleEquiv_map_smul, representation.asModuleEquiv_map_smul,
      representation.asAlgebraHom_of, representation.asAlgebraHom_of,
      representation.asModuleEquiv.apply_symm_apply] at hfixed
    exact hfixed
  have h := card_le_pow_div_three_of_faithful_module representation.asModule hp hpK h1 h2 hexp
    hmoduleInjective
  rwa [representation.asModuleEquiv.finrank_eq] at h

theorem card_le_pow_div_three_of_gl {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K)
    (h1 : ¬ p ∣ Nat.card K - 1) (h2 : ¬ p ∣ Nat.card K ^ 2 - 1)
    (E : Subgroup (Matrix.GeneralLinearGroup ι K))
    (hc : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (he : ∀ g ∈ E, g ^ p = 1) :
    Nat.card E ≤ p ^ (Fintype.card ι / 3) := by
  let _ : CommGroup E := { (inferInstance : Group E) with
    mul_comm := fun a b => Subtype.ext (hc a a.2 b b.2) }
  let ρ : E →* ((ι → K) ≃ₗ[K] (ι → K)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)).toMonoidHom.comp
      (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp E.subtype)
  have hρ : Function.Injective ρ :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)).injective.comp
      (Matrix.GeneralLinearGroup.toLin.injective.comp E.subtype_injective)
  have hexp : ∀ a : E, a ^ p = 1 := fun a => Subtype.ext (he a a.2)
  have h := card_le_pow_div_three_of_faithful hp hpK h1 h2 hexp ρ hρ
  rwa [Module.finrank_fintype_fun_eq_card] at h

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
