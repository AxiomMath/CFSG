module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSplitFour
public import CFSG.LocalAnalysis.ComponentInitial.SimpleOrder33792
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorOrthogonal

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

variable {k : Type} [Field k] [Finite k]

omit [Finite k] in
theorem transpose_inv_eq_of_transpose_eq {m : ℕ} {B : GL (Fin m) k}
    (hB : (B : Matrix (Fin m) (Fin m) k)ᵀ = B) :
    ((B⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)ᵀ = (B⁻¹ : GL (Fin m) k) := by
  set Rm : Matrix (Fin m) (Fin m) k := ((B⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) with hRm
  set Bm : Matrix (Fin m) (Fin m) k := (B : Matrix (Fin m) (Fin m) k) with hBm
  have hBR : Bm * Rm = 1 := by
    rw [hBm, hRm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc Rmᵀ = Rmᵀ * (Bm * Rm) := by rw [hBR, Matrix.mul_one]
    _ = (Bm * Rm)ᵀ * Rm := by rw [transpose_mul, hB, Matrix.mul_assoc]
    _ = Rm := by rw [hBR, transpose_one, Matrix.one_mul]

omit [Finite k] in
theorem matrixOrthogonalEquiv_mulVec {m : ℕ} (hk2 : ringChar k ≠ 2) (R : GL (Fin m) k)
    (hR : (R : Matrix (Fin m) (Fin m) k)ᵀ = R)
    (g : TauCeti.QuadraticMap.orthogonalGroup (CatalogueBLinearHigherB.matrixQuadraticForm R))
    (v : Fin m → k) :
    (((matrixOrthogonalEquiv hk2 R hR g : GL (Fin m) k)) : Matrix (Fin m) (Fin m) k) *ᵥ v =
      g.val v := by
  have h := CatalogueBAlternatingIsometry.basisMatrixEquiv_mulVec (Pi.basisFun k (Fin m))
    g.val v
  rw [Pi.basisFun_equivFun] at h
  exact h

theorem not_commute_of_isQuasisimple {G : Type*} [Group G] {X : Subgroup G}
    (hX : CFSG.Assembly.IsQuasisimple X) : ¬ ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
  intro h
  have hq := (AssemblyBPredicates.isQuasisimple_iff_native X).1 hX
  have : Nontrivial X := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have : Group.IsPerfect X := hq.1
  have hcomm : ∀ a b : X, a * b = b * a := fun a b => Subtype.ext (h a a.2 b b.2)
  exact Group.IsPerfect.not_isSolvable X (Group.isSolvable_of_comm hcomm)

variable {A : Type} [Group A] {a : A} {L : Subgroup A}

theorem split_four_case_false [Finite A] {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hk : Nat.card k = ℓ ^ e) {ρ : A →* MulAut (projectiveSL 4 k)} (hinj : Function.Injective ρ)
    (hinn : OuterAutomorphisms.inner (projectiveSL 4 k) ≤ ρ.range)
    (hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {ρ a}))
    {B : GL (Fin 4) k} (hρa : ρ a = conjAut 4 k B * dualAut 4 k)
    (hB : (B : Matrix (Fin 4) (Fin 4) k)ᵀ = B)
    (hsplit : ∃ S : Submodule k (Fin 4 → k), Module.finrank k S = 2 ∧
      ∀ x ∈ S, CatalogueBLinearHigherB.matrixQuadraticForm B⁻¹ x = 0)
    (hstd : IsStandardSubgroup L) : False := by
  classical
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k ℓ]; exact hℓ2
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (hℓ.odd_of_ne_two hℓ2).pow
  rw [hρa] at hL₁
  obtain ⟨hXh, hmap, -⟩ := graph_component_lift (by norm_num) B hL₁
  set Xh := ⁅(L.map ρ).comap (conjAut 4 k), (L.map ρ).comap (conjAut 4 k)⁆ with hXhdef
  set R : GL (Fin 4) k := B⁻¹ with hRdef
  set O := CatalogueBGraphForm.isometryGroup 4 k R with hOdef
  have hR : (R : Matrix (Fin 4) (Fin 4) k)ᵀ = R := transpose_inv_eq_of_transpose_eq hB
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm R with hQdef
  have hQ : Q.polarBilin.Nondegenerate :=
    CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hk2 R hR
  have hdim : Module.finrank k (Fin 4 → k) = 4 := Module.finrank_fin_fun k
  set eO := matrixOrthogonalEquiv hk2 R hR with heO
  set f : TauCeti.QuadraticMap.orthogonalGroup Q →* GL (Fin 4) k :=
    O.subtype.comp eO.toMonoidHom with hf
  have hfi : Function.Injective f := O.subtype_injective.comp eO.injective
  have hfr : (⊤ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)).map f = O := by
    rw [← MonoidHom.range_eq_map, hf, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr
      eO.surjective, ← MonoidHom.range_eq_map, range_subtype]
  have hcov := orthogonal_low_dimensional_fixed_derived_component_coverage Q hQ
    (Or.inr (Or.inr ⟨hdim, hsplit⟩))
  have hXq := (AssemblyBPredicates.isQuasisimple_iff_native Xh).1 hXh.2.2
  by_cases hq3 : Nat.card k = 3
  ·
    obtain ⟨hexc, -⟩ := hcov
    obtain ⟨hprime, -⟩ := hexc (Or.inr ⟨⟨hdim, hsplit⟩, Or.inr hq3⟩)
    have : Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) :=
      isSolvable_of_prime_dvd_card_eq_or_eq hprime
    have : Group.IsSolvable O :=
      Group.isSolvable_of_isSolvable_injective (f := eO.symm.toMonoidHom) eO.symm.injective
    have : Group.IsSolvable Xh :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hXh.1)
        (Subgroup.inclusion_injective hXh.1)
    have : Nontrivial Xh := CFSG.LocalCores.isQuasisimple_nontrivial hXq
    have : Group.IsPerfect Xh := hXq.1
    exact Group.IsPerfect.not_isSolvable Xh inferInstance
  have hq2 : Nat.card k ≠ 2 := by
    intro h
    rw [h] at hodd
    exact (Nat.not_odd_iff_even.mpr even_two) hodd
  have hq5 : 5 ≤ Nat.card k := by
    have h1 : 2 ≤ Nat.card k := by
      rw [hk]
      exact hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
    have h4 : Nat.card k ≠ 4 := fun h => by
      rw [h] at hodd
      exact (Nat.not_odd_iff_even.mpr (by decide)) hodd
    omega
  obtain ⟨-, -, -, hsplitm, -, -, -⟩ := hcov
  obtain ⟨ψ, e, -, hψe, hsup, hq₁, hq₂, hn₁, hn₂, -⟩ := hsplitm hdim hsplit hq2 hq3
  have hfe : ∀ d : DeterminantIsometries k, f (e.symm d) = linearConjGL ψ d.val := by
    intro d
    apply eq_of_mulVec_eq
    intro v
    rw [linearConjGL_mulVec]
    change ((eO (e.symm d) : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) *ᵥ v = _
    rw [matrixOrthogonalEquiv_mulVec]
    have h1 := hψe (e.symm d) (ψ v)
    rw [MulEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h1
    rw [h1, LinearEquiv.symm_apply_apply]
  have hL₁r : ((determinantLeftFactor k).map e.symm.toMonoidHom).map f =
      (splitLeftHom ψ).range := by
    rw [determinantLeftFactor, MonoidHom.range_eq_map, Subgroup.map_map, Subgroup.map_map,
      MonoidHom.range_eq_map]
    congr 1
    ext U : 1
    exact hfe _
  have hL₂r : ((determinantRightFactor k).map e.symm.toMonoidHom).map f =
      (splitRightHom ψ).range := by
    rw [determinantRightFactor, MonoidHom.range_eq_map, Subgroup.map_map, Subgroup.map_map,
      MonoidHom.range_eq_map]
    congr 1
    ext W : 1
    exact hfe _
  have hcomp : ∀ M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q),
      CFSG.IsQuasisimple M → M ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) →
      (M.subgroupOf (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))).Normal →
      CFSG.Assembly.IsComponentOf (M.map f) O := by
    intro M hMq hMle hMn
    have hM : CFSG.Assembly.IsComponentOf M ⊤ := by
      refine ⟨le_top, CFSG.Assembly.IsSubnormal.step hMle hMn
        (CFSG.Assembly.IsSubnormal.step le_top ?_ (CFSG.Assembly.IsSubnormal.refl _)),
        (AssemblyBPredicates.isQuasisimple_iff_native M).2 hMq⟩
      exact Subgroup.Normal.subgroupOf inferInstance _
    have := SymmetricLocal.isComponentOf_map_of_injective f hfi hM
    rwa [hfr] at this
  have hc₁ := hcomp _ hq₁ (hsup ▸ le_sup_left) hn₁
  have hc₂ := hcomp _ hq₂ (hsup ▸ le_sup_right) hn₂
  rw [hL₁r] at hc₁
  rw [hL₂r] at hc₂
  have hcommO : (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).map f = ⁅O, O⁆ := by
    rw [hf, ← Subgroup.map_map, ← Subgroup.map_subtype_commutator]
    congr 1
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ eO.surjective]
  have hD : ⁅O, O⁆ = (splitLeftHom ψ).range ⊔ (splitRightHom ψ).range := by
    rw [← hcommO, hsup, Subgroup.map_sup, hL₁r, hL₂r]
  have hXhD : Xh ≤ ⁅O, O⁆ := by
    have : Group.IsPerfect Xh := ⟨hXh.2.2.1⟩
    rw [← Subgroup.commutator_eq_self (H := Xh)]
    exact Subgroup.commutator_mono hXh.1 hXh.1
  have hX : Xh = (splitLeftHom ψ).range ∨ Xh = (splitRightHom ψ).range := by
    rcases isComponentOf_eq_or_commute hXh hc₁ with h1 | h1
    · exact Or.inl h1
    rcases isComponentOf_eq_or_commute hXh hc₂ with h2 | h2
    · exact Or.inr h2
    exfalso
    have h1' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
    have h2' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2
    refine not_commute_of_isQuasisimple hXh.2.2 fun x hx y hy => ?_
    have hle : (splitLeftHom ψ).range ⊔ (splitRightHom ψ).range ≤ centralizer {x} :=
      sup_le (fun z hz => mem_centralizer_singleton_iff.mpr
          ((mem_centralizer_iff.mp (h1' hx)) z hz))
        (fun z hz => mem_centralizer_singleton_iff.mpr
          ((mem_centralizer_iff.mp (h2' hx)) z hz))
    have hy' := hle (hD ▸ hXhD hy)
    exact (mem_centralizer_singleton_iff.mp hy').symm
  have hLX : L.map ρ = Xh.map (conjAut 4 k) := hmap.symm
  rcases hX with h | h
  · rw [h] at hLX
    exact not_isStandardSubgroup_of_splitLeft ψ hodd hq5 hinj hinn hLX hstd
  · rw [h] at hLX
    exact not_isStandardSubgroup_of_splitRight ψ hodd hq5 hinj hinn hLX hstd

end CFSG.ComponentClassification.OddSelector
