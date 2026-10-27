module

public import CFSG.LieType.Sp6Spin.Model
public import CFSG.LieType.Sp6Spin.Signs

public section

namespace CFSG.LieType.Sp6Spin

open CFSG.StandardType CFSG.StandardType.Triality CFSG.LieType.D4Small
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LieType.Universal.Spin (toStdD)
open CFSG.LieType.Universal.Symplectic CFSG.Assembly.LowTwoRank TauCeti.GLSymplecticFin
  QuadraticMap
open scoped Matrix

@[expose] def fr (σ : Fin 3 → Bool) : Fin 4 × Bool :=
  (if σ 1 = σ 2 then (if σ 0 = σ 1 then 1 else 0) else if σ 0 = σ 1 then 2 else 3,
    (σ 0 && σ 1) || (σ 1 && σ 2) || (σ 0 && σ 2))

noncomputable abbrev pv (K : Type) [Field K] (σ : Fin 3 → Bool) : Fin (2 * 4) → K :=
  AutOm.pvec (fr σ).1 (fr σ).2

variable {K : Type} [Field K]

private theorem fr_dual_iff (σ τ : Fin 3 → Bool) :
    ((fr σ).1 = (fr τ).1 ∧ (fr σ).2 = !(fr τ).2) ↔ τ = (fun i => !σ i) := by
  revert σ τ
  decide

theorem polar_pv (σ τ : Fin 3 → Bool) :
    polar (coordinateQuadPlus 4 K) (pv K σ) (pv K τ) = if τ = (fun i => !σ i) then 1 else 0 := by
  rw [AutOm.polar_pvec]
  by_cases hτ : τ = (fun i => !σ i)
  · rw [if_pos ((fr_dual_iff σ τ).2 hτ), if_pos hτ]
  · rw [if_neg (fun hc => hτ ((fr_dual_iff σ τ).1 hc)), if_neg hτ]

private theorem linearIndependent_frame {V : Type} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (v : (Fin 3 → Bool) → V)
    (hpol : ∀ σ τ, polar Q (v σ) (v τ) = if τ = (fun i => !σ i) then 1 else 0) :
    LinearIndependent K v := by
  rw [linearIndependent_iff']
  intro s g hsum τ hτ
  have hnot : ∀ i : Fin 3 → Bool, ((fun j => !τ j) = (fun j => !i j)) ↔ i = τ := by
    intro i
    constructor
    · intro h'
      funext j
      have hj := congrFun h' j
      simpa using hj.symm
    · rintro rfl
      rfl
  have h := congrArg (fun x => polar Q x (v (fun i => !τ i))) hsum
  rw [QuadraticMap.polar_zero_left] at h
  have hcalc : polar Q (∑ i ∈ s, g i • v i) (v (fun i => !τ i)) =
      ∑ i ∈ s, g i • polar Q (v i) (v (fun i => !τ i)) := by
    rw [← polarBilin_apply_apply, LinearMap.map_sum₂]
    exact Finset.sum_congr rfl fun i _ => by
      rw [polarBilin_apply_apply, QuadraticMap.polar_smul_left]
  rw [hcalc] at h
  simp only [hpol, hnot, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', hτ, if_pos] at h
  exact h

theorem span_eq_top_of_frame {V : Type} [AddCommGroup V] [Module K V]
    (hV : Module.finrank K V = 8) (Q : QuadraticForm K V) (v : (Fin 3 → Bool) → V)
    (hpol : ∀ σ τ, polar Q (v σ) (v τ) = if τ = (fun i => !σ i) then 1 else 0) :
    Submodule.span K (Set.range v) = ⊤ := by
  have hcard : Fintype.card (Fin 3 → Bool) = Module.finrank K V := by
    rw [hV]
    norm_num [Fintype.card_fun]
  exact (linearIndependent_frame Q v hpol).span_eq_top_of_card_eq_finrank hcard

theorem exists_isometry_of_frame {V : Type} [AddCommGroup V] [Module K V]
    (hV : Module.finrank K V = 8) (Q : QuadraticForm K V) (v : (Fin 3 → Bool) → V)
    (hQ : ∀ σ, Q (v σ) = 0)
    (hpol : ∀ σ τ, polar Q (v σ) (v τ) = if τ = (fun i => !σ i) then 1 else 0) :
    ∃ e : V ≃ₗ[K] (Fin (2 * 4) → K), (∀ σ, e (v σ) = pv K σ) ∧
      ∀ w, coordinateQuadPlus 4 K (e w) = Q w := by
  have hli : LinearIndependent K v := linearIndependent_frame Q v hpol
  have hli' : LinearIndependent K (pv K : (Fin 3 → Bool) → Fin (2 * 4) → K) :=
    linearIndependent_frame (coordinateQuadPlus 4 K) (pv K)
      (fun σ τ => polar_pv σ τ)
  have hcard : Fintype.card (Fin 3 → Bool) = Module.finrank K V := by
    rw [hV]
    norm_num [Fintype.card_fun]
  have hcard' : Fintype.card (Fin 3 → Bool) = Module.finrank K (Fin (2 * 4) → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    norm_num [Fintype.card_fun]
  let bm := basisOfLinearIndependentOfCardEqFinrank hli hcard
  let bm' := basisOfLinearIndependentOfCardEqFinrank hli' hcard'
  have hbm : ∀ σ, bm σ = v σ :=
    fun σ => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli hcard) σ
  have hbm' : ∀ σ, bm' σ = pv K σ :=
    fun σ => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli' hcard') σ
  refine ⟨bm.equiv bm' (Equiv.refl (Fin 3 → Bool)), ?_, ?_⟩
  · intro σ
    rw [← hbm σ, Module.Basis.equiv_apply, Equiv.refl_apply, hbm']
  · intro w
    let l := bm.repr w
    have hw : w = (Finsupp.linearCombination K ⇑bm) l :=
      (Module.Basis.linearCombination_repr bm w).symm
    have hew : (bm.equiv bm' (Equiv.refl (Fin 3 → Bool))) w =
        (Finsupp.linearCombination K ⇑bm') l := by
      rw [hw]
      change ((bm.equiv bm' (Equiv.refl (Fin 3 → Bool))).toLinearMap :
        V →ₗ[K] (Fin (2 * 4) → K)) ((Finsupp.linearCombination K ⇑bm) l) = _
      rw [Finsupp.apply_linearCombination]
      rw [show ((↑(bm.equiv bm' (Equiv.refl (Fin 3 → Bool))) :
          V →ₗ[K] (Fin (2 * 4) → K)) ∘ ⇑bm) = ⇑bm' from by
        funext σ
        change ⇑((bm.equiv bm' (Equiv.refl (Fin 3 → Bool))).toLinearMap) (bm σ) = bm' σ
        rw [LinearEquiv.coe_toLinearMap, Module.Basis.equiv_apply, Equiv.refl_apply]]
    have hq : (Q ∘ ⇑bm) = ((coordinateQuadPlus 4 K) ∘ ⇑bm') := by
      funext σ
      simp only [Function.comp_apply]
      rw [hbm, hbm', hQ]
      exact (AutOm.form_pvec (K := K) (fr σ).1 (fr σ).2).symm
    have hp : (polarSym2 Q ∘ Sym2.map ⇑bm) =
        (polarSym2 (coordinateQuadPlus 4 K) ∘ Sym2.map ⇑bm') := by
      funext p
      induction p using Sym2.ind with
      | h a b =>
        simp only [Function.comp_apply, Sym2.map_mk, polarSym2_sym2Mk, hbm, hbm']
        rw [hpol, polar_pv]
    calc coordinateQuadPlus 4 K ((bm.equiv bm' (Equiv.refl (Fin 3 → Bool))) w)
        = coordinateQuadPlus 4 K ((Finsupp.linearCombination K ⇑bm') l) := by rw [hew]
      _ = Finsupp.linearCombination K (polarSym2 (coordinateQuadPlus 4 K) ∘ Sym2.map ⇑bm')
            l.sym2Mul -
            Finsupp.linearCombination K ((coordinateQuadPlus 4 K) ∘ ⇑bm') (l * l) :=
          QuadraticMap.apply_linearCombination' (coordinateQuadPlus 4 K) l
      _ = Finsupp.linearCombination K (polarSym2 Q ∘ Sym2.map ⇑bm) l.sym2Mul -
            Finsupp.linearCombination K (Q ∘ ⇑bm) (l * l) := by rw [← hp, ← hq]
      _ = Q ((Finsupp.linearCombination K ⇑bm) l) :=
          (QuadraticMap.apply_linearCombination' Q l).symm
      _ = Q w := by rw [hw]

variable [Finite K] [CharP K 2]

omit [Finite K] in
private theorem X8_action_of_frame {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (h : toStdD 4 γ = lv i j s t) {α : Fin 3 → ℤ}
    (hc : ∀ σ : Fin 3 → Bool,
      (IsSrc α σ ↔ fr σ = (j, !t) ∨ fr σ = (i, !s)) ∧
      (fr σ = (j, !t) → fr (flipAt α σ) = (i, s)) ∧
      (fr σ = (i, !s) → fr (flipAt α σ) = (j, t)))
    (d : K) (σ : Fin 3 → Bool) :
    ((X8 γ d : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ pv K σ =
      pv K σ + if IsSrc α σ then d • pv K (flipAt α σ) else 0 := by
  rw [X8_mulVec_pvec hij h]
  by_cases h1 : fr σ = (j, !t)
  · have h1' : (fr σ).1 = j ∧ (fr σ).2 = !t := Prod.ext_iff.1 h1
    have hsrc : IsSrc α σ := (hc σ).1.2 (Or.inl h1)
    have h2' : ¬ ((fr σ).1 = i ∧ (fr σ).2 = !s) := by
      rintro ⟨h1i, h2i⟩
      have h2 : fr σ = (i, !s) := Prod.ext_iff.2 ⟨h1i, h2i⟩
      have hji : j = i := congrArg Prod.fst (h1.symm.trans h2)
      exact hij hji.symm
    have hflip : pv K (flipAt α σ) = AutOm.pvec i s := by
      change AutOm.pvec (fr (flipAt α σ)).1 (fr (flipAt α σ)).2 = AutOm.pvec i s
      rw [(hc σ).2.1 h1]
    rw [if_pos h1', if_neg h2', if_pos hsrc, hflip]
    simp
  · by_cases h2 : fr σ = (i, !s)
    · have h2' : (fr σ).1 = i ∧ (fr σ).2 = !s := Prod.ext_iff.1 h2
      have hsrc : IsSrc α σ := (hc σ).1.2 (Or.inr h2)
      have h1' : ¬ ((fr σ).1 = j ∧ (fr σ).2 = !t) := by
        rintro ⟨h1j, h2j⟩
        have h1 : fr σ = (j, !t) := Prod.ext_iff.2 ⟨h1j, h2j⟩
        have hji : i = j := congrArg Prod.fst (h2.symm.trans h1)
        exact hij hji
      have hflip : pv K (flipAt α σ) = AutOm.pvec j t := by
        change AutOm.pvec (fr (flipAt α σ)).1 (fr (flipAt α σ)).2 = AutOm.pvec j t
        rw [(hc σ).2.2 h2]
      rw [if_neg h1', if_pos h2', if_pos hsrc, hflip]
      simp
    · have hsrc : ¬ IsSrc α σ := by
        intro hs
        rcases (hc σ).1.1 hs with h | h
        · exact h1 h
        · exact h2 h
      have h1' : ¬ ((fr σ).1 = j ∧ (fr σ).2 = !t) := fun hc' => h1 (Prod.ext_iff.2 hc')
      have h2' : ¬ ((fr σ).1 = i ∧ (fr σ).2 = !s) := fun hc' => h2 (Prod.ext_iff.2 hc')
      rw [if_neg h1', if_neg h2', if_neg hsrc]
      simp

private theorem X8_fromStd_mem_spinSeven {i j : Fin 4} {s t : Bool} (hij : i ≠ j)
    (hdata : ∃ i' j' : Fin 4, ∃ s' t' : Bool, i' ≠ j' ∧ i' ≠ 0 ∧ j' ≠ 0 ∧
      toStdD 4 (tri (tri (fromStd (lv i j s t)))) = lv i' j' s' t')
    (d : K) : X8 (fromStd (lv i j s t)) d ∈ spinSeven K := by
  obtain ⟨i', j', s', t', hij', hi', hj', h'⟩ := hdata
  have hγ : fromStd (lv i j s t) ∈ rootsD4 :=
    mem_rootsD4_iff.2 ⟨i, j, hij, s, t, (roots_check i j s t hij).1⟩
  have hγ' : tri (tri (fromStd (lv i j s t))) ∈ rootsD4 :=
    tri_mem_roots (tri_mem_roots hγ)
  have hfix : X8 (tri (tri (fromStd (lv i j s t)))) d ∈ fixRho K :=
    X8_mem_fixRho hij' h' hi' hj' d
  have htheta : theta (X8 (tri (tri (fromStd (lv i j s t)))) d) =
      X8 (fromStd (lv i j s t)) d := by
    rw [theta_X8 hγ' d, tri_tri_tri]
  rw [spinSeven_eq, ← htheta]
  exact Subgroup.mem_map_of_mem _ hfix

private theorem exists_X8_of_data {i j : Fin 4} {s t : Bool} (hij : i ≠ j) (α : Fin 3 → ℤ)
    (hI : ∃ i' j' : Fin 4, ∃ s' t' : Bool, i' ≠ j' ∧ i' ≠ 0 ∧ j' ≠ 0 ∧
      toStdD 4 (tri (tri (fromStd (lv i j s t)))) = lv i' j' s' t')
    (hA : ∀ σ : Fin 3 → Bool,
      (IsSrc α σ ↔ fr σ = (j, !t) ∨ fr σ = (i, !s)) ∧
      (fr σ = (j, !t) → fr (flipAt α σ) = (i, s)) ∧
      (fr σ = (i, !s) → fr (flipAt α σ) = (j, t))) :
    ∃ γ : Fin 4 → ℤ, (∀ d : K, X8 γ d ∈ spinSeven K) ∧
      ∀ (d : K) (σ : Fin 3 → Bool),
        ((X8 γ d : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ pv K σ =
          pv K σ + if IsSrc α σ then d • pv K (flipAt α σ) else 0 :=
  ⟨fromStd (lv i j s t), fun d => X8_fromStd_mem_spinSeven hij hI d,
    fun d σ => X8_action_of_frame hij (roots_check i j s t hij).1 hA d σ⟩

private theorem exists_X8_difference {i j : Fin 3} (hij : i ≠ j) :
    ∃ γ : Fin 4 → ℤ, (∀ d : K, X8 γ d ∈ spinSeven K) ∧
      ∀ (d : K) (σ : Fin 3 → Bool),
        ((X8 γ d : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ pv K σ =
          pv K σ + if IsSrc (stdVec (.difference i j hij)) σ then
            d • pv K (flipAt (stdVec (.difference i j hij)) σ) else 0 := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact exists_X8_of_data (i := (0 : Fin 4)) (j := (3 : Fin 4)) (s := false) (t := true)
      (by decide) (stdVec (.difference (0 : Fin 3) 1 (by decide))) (by decide) (by decide)
  · exact exists_X8_of_data (i := (0 : Fin 4)) (j := (2 : Fin 4)) (s := false) (t := true)
      (by decide) (stdVec (.difference (0 : Fin 3) 2 (by decide))) (by decide) (by decide)
  · exact exists_X8_of_data (i := (0 : Fin 4)) (j := (3 : Fin 4)) (s := true) (t := false)
      (by decide) (stdVec (.difference (1 : Fin 3) 0 (by decide))) (by decide) (by decide)
  · exact (hij rfl).elim
  · exact exists_X8_of_data (i := (2 : Fin 4)) (j := (3 : Fin 4)) (s := true) (t := false)
      (by decide) (stdVec (.difference (1 : Fin 3) 2 (by decide))) (by decide) (by decide)
  · exact exists_X8_of_data (i := (0 : Fin 4)) (j := (2 : Fin 4)) (s := true) (t := false)
      (by decide) (stdVec (.difference (2 : Fin 3) 0 (by decide))) (by decide) (by decide)
  · exact exists_X8_of_data (i := (2 : Fin 4)) (j := (3 : Fin 4)) (s := false) (t := true)
      (by decide) (stdVec (.difference (2 : Fin 3) 1 (by decide))) (by decide) (by decide)
  · exact (hij rfl).elim

private theorem exists_X8_positiveSum {i j : Fin 3} (hij : i < j) :
    ∃ γ : Fin 4 → ℤ, (∀ d : K, X8 γ d ∈ spinSeven K) ∧
      ∀ (d : K) (σ : Fin 3 → Bool),
        ((X8 γ d : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ pv K σ =
          pv K σ + if IsSrc (stdVec (.positiveSum i j hij)) σ then
            d • pv K (flipAt (stdVec (.positiveSum i j hij)) σ) else 0 := by
  fin_cases i <;> fin_cases j
  · exact absurd hij (by decide)
  · exact exists_X8_of_data (i := (1 : Fin 4)) (j := (2 : Fin 4)) (s := true) (t := true)
      (by decide) (stdVec (.positiveSum (0 : Fin 3) 1 (by decide))) (by decide) (by decide)
  · exact exists_X8_of_data (i := (1 : Fin 4)) (j := (3 : Fin 4)) (s := true) (t := true)
      (by decide) (stdVec (.positiveSum (0 : Fin 3) 2 (by decide))) (by decide) (by decide)
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)
  · exact exists_X8_of_data (i := (0 : Fin 4)) (j := (1 : Fin 4)) (s := true) (t := true)
      (by decide) (stdVec (.positiveSum (1 : Fin 3) 2 (by decide))) (by decide) (by decide)
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)

private theorem exists_X8_negativeSum {i j : Fin 3} (hij : i < j) :
    ∃ γ : Fin 4 → ℤ, (∀ d : K, X8 γ d ∈ spinSeven K) ∧
      ∀ (d : K) (σ : Fin 3 → Bool),
        ((X8 γ d : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ pv K σ =
          pv K σ + if IsSrc (stdVec (.negativeSum i j hij)) σ then
            d • pv K (flipAt (stdVec (.negativeSum i j hij)) σ) else 0 := by
  fin_cases i <;> fin_cases j
  · exact absurd hij (by decide)
  · exact exists_X8_of_data (i := (1 : Fin 4)) (j := (2 : Fin 4)) (s := false) (t := false)
      (by decide) (stdVec (.negativeSum (0 : Fin 3) 1 (by decide))) (by decide) (by decide)
  · exact exists_X8_of_data (i := (1 : Fin 4)) (j := (3 : Fin 4)) (s := false) (t := false)
      (by decide) (stdVec (.negativeSum (0 : Fin 3) 2 (by decide))) (by decide) (by decide)
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)
  · exact exists_X8_of_data (i := (0 : Fin 4)) (j := (1 : Fin 4)) (s := false) (t := false)
      (by decide) (stdVec (.negativeSum (1 : Fin 3) 2 (by decide))) (by decide) (by decide)
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)

theorem exists_X8_short (r : RootSubgroupIndex 3) (hr : IsShortIndex r) :
    ∃ γ : Fin 4 → ℤ, (∀ d : K, X8 γ d ∈ spinSeven K) ∧ ∀ (d : K) (σ : Fin 3 → Bool),
      ((X8 γ d : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ pv K σ =
        pv K σ + if IsSrc (stdVec r) σ then d • pv K (flipAt (stdVec r) σ) else 0 := by
  rcases r with i | i | ⟨i, j, hij⟩ | ⟨i, j, hij⟩ | ⟨i, j, hij⟩
  · exact hr.elim
  · exact hr.elim
  · exact exists_X8_difference hij
  · exact exists_X8_positiveSum hij
  · exact exists_X8_negativeSum hij

omit [Finite K] in
private theorem X8_rootA_rootD_pv (d : K) (σ : Fin 3 → Bool) :
    ((X8 rootA d : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
      (((X8 rootD d : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
        pv K σ) =
      pv K σ + if σ 2 = false then d • pv K (Function.update σ 2 true) else 0 := by
  rcases h0 : σ 0 with _ | _ <;> rcases h1 : σ 1 with _ | _ <;> rcases h2 : σ 2 with _ | _
  all_goals
    rw [X8_mulVec_pvec (i := 0) (j := 3) (s := true) (t := true) (by decide) toStdD_rootD d]
    simp only [h0, h1, h2, fr]
    simp
    repeat rw [Matrix.mulVec_add]
    repeat rw [Matrix.mulVec_smul]
    simp only [X8_mulVec_pvec (i := 1) (j := 2) (s := true) (t := false) (by decide)
      toStdD_rootA d]
    simp [pv, fr, h0, h1, h2, Function.update]

theorem theta_Y_mulVec (d : K) (σ : Fin 3 → Bool) :
    ((theta (Y d) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ pv K σ =
      pv K σ + if σ 2 = false then d • pv K (Function.update σ 2 true) else 0 := by
  rw [theta_Y]
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [← Matrix.mulVec_mulVec]
  exact X8_rootA_rootD_pv d σ

theorem theta_Y_mem (d : K) : theta (Y d) ∈ spinSeven K := by
  rw [spinSeven_eq]
  exact Subgroup.mem_map_of_mem _ (Y_mem_fixRho d)

end CFSG.LieType.Sp6Spin
