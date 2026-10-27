module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleSteps

public noncomputable section

namespace CFSG.ComponentClassification.OutcomeLocal

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open FourGroupEvenCanonical CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem faithful_even_unitary_socle_small_source_involution_selector
    {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
    (hWsimple : IsSimpleGroup W) (hWnonab : ∃ x y : W, x * y ≠ y * x)
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLW : L ≤ W) (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    {p f : ℕ} (_hp : p.Prime) (hp2 : p ≠ 2) (_hf : 1 ≤ f)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2)
    {e n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 e K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ 2 ^ e = 2)) (φ : W ≃* unitaryPSU h n) :
    ∃ ρ : A →* MulAut (unitaryPSU h n), Function.Injective ρ ∧
      (∀ w : W, ρ w = MulAut.conj (φ w)) ∧
      (∀ ρ' : A →* MulAut (unitaryPSU h n), (∀ w : W, ρ' w = MulAut.conj (φ w)) → ρ' = ρ) ∧
      ρ a ∉ inner (unitaryPSU h n) ∧
      ∃ (H₀ C : GL (Fin n) K) (hC : IsPrimeFormGram C),
        ((H₀ : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (H₀ : Matrix (Fin n) (Fin n) K) = C ∧
        ∃ θ : primeFormP h (C : Matrix (Fin n) (Fin n) K) ≃* unitaryPSU h n,
          (∀ (g : gramSU h (C : Matrix (Fin n) (Fin n) K)) (g' : unitarySU 2 e K n),
            (g' : GL (Fin n) K) = H₀ * g * H₀⁻¹ →
              θ (g : primeFormP h (C : Matrix (Fin n) (Fin n) K)) = unitaryProj h n g') ∧
        ∃ ρC : A →* MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)),
          (∀ (t : A) (x : primeFormP h (C : Matrix (Fin n) (Fin n) K)),
            ρC t x = θ.symm (ρ t (θ x))) ∧ Function.Injective ρC ∧
        ∃ σ : K ≃+* K, (∀ x, σ x = h.bar x) ∧ ρC a = primeFormFieldHom h hC σ ∧
        ∃ (Cl : GL (Fin n) h.fixedField)
          (hCl : (Cl : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype = C),
          let γ := primeFormFieldHom h hC σ
          let N := ((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp
            (fixedIsometryHom h hCl)).range
          let N' : Subgroup (MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))) := ⁅N, N⁆
          let B := Matrix.toBilin' (Cl : Matrix (Fin n) (Fin n) h.fixedField)
          let dperp := LinearMap.ker (B fun _ => 1)
          (∀ α : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K)),
            α ∈ centralizer {γ} ↔
              ∃ (g : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField))
                (τ : K ≃+* K), α = primeFormPsi h hC ⟨fixedIsometryHom h hCl g, τ⟩) ∧
          (∀ (g g' : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField))
            (τ τ' : K ≃+* K), primeFormPsi h hC ⟨fixedIsometryHom h hCl g, τ⟩ =
              primeFormPsi h hC ⟨fixedIsometryHom h hCl g', τ'⟩ → g = g' ∧ τ = τ') ∧
          Function.Injective ((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp
            (fixedIsometryHom h hCl)) ∧
          N ≤ inner (primeFormP h (C : Matrix (Fin n) (Fin n) K)) ∧ N ≤ centralizer {γ} ∧
          (N.subgroupOf (centralizer {γ})).Normal ∧
          (centralizer {a}).map ρC = ρC.range ⊓ centralizer {γ} ∧
          (W ⊓ centralizer {a}).map ρC = N ∧
          ((n = 3 ∧ e = 2 ∧ p = 5 ∧ f = 1 ∧ (C : Matrix (Fin n) (Fin n) K) = 1 ∧
              (∀ g : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField),
                ((g : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField) *ᵥ
                  (fun _ => 1) = fun _ => 1) ∧
              (∃ R : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField) ≃*
                  isometryGroup (B.restrict dperp),
                (∀ g w, ((R g).1 w : Fin n → h.fixedField) =
                  ((g : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField) *ᵥ w) ∧
                Nonempty (isometryGroup (B.restrict dperp) ≃* StatedSp 1 h.fixedField) ∧
                Nonempty (isometryGroup (B.restrict dperp) ≃*
                  Matrix.SpecialLinearGroup (Fin 2) h.fixedField)) ∧
              L.map ρC = N ∧ Nonempty (L ≃* StatedSp 1 h.fixedField) ∧
              Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) h.fixedField)) ∨
            (n = 4 ∧ e = 1 ∧ p = 3 ∧ f = 2 ∧
              (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n 2 ∧
              (∀ hr : 2 + 2 = n,
                ∃ E : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField) ≃*
                    StatedSp 2 h.fixedField,
                  ∀ g, ((E g : GL (Fin 2 ⊕ Fin 2) h.fixedField) :
                      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField) =
                    ((g : GL (Fin n) h.fixedField) :
                      Matrix (Fin n) (Fin n) h.fixedField).submatrix
                        (finSumFinEquiv.trans (finCongr hr))
                        (finSumFinEquiv.trans (finCongr hr))) ∧
              (∃ E : N ≃* PresentationLocal.sympFour, ∀ x : N,
                (x : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))) ∈ N' ↔
                  PresentationLocal.omegaPerm (E x) ∈ alternatingGroup (Fin 6)) ∧
              Nonempty (N ≃* Equiv.Perm (Fin 6)) ∧
              Nonempty (N' ≃* alternatingGroup (Fin 6)) ∧
              L.map ρC = N' ∧ Nonempty (L ≃* alternatingGroup (Fin 6))) ∨
            (n = 5 ∧ e = 1 ∧ p = 3 ∧ f = 2 ∧ (C : Matrix (Fin n) (Fin n) K) = 1 ∧
              (∀ g : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField),
                ((g : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField) *ᵥ
                  (fun _ => 1) = fun _ => 1) ∧
              (∃ R : matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField) ≃*
                  isometryGroup (B.restrict dperp),
                (∀ g w, ((R g).1 w : Fin n → h.fixedField) =
                  ((g : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField) *ᵥ w) ∧
                Nonempty (isometryGroup (B.restrict dperp) ≃* StatedSp 2 h.fixedField)) ∧
              (∃ E : N ≃* PresentationLocal.sympFour, ∀ x : N,
                (x : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))) ∈ N' ↔
                  PresentationLocal.omegaPerm (E x) ∈ alternatingGroup (Fin 6)) ∧
              Nonempty (N ≃* Equiv.Perm (Fin 6)) ∧
              Nonempty (N' ≃* alternatingGroup (Fin 6)) ∧
              L.map ρC = N' ∧ Nonempty (L ≃* alternatingGroup (Fin 6)))) ∧
          IsSimpleGroup L ∧ (∃ x y : L, x * y ≠ y * x) ∧
          StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∧
          IsEmpty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∧
          ¬ StatedClassicalModel (L ⧸ center L) .PSL 3 2 2 := by
  classical
  have := fixedField_charP h
  have := fixedField_finite h
  have : IsSimpleGroup (unitaryPSU h n) := φ.symm.isSimpleGroup
  have hnabP : ∃ x y : unitaryPSU h n, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hWnonab
    refine ⟨φ x, φ y, fun hc => hxy (φ.injective ?_)⟩
    rw [map_mul, map_mul, hc]
  obtain ⟨ρ, hinj, hρW, huniq, -⟩ :=
    socle_extension hCW φ (center_eq_bot_of_isSimpleGroup hnabP)
  have hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}) :=
    isComponentOf_of_le hL (le_inf hLW hL.1) inf_le_right
  obtain ⟨H₀, C, hC, hcase, hH₀', θ, hθmk, ρC, hρCapp, hρCinj, hρCW, σ, hσ, hρCa, hnotinner⟩ :=
    socle_descent h hn hq ha hLCW φ hinj hρW
  have hLnab := nonabelian_of_isQuasisimple hL.2.2
  have eLC : L ≃* L.map ρC := L.equivMapOfInjective ρC hρCinj
  have hk : Nat.card h.fixedField = 2 ^ e := h.card_fixedField
  rcases hcase with hC1 | ⟨r, hr, hCJ⟩
  ·
    have hCl : ((1 : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField).map
        h.fixedField.subtype = C := by
      rw [hC1, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    obtain ⟨hM, huniqΨ, hinjU, hNinner, hNM, hNnormal, hCAM, hCWN, hLC⟩ :=
      socle_transfer h hn hq hLCW hC (Or.inl hC1) 1 hCl hσ hρCinj _ hρCW hρCa
    rcases Nat.even_or_odd n with hev | ⟨r, hr⟩
    ·
      exact absurd (SymmetricLocal.isComponent_comap_of_isComponentOf_range _ hinjU hLC).1
        (no_component_matrixIsometryGroup_one_of_even hev hn _)
    obtain ⟨hrows, hLs, hPSL, hA7, hP34⟩ :=
      socle_rows_one hk hr hn hq hinjU hLC eLC hLnab hp2 hsrc
    refine ⟨ρ, hinj, hρW, huniq, hnotinner, H₀, C, hC, hH₀', θ, hθmk, ρC, hρCapp, hρCinj, σ,
      hσ, hρCa, 1, hCl, ?_⟩
    intro γ N N' B dperp
    refine ⟨hM, huniqΨ, hinjU, hNinner, hNM, hNnormal, hCAM, hCWN, ?_, hLs, hLnab, hPSL, hA7,
      hP34⟩
    rcases hrows with ⟨hn3, he2, hp5, hf1, hSp1, hSL, hXc, hL1, hL2⟩ |
      ⟨hn5, he1, hp3, hf2, hSp2, hE, hP6, hA6, hXc, hL6⟩
    · exact Or.inl ⟨hn3, he2, hp5, hf1, hC1, mulVec_ones_of_mem_one,
        ⟨oneRestrictEquiv hr, oneRestrictEquiv_apply hr, hSp1, hSL⟩, hXc, hL1, hL2⟩
    · exact Or.inr (Or.inr ⟨hn5, he1, hp3, hf2, hC1, mulVec_ones_of_mem_one,
        ⟨oneRestrictEquiv hr, oneRestrictEquiv_apply hr, hSp2⟩, hE, hP6, hA6, hXc, hL6⟩)
  ·
    have hrr : r + r = n := by omega
    have hClJ := coe_blockSwapGL (K := h.fixedField) hrr
    have hCl : ((blockSwapGL (K := h.fixedField) hrr : GL (Fin n) h.fixedField) :
        Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype = C := by
      rw [hClJ, hCJ]
      ext i j
      simp only [Matrix.map_apply, blockSwapJ, Matrix.of_apply]
      split_ifs <;> simp
    obtain ⟨hM, huniqΨ, hinjU, hNinner, hNM, hNnormal, hCAM, hCWN, hLC⟩ :=
      socle_transfer h hn hq hLCW hC (Or.inr ⟨r, hr, hCJ⟩) _ hCl hσ hρCinj _ hρCW hρCa
    obtain ⟨hn4, rfl, he1, hp3, hf2, hE, hP6, hA6, hXc, hL6, hLs, hPSL, hA7, hP34⟩ :=
      socle_rows_blockSwap hk hr hn hClJ hinjU hLC eLC hLnab hp2 hsrc
    refine ⟨ρ, hinj, hρW, huniq, hnotinner, H₀, C, hC, hH₀', θ, hθmk, ρC, hρCapp, hρCinj, σ,
      hσ, hρCa, _, hCl, ?_⟩
    intro γ N N' B dperp
    refine ⟨hM, huniqΨ, hinjU, hNinner, hNM, hNnormal, hCAM, hCWN, Or.inr (Or.inl
      ⟨hn4, he1, hp3, hf2, hCJ, fun hr' => ⟨(MulEquiv.subgroupCongr
        (congrArg matrixIsometryGroup hClJ)).trans
          (blockSwapIsometryEquivStatedSp (k := h.fixedField) hr'), fun g => rfl⟩,
        hE, hP6, hA6, hXc, hL6⟩), hLs, hLnab, hPSL, hA7, hP34⟩

end CFSG.ComponentClassification.OutcomeLocal
