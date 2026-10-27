module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthData
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCData

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.Burgoyne.PSL (isoOrthGL transportGL trans_commutator
  isQuasisimple_trans trans_le_commutator conj_mem_trans diagGL coe_diagGL)
open scoped MatrixGroups

variable {n : ℕ} {K : Type} [Field K]

abbrev omegaR (R : GL (Fin n) K) : Subgroup (GL (Fin n) K) :=
  ⁅CatalogueBGraphForm.isometryGroup n K R, CatalogueBGraphForm.isometryGroup n K R⁆

theorem det_eq_one_of_mem_omegaR {R : GL (Fin n) K} {g : GL (Fin n) K} (hg : g ∈ omegaR R) :
    (g : Matrix (Fin n) (Fin n) K).det = 1 := by
  have hle : omegaR R ≤ (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker := by
    rw [commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm,
      mul_comm]
  have h := MonoidHom.mem_ker.1 (hle hg)
  have h' := congrArg Units.val h
  rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at h'

theorem isSolvable_omegaR_of_le_two (hn : n ≤ 2) {w : Fin n → K} (hw : ∀ i, w i ≠ 0) :
    Group.IsSolvable (omegaR (diagGL hw)) := by
  refine Group.isSolvable_of_comm fun g h => Subtype.ext (Units.ext ?_)
  have hg := g.2
  have hh := h.2
  have hgd := det_eq_one_of_mem_omegaR hg
  have hhd := det_eq_one_of_mem_omegaR hh
  have hgI : (g : GL (Fin n) K) ∈ CatalogueBGraphForm.isometryGroup n K (diagGL hw) :=
    commutator_le_self _ hg
  have hhI : (h : GL (Fin n) K) ∈ CatalogueBGraphForm.isometryGroup n K (diagGL hw) :=
    commutator_le_self _ hh
  rw [CatalogueBGraphForm.mem_isometryGroup, coe_diagGL] at hgI hhI
  change ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (h : GL (Fin n) K) =
    ((h : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : GL (Fin n) K)
  interval_cases n
  · exact Subsingleton.elim _ _
  · have e1 : ∀ M : Matrix (Fin 1) (Fin 1) K, M.det = 1 → M = 1 := by
      intro M hM
      ext i j
      fin_cases i; fin_cases j
      simpa [Matrix.det_fin_one] using hM
    rw [e1 _ hgd, e1 _ hhd]
  · have hdiag : diagonal w = CatalogueBOrthogonal.planeGram (w 0) (w 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [CatalogueBOrthogonal.planeGram]
    rw [hdiag] at hgI hhI
    exact CatalogueBOrthogonal.plane_matrices_commute (w 0) (w 1) (hw 0) _ _ hgd hhd hgI hhI

theorem nonempty_equiv_determinantLeftFactor :
    Nonempty (determinantLeftFactor K ≃* SL(2, K)) := by
  have hinj : Function.Injective
      ((CatalogueBOrthogonalFourSplit.specialRho (K := K)).comp (MonoidHom.inl _ _)) := by
    rw [injective_iff_map_eq_one]
    intro A hA
    obtain ⟨c, -, h1, h2⟩ := (CatalogueBOrthogonalFourSplit.specialRho_eq_one_iff _).1 hA
    change SpecialLinearGroup.toGL (1 : SL(2, K)) = _ at h2
    rw [map_one] at h2
    change SpecialLinearGroup.toGL A = _ at h1
    rw [← h2] at h1
    exact SpecialLinearGroup.toGL_injective (h1.trans (map_one _).symm)
  exact ⟨(MonoidHom.ofInjective hinj).symm⟩

theorem nonempty_equiv_determinantRightFactor :
    Nonempty (determinantRightFactor K ≃* SL(2, K)) := by
  have hinj : Function.Injective
      ((CatalogueBOrthogonalFourSplit.specialRho (K := K)).comp (MonoidHom.inr _ _)) := by
    rw [injective_iff_map_eq_one]
    intro A hA
    obtain ⟨c, -, h1, h2⟩ := (CatalogueBOrthogonalFourSplit.specialRho_eq_one_iff _).1 hA
    change SpecialLinearGroup.toGL (1 : SL(2, K)) = _ at h1
    rw [map_one] at h1
    change SpecialLinearGroup.toGL A = _ at h2
    rw [← h1] at h2
    exact SpecialLinearGroup.toGL_injective (h2.trans (map_one _).symm)
  exact ⟨(MonoidHom.ofInjective hinj).symm⟩

@[expose] def SplitBlockData (R : GL (Fin n) K) : Prop :=
  ∃ L₁ L₂ : Subgroup (GL (Fin n) K), omegaR R = L₁ ⊔ L₂ ∧ L₁ ≤ omegaR R ∧ L₂ ≤ omegaR R ∧
    (L₁.subgroupOf (omegaR R)).Normal ∧ (L₂.subgroupOf (omegaR R)).Normal ∧
    IsQuasisimple L₁ ∧ IsQuasisimple L₂ ∧ Nonempty (L₁ ≃* SL(2, K)) ∧ Nonempty (L₂ ≃* SL(2, K))

theorem orth_block_cases [Finite K] (hK : ringChar K ≠ 2) (hn : 3 ≤ n) (R : GL (Fin n) K)
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = R) :
    Group.IsSolvable (omegaR R) ∨ IsQuasisimple (omegaR R) ∨
      (n = 4 ∧ Nat.card K ≠ 3 ∧ SplitBlockData R) := by
  have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm R with hQ
  have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK R hR
  have hdim : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  set e := isoOrthGL hK R hR with he
  have hK2 : Nat.card K ≠ 2 := by
    intro h
    rw [h] at hodd
    exact absurd hodd (by decide)
  have hsolv : (∀ p : ℕ, p.Prime →
      p ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) → p = 2 ∨ p = 3) →
      Group.IsSolvable (omegaR R) := by
    intro hp
    have hI : Group.IsSolvable (CatalogueBGraphForm.isometryGroup n K R) := by
      refine isSolvable_of_prime_dvd_two_three fun p hpp hdvd => hp p hpp ?_
      rwa [Nat.card_congr e.toEquiv]
    exact Group.isSolvable_of_isSolvable_injective
      (f := inclusion (commutator_le_self (CatalogueBGraphForm.isometryGroup n K R)))
      (inclusion_injective _)
  have hquasi : IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) →
      IsQuasisimple (omegaR R) := by
    intro hq
    have := isQuasisimple_trans e hq
    rwa [trans_commutator] at this
  by_cases hT : ∃ T : Submodule K (Fin n → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0
  · obtain ⟨T, hT3, hTQ⟩ := hT
    exact Or.inr (Or.inl (hquasi (CatalogueBOrthogonal.derived_quasisimple Q h2 hQnd hT3.ge hTQ)))
  have hcases := CatalogueBOrthogonalAssembly.low_Witt_finrank_cases hodd Q hQnd
    (by rw [hdim]; exact hn) hT
  have hcase : (Odd (Nat.card K) ∧ (Module.finrank K (Fin n → K) = 3 ∨
      Module.finrank K (Fin n → K) = 4 ∨ Module.finrank K (Fin n → K) = 5)) ∨
      (Odd (Nat.card K) ∧ Module.finrank K (Fin n → K) = 6 ∧
        ¬ ∃ T : Submodule K (Fin n → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) ∨
      (Module.finrank K (Fin n → K) = 4 ∧
        ∃ S : Submodule K (Fin n → K), Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) := by
    rcases hcases with h | h | h | h
    · exact Or.inl ⟨hodd, Or.inl h⟩
    · exact Or.inl ⟨hodd, Or.inr (Or.inl h)⟩
    · exact Or.inl ⟨hodd, Or.inr (Or.inr h)⟩
    · exact Or.inr (Or.inl ⟨hodd, h, hT⟩)
  obtain ⟨hexc, -, h3c, h4s, h4n, h5c, h6c⟩ :=
    orthogonal_low_dimensional_fixed_derived_component_coverage Q hQnd hcase
  rw [hdim] at hcases
  rcases hcases with h | h | h | h
  ·
    by_cases hK3 : Nat.card K = 3
    · exact Or.inl (hsolv (hexc (Or.inl ⟨by rw [hdim]; exact h, hK3⟩)).1)
    · obtain ⟨-, -, -, -, -, -, hq⟩ := h3c hodd (by rw [hdim]; exact h) hK3
      exact Or.inr (Or.inl (hquasi hq))
  ·
    by_cases hS : ∃ S : Submodule K (Fin n → K), Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0
    · by_cases hK3 : Nat.card K = 3
      · exact Or.inl (hsolv (hexc (Or.inr ⟨⟨by rw [hdim]; exact h, hS⟩, Or.inr hK3⟩)).1)
      · obtain ⟨-, e', -, -, hsup, hq₁, hq₂, hn₁, hn₂, -⟩ :=
          h4s (by rw [hdim]; exact h) hS hK2 hK3
        refine Or.inr (Or.inr ⟨h, hK3, ?_⟩)
        set M₁ := (determinantLeftFactor K).map e'.symm.toMonoidHom with hM₁
        set M₂ := (determinantRightFactor K).map e'.symm.toMonoidHom with hM₂
        have hM₁c : M₁ ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) :=
          hsup ▸ le_sup_left
        have hM₂c : M₂ ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) :=
          hsup ▸ le_sup_right
        have hiso : ∀ (M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)),
            transportGL e M ≃* M := fun M =>
          ((M.equivMapOfInjective _ e.injective).trans
            ((M.map e.toMonoidHom).equivMapOfInjective _ (Subgroup.subtype_injective _))).symm
        have hnorm : ∀ {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)},
            M ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) →
            (M.subgroupOf (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))).Normal →
            ((transportGL e M).subgroupOf (omegaR R)).Normal := by
          intro M hMc hMn
          rw [normal_subgroupOf_iff (trans_le_commutator e hMc)]
          intro l x hl hx
          exact conj_mem_trans e hMc hMn hx hl
        obtain ⟨eL⟩ := nonempty_equiv_determinantLeftFactor (K := K)
        obtain ⟨eR⟩ := nonempty_equiv_determinantRightFactor (K := K)
        refine ⟨transportGL e M₁, transportGL e M₂, ?_, trans_le_commutator e hM₁c,
          trans_le_commutator e hM₂c, hnorm hM₁c hn₁, hnorm hM₂c hn₂, isQuasisimple_trans e hq₁,
          isQuasisimple_trans e hq₂,
          ⟨(hiso M₁).trans (((determinantLeftFactor K).equivMapOfInjective
            _ e'.symm.injective).symm.trans eL)⟩,
          ⟨(hiso M₂).trans (((determinantRightFactor K).equivMapOfInjective
            _ e'.symm.injective).symm.trans eR)⟩⟩
        change ⁅CatalogueBGraphForm.isometryGroup n K R,
          CatalogueBGraphForm.isometryGroup n K R⁆ = _
        rw [← trans_commutator e, hsup, transportGL, transportGL, transportGL, Subgroup.map_sup,
          Subgroup.map_sup]
    · obtain ⟨-, -, -, -, -, -, -, -, hq⟩ := h4n hodd (by rw [hdim]; exact h) hS
      exact Or.inr (Or.inl (hquasi hq))
  ·
    obtain ⟨-, -, -, -, -, -, hq⟩ := h5c hodd (by rw [hdim]; exact h)
    exact Or.inr (Or.inl (hquasi hq))
  ·
    obtain ⟨-, -, -, -, -, -, -, -, hq⟩ := h6c hodd (by rw [hdim]; exact h) hT
    exact Or.inr (Or.inl (hquasi hq))

theorem card_center_SL_two {F : Type*} [Field F] [Finite F] (hF : ringChar F ≠ 2) :
    Nat.card (center SL(2, F)) = 2 := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 2)).toEquiv,
    Fintype.card_fin]
  have : CharP F (ringChar F) := ringChar.charP F
  exact (IsPrimitiveRoot.neg_one (ringChar F) hF).card_rootsOfUnity

theorem card_traceZeroSpecialImage [Finite K] (hK : ringChar K ≠ 2) :
    Nat.card (traceZeroSpecialImage K) * 2 = Nat.card SL(2, K) := by
  set f := CatalogueBOrthogonal.traceZeroOrthogonalAction.comp
    (SpecialLinearGroup.toGL : SL(2, K) →* GL (Fin 2) K) with hf
  have hker : f.ker = center SL(2, K) := by
    ext A
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply,
      CatalogueBOrthogonal.traceZeroOrthogonalAction_eq_one_iff,
      Matrix.SpecialLinearGroup.mem_center_iff]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_, ?_⟩
      · have hd := congrArg Matrix.det (congrArg Units.val hc)
        rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hd
        rw [Fintype.card_fin]
        rw [hd]
        exact A.2
      · exact congrArg Units.val hc
    · rintro ⟨r, hr, hrA⟩
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [Fintype.card_fin, zero_pow (by norm_num)] at hr
        exact zero_ne_one hr
      refine ⟨Units.mk0 r hr0, Units.ext ?_⟩
      rw [GeneralLinearGroup.coe_scalar, Units.val_mk0]
      exact hrA
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hker, card_center_SL_two hK] at h1
  rw [← h1, mul_comm]
  rfl

theorem card_omegaR_three [Finite K] (hK : ringChar K ≠ 2) (hK3 : Nat.card K ≠ 3)
    (R : GL (Fin 3) K) (hR : (R : Matrix (Fin 3) (Fin 3) K)ᵀ = R) :
    Nat.card (omegaR R) * 2 = Nat.card SL(2, K) := by
  have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm R with hQ
  have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK R hR
  have hdim : Module.finrank K (Fin 3 → K) = 3 := Module.finrank_fin_fun K
  set e := isoOrthGL hK R hR with he
  obtain ⟨-, -, h3c, -⟩ := orthogonal_low_dimensional_fixed_derived_component_coverage Q hQnd
    (Or.inl ⟨hodd, Or.inl hdim⟩)
  obtain ⟨-, -, e', -, -, hc, -⟩ := h3c hodd hdim hK3
  have hcard : Nat.card (omegaR R) =
      Nat.card (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
    change Nat.card (⁅CatalogueBGraphForm.isometryGroup 3 K R,
      CatalogueBGraphForm.isometryGroup 3 K R⁆ : Subgroup (GL (Fin 3) K)) = _
    rw [← trans_commutator e, transportGL, Subgroup.card_map_of_injective
      (Subgroup.subtype_injective _), Subgroup.card_map_of_injective e.injective]
  rw [hcard, hc, Subgroup.card_map_of_injective e'.symm.injective]
  exact card_traceZeroSpecialImage hK

end CFSG.ComponentClassification.Burgoyne.C
