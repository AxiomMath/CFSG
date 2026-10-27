module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Subgroup CFSG.RankThree.OrthogonalInvolutions CFSG.Assembly.LowTwoRank
open CFSG.RankThree.Classical2 (orthDerived)
open scoped Matrix

theorem mem_statedOmega_of {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
    [CharP K 2] (Q : QuadraticForm K (ι → K)) (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {M : GL ι K}
    (hM : ∀ v, Q ((M : Matrix ι ι K) *ᵥ v) = Q v) (hev : Even (commRank M)) :
    M ∈ StatedOmega ⇑Q := by
  set φ : GL ι K ≃* ((ι → K) ≃ₗ[K] (ι → K)) := Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)) with hφdef
  have hφ : ∀ (N : GL ι K) v, φ N v = (N : Matrix ι ι K) *ᵥ v := fun _ _ => rfl
  have hO : φ M ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by rw [hφ]; exact hM v
  have hrange : commSpace (φ M) = LinearMap.range ((M : Matrix ι ι K) - 1).mulVecLin := by
    ext v
    simp [hφ]
  have hΩ : φ M ∈ omegaGroup Q hQ := mem_omegaGroup.mpr ⟨hO, by rw [hrange]; exact hev⟩
  have hD := CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT hΩ
  have hC : TauCeti.QuadraticMap.orthogonalGroup Q ≤
      (closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v}).map φ.toMonoidHom := by
    intro g hg
    refine ⟨φ.symm g, subset_closure fun v => ?_, by simp⟩
    rw [← hφ, MulEquiv.apply_symm_apply]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg v
  have hmap : orthDerived Q ≤ (StatedOmega ⇑Q).map φ.toMonoidHom := by
    rw [StatedOmega, Subgroup.map_commutator]
    exact commutator_mono hC hC
  obtain ⟨M', hM', hMM'⟩ := hmap hD
  rw [MulEquiv.coe_toMonoidHom] at hMM'
  rwa [← φ.injective hMM']

theorem exists_totallySingular_of {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Q : QuadraticForm K (ι → K)) (f : Fin 3 → ι) (hf : Function.Injective f)
    (h0 : ∀ v : ι → K, (∀ i, i ∉ Set.range f → v i = 0) → Q v = 0) :
    ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0 := by
  let g : Fin 3 → ι → K := fun k => Pi.single (f k) 1
  have hg : LinearIndependent K g := by
    convert (Pi.basisFun K ι).linearIndependent.comp f hf using 1
    funext k
    simp [g]
  let S : Submodule K (ι → K) :=
    { carrier := {v | ∀ i, i ∉ Set.range f → v i = 0}
      add_mem' := fun ha hb i hi => by simp [ha i hi, hb i hi]
      zero_mem' := fun i _ => rfl
      smul_mem' := fun c v hv i hi => by simp [hv i hi] }
  refine ⟨Submodule.span K (Set.range g), ?_, fun x hx => h0 x ?_⟩
  · rw [finrank_span_eq_card hg, Fintype.card_fin]
  · have hle : Submodule.span K (Set.range g) ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩ i hi
      have hne : i ≠ f k := fun h => hi ⟨k, h.symm⟩
      simp [g, hne]
    exact hle hx

theorem exists_totallySingular_quadPlus {n : ℕ} (hn : 3 ≤ n) (K : Type) [Field K] :
    ∃ T : Submodule K (Fin n ⊕ Fin n → K),
      finrank K T = 3 ∧ ∀ x ∈ T, CFSG.LieType.Universal.Spin.quadPlus n K x = 0 := by
  refine exists_totallySingular_of _ (fun k => .inl (Fin.castLE hn k))
    (fun a b h => Fin.castLE_injective hn (Sum.inl_injective h)) fun v hv => ?_
  rw [CFSG.LieType.Universal.Spin.coe_quadPlus, StatedQuadPlus]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hv (.inr i) (by rintro ⟨k, hk⟩; exact Sum.inl_ne_inr hk), mul_zero]

theorem exists_totallySingular_quadMinus {n : ℕ} (hn : 4 ≤ n) (K : Type) [Field K] (b c : K) :
    ∃ T : Submodule K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K),
      finrank K T = 3 ∧ ∀ x ∈ T, CFSG.LieType.Universal.Spin.quadMinus n K b c x = 0 := by
  have hn' : 3 ≤ n - 1 := by omega
  refine exists_totallySingular_of _ (fun k => .inl (Fin.castLE hn' k))
    (fun a b h => Fin.castLE_injective hn' (Sum.inl_injective h)) fun v hv => ?_
  rw [CFSG.LieType.Universal.Spin.coe_quadMinus, StatedQuadMinus]
  have h1 : ∀ k : Fin (n - 1) ⊕ Fin 2, v (.inr k) = 0 := fun k =>
    hv (.inr k) (by rintro ⟨j, hj⟩; exact Sum.inl_ne_inr hj)
  simp [h1]

end CFSG.ComponentClassification.RankTwoClassical
