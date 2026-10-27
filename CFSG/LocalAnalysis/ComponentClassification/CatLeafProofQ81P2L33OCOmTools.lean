module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33OCSpHom
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphSymm
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquareOrthogonalModel

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.OC

open CFSG Subgroup Matrix Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare QuaternionMatrices

section Omega

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem mem_omega_of_odd [Finite K] [FiniteDimensional K V] (hK : ringChar K ≠ 2)
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hodd : Odd (orderOf g)) :
    g ∈ orthogonalOmega Q := by
  obtain ⟨hab, -, -, -⟩ := odd_orthogonal_abelianization_order_bound hK hQ
  set O := TauCeti.QuadraticMap.orthogonalGroup Q
  set y : O := ⟨g, hg⟩
  have hx2 : (Abelianization.of y) ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 _) _
  have hd2 : orderOf (Abelianization.of y) ∣ orderOf g := by
    rw [← Subgroup.orderOf_mk g hg]
    exact orderOf_map_dvd _ _
  have h1 : orderOf (Abelianization.of y) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.coprime_two_right.2 (Odd.of_dvd_nat hodd hd2))
      (orderOf_dvd_of_pow_eq_one hx2)
  have hy : y ∈ commutator O := (QuotientGroup.eq_one_iff y).1 (orderOf_eq_one_iff.1 h1)
  have hmap : (commutator O).map O.subtype = orthogonalOmega Q := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  rw [← hmap]
  exact ⟨y, hy, rfl⟩

@[expose] def OmWit {K V : Type} [Field K] [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
    (C : Subgroup (V ≃ₗ[K] V)) : Prop :=
  ∃ (G : Type) (_ : Group G) (S : Set G) (ψ : G →* (V ≃ₗ[K] V)), closure S = ⊤ ∧
    (∀ s ∈ S, Odd (orderOf s)) ∧ (∀ g, ψ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) ∧
      (∀ g, ψ g ∈ C) ∧ ∃ x : G, x ^ 4 = 1 ∧ NotScalar (ψ x)

theorem exists_odd_of_omWit {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hK : ringChar K ≠ 2) {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {C : Subgroup (V ≃ₗ[K] V)} (h : OmWit Q C) :
    ∃ T : Set (OrthogonalProj Q),
      T ⊆ (C.subgroupOf (orthogonalOmega Q)).map (orthogonalProj Q) ∧
        (∀ t ∈ T, Odd (orderOf t)) ∧ 2 ∣ Nat.card (closure T) := by
  obtain ⟨G, _, S, ψ, hS, hSo, hψO, hψC, x, hx4, hxs⟩ := h
  have hle : closure S ≤ (orthogonalOmega Q).comap ψ := by
    rw [closure_le]
    intro s hs
    exact mem_omega_of_odd hK hQ (hψO s) (Odd.of_dvd_nat (hSo s hs) (orderOf_map_dvd ψ s))
  have hψΩ : ∀ g, ψ g ∈ orthogonalOmega Q := fun g => hle (hS ▸ mem_top g)
  let ψ' : G →* orthogonalOmega Q := ψ.codRestrict _ hψΩ
  have hθx : (orthogonalProj Q).comp ψ' x ≠ 1 := fun h1 => by
    obtain ⟨c, hc⟩ := (mem_omegaScalars Q).1 ((QuotientGroup.eq_one_iff _).1 h1)
    exact hxs c hc
  obtain ⟨hTo, hT2⟩ := odd_closure_image _ hS hSo hx4 hθx
  refine ⟨_, ?_, hTo, hT2⟩
  rintro _ ⟨s, -, rfl⟩
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (hψC s))

end Omega

section Ternary

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W]

theorem exists_sl2_orth [Finite F] (hF : ringChar F ≠ 2) [FiniteDimensional F W]
    (Q : QuadraticForm F W) (hQ : Q.polarBilin.Nondegenerate) (h3 : 3 ≤ finrank F W) :
    ∃ ψ : SpecialLinearGroup (Fin 2) F →* (W ≃ₗ[F] W),
      (∀ X, ψ X ∈ TauCeti.QuadraticMap.orthogonalGroup Q) ∧ NotScalar (ψ (slQuatI F)) := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have : Invertible (2 : F) := invertibleOfNonzero h2
  set B : LinearMap.BilinForm F W := Q.polarBilin with hB
  have hsym : LinearMap.BilinForm.IsSymm B := ⟨fun x y => QuadraticMap.polar_comm Q x y⟩
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.1 hsym)
  obtain ⟨m, hm⟩ : ∃ m, finrank F W = 3 + m := ⟨_, (Nat.add_sub_cancel' h3).symm⟩
  set b := v.reindex (finCongr hm) with hb
  have hbo : B.iIsOrtho b := fun i j hij => by
    change B (b i) (b j) = 0
    rw [hb, Basis.reindex_apply, Basis.reindex_apply]
    exact hv (by simpa using hij)
  set d : Fin (3 + m) → F := fun i => B (b i) (b i) with hd
  have hd0 : ∀ i, d i ≠ 0 := hbo.not_isOrtho_basis_self_of_nondegenerate hQ
  have hG : ∀ i j, B (b i) (b j) = diagonal d i j := fun i j => by
    rw [diagonal_apply]
    split_ifs with h
    · rw [h]
    · exact hbo h
  obtain ⟨ζ, hζ, hζs⟩ :=
    LinearFlag.exists_ternary_isometry_hom hF (fun i => d (finSumFinEquiv (Sum.inl i)))
      fun i => hd0 _
  let ψ : SpecialLinearGroup (Fin 2) F →* (W ≃ₗ[F] W) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F W).toMonoidHom.comp
      ((CLSFourGroupScalarSquare.basisGL b).comp ((LinearFlag.blockGL F 3 m).comp ζ))
  have hψ : ∀ X w, ψ X w = Matrix.toLin b b
      ((LinearFlag.blockGL F 3 m (ζ X) : GL (Fin (3 + m)) F) : Matrix (Fin (3 + m))
        (Fin (3 + m)) F) w := fun X w => rfl
  refine ⟨ψ, fun X => ?_, fun c hc => ?_⟩
  · refine (TauCeti.QuadraticMap.mem_orthogonalGroup_iff_polar
      (IsSMulRegular.of_ne_zero h2)).2 fun x y => ?_
    change B (ψ X x) (ψ X y) = B x y
    rw [hψ, hψ]
    refine toLin_preserves B b (diagonal d) hG (fun _ _ => rfl) ?_ x y
    rw [LinearFlag.diagonal_eq_diagBlock, LinearFlag.coe_blockGL_eq_diagBlock,
      LinearFlag.diagBlock_transpose, LinearFlag.diagBlock_mul, LinearFlag.diagBlock_mul, hζ,
      transpose_one, Matrix.one_mul, Matrix.mul_one]
  · have h1 : Matrix.toLin b b ((LinearFlag.blockGL F 3 m (ζ (slQuatI F)) : GL (Fin (3 + m)) F) :
        Matrix (Fin (3 + m)) (Fin (3 + m)) F) = c • (1 : Module.End F W) := by
      refine LinearMap.ext fun w => ?_
      rw [← hψ]
      exact LinearMap.congr_fun hc w
    exact LinearFlag.blockGL_ne_scalar_of_ne_scalar hζs c
      (by
        rw [scalar_apply, ← smul_one_eq_diagonal]
        exact FourGroupOddUnitary.toLin_eq_smul_id b h1)

end Ternary

end CFSG.ComponentClassification.HarrisLit.L33.OC
