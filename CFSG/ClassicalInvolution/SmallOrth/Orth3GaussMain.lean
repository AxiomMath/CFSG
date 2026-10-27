module

public import CFSG.ClassicalInvolution.SmallOrth.Orth3GaussTheta
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerCentralKernel
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Split

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap Matrix CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Balance
  CFSG.LieType.Universal.Unitary CFSG.Open CFSG.ComponentClassification
  CFSG.Assembly.LowTwoRank

theorem range_le_commutator {G H : Type*} [Group G] [Group H] (hG : Group.IsPerfect G)
    (ψ : G →* H) {O : Subgroup H} (hO : ψ.range ≤ O) : ψ.range ≤ ⁅O, O⁆ := by
  have h1 : ψ.range = ⁅ψ.range, ψ.range⁆ := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hG.commutator_eq_top]
  rw [h1]
  exact Subgroup.commutator_mono hO hO

section SU

variable {F : Type} [Field F] [Finite F] [Fact (Nat.card F = 3)]

theorem isPerfect_suid {m : ℕ} (hm : 3 ≤ m) : Group.IsPerfect (SUid (gaussSigma (F := F)) m) := by
  have hnq : (m, 3 ^ 1) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.snd h'
    simp only at this
    omega
  have hq' := isQuasisimple_statedSU_of_card (F := GaussField F) (p := 3) (f := 1)
    card_gaussField_sq hm hnq
  let e : SUid (gaussSigma (F := F)) m ≃* StatedSU m (3 ^ 1) (GaussField F) :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU card_gaussField_sq m)
  exact ⟨(CFSG.ClassicalInvolution.ModelFacts.open_isQuasisimple
    (CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv e.symm hq'.1)).1⟩

end SU

section Main

variable {F : Type} [Field F] [Finite F] [Fact (Nat.card F = 3)] {V : Type} [AddCommGroup V]
  [Module F V] {Q : QuadraticForm F V} {g : V ≃ₗ[F] V} {m : ℕ}

theorem thetaHom_su_mem (ab : AdaptedBasis Q g m) (h2 : (2 : F) ≠ 0) (hm : 3 ≤ m)
    (hOE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      elementaryGroup Q) (X : SUid (gaussSigma (F := F)) m) :
    thetaHom ab (X : GL (Fin m) (GaussField F)) ∈ elementaryGroup Q := by
  have hO : ((thetaHom ab).comp (SUid (gaussSigma (F := F)) m).subtype).range ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨Y, rfl⟩
    exact thetaHom_mem_orthogonalGroup ab h2 Y.2.2
  exact hOE (range_le_commutator (isPerfect_suid hm) _ hO ⟨X, rfl⟩)

@[expose] noncomputable def thetaSU (ab : AdaptedBasis Q g m) (h2 : (2 : F) ≠ 0) (hm : 3 ≤ m)
    (hOE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      elementaryGroup Q) : SUid (gaussSigma (F := F)) m →* ↥(elementaryGroup Q) :=
  ((thetaHom ab).comp (SUid (gaussSigma (F := F)) m).subtype).codRestrict (elementaryGroup Q)
    (thetaHom_su_mem ab h2 hm hOE)

theorem coe_thetaSU (ab : AdaptedBasis Q g m) (h2 : (2 : F) ≠ 0) (hm : 3 ≤ m)
    (hOE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      elementaryGroup Q) (X : SUid (gaussSigma (F := F)) m) :
    ((thetaSU ab h2 hm hOE X : ↥(elementaryGroup Q)) : V ≃ₗ[F] V) =
      thetaHom ab (X : GL (Fin m) (GaussField F)) := rfl

theorem thetaSU_injective (ab : AdaptedBasis Q g m) (h2 : (2 : F) ≠ 0) (hm : 3 ≤ m)
    (hOE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      elementaryGroup Q) : Function.Injective (thetaSU ab h2 hm hOE) := fun _ _ h =>
  Subtype.ext (thetaHom_injective ab (congrArg Subtype.val h))

omit [Finite F] [Fact (Nat.card F = 3)] in
theorem thetaHom_mul_comm (ab : AdaptedBasis Q g m) (hg2 : ∀ x, g (g x) = -x)
    (A : GL (Fin m) (GaussField F)) : thetaHom ab A * g = g * thetaHom ab A := by
  refine LinearEquiv.ext fun x => ?_
  have h := congrArg (fun M => thetaEnd ab M x)
    (Matrix.scalar_commute (n := Fin m) (QuadraticAlgebra.omega : GaussField F)
      (fun r => Commute.all _ r) (A : Matrix (Fin m) (Fin m) (GaussField F))).eq
  simp only [map_mul, Module.End.mul_apply, thetaEnd_scalar_omega ab hg2] at h
  exact h.symm

theorem conj_thetaHom (ab : AdaptedBasis Q g m) {ν : V ≃ₗ[F] V}
    {A : Matrix (Fin m) (Fin m) (GaussField F)} (hA : conjTr (gaussSigma (F := F)) A * A = 1)
    (hνA : (ν : V →ₗ[F] V) = thetaEnd ab A) (X X' : GL (Fin m) (GaussField F))
    (hX' : (X' : Matrix (Fin m) (Fin m) (GaussField F)) =
      A * X * conjTr (gaussSigma (F := F)) A) :
    ν * thetaHom ab X * ν⁻¹ = thetaHom ab X' := by
  have hAA : A * conjTr (gaussSigma (F := F)) A = 1 := mul_eq_one_comm.mp hA
  have hν : ∀ w, ν w = thetaEnd ab A w := fun w => LinearMap.congr_fun hνA w
  have hmul : ∀ v, ν (thetaEnd ab (conjTr (gaussSigma (F := F)) A) v) = v := fun v => by
    rw [hν, ← Module.End.mul_apply, ← map_mul, hAA, map_one]
    rfl
  have hinv : ∀ v, ν⁻¹ v = thetaEnd ab (conjTr (gaussSigma (F := F)) A) v := fun v => by
    show ν.symm v = _
    exact ν.symm_apply_eq.mpr (hmul v).symm
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hinv, hν, thetaHom_apply, thetaHom_apply,
    hX', map_mul, map_mul]
  rfl

end Main

section Final

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

theorem oddCoreIn_centralizer_eq_bot_of_neg_one (hF : Nat.card F = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 6 ≤ Module.finrank F V)
    (hOE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      elementaryGroup Q) (g : ↥(elementaryGroup Q))
    (hg2 : ∀ x, (g : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V) x) = -x) :
    oddCoreIn (Subgroup.centralizer ({(QuotientGroup.mk g : ↥(elementaryGroup Q) ⧸
      Subgroup.center ↥(elementaryGroup Q))} : Set (↥(elementaryGroup Q) ⧸
        Subgroup.center ↥(elementaryGroup Q)))) = ⊥ := by
  have : Fact (Nat.card F = 3) := ⟨hF⟩
  obtain ⟨-, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hF
  have hgO : (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q g.2
  obtain ⟨m, hm, ⟨ab⟩⟩ := exists_adaptedBasis hF hQ hgO hg2
  have hm3 : 3 ≤ m := by omega
  have hZ := isPGroup_center_elementaryGroup hF hQ (by omega : 3 ≤ Module.finrank F V)
  set θ := thetaSU ab h2 hm3 hOE with hθ
  refine oddCoreIn_centralizer_eq_bot_of_blocks hZ g (ι := Unit) (fun _ => θ.range) ?_ ?_ ?_ ?_
  · rintro - x ⟨X, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (thetaHom_mul_comm ab hg2 (X : GL (Fin m) (GaussField F))))
  · intro _ b hb x hx
    obtain ⟨X, rfl⟩ := hx
    have hcomm : (b : V ≃ₗ[F] V) * g = g * b :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hb)
    obtain ⟨A, hA, hνA⟩ :=
      exists_unitary_of_commute ab hg2 (elementaryGroup_le_orthogonalGroup Q b.2) hcomm
    obtain ⟨X', hX'⟩ := exists_su_conj hA X
    exact ⟨X', Subtype.ext (conj_thetaHom ab hA hνA _ _ hX').symm⟩
  · intro _
    show oddCoreIn (θ.range.map (QuotientGroup.mk' (Subgroup.center ↥(elementaryGroup Q)))) = ⊥
    rw [← MonoidHom.range_comp]
    refine oddCoreIn_range_eq_bot_of_central_kernel
      ((QuotientGroup.mk' (Subgroup.center ↥(elementaryGroup Q))).comp θ)
      (componentOddCore_su_eq_bot m) ?_ ?_
    · intro X hX
      have h1 : θ X ∈ Subgroup.center ↥(elementaryGroup Q) := (QuotientGroup.eq_one_iff _).mp hX
      rw [Subgroup.mem_center_iff]
      intro Y
      apply thetaSU_injective ab h2 hm3 hOE
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp h1 (θ Y)
    · intro X
      obtain ⟨k, hk⟩ := hZ ⟨θ X.1, (QuotientGroup.eq_one_iff _).mp X.2⟩
      refine ⟨k, Subtype.ext (thetaSU_injective ab h2 hm3 hOE ?_)⟩
      simpa using congrArg Subtype.val hk
  · intro ν hν hL
    have hcomm : (ν : V ≃ₗ[F] V) * g = g * ν :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hν)
    obtain ⟨A, hA, hνA⟩ :=
      exists_unitary_of_commute ab hg2 (elementaryGroup_le_orthogonalGroup Q ν.2) hcomm
    have hAX : ∀ X : SUid (gaussSigma (F := F)) m,
        A * ((X : GL (Fin m) (GaussField F)) : Matrix (Fin m) (Fin m) (GaussField F)) =
          ((X : GL (Fin m) (GaussField F)) : Matrix (Fin m) (Fin m) (GaussField F)) * A := by
      intro X
      apply thetaEnd_injective ab
      rw [map_mul, map_mul, ← hνA]
      exact LinearMap.ext fun x =>
        LinearEquiv.congr_fun (congrArg Subtype.val (hL () (θ X) ⟨X, rfl⟩)) x
    obtain ⟨c, hc⟩ := exists_scalar_of_commute_su (by omega : 2 ≤ m) hAX
    have hc4 : c ^ 4 = 1 := by
      rw [hc, conjTr_scalar, ← map_mul] at hA
      have h1 := congrFun (congrFun hA ⟨0, by omega⟩) ⟨0, by omega⟩
      simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h1
      have h3 : gaussSigma (F := F) c = c ^ 3 := by
        rw [gaussSigma_apply, gauss_pow_three]
      rw [h3] at h1
      calc c ^ 4 = c ^ 3 * c := by ring
        _ = 1 := h1
    have h4 : thetaEnd ab A ^ 4 = 1 := by
      rw [hc, ← map_pow, ← map_pow, hc4, map_one, map_one]
    refine ⟨2, Subtype.ext (LinearEquiv.ext fun x => ?_)⟩
    rw [Subgroup.coe_pow, LinearEquiv.coe_pow]
    have h5 := congrArg (fun φ : V →ₗ[F] V => φ x) h4
    rw [← hνA, Module.End.coe_pow] at h5
    exact h5

end Final

end CFSG.ClassicalGroups.Orthogonal.Small
