module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorBasic
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOddOrthogonal

public noncomputable section

namespace CFSG.ComponentClassification.OddClassSelector

open Subgroup Matrix CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal (commutant mem_commutant)
open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare (orthogonalOmega)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {K : Type} [Field K] {d : ℕ}

@[expose] def derivedLinear (Q : QuadraticForm K (Fin d → K)) :
    matrixDerived Q →* ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
  matrixLinearIso.toMonoidHom.comp (matrixDerived Q).subtype

theorem derivedLinear_apply (Q : QuadraticForm K (Fin d → K)) (X : matrixDerived Q)
    (v : Fin d → K) : derivedLinear Q X v = matrixLinearEquiv X.val v :=
  rfl

theorem derivedLinear_injective (Q : QuadraticForm K (Fin d → K)) :
    Function.Injective (derivedLinear Q) :=
  matrixLinearIso.injective.comp (matrixDerived Q).subtype_injective

theorem range_derivedLinear (Q : QuadraticForm K (Fin d → K)) :
    (derivedLinear Q).range = orthogonalOmega Q := by
  rw [derivedLinear, MonoidHom.range_comp, Subgroup.range_subtype]
  exact CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal.map_matrixDerived Q

theorem derivedConj_eq_iff (Q : QuadraticForm K (Fin d → K)) (g : similarityPairs Q)
    (X : matrixDerived Q) :
    matrixDerivedConjugation Q g X = X ↔
      derivedLinear Q X ∈ commutant (coordinateSemilinearMap g.val) := by
  rw [mem_commutant]
  constructor
  · intro h v
    have h1 : matrixConjugation g.val X.val = X.val := congrArg Subtype.val h
    have h2 := matrixConjugation_vector g.val X.val (coordinateSemilinearMap g.val v)
    rw [h1, AddEquiv.symm_apply_apply] at h2
    exact h2
  · intro h
    apply Subtype.ext
    change matrixConjugation g.val X.val = X.val
    apply matrixLinearIso.injective
    refine LinearEquiv.ext fun v => ?_
    change matrixLinearEquiv (matrixConjugation g.val X.val) v = matrixLinearEquiv X.val v
    rw [matrixConjugation_vector]
    have h1 := h ((coordinateSemilinearMap g.val).symm v)
    rw [AddEquiv.apply_symm_apply] at h1
    exact h1.symm

theorem map_derivedLinear_fixed (Q : QuadraticForm K (Fin d → K)) (g : similarityPairs Q) :
    (fixedSubgroup (matrixDerivedConjugation Q g)).map (derivedLinear Q) =
      orthogonalOmega Q ⊓ commutant (coordinateSemilinearMap g.val) := by
  ext u
  constructor
  · rintro ⟨X, hX, rfl⟩
    refine ⟨?_, (derivedConj_eq_iff Q g X).mp hX⟩
    rw [← range_derivedLinear]
    exact ⟨X, rfl⟩
  · rintro ⟨hu, hc⟩
    rw [← range_derivedLinear] at hu
    obtain ⟨X, rfl⟩ := hu
    exact ⟨X, (derivedConj_eq_iff Q g X).mpr hc, rfl⟩

section Helpers

variable {G : Type*} [Group G]

theorem isComponentOf_of_normal_le {Y N M : Subgroup G} (hY : CFSG.Assembly.IsComponentOf Y N)
    (hNM : N ≤ M) (hN : (N.subgroupOf M).Normal) : CFSG.Assembly.IsComponentOf Y M :=
  ⟨hY.1.trans hNM, LocalAnalysis.ComponentInitial.assembly_isSubnormal_trans hY.2.1
    (CFSG.Assembly.IsSubnormal.step hNM hN (CFSG.Assembly.IsSubnormal.refl M)), hY.2.2⟩

theorem mem_normalizer_commutator {H : Subgroup G} {g : G} (hg : g ∈ normalizer (H : Set G)) :
    g ∈ normalizer ((⁅H, H⁆ : Subgroup G) : Set G) := by
  have hmap : H.map (MulAut.conj g).toMonoidHom = H := by
    ext x
    rw [mem_normalizer_iff] at hg
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hg y).mp hy
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, by simp [mul_assoc]⟩
      have h := (hg (g⁻¹ * x * g)).mpr
      have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      rw [e] at h
      exact h hx
  have hcomm : ⁅H, H⁆.map (MulAut.conj g).toMonoidHom = ⁅H, H⁆ := by
    rw [Subgroup.map_commutator, hmap]
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← hcomm]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← hcomm] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := by
      have h2 : g * z * g⁻¹ = g * y * g⁻¹ := hzy
      simpa using h2
    rwa [← this]

theorem map_mem_normalizer {H' : Type*} [Group H'] (f : G →* H') {K : Subgroup G} {g : G}
    (hg : g ∈ normalizer (K : Set G)) : f g ∈ normalizer ((K.map f : Subgroup H') : Set H') := by
  rw [mem_normalizer_iff] at hg ⊢
  intro y
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨g * k * g⁻¹, (hg k).mp hk, by simp⟩
  · rintro ⟨k, hk, hky⟩
    refine ⟨g⁻¹ * k * g, ?_, ?_⟩
    · have h := (hg (g⁻¹ * k * g)).mpr
      have e : g * (g⁻¹ * k * g) * g⁻¹ = k := by group
      rw [e] at h
      exact h hk
    · rw [map_mul, map_mul, map_inv, hky]
      group

end Helpers

section Lift

variable (Q : QuadraticForm K (Fin d → K))

theorem ker_matrixProjectiveProjection_le :
    (matrixProjectiveProjection Q).ker ≤ center (matrixDerived Q) := by
  rw [matrixProjectiveProjection, QuotientGroup.ker_mk']
  exact matrixDerivedScalars_le_center Q

theorem matrixDerivedConjugation_involutive (g : similarityPairs Q) (hσ : g.val.right ^ 2 = 1)
    (hc : ∃ c : Kˣ, g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right
      g.val.left = GeneralLinearGroup.scalar (Fin d) c)
    (X : matrixDerived Q) :
    matrixDerivedConjugation Q g (matrixDerivedConjugation Q g X) = X := by
  rw [← matrixDerivedConjugation_mul]
  apply Subtype.ext
  rw [matrixDerivedConjugation_val]
  obtain ⟨hl, hr⟩ := CatalogueBOrthogonalInvolutionRepresentation.sq_val Q g
  obtain ⟨c, hc⟩ := hc
  rw [hl, hr, hσ, hc, map_one, MulAut.one_apply]
  have hcen : GeneralLinearGroup.scalar (Fin d) c ∈ Subgroup.center (GL (Fin d) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  rw [(Subgroup.mem_center_iff.mp hcen X.val).symm, mul_inv_cancel_right]

theorem matrixProjective_comm (g : similarityPairs Q) (X : matrixDerived Q) :
    matrixProjectiveProjection Q (matrixDerivedConjugation Q g X) =
      matrixProjectiveConjugationHom Q g (matrixProjectiveProjection Q X) :=
  (matrixProjectiveConjugation_mk Q g X).symm

theorem orth_lift [Finite K] (g : similarityPairs Q) (hσ : g.val.right ^ 2 = 1)
    (hc : ∃ c : Kˣ, g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right
      g.val.left = GeneralLinearGroup.scalar (Fin d) c)
    {X : Subgroup (matrixProjectiveDerived Q)}
    (hX : CFSG.Assembly.IsComponentOf X (fixedSubgroup (matrixProjectiveConjugationHom Q g))) :
    ∃ Y : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)),
      CFSG.Assembly.IsComponentOf Y (TauCeti.QuadraticMap.orthogonalGroup Q ⊓
        commutant (coordinateSemilinearMap g.val)) ∧
      Y ≤ orthogonalOmega Q ∧
      (∃ σ : Y →* X, Function.Surjective σ ∧ σ.ker ≤ center Y) ∧
      (NoTightWitness X → ∀ t s : (Fin d → K) ≃ₗ[K] (Fin d → K), t ∈ orthogonalOmega Q →
        s ∈ orthogonalOmega Q →
        (∃ c : K, ((t * t : (Fin d → K) ≃ₗ[K] (Fin d → K)) : (Fin d → K) →ₗ[K] (Fin d → K)) =
          c • LinearMap.id) →
        (∀ c : K, ((t : (Fin d → K) ≃ₗ[K] (Fin d → K)) : (Fin d → K) →ₗ[K] (Fin d → K)) ≠
          c • LinearMap.id) →
        (∀ y ∈ Y, y * t = t * y) → s * t = t * s → s ∈ normalizer (Y : Set _)) := by
  classical
  set π := matrixProjectiveProjection Q with hπ
  set a := matrixDerivedConjugation Q g with ha
  obtain ⟨-, hYm, hYmap, -⟩ := LocalAnalysis.ComponentInitial.lift_isComponentOf_fixed
    (π := π) (a := a) (α := matrixProjectiveConjugationHom Q g)
    (matrixProjectiveProjection_surjective Q) (ker_matrixProjectiveProjection_le Q)
    (matrixDerivedConjugation_involutive Q g hσ hc) (matrixProjective_comm Q g) hX
  set Ym := ⁅X.comap π, X.comap π⁆ with hYmdef
  set J := derivedLinear Q with hJ
  have hJi : Function.Injective J := derivedLinear_injective Q
  set Y := Ym.map J with hYdef
  have hYc1 : CFSG.Assembly.IsComponentOf Y
      (orthogonalOmega Q ⊓ commutant (coordinateSemilinearMap g.val)) := by
    rw [← map_derivedLinear_fixed]
    exact SymmetricLocal.isComponentOf_map_of_injective J hJi hYm
  have hle : orthogonalOmega Q ⊓ commutant (coordinateSemilinearMap g.val) ≤
      TauCeti.QuadraticMap.orthogonalGroup Q ⊓ commutant (coordinateSemilinearMap g.val) :=
    inf_le_inf_right _ (Subgroup.commutator_le_self _)
  have hnorm : ((orthogonalOmega Q ⊓ commutant (coordinateSemilinearMap g.val)).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup Q ⊓ commutant (coordinateSemilinearMap g.val))).Normal
      := by
    rw [normal_subgroupOf_iff hle]
    intro h k hh hk
    rw [Subgroup.mem_inf] at hh hk ⊢
    refine ⟨?_, mul_mem (mul_mem hk.2 hh.2) (inv_mem hk.2)⟩
    exact (mem_normalizer_iff.mp (Subgroup.normalizer_commutator_ge_left _ _ hk.1) h).mp hh.1
  refine ⟨Y, isComponentOf_of_normal_le hYc1 hle hnorm, hYc1.1.trans inf_le_left, ?_, ?_⟩
  · set eY : Ym ≃* Y := Ym.equivMapOfInjective J hJi with heY
    have hρ : ∀ y : Ym, π y ∈ X := fun y => by
      rw [← hYmap]
      exact mem_map_of_mem π y.2
    set ρm : Ym →* X := (π.comp Ym.subtype).codRestrict X hρ with hρm
    refine ⟨ρm.comp eY.symm.toMonoidHom, ?_, ?_⟩
    · intro x
      have hx : (x : matrixProjectiveDerived Q) ∈ Ym.map π := by rw [hYmap]; exact x.2
      obtain ⟨y, hy, hyx⟩ := hx
      refine ⟨eY ⟨y, hy⟩, Subtype.ext ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      exact hyx
    · intro y hy
      have h1 : π (eY.symm y : matrixDerived Q) = 1 := congrArg Subtype.val hy
      have h2 : (eY.symm y : matrixDerived Q) ∈ center (matrixDerived Q) :=
        ker_matrixProjectiveProjection_le Q h1
      rw [mem_center_iff] at h2 ⊢
      intro z
      apply eY.symm.injective
      apply Subtype.ext
      rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
      exact h2 _
  · intro hW t s ht hs ht2 htn htY hst
    obtain ⟨tm, rfl⟩ : ∃ tm, J tm = t := by
      rw [← range_derivedLinear] at ht
      exact ht
    obtain ⟨sm, rfl⟩ : ∃ sm, J sm = s := by
      rw [← range_derivedLinear] at hs
      exact hs
    have hd : 0 < d := by
      by_contra hd0
      obtain rfl : d = 0 := by omega
      apply htn 0
      ext v i
      exact Fin.elim0 i
    have hscal : ∀ (M : matrixDerived Q) (c : K),
        ((J M : (Fin d → K) ≃ₗ[K] (Fin d → K)) : (Fin d → K) →ₗ[K] (Fin d → K)) =
          c • LinearMap.id → M ∈ matrixDerivedScalars Q := by
      intro M c hM
      have hc0 : c ≠ 0 := by
        rintro rfl
        have h0 := LinearMap.congr_fun hM (Pi.single ⟨0, hd⟩ 1)
        rw [zero_smul, LinearMap.zero_apply, LinearEquiv.coe_coe,
          LinearEquiv.map_eq_zero_iff] at h0
        simpa using congrFun h0 ⟨0, hd⟩
      refine ⟨Units.mk0 c hc0, ?_⟩
      apply matrixLinearIso.injective
      refine LinearEquiv.ext fun v => ?_
      rw [show matrixLinearIso (GeneralLinearGroup.scalar (Fin d) (Units.mk0 c hc0)) v =
        matrixLinearEquiv (GeneralLinearGroup.scalar (Fin d) (Units.mk0 c hc0)) v from rfl,
        LocalAnalysis.ComponentInitial.OddOrthogonal.matrixLinearEquiv_scalar]
      have := LinearMap.congr_fun hM v
      rw [LinearEquiv.coe_coe] at this
      exact (this.trans (by simp)).symm
    have htP1 : π tm ≠ 1 := by
      intro h
      have hmem : tm ∈ matrixDerivedScalars Q := by
        rw [← QuotientGroup.ker_mk' (matrixDerivedScalars Q)]
        exact h
      obtain ⟨c, hc⟩ := (mem_matrixDerivedScalars_iff Q tm).mp hmem
      apply htn c
      refine LinearMap.ext fun v => ?_
      change matrixLinearEquiv tm.val v = (c : K) • v
      rw [← hc, LocalAnalysis.ComponentInitial.OddOrthogonal.matrixLinearEquiv_scalar]
    have htP2 : π tm * π tm = 1 := by
      obtain ⟨c, hc⟩ := ht2
      rw [← map_mul]
      have hmem := hscal (tm * tm) c (by rw [map_mul]; exact hc)
      rw [← QuotientGroup.ker_mk' (matrixDerivedScalars Q)] at hmem
      exact hmem
    have hord : orderOf (π tm) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact htP2) htP1
    have hcomm : ∀ x ∈ X, x * π tm = π tm * x := by
      intro x hx
      rw [← hYmap] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have h1 := htY (J y) (mem_map_of_mem J hy)
      rw [← map_mul, ← map_mul] at h1 ⊢
      rw [hJi h1]
    have hst' : π sm * π tm = π tm * π sm := by
      have h1 : sm * tm = tm * sm := hJi (by rw [map_mul, map_mul]; exact hst)
      rw [← map_mul, ← map_mul, h1]
    have hN := hW (π tm) (π sm) hord hcomm hst'
    have hN' : sm ∈ normalizer ((X.comap π : Subgroup (matrixDerived Q)) : Set (matrixDerived Q))
        := by
      rw [mem_normalizer_iff] at hN ⊢
      intro z
      rw [mem_comap, mem_comap, map_mul, map_mul, map_inv]
      exact hN (π z)
    exact map_mem_normalizer J (mem_normalizer_commutator hN')

end Lift

end CFSG.ComponentClassification.OddClassSelector
