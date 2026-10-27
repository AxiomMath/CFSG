module

public import CFSG.LieType.AlgebraicGroups.MaximalTorusConjugacy
public import CFSG.LieType.AlgebraicGroups.ClosedConeLimit

public noncomputable section

open WithConv TauCeti.Comodule CFSG.LieType.AlgebraicGroups.ClosedCone
open CFSG.LieType.AlgebraicGroups.TorusConjugacy

namespace CFSG.LieType.AlgebraicGroups.NormalizerFixedScalar

universe u

variable {k : Type u} [Field k]

section Weight

variable {M : Type u} [CommRing M] [HopfAlgebra k M]
variable {W : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k M W]

@[expose] def weightCoordinate (μ : M →ₐc[k] LaurentPolynomial k) :
    M →ₐc[k] MonoidAlgebra k (Multiplicative ℤ) :=
  (AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp μ

variable (W) in
abbrev weightSpace (μ : M →ₐc[k] LaurentPolynomial k) (m : Multiplicative ℤ) : Submodule k W :=
  TauCeti.DiagonalizableGroup.weightSpace W
    (weightCoordinate μ : M →ₗc[k] MonoidAlgebra k (Multiplicative ℤ)) m

theorem basePointsRepresentation_pointsHom_of_mem_weightSpace
    (μ : M →ₐc[k] LaurentPolynomial k) (t : kˣ) {m : Multiplicative ℤ} {v : W}
    (hv : v ∈ weightSpace W μ m) :
    basePointsRepresentation (H := M) W (TauCeti.Cocharacter.pointsHom k μ t) v =
      ((t : k) ^ Multiplicative.toAdd m) • v := by
  set σ : MonoidAlgebra k (Multiplicative ℤ) →ₐ[k] k :=
    (TauCeti.MultiplicativeGroup.point (R := k) t).comp
      ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).symm.toBialgHom :
        MonoidAlgebra k (Multiplicative ℤ) →ₐ[k] LaurentPolynomial k) with hσ
  have hpt : TauCeti.Cocharacter.pointsHom k μ t =
      toConv (σ.comp (weightCoordinate μ : M →ₐ[k] MonoidAlgebra k (Multiplicative ℤ))) := by
    rw [TauCeti.Cocharacter.pointsHom_apply]
    apply WithConv.ofConv_injective
    refine AlgHom.ext fun x => ?_
    change TauCeti.MultiplicativeGroup.point (R := k) t (μ x) =
      TauCeti.MultiplicativeGroup.point (R := k) t
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).symm
          (AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ (μ x)))
    rw [BialgEquiv.symm_apply_apply]
  have hσm : σ (MonoidAlgebra.single m 1) = (t : k) ^ Multiplicative.toAdd m := by
    have h1 : MonoidAlgebra.single m (1 : k) = AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ
        (AddMonoidAlgebra.single (Multiplicative.toAdd m) 1) := by
      rw [AddMonoidAlgebra.toMultiplicativeBialgEquiv_single, ofAdd_toAdd]
    have hT : (AddMonoidAlgebra.single (Multiplicative.toAdd m) (1 : k) : LaurentPolynomial k) =
        LaurentPolynomial.T (Multiplicative.toAdd m) := by
      rw [LaurentPolynomial.single_eq_C_mul_T]
      simp
    rw [hσ, h1]
    change TauCeti.MultiplicativeGroup.point (R := k) t
      ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).symm
        (AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ
          (AddMonoidAlgebra.single (Multiplicative.toAdd m) 1))) = _
    rw [BialgEquiv.symm_apply_apply, hT, TauCeti.MultiplicativeGroup.point_T,
      Units.val_zpow_eq_zpow_val]
  rw [hpt, basePointsRepresentation_apply]
  change TensorProduct.lid k W
    (endOfPoint W (σ.comp (weightCoordinate μ : M →ₐ[k] MonoidAlgebra k (Multiplicative ℤ)))
      (1 ⊗ₜ[k] v)) = _
  rw [TauCeti.DiagonalizableGroup.endOfPoint_tmul_of_mem_weightSpace (V := W)
    (π := weightCoordinate μ) (f := σ) (a := 1) hv, TensorProduct.lid_tmul, one_mul, hσm]

theorem exists_finsupp_mem_weightSpace (μ : M →ₐc[k] LaurentPolynomial k) (v : W) :
    ∃ f : Multiplicative ℤ →₀ W, (∀ m, f m ∈ weightSpace W μ m) ∧ (f.sum fun _ x => x) = v := by
  have htop : ⨆ m, weightSpace W μ m = ⊤ :=
    DirectSum.IsInternal.submodule_iSup_eq_top (dec_ι := Classical.decEq _)
      (TauCeti.DiagonalizableGroup.isInternal_weightSpace W
        (weightCoordinate μ : M →ₗc[k] MonoidAlgebra k (Multiplicative ℤ)))
  refine (Submodule.mem_iSup_iff_exists_finsupp _ v).mp ?_
  rw [htop]
  exact Submodule.mem_top

variable (W) in
@[expose] def eigenWeight (μ : M →ₐc[k] LaurentPolynomial k) (m : ℤ) : Submodule k W where
  carrier := {v | ∀ t : kˣ,
    basePointsRepresentation (H := M) W (TauCeti.Cocharacter.pointsHom k μ t) v =
      ((t : k) ^ m) • v}
  add_mem' {v w} hv hw t := by
    rw [map_add, hv t, hw t, smul_add]
  zero_mem' t := by
    rw [map_zero, smul_zero]
  smul_mem' c v hv t := by
    rw [map_smul, hv t, smul_comm]

theorem weightSpace_le_eigenWeight (μ : M →ₐc[k] LaurentPolynomial k) (m : Multiplicative ℤ) :
    weightSpace W μ m ≤ eigenWeight W μ (Multiplicative.toAdd m) :=
  fun _ hv t => basePointsRepresentation_pointsHom_of_mem_weightSpace μ t hv

theorem basePointsRepresentation_mem_eigenWeight {μ : M →ₐc[k] LaurentPolynomial k} {m : ℤ}
    {s : WithConv (M →ₐ[k] k)} (hs : ∀ t : kˣ, Commute (TauCeti.Cocharacter.pointsHom k μ t) s)
    {v : W} (hv : v ∈ eigenWeight W μ m) :
    basePointsRepresentation (H := M) W s v ∈ eigenWeight W μ m := by
  intro t
  rw [← Module.End.mul_apply, ← map_mul, (hs t).eq, map_mul, Module.End.mul_apply, hv t,
    map_smul]

end Weight

section OrbitCone

variable {M : Type u} [CommRing M] [HopfAlgebra k M]
variable {W : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k M W]

theorem mem_orbitCone_of_mem_orbitCone {w x z : W} (hx : x ∈ orbitCone k M w) (hx0 : x ≠ 0)
    (hz : z ∈ orbitCone k M w) : z ∈ orbitCone k M x := by
  obtain ⟨g, c, rfl⟩ := hx
  obtain ⟨h, d, rfl⟩ := hz
  have hc : c ≠ 0 := by
    rintro rfl
    exact hx0 (zero_smul k _)
  refine ⟨h * g⁻¹, d * c⁻¹, ?_⟩
  rw [map_smul, ← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one,
    smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]

end OrbitCone

variable [IsAlgClosed k]

section Normalizer

variable (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
variable {W : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k M W]

theorem exists_mem_normalizer_mem_span {I : TauCeti.HopfIdeal k M}
    (hI : TauCeti.HopfIdeal.IsMaximalTorus k M.obj I) {x y : W} (hx0 : x ≠ 0)
    (hy : y ∈ orbitCone k M x)
    (hxT : ∀ s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k),
      basePointsRepresentation (H := M) W s x ∈ k ∙ x)
    (hyT : ∀ s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k),
      basePointsRepresentation (H := M) W s y ∈ k ∙ y) :
    ∃ n ∈ Subgroup.normalizer
        (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
          Set (WithConv (M →ₐ[k] k))),
      y ∈ k ∙ basePointsRepresentation (H := M) W n x := by
  obtain ⟨g, c, rfl⟩ := hy
  by_cases hc : c = 0
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [hc, zero_smul]
    exact Submodule.zero_mem _
  have hmv : ∀ x : WithConv (M →ₐ[k] k),
      TauCeti.AlgHom.mapValue (H := M) (Algebra.ofId k k) x = x := fun x => by
    ext h
    simp
  let S := lineStabilizer k M x
  have hTS : TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) ≤ S :=
    fun s hs => (mem_lineStabilizer_iff hx0 s).mpr (hxT s hs)
  have hT'S : TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj (I.conjugate g⁻¹)
      (CommAlgCat.of k k) ≤ S := by
    intro z hz
    have hs : g * z * g⁻¹ ∈
        TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) := by
      refine (TauCeti.CommHopfAlgCat.pointConjugation_mem_conjugate_iff I g⁻¹
        (CommAlgCat.of k k) (g * z * g⁻¹)).mp ?_
      rw [hmv, inv_inv, show g⁻¹ * (g * z * g⁻¹) * g = z by group]
      exact hz
    have h1 := hyT _ hs
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, show g * z * g⁻¹ * g = g * z by group,
      map_mul, Module.End.mul_apply] at h1
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h1
    rw [mem_lineStabilizer_iff hx0]
    refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
    have h2 := congrArg (fun v => c⁻¹ • basePointsRepresentation (H := M) W g⁻¹ v) ha
    simp only [map_smul, smul_smul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left] at h2
    rwa [show c⁻¹ * (a * c) = a by field_simp, inv_mul_cancel₀ hc, one_smul, inv_mul_cancel,
      map_one, Module.End.one_apply] at h2
  let J := closureIdentityComponent M S
  have hdomJ : IsDomain (TauCeti.FiniteTypeCommHopfAlgCat.quotient M J) :=
    isDomain_quotient_closureIdentityComponent M S
  have hT' := hI.conjugate g⁻¹
  have hJ : ∀ {I' : TauCeti.HopfIdeal k M}, TauCeti.HopfIdeal.IsMaximalTorus k M.obj I' →
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I' (CommAlgCat.of k k) ≤ S →
        J ≤ I' := by
    intro I' hI' hI'S
    have : IsDomain (TauCeti.FiniteTypeCommHopfAlgCat.quotient M I') :=
      isDomain_quotient_of_isMaximalTorus M hI'
    have : ConnectedSpace (PrimeSpectrum (TauCeti.FiniteTypeCommHopfAlgCat.quotient M I')) :=
      connectedSpace_iff_univ.mpr (IrreducibleSpace.isIrreducible_univ _).isConnected
    exact closureIdentityComponent_le M hI'S
  have hJ₁ : J ≤ I := hJ hI hTS
  have hJ₂ : J ≤ I.conjugate g⁻¹ := hJ hT' hT'S
  obtain ⟨h', hh'⟩ := exists_conjugate_eq_of_isMaximalTorus
    (TauCeti.FiniteTypeCommHopfAlgCat.quotient M J) (isMaximalTorus_map M hJ₁ hI)
    (isMaximalTorus_map M hJ₂ hT')
  have hconj := conjugate_eq_of_map_conjugate_eq M hJ₁ hJ₂ h' hh'
  set s := TauCeti.CommHopfAlgCat.quotientPointsHom M.obj J (CommAlgCat.of k k) h'
  have hsS : s ∈ S := by
    have hmem : s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k) :=
      ⟨h', rfl⟩
    have hmem' := quotientPointsSubgroup_closureIdentityComponent_le M S hmem
    rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hmem'
    exact mem_lineStabilizer_of_forall_mem_vanishingIdeal hx0 hmem'
  have hn : I.conjugate (g * s) = I := by
    rw [TauCeti.HopfIdeal.conjugate_mul, hconj, TauCeti.HopfIdeal.conjugate_conjugate_inv]
  refine ⟨g * s, ?_, ?_⟩
  · refine Subgroup.mem_normalizer_iff.mpr fun z => ?_
    have h := TauCeti.CommHopfAlgCat.pointConjugation_mem_conjugate_iff I (g * s)
      (CommAlgCat.of k k) z
    rw [hmv, hn] at h
    exact h.symm
  · obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (mem_lineStabilizer.mp hsS).2
    have hx : x = b • basePointsRepresentation (H := M) W s x := by
      have := congrArg (basePointsRepresentation (H := M) W s) hb
      rwa [map_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply, eq_comm] at this
    refine Submodule.mem_span_singleton.mpr ⟨c * b, ?_⟩
    conv_rhs => rw [hx]
    rw [map_smul, map_mul, Module.End.mul_apply, smul_smul]

variable {M}

theorem basePointsRepresentation_pointsHom_eq_smul_of_mem_orbitCone
    {I : TauCeti.HopfIdeal k M} (hI : TauCeti.HopfIdeal.IsMaximalTorus k M.obj I)
    (μ : M →ₐc[k] LaurentPolynomial k)
    (hfixed : ∀ g ∈ Subgroup.normalizer
        (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
          Set (WithConv (M →ₐ[k] k))),
      ∀ t : kˣ, g * TauCeti.Cocharacter.pointsHom k μ t * g⁻¹ =
        TauCeti.Cocharacter.pointsHom k μ t)
    {x y : W} (hx0 : x ≠ 0) (hy : y ∈ orbitCone k M x)
    (hxT : ∀ s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k),
      basePointsRepresentation (H := M) W s x ∈ k ∙ x)
    (hyT : ∀ s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k),
      basePointsRepresentation (H := M) W s y ∈ k ∙ y)
    (t : kˣ) {c : k}
    (hc : basePointsRepresentation (H := M) W (TauCeti.Cocharacter.pointsHom k μ t) x = c • x) :
    basePointsRepresentation (H := M) W (TauCeti.Cocharacter.pointsHom k μ t) y = c • y := by
  obtain ⟨n, hn, hy'⟩ := exists_mem_normalizer_mem_span M hI hx0 hy hxT hyT
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy'
  have hcomm : TauCeti.Cocharacter.pointsHom k μ t * n =
      n * TauCeti.Cocharacter.pointsHom k μ t := by
    have h := hfixed n⁻¹ (Subgroup.inv_mem _ hn) t
    rw [inv_inv] at h
    calc TauCeti.Cocharacter.pointsHom k μ t * n =
        n * (n⁻¹ * TauCeti.Cocharacter.pointsHom k μ t * n) := by group
      _ = n * TauCeti.Cocharacter.pointsHom k μ t := by rw [h]
  rw [map_smul, ← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply, hc,
    map_smul, smul_comm]

theorem exists_forall_mem_orbitCone_eq_smul {I : TauCeti.HopfIdeal k M}
    (hI : TauCeti.HopfIdeal.IsMaximalTorus k M.obj I) (μ : M →ₐc[k] LaurentPolynomial k)
    (hμ : ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k μ t ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k))
    (hfixed : ∀ g ∈ Subgroup.normalizer
        (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
          Set (WithConv (M →ₐ[k] k))),
      ∀ t : kˣ, g * TauCeti.Cocharacter.pointsHom k μ t * g⁻¹ =
        TauCeti.Cocharacter.pointsHom k μ t)
    [FiniteDimensional k W] {w : W} (hw0 : w ≠ 0)
    (hclosed : IsZariskiClosed k (orbitCone k M w)) :
    ∃ χ : kˣ → k, ∀ t : kˣ, ∀ y ∈ orbitCone k M w,
      basePointsRepresentation (H := M) W (TauCeti.Cocharacter.pointsHom k μ t) y = χ t • y := by
  have hcone : IsCone k (orbitCone k M w) := by
    rintro c _ ⟨g, d, rfl⟩
    exact ⟨g, c * d, by rw [smul_smul]⟩
  have hG : ∀ g : WithConv (M →ₐ[k] k), ∀ v ∈ orbitCone k M w,
      basePointsRepresentation (H := M) W g v ∈ orbitCone k M w := by
    rintro g _ ⟨h, d, rfl⟩
    exact ⟨g * h, d, by rw [map_smul, map_mul, Module.End.mul_apply]⟩
  have hne : ∃ v ∈ orbitCone k M w, v ≠ 0 := ⟨w, ⟨1, 1, by simp⟩, hw0⟩
  obtain ⟨x₀, hx₀, hx₀0, hx₀T⟩ := exists_ne_zero_mem_forall_mem_span_of_isMaximalTorus M hI
    hclosed hcone (fun s _ => hG s) hne
  choose χ hχ using fun t : kˣ => Submodule.mem_span_singleton.mp (hx₀T _ (hμ t))
  have hfix : ∀ z ∈ orbitCone k M w,
      (∀ s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k),
        basePointsRepresentation (H := M) W s z ∈ k ∙ z) → ∀ t : kˣ,
      basePointsRepresentation (H := M) W (TauCeti.Cocharacter.pointsHom k μ t) z = χ t • z :=
    fun z hz hzT t => basePointsRepresentation_pointsHom_eq_smul_of_mem_orbitCone hI μ hfixed
      hx₀0 (mem_orbitCone_of_mem_orbitCone hx₀ hx₀0 hz) hx₀T hzT t (hχ t).symm
  have hweight : ∀ (m : ℤ) (v : W), v ∈ orbitCone k M w → v ∈ eigenWeight W μ m → v ≠ 0 →
      ∀ t : kˣ, χ t = (t : k) ^ m := by
    intro m v hvX hvm hv0 t
    have hC : IsZariskiClosed k (orbitCone k M w ∩ (eigenWeight W μ m : Set W)) :=
      hclosed.inter (isZariskiClosed_submodule _)
    have hCcone : IsCone k (orbitCone k M w ∩ (eigenWeight W μ m : Set W)) :=
      fun c v hv => ⟨hcone c v hv.1, Submodule.smul_mem _ c hv.2⟩
    have hCT : ∀ s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k),
        ∀ v ∈ orbitCone k M w ∩ (eigenWeight W μ m : Set W),
          basePointsRepresentation (H := M) W s v ∈
            orbitCone k M w ∩ (eigenWeight W μ m : Set W) :=
      fun s hs v hv => ⟨hG s v hv.1, basePointsRepresentation_mem_eigenWeight
        (fun t => commute_of_mem_quotientPointsSubgroup_of_isMaximalTorus M hI (hμ t) hs) hv.2⟩
    obtain ⟨z, hz, hz0, hzT⟩ := exists_ne_zero_mem_forall_mem_span_of_isMaximalTorus M hI hC
      hCcone hCT ⟨v, ⟨hvX, hvm⟩, hv0⟩
    have h1 := hfix z hz.1 hzT t
    rw [hz.2 t] at h1
    exact (smul_left_injective k hz0 h1).symm
  refine ⟨χ, fun t y hy => ?_⟩
  by_cases hy0 : y = 0
  · rw [hy0, map_zero, smul_zero]
  obtain ⟨f, hfW, hfsum⟩ := exists_finsupp_mem_weightSpace μ y
  have hs : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hy0
    rw [← hfsum, Finsupp.sum, h, Finset.sum_empty]
  have hact : ∀ t : kˣ,
      basePointsRepresentation (H := M) W (TauCeti.Cocharacter.pointsHom k μ t) y =
        ∑ m ∈ f.support, ((t : k) ^ Multiplicative.toAdd m) • f m := by
    intro t
    rw [← hfsum, Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun m _ =>
      basePointsRepresentation_pointsHom_of_mem_weightSpace μ t (hfW m)
  have hcurve : ∀ t : k, t ≠ 0 →
      ∑ m ∈ f.support, t ^ Multiplicative.toAdd m • f m ∈ orbitCone k M w := by
    intro t ht
    rw [show t = ((Units.mk0 t ht : kˣ) : k) from rfl, ← hact]
    exact hG _ y hy
  have hext : ∀ m ∈ f.support, f m ∈ orbitCone k M w → ∀ t : kˣ,
      χ t = (t : k) ^ Multiplicative.toAdd m := fun m hm hmX =>
    hweight _ (f m) hmX (weightSpace_le_eigenWeight μ m (hfW m)) (Finsupp.mem_support_iff.mp hm)
  obtain ⟨m₁, hm₁, hm₁min⟩ := f.support.exists_min_image (fun m => Multiplicative.toAdd m) hs
  obtain ⟨m₂, hm₂, hm₂max⟩ := f.support.exists_max_image (fun m => Multiplicative.toAdd m) hs
  have hlow : f m₁ ∈ orbitCone k M w := by
    have h := hclosed.sum_lowest_mem hcone f.support hs (fun m => Multiplicative.toAdd m) f hcurve
    rwa [Finset.sum_eq_single_of_mem m₁ ?_ ?_] at h
    · exact Finset.mem_filter.mpr ⟨hm₁, hm₁min⟩
    · intro b hb hne
      exact absurd (Multiplicative.toAdd.injective (le_antisymm
        ((Finset.mem_filter.mp hb).2 m₁ hm₁) (hm₁min b (Finset.mem_filter.mp hb).1))) hne
  have hhigh : f m₂ ∈ orbitCone k M w := by
    have h := hclosed.sum_highest_mem hcone f.support hs (fun m => Multiplicative.toAdd m) f hcurve
    rwa [Finset.sum_eq_single_of_mem m₂ ?_ ?_] at h
    · exact Finset.mem_filter.mpr ⟨hm₂, hm₂max⟩
    · intro b hb hne
      exact absurd (Multiplicative.toAdd.injective (le_antisymm
        (hm₂max b (Finset.mem_filter.mp hb).1) ((Finset.mem_filter.mp hb).2 m₂ hm₂))) hne
  have h₁ := hext m₁ hm₁ hlow
  have h₂ := hext m₂ hm₂ hhigh
  have heq : Multiplicative.toAdd m₁ = Multiplicative.toAdd m₂ := by
    by_contra hne
    obtain ⟨t₀, ht₀⟩ := RegularCocharacter.exists_unit_pow_separating (k := k)
      {Multiplicative.toAdd m₁, Multiplicative.toAdd m₂}
    exact ht₀ _ (Finset.mem_insert_self _ _) _
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hne ((h₁ t₀).symm.trans (h₂ t₀))
  rw [hact t]
  rw [← hfsum, Finsupp.sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : Multiplicative.toAdd m = Multiplicative.toAdd m₁ :=
    le_antisymm (heq ▸ hm₂max m hm) (hm₁min m hm)
  rw [hm', h₁ t]

theorem exists_ne_bot_stable_smul_of_normalizer_fixed [IsDomain M] {I : TauCeti.HopfIdeal k M}
    (hI : TauCeti.HopfIdeal.IsMaximalTorus k M.obj I) (μ : M →ₐc[k] LaurentPolynomial k)
    (hμ : ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k μ t ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k))
    (hfixed : ∀ g ∈ Subgroup.normalizer
        (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
          Set (WithConv (M →ₐ[k] k))),
      ∀ t : kˣ, g * TauCeti.Cocharacter.pointsHom k μ t * g⁻¹ =
        TauCeti.Cocharacter.pointsHom k μ t)
    [FiniteDimensional k W] (hW : ∃ v : W, v ≠ 0) :
    ∃ U : Submodule k W, U ≠ ⊥ ∧
      (∀ g : WithConv (M →ₐ[k] k), ∀ v ∈ U, basePointsRepresentation (H := M) W g v ∈ U) ∧
      ∀ t : kˣ, ∃ c : k, ∀ v ∈ U,
        basePointsRepresentation (H := M) W (TauCeti.Cocharacter.pointsHom k μ t) v = c • v := by
  obtain ⟨v₀, hv₀⟩ := hW
  have hC : IsZariskiClosed k (Set.univ : Set W) := ⟨∅, by ext v; simp [zeroSet]⟩
  obtain ⟨w, -, hw0, hclosed⟩ := exists_isZariskiClosed_orbitCone (k := k) (H := M) (M := W)
    hC (fun _ _ _ => Set.mem_univ _) (fun _ _ _ => Set.mem_univ _) ⟨v₀, Set.mem_univ _, hv₀⟩
  obtain ⟨χ, hχ⟩ := exists_forall_mem_orbitCone_eq_smul hI μ hμ hfixed hw0 hclosed
  refine ⟨Submodule.span k (orbitCone k M w), ?_, fun g v hv => ?_, fun t => ⟨χ t, fun v hv => ?_⟩⟩
  · rw [Ne, Submodule.span_eq_bot]
    exact fun h => hw0 (h w ⟨1, 1, by simp⟩)
  · have hle : Submodule.span k (orbitCone k M w) ≤
        (Submodule.span k (orbitCone k M w)).comap
          (basePointsRepresentation (H := M) W g : W →ₗ[k] W) := by
      refine Submodule.span_le.mpr fun y hy => Submodule.subset_span ?_
      obtain ⟨h, d, rfl⟩ := hy
      exact ⟨g * h, d, by rw [map_smul, map_mul, Module.End.mul_apply]⟩
    exact hle hv
  · induction hv using Submodule.span_induction with
    | mem y hy => exact hχ t y hy
    | zero => rw [map_zero, smul_zero]
    | add y z _ _ hy hz => rw [map_add, hy, hz, smul_add]
    | smul a y _ hy => rw [map_smul, hy, smul_comm]

theorem exists_smul_of_forall_eq_bot_or_eq_top [IsDomain M] {I : TauCeti.HopfIdeal k M}
    (hI : TauCeti.HopfIdeal.IsMaximalTorus k M.obj I) (μ : M →ₐc[k] LaurentPolynomial k)
    (hμ : ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k μ t ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k))
    (hfixed : ∀ g ∈ Subgroup.normalizer
        (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
          Set (WithConv (M →ₐ[k] k))),
      ∀ t : kˣ, g * TauCeti.Cocharacter.pointsHom k μ t * g⁻¹ =
        TauCeti.Cocharacter.pointsHom k μ t)
    [FiniteDimensional k W] (hW : ∀ N : TauCeti.Subcomodule k M W, N = ⊥ ∨ N = ⊤) (t : kˣ) :
    ∃ c : k, ∀ v : W,
      basePointsRepresentation (H := M) W (TauCeti.Cocharacter.pointsHom k μ t) v = c • v := by
  by_cases hW0 : ∃ v : W, v ≠ 0
  swap
  · simp only [ne_eq, not_exists, not_not] at hW0
    exact ⟨0, fun v => by rw [hW0 v, map_zero, smul_zero]⟩
  obtain ⟨U, hU0, hUstab, hUμ⟩ :=
    exists_ne_bot_stable_smul_of_normalizer_fixed hI μ hμ hfixed hW0
  have hstable : ∀ (g : M →ₐ[k] k) {m : W}, m ∈ U →
      TauCeti.Comodule.endOfPoint W g ((1 : k) ⊗ₜ[k] m) ∈ U.baseChange k := by
    intro g m hm
    rw [endOfPoint_tmul, one_smul, endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation]
    exact Submodule.tmul_mem_baseChange_of_mem _ (hUstab (toConv g) m hm)
  have hUtop : U = ⊤ := by
    rw [← TauCeti.Subcomodule.ofEndOfPointStable_toSubmodule (K := k) U hstable]
    refine TauCeti.Subcomodule.toSubmodule_eq_top.mpr
      ((hW (TauCeti.Subcomodule.ofEndOfPointStable (K := k) U hstable)).resolve_left fun h => ?_)
    apply hU0
    rw [← TauCeti.Subcomodule.ofEndOfPointStable_toSubmodule (K := k) U hstable]
    exact TauCeti.Subcomodule.toSubmodule_eq_bot.mpr h
  obtain ⟨c, hc⟩ := hUμ t
  exact ⟨c, fun v => hc v (hUtop ▸ Submodule.mem_top)⟩

end Normalizer

theorem exists_smul_of_reductive
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hM : TauCeti.reductiveCommHopfAlgProperty k M)
    (I : TauCeti.HopfIdeal k M) (hI : TauCeti.HopfIdeal.IsMaximalTorus k M.obj I)
    (μ : M →ₐc[k] LaurentPolynomial k)
    (hμ : ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k μ t ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k))
    (hfixed : ∀ g ∈ Subgroup.normalizer
        (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
          Set (WithConv (M →ₐ[k] k))),
      ∀ t : kˣ, g * TauCeti.Cocharacter.pointsHom k μ t * g⁻¹ =
        TauCeti.Cocharacter.pointsHom k μ t)
    (W : TauCeti.FGComoduleCat.{u,u,u} k M)
    (hW : ∀ N : TauCeti.Subcomodule k M W, N = ⊥ ∨ N = ⊤) (t : kˣ) :
    ∃ c : k, ∀ v : W,
      basePointsRepresentation (H := M) W (TauCeti.Cocharacter.pointsHom k μ t) v = c • v := by
  let : Algebra.Smooth k M := hM.smooth
  let : ConnectedSpace (PrimeSpectrum M) :=
    TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace k M.obj
      hM.geometricallyConnected
  let : IsDomain M := CFSG.isDomain_of_smooth_of_connected (k := k) M
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup k
  exact exists_smul_of_forall_eq_bot_or_eq_top hI μ hμ hfixed hW t

end CFSG.LieType.AlgebraicGroups.NormalizerFixedScalar
