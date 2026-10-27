module

public import CFSG.LieType.AlgebraicGroups.NormalizerFixedScalar
public import CFSG.LieType.AlgebraicGroups.TorusNormalizerOrbit
public import CFSG.LieType.AlgebraicGroups.FiniteComoduleScalarFiltration
public import CFSG.LieType.AlgebraicGroups.GradedRepresentationKernel
public import CFSG.LieType.AlgebraicGroups.ReductiveNormalUnipotent

public noncomputable section

open WithConv TauCeti.Comodule CFSG.LieType.AlgebraicGroups.ClosedCone
open CFSG.LieType.AlgebraicGroups.TorusConjugacy CFSG.LieType.AlgebraicGroups.RegularCocharacter
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.CentralizerUnipotent

universe u

variable {k : Type u} [Field k]

section Lagrange

variable {V : Type u} [AddCommGroup V] [Module k V]

theorem aeval_apply_mem {D : Module.End k V} {E : Submodule k V} (hE : ∀ v ∈ E, D v ∈ E)
    (p : Polynomial k) {v : V} (hv : v ∈ E) : Polynomial.aeval D p v ∈ E := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply]; exact E.add_mem hp hq
  | monomial m a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    refine E.smul_mem a ?_
    induction m with
    | zero => simpa using hv
    | succ m ih => rw [pow_succ', Module.End.mul_apply]; exact hE _ ih

theorem aeval_apply_comm {D A : Module.End k V} (h : Commute A D) (p : Polynomial k) (v : V) :
    A (Polynomial.aeval D p v) = Polynomial.aeval D p (A v) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, hp, hq]
  | monomial m a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul,
      ← Module.End.mul_apply, ← Module.End.mul_apply, (h.pow_right m).eq]

end Lagrange

section Weights

variable {M : Type u} [CommRing M] [HopfAlgebra k M] {n : ℕ}
variable (π : M →ₐc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))
variable {W : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k M W]

abbrev wt (χ : Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) : Submodule k W :=
  TauCeti.DiagonalizableGroup.weightSpace W
    (π : M →ₗc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) χ

theorem exists_finsupp_mem_wt (v : W) :
    ∃ f : Multiplicative (ULift.{u} (Fin n) →₀ ℤ) →₀ W, (∀ χ, f χ ∈ wt π (W := W) χ) ∧
      (f.sum fun _ x => x) = v := by
  have htop : ⨆ χ, wt π (W := W) χ = ⊤ :=
    DirectSum.IsInternal.submodule_iSup_eq_top (dec_ι := Classical.decEq _)
      (TauCeti.DiagonalizableGroup.isInternal_weightSpace W
        (π : M →ₗc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))))
  refine (Submodule.mem_iSup_iff_exists_finsupp _ v).mp ?_
  rw [htop]
  exact Submodule.mem_top

theorem basePointsRepresentation_mapDomain_of_mem_wt
    (σ : WithConv (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) →ₐ[k] k))
    {χ : Multiplicative (ULift.{u} (Fin n) →₀ ℤ)} {v : W} (hv : v ∈ wt π χ) :
    basePointsRepresentation (H := M) W (TauCeti.AlgHom.mapDomain (A := k) π σ) v =
      σ.ofConv (MonoidAlgebra.single χ 1) • v :=
  basePointsRepresentation_comp_pi_eq_smul π σ.ofConv hv

theorem basePointsRepresentation_pointsHom_of_mem_wt
    (ψ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ) (t : kˣ)
    {χ : Multiplicative (ULift.{u} (Fin n) →₀ ℤ)} {v : W} (hv : v ∈ wt π χ) :
    basePointsRepresentation (H := M) W
        (TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ π) t) v =
      ((t : k) ^ ψ (Multiplicative.toAdd χ)) • v := by
  rw [pointsHom_cocharacterOfAddHom, basePointsRepresentation_mapDomain_of_mem_wt π _ hv]
  congr 1
  exact point_cocharacterOfAddHom_single ψ t χ

end Weights

section Separating

variable {M : Type u} [CommRing M] [HopfAlgebra k M] {n : ℕ}
variable (π : M →ₐc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))
variable {W : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k M W]

theorem exists_separating [IsAlgClosed k]
    (S : Finset (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))) :
    ∃ (ψ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ) (t₀ : kˣ),
      Set.InjOn (fun χ : Multiplicative (ULift.{u} (Fin n) →₀ ℤ) =>
        ψ (Multiplicative.toAdd χ)) S ∧
      Set.InjOn (fun χ : Multiplicative (ULift.{u} (Fin n) →₀ ℤ) =>
        (t₀ : k) ^ ψ (Multiplicative.toAdd χ)) S := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_addHom_separating (σ := ULift.{u} (Fin n))
    (S.image Multiplicative.toAdd)
  obtain ⟨t₀, ht₀⟩ := exists_unit_pow_separating (k := k)
    (S.image fun χ => ψ (Multiplicative.toAdd χ))
  have hinj : Set.InjOn (fun χ : Multiplicative (ULift.{u} (Fin n) →₀ ℤ) =>
      ψ (Multiplicative.toAdd χ)) S := by
    intro a ha b hb hab
    by_contra hne
    exact hψ _ (Finset.mem_image_of_mem _ ha) _ (Finset.mem_image_of_mem _ hb)
      (fun h => hne (Multiplicative.toAdd.injective h)) hab
  refine ⟨ψ, t₀, hinj, fun a ha b hb hab => ?_⟩
  by_contra hne
  exact ht₀ _ (Finset.mem_image_of_mem _ ha) _ (Finset.mem_image_of_mem _ hb)
    (fun h => hne (hinj ha hb h)) hab

variable (W) in
@[expose] def proj (S : Finset (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))
    (ψ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ) (t₀ : kˣ)
    (χ : Multiplicative (ULift.{u} (Fin n) →₀ ℤ)) : Module.End k W :=
  Polynomial.aeval (basePointsRepresentation (H := M) W
      (TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ π) t₀))
    (Lagrange.basis S (fun χ => (t₀ : k) ^ ψ (Multiplicative.toAdd χ)) χ)

theorem proj_finsupp_sum (S : Finset (Multiplicative (ULift.{u} (Fin n) →₀ ℤ)))
    (hS : ∀ χ, wt π (W := W) χ ≠ ⊥ → χ ∈ S) (ψ : (ULift.{u} (Fin n) →₀ ℤ) →+ ℤ) (t₀ : kˣ)
    (hc : Set.InjOn (fun χ : Multiplicative (ULift.{u} (Fin n) →₀ ℤ) =>
      (t₀ : k) ^ ψ (Multiplicative.toAdd χ)) S)
    {χ : Multiplicative (ULift.{u} (Fin n) →₀ ℤ)} (hχ : χ ∈ S)
    {f : Multiplicative (ULift.{u} (Fin n) →₀ ℤ) →₀ W} (hf : ∀ χ', f χ' ∈ wt π χ') :
    proj π W S ψ t₀ χ (f.sum fun _ x => x) = f χ := by
  have hterm : ∀ χ', proj π W S ψ t₀ χ (f χ') =
      (Lagrange.basis S (fun χ => (t₀ : k) ^ ψ (Multiplicative.toAdd χ)) χ).eval
        ((t₀ : k) ^ ψ (Multiplicative.toAdd χ')) • f χ' := fun χ' =>
    aeval_apply_of_apply_eq_smul _ (basePointsRepresentation_pointsHom_of_mem_wt π ψ t₀ (hf χ')) _
  have hS' : ∀ χ', f χ' ≠ 0 → χ' ∈ S := fun χ' h0 =>
    hS χ' fun hbot => h0 ((Submodule.eq_bot_iff _).mp hbot _ (hf χ'))
  rw [Finsupp.sum, map_sum, Finset.sum_eq_single χ]
  · rw [hterm, Lagrange.eval_basis_self hc hχ, one_smul]
  · intro χ' hχ' hne
    have h := Lagrange.eval_basis_of_ne (s := S)
      (v := fun χ : Multiplicative (ULift.{u} (Fin n) →₀ ℤ) =>
        (t₀ : k) ^ ψ (Multiplicative.toAdd χ))
      (Ne.symm hne) (hS' χ' (Finsupp.mem_support_iff.mp hχ'))
    rw [hterm, h, zero_smul]
  · intro hχ'
    rw [Finsupp.notMem_support_iff.mp hχ', map_zero]

end Separating

section Kolchin

variable {G : Type*} [Group G] {V : Type u} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

theorem exists_dual_ne_zero_forall_apply_eq [Nontrivial V] (ρ : G →* Module.End k V)
    (hρ : ∀ g, IsNilpotent (ρ g - 1)) :
    ∃ ℓ : Module.Dual k V, ℓ ≠ 0 ∧ ∀ g v, ℓ (ρ g v) = ℓ v := by
  let ρ' : Representation k G (Module.Dual k V) :=
    { toFun := fun g => (ρ g⁻¹).dualMap
      map_one' := by
        ext ℓ v
        simp
      map_mul' := fun g h => by
        ext ℓ v
        simp [mul_inv_rev, map_mul, Module.End.mul_apply] }
  have hpow : ∀ (f : Module.End k V) (m : ℕ), f.dualMap ^ m = (f ^ m).dualMap := by
    intro f m
    induction m with
    | zero =>
      ext ℓ v
      simp
    | succ m ih =>
      rw [pow_succ, ih, pow_succ']
      ext ℓ v
      simp [Module.End.mul_apply]
  have hnil : ∀ g, IsNilpotent (ρ' g - 1) := by
    intro g
    obtain ⟨m, hm⟩ := hρ g⁻¹
    refine ⟨m, ?_⟩
    have h1 : ρ' g - 1 = (ρ g⁻¹ - 1).dualMap := by
      ext ℓ v
      simp [ρ']
    rw [h1, hpow, hm]
    ext ℓ v
    simp
  have : Nontrivial (Module.Dual k V) := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k V, φ v ≠ 0 := by
      by_contra h
      simp only [ne_eq, not_exists, not_not] at h
      exact hv ((Module.forall_dual_apply_eq_zero_iff k v).mp h)
    exact ⟨⟨φ, 0, fun h => hφ (by rw [h, LinearMap.zero_apply])⟩⟩
  obtain ⟨ℓ, hℓ0, hℓ⟩ := Representation.exists_common_fixed_vector_of_isUnipotent ρ' hnil
  refine ⟨ℓ, hℓ0, fun g v => ?_⟩
  have h := congrArg (fun φ : Module.Dual k V => φ v) (hℓ g⁻¹)
  simpa [ρ'] using h

end Kolchin

section Main

variable [IsAlgClosed k]

theorem basePointsRepresentation_eq_self_of_mem_orbitCone
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    {I : TauCeti.HopfIdeal k M} (hI : TauCeti.HopfIdeal.IsMaximalTorus k M.obj I)
    (J : TauCeti.HopfIdeal k M) [IsDomain (TauCeti.FiniteTypeCommHopfAlgCat.quotient M J)]
    {W : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k M W] [FiniteDimensional k W]
    (hJu : ∀ x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k),
      IsNilpotent (basePointsRepresentation (H := M) W x - 1))
    (hJT : ∀ x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k),
      ∀ s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k),
        Commute x s)
    (hJN : ∀ g ∈ Subgroup.normalizer
        (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
          Set (WithConv (M →ₐ[k] k))),
      ∀ x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k),
        g * x * g⁻¹ ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k))
    {w : W} (hclosed : IsZariskiClosed k (orbitCone k M w))
    {x : WithConv (M →ₐ[k] k)}
    (hx : x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k))
    {y : W} (hy : y ∈ orbitCone k M w) :
    basePointsRepresentation (H := M) W x y = y := by
  classical
  have hcone : IsCone k (orbitCone k M w) := by
    rintro c _ ⟨g, d, rfl⟩
    exact ⟨g, c * d, by rw [smul_smul]⟩
  have hG : ∀ g : WithConv (M →ₐ[k] k), ∀ v ∈ orbitCone k M w,
      basePointsRepresentation (H := M) W g v ∈ orbitCone k M w := by
    rintro g _ ⟨h, d, rfl⟩
    exact ⟨g * h, d, by rw [map_smul, map_mul, Module.End.mul_apply]⟩
  let E : Submodule k W := Submodule.span k (orbitCone k M w)
  have hEG : ∀ g : WithConv (M →ₐ[k] k), ∀ v ∈ E,
      basePointsRepresentation (H := M) W g v ∈ E := by
    intro g v hv
    induction hv using Submodule.span_induction with
    | mem v hv => exact Submodule.subset_span (hG g v hv)
    | zero => rw [map_zero]; exact E.zero_mem
    | add v v' _ _ h h' => rw [map_add]; exact E.add_mem h h'
    | smul a v _ h => rw [map_smul]; exact E.smul_mem a h
  let N : Submodule k W := Submodule.span k {z | ∃ u ∈
    TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k), ∃ v ∈ E,
      z = basePointsRepresentation (H := M) W u v - v}
  have hdisp : ∀ u ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k),
      ∀ v ∈ E, basePointsRepresentation (H := M) W u v - v ∈ N := fun u hu v hv =>
    Submodule.subset_span ⟨u, hu, v, hv, rfl⟩
  have hNstab : ∀ g : WithConv (M →ₐ[k] k),
      (∀ u ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k),
        g * u * g⁻¹ ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J
          (CommAlgCat.of k k)) →
      ∀ z ∈ N, basePointsRepresentation (H := M) W g z ∈ N := by
    intro g hg z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨u, hu, v, hv, rfl⟩ := hz
      have h : basePointsRepresentation (H := M) W g
            (basePointsRepresentation (H := M) W u v - v) =
          basePointsRepresentation (H := M) W (g * u * g⁻¹)
            (basePointsRepresentation (H := M) W g v) -
            basePointsRepresentation (H := M) W g v := by
        rw [map_sub, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
          show g * u * g⁻¹ * g = g * u by group]
      rw [h]
      exact hdisp _ (hg u hu) _ (hEG g v hv)
    | zero => rw [map_zero]; exact N.zero_mem
    | add z z' _ _ h h' => rw [map_add]; exact N.add_mem h h'
    | smul a z _ h => rw [map_smul]; exact N.smul_mem a h
  have hNT : ∀ s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k),
      ∀ z ∈ N, basePointsRepresentation (H := M) W s z ∈ N := fun s hs =>
    hNstab s fun u hu => by
      rw [← (hJT u hu s hs).eq, mul_inv_cancel_right]
      exact hu
  have hNN : ∀ g ∈ Subgroup.normalizer
      (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
        Set (WithConv (M →ₐ[k] k))),
      ∀ z ∈ N, basePointsRepresentation (H := M) W g z ∈ N := fun g hg =>
    hNstab g fun u hu => hJN g hg u hu
  obtain ⟨n, π, hπ, hker⟩ :=
    exists_splitCoordinates M I ((TauCeti.HopfIdeal.isMaximalTorus_iff k M.obj I).mp hI).1
  have hTmem : ∀ s, s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I
      (CommAlgCat.of k k) ↔ ∃ σ, TauCeti.AlgHom.mapDomain (A := k) π σ = s :=
    mem_quotientPointsSubgroup_iff_exists_mapDomain M I π hπ hker
  have hSfin := TauCeti.DiagonalizableGroup.finite_setOf_weightSpace_ne_bot (V := W)
    (π := (π : M →ₗc[k] MonoidAlgebra k (Multiplicative (ULift.{u} (Fin n) →₀ ℤ))))
  let S := hSfin.toFinset
  have hS : ∀ χ, wt π (W := W) χ ≠ ⊥ → χ ∈ S := fun χ h => hSfin.mem_toFinset.mpr h
  obtain ⟨ψ, t₀, hψ, hc⟩ := exists_separating (k := k) S
  have hμT : ∀ t : kˣ, TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ π) t ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) := fun t =>
    (hTmem _).mpr ⟨_, (pointsHom_cocharacterOfAddHom ψ π t).symm⟩
  have hPf : ∀ χ ∈ S, ∀ f : Multiplicative (ULift.{u} (Fin n) →₀ ℤ) →₀ W,
      (∀ χ', f χ' ∈ wt π χ') → proj π W S ψ t₀ χ (f.sum fun _ x => x) = f χ :=
    fun χ hχ f hf => proj_finsupp_sum π S hS ψ t₀ hc hχ hf
  have hPwt : ∀ χ ∈ S, ∀ v, proj π W S ψ t₀ χ v ∈ wt π (W := W) χ := by
    intro χ hχ v
    obtain ⟨f, hf, rfl⟩ := exists_finsupp_mem_wt π v
    rw [hPf χ hχ f hf]
    exact hf χ
  have hPself : ∀ χ ∈ S, ∀ v ∈ wt π (W := W) χ, proj π W S ψ t₀ χ v = v := by
    intro χ hχ v hv
    have h := hPf χ hχ (Finsupp.single χ v) fun χ' => by
      by_cases h : χ = χ'
      · subst h
        simpa using hv
      · rw [Finsupp.single_eq_of_ne (Ne.symm h)]
        exact Submodule.zero_mem _
    rwa [Finsupp.sum_single_index rfl, Finsupp.single_eq_same] at h
  have hPsum : ∀ v, ∑ χ ∈ S, proj π W S ψ t₀ χ v = v := by
    intro v
    obtain ⟨f, hf, rfl⟩ := exists_finsupp_mem_wt π v
    rw [Finset.sum_congr rfl fun χ hχ => hPf χ hχ f hf, Finsupp.sum]
    refine (Finset.sum_subset (fun χ hχ => hS χ fun hbot => Finsupp.mem_support_iff.mp hχ
      ((Submodule.eq_bot_iff _).mp hbot _ (hf χ))) fun χ _ hχ => ?_).symm
    exact Finsupp.notMem_support_iff.mp hχ
  have hPE : ∀ χ, ∀ v ∈ E, proj π W S ψ t₀ χ v ∈ E := fun χ v hv =>
    aeval_apply_mem (hEG _) _ hv
  have hPU : ∀ χ, ∀ u ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J
      (CommAlgCat.of k k), ∀ v, basePointsRepresentation (H := M) W u (proj π W S ψ t₀ χ v) =
        proj π W S ψ t₀ χ (basePointsRepresentation (H := M) W u v) := by
    intro χ u hu v
    refine aeval_apply_comm ?_ _ v
    have h := (hJT u hu _ (hμT t₀)).eq
    change basePointsRepresentation (H := M) W u * _ = _ * basePointsRepresentation (H := M) W u
    rw [← map_mul, ← map_mul, h]
  have hwtT : ∀ χ, ∀ v ∈ wt π (W := W) χ, ∀ s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup
      M.obj I (CommAlgCat.of k k), basePointsRepresentation (H := M) W s v ∈ k ∙ v := by
    intro χ v hv s hs
    obtain ⟨σ, rfl⟩ := (hTmem s).mp hs
    rw [basePointsRepresentation_mapDomain_of_mem_wt π σ hv]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  by_cases hE0 : ∀ v ∈ E, v = 0
  · rw [hE0 y (Submodule.subset_span hy), map_zero]
  simp only [not_forall, exists_prop] at hE0
  obtain ⟨v₁, hv₁E, hv₁0⟩ := hE0
  let SE := S.filter fun χ => ∃ v ∈ E, proj π W S ψ t₀ χ v ≠ 0
  have hSE : SE.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hv₁0
    rw [← hPsum v₁]
    refine Finset.sum_eq_zero fun χ hχ => ?_
    by_contra hne
    have hmem : χ ∈ SE := Finset.mem_filter.mpr ⟨hχ, v₁, hv₁E, hne⟩
    rw [h] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  obtain ⟨χm, hχmSE, hχmin⟩ := SE.exists_min_image (fun χ => ψ (Multiplicative.toAdd χ)) hSE
  have hχmS : χm ∈ S := (Finset.mem_filter.mp hχmSE).1
  have hlow : ∀ y' ∈ orbitCone k M w, proj π W S ψ t₀ χm y' ∈ orbitCone k M w := by
    intro y' hy'
    by_cases h0 : proj π W S ψ t₀ χm y' = 0
    · rw [h0]
      exact ⟨1, 0, by rw [zero_smul]⟩
    let s := S.filter fun χ => proj π W S ψ t₀ χ y' ≠ 0
    have hs : s.Nonempty := ⟨χm, Finset.mem_filter.mpr ⟨hχmS, h0⟩⟩
    have hsE : ∀ χ ∈ s, χ ∈ SE := fun χ hχ => Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hχ).1, y', Submodule.subset_span hy', (Finset.mem_filter.mp hχ).2⟩
    have hcurve : ∀ t : k, t ≠ 0 →
        ∑ χ ∈ s, t ^ ψ (Multiplicative.toAdd χ) • proj π W S ψ t₀ χ y' ∈ orbitCone k M w := by
      intro t ht
      have hexp : basePointsRepresentation (H := M) W
          (TauCeti.Cocharacter.pointsHom k (cocharacterOfAddHom ψ π) (Units.mk0 t ht)) y' =
          ∑ χ ∈ s, t ^ ψ (Multiplicative.toAdd χ) • proj π W S ψ t₀ χ y' := by
        conv_lhs => rw [← hPsum y']
        rw [map_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun χ hχ => ?_
        rw [basePointsRepresentation_pointsHom_of_mem_wt π ψ _ (hPwt χ hχ y'), Units.val_mk0]
        split_ifs with hne
        · rfl
        · rw [not_not.mp hne, smul_zero]
      rw [← hexp]
      exact hG _ y' hy'
    have h := hclosed.sum_lowest_mem hcone s hs (fun χ => ψ (Multiplicative.toAdd χ))
      (fun χ => proj π W S ψ t₀ χ y') hcurve
    rwa [Finset.sum_eq_single_of_mem χm ?_ ?_] at h
    · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hχmS, h0⟩,
        fun j hj => hχmin j (hsE j hj)⟩
    · intro b hb hne
      exfalso
      apply hne
      have hbs := Finset.mem_filter.mp hb
      exact hψ (Finset.mem_filter.mp hbs.1).1 hχmS (le_antisymm
        (hbs.2 χm (Finset.mem_filter.mpr ⟨hχmS, h0⟩)) (hχmin b (hsE b hbs.1)))
  let E₀ : Submodule k W := E ⊓ wt π (W := W) χm
  have hE₀U : ∀ u : TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k),
      ∀ v ∈ E₀, basePointsRepresentation (R := k) (H := M) W (u : WithConv (M →ₐ[k] k)) v ∈
        E₀ := by
    intro u v hv
    refine ⟨hEG u v hv.1, ?_⟩
    rw [← hPself χm hχmS v hv.2, hPU χm u u.2]
    exact hPwt χm hχmS _
  have hE₀nt : Nontrivial E₀ := by
    obtain ⟨v, hvE, hv0⟩ := (Finset.mem_filter.mp hχmSE).2
    exact ⟨⟨⟨_, hPE χm v hvE, hPwt χm hχmS v⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  let ρ₀ : TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k) →*
      Module.End k E₀ :=
    { toFun := fun u => (basePointsRepresentation (R := k) (H := M) W
        (u : WithConv (M →ₐ[k] k))).restrict (hE₀U u)
      map_one' := by
        ext v
        simp
      map_mul' := fun u u' => by
        ext v
        simp [Module.End.mul_apply] }
  have hρ₀ : ∀ u, IsNilpotent (ρ₀ u - 1) := by
    intro u
    obtain ⟨m, hm⟩ := hJu u u.2
    refine ⟨m, ?_⟩
    have hpow : ∀ j : ℕ, ∀ v : E₀, (((ρ₀ u - 1) ^ j) v : W) =
        ((basePointsRepresentation (R := k) (H := M) W (u : WithConv (M →ₐ[k] k)) - 1) ^ j)
          v := by
      intro j
      induction j with
      | zero => intro v; simp
      | succ j ih =>
        intro v
        rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
        congr 1
    ext v
    rw [hpow, hm]
    simp
  obtain ⟨ℓ₀, hℓ₀0, hℓ₀⟩ := exists_dual_ne_zero_forall_apply_eq ρ₀ hρ₀
  obtain ⟨ℓ₁, hℓ₁⟩ := LinearMap.exists_extend ℓ₀
  let L : Module.Dual k W := ℓ₁ ∘ₗ proj π W S ψ t₀ χm
  have hLE₀ : ∀ v (hv : v ∈ E), L v = ℓ₀ ⟨_, hPE χm v hv, hPwt χm hχmS v⟩ := by
    intro v hv
    change ℓ₁ (proj π W S ψ t₀ χm v) = _
    rw [← hℓ₁]
    rfl
  have hLN : ∀ z ∈ N, L z = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨u, hu, v, hv, rfl⟩ := hz
      rw [map_sub, hLE₀ _ (hEG u v hv), hLE₀ v hv, sub_eq_zero]
      have h := hℓ₀ ⟨u, hu⟩ ⟨_, hPE χm v hv, hPwt χm hχmS v⟩
      convert h using 2
      exact Subtype.ext (hPU χm u hu v).symm
    | zero => exact map_zero L
    | add z z' _ _ h h' => rw [map_add, h, h', add_zero]
    | smul a z _ h => rw [map_smul, h, smul_zero]
  obtain ⟨y₁, hy₁, hLy₁⟩ : ∃ y₁ ∈ orbitCone k M w, L y₁ ≠ 0 := by
    by_contra hcon
    simp only [ne_eq, not_exists, not_and, not_not] at hcon
    have hLE : ∀ v ∈ E, L v = 0 := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv => exact hcon v hv
      | zero => exact map_zero L
      | add v v' _ _ h h' => rw [map_add, h, h', add_zero]
      | smul a v _ h => rw [map_smul, h, smul_zero]
    apply hℓ₀0
    ext ⟨v, hvE, hvwt⟩
    have hLv := hLE v hvE
    rw [hLE₀ v hvE] at hLv
    convert hLv using 2
    exact Subtype.ext (hPself χm hχmS v hvwt).symm
  set x₀ := proj π W S ψ t₀ χm y₁ with hx₀def
  have hx₀X : x₀ ∈ orbitCone k M w := hlow y₁ hy₁
  have hLx₀ : L x₀ = L y₁ := by
    change ℓ₁ (proj π W S ψ t₀ χm (proj π W S ψ t₀ χm y₁)) = ℓ₁ (proj π W S ψ t₀ χm y₁)
    rw [hPself χm hχmS _ (hPwt χm hχmS y₁)]
  have hx₀N : x₀ ∉ N := fun h => hLy₁ (hLx₀ ▸ hLN x₀ h)
  have hx₀0 : x₀ ≠ 0 := fun h => hx₀N (h ▸ N.zero_mem)
  have hx₀T := hwtT χm x₀ (hPwt χm hχmS y₁)
  have hXN : ∀ z ∈ orbitCone k M w, z ∈ N → z = 0 := by
    intro z hzX hzN
    by_contra hz0
    have hC : IsZariskiClosed k (orbitCone k M w ∩ (N : Set W)) :=
      hclosed.inter (isZariskiClosed_submodule N)
    have hCcone : IsCone k (orbitCone k M w ∩ (N : Set W)) := fun c v hv =>
      ⟨hcone c v hv.1, N.smul_mem c hv.2⟩
    have hCT : ∀ s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k),
        ∀ v ∈ orbitCone k M w ∩ (N : Set W),
          basePointsRepresentation (H := M) W s v ∈ orbitCone k M w ∩ (N : Set W) :=
      fun s hs v hv => ⟨hG s v hv.1, hNT s hs v hv.2⟩
    obtain ⟨z₀, hz₀, hz₀0, hz₀T⟩ := exists_ne_zero_mem_forall_mem_span_of_isMaximalTorus M hI hC
      hCcone hCT ⟨z, ⟨hzX, hzN⟩, hz0⟩
    obtain ⟨g, hg, hz₀g⟩ := NormalizerFixedScalar.exists_mem_normalizer_mem_span M hI hx₀0
      (NormalizerFixedScalar.mem_orbitCone_of_mem_orbitCone hx₀X hx₀0 hz₀.1) hx₀T hz₀T
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz₀g
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hz₀0 (by rw [← hc, zero_smul])
    have hgx : basePointsRepresentation (H := M) W g x₀ ∈ N := by
      have : basePointsRepresentation (H := M) W g x₀ = c⁻¹ • z₀ := by
        rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this]
      exact N.smul_mem _ hz₀.2
    have h := hNN g⁻¹ (Subgroup.inv_mem _ hg) _ hgx
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h
    exact hx₀N h
  by_cases hy0 : y = 0
  · rw [hy0, map_zero]
  have hyN : y ∉ N := fun h => hy0 (hXN y hy h)
  obtain ⟨φ, hφy, hφN⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hyN inferInstance
  have hφN' : ∀ z ∈ N, φ z = 0 := fun z hz => by
    have hmem : φ z ∈ N.map φ := Submodule.mem_map_of_mem hz
    rwa [hφN, Submodule.mem_bot] at hmem
  let ℓ : Module.Dual k W := (φ y)⁻¹ • φ
  have hℓy : ℓ y = 1 := by
    simp [ℓ, inv_mul_cancel₀ hφy]
  have hℓN : ∀ z ∈ N, ℓ z = 0 := fun z hz => by
    simp [ℓ, hφN' z hz]
  have hC' : IsZariskiClosed k (orbitCone k M w ∩ ((k ∙ y ⊔ N : Submodule k W) : Set W)) :=
    hclosed.inter (isZariskiClosed_submodule _)
  have hC'cone : IsCone k (orbitCone k M w ∩ ((k ∙ y ⊔ N : Submodule k W) : Set W)) :=
    fun c v hv => ⟨hcone c v hv.1, Submodule.smul_mem _ c hv.2⟩
  have hC'ker : ∀ v ∈ orbitCone k M w ∩ ((k ∙ y ⊔ N : Submodule k W) : Set W),
      ℓ v = 0 → v = 0 := by
    intro v hv hℓv
    obtain ⟨a, ha, m, hm, rfl⟩ := Submodule.mem_sup.mp hv.2
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp ha
    rw [map_add, map_smul, hℓy, hℓN m hm, smul_eq_mul, mul_one, add_zero] at hℓv
    subst hℓv
    rw [zero_smul, zero_add] at hv ⊢
    exact hXN m hv.1 hm
  have hAfin := finite_setOf_mem_and_eq_one hC' hC'cone ℓ hC'ker
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient M J
  let πJ : M →ₐc[k] Q := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient M J)
  let : TauCeti.Comodule k Q W := TauCeti.Comodule.Corestrict πJ.toCoalgHom
  have hQU : ∀ g : WithConv (Q →ₐ[k] k), TauCeti.AlgHom.mapDomain (A := k) πJ g ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k) := fun g =>
    ⟨g, by rw [TauCeti.CommHopfAlgCat.quotientPointsHom_apply]; rfl⟩
  have hact : ∀ g : WithConv (Q →ₐ[k] k),
      ∀ v ∈ {v | v ∈ orbitCone k M w ∩ ((k ∙ y ⊔ N : Submodule k W) : Set W) ∧ ℓ v = 1},
        (g.ofConv 1)⁻¹ • basePointsRepresentation (H := Q) W g v ∈
          {v | v ∈ orbitCone k M w ∩ ((k ∙ y ⊔ N : Submodule k W) : Set W) ∧ ℓ v = 1} := by
    intro g v hv
    rw [map_one, inv_one, one_smul,
      TauCeti.Comodule.basePointsRepresentation_corestrict (φ := πJ) (g := g)]
    have hd := hdisp _ (hQU g) v (Submodule.subset_span hv.1.1)
    have hsplit : basePointsRepresentation (H := M) W (TauCeti.AlgHom.mapDomain (A := k) πJ g) v =
        v + (basePointsRepresentation (H := M) W (TauCeti.AlgHom.mapDomain (A := k) πJ g) v -
          v) := by abel
    refine ⟨⟨hG _ v hv.1.1, ?_⟩, ?_⟩
    · rw [hsplit]
      exact Submodule.add_mem _ hv.1.2 (Submodule.mem_sup_right hd)
    · rw [hsplit, map_add, hv.2, hℓN _ hd, add_zero]
  have hyA : y ∈ {v | v ∈ orbitCone k M w ∩ ((k ∙ y ⊔ N : Submodule k W) : Set W) ∧ ℓ v = 1} :=
    ⟨⟨hy, Submodule.mem_sup_left (Submodule.mem_span_singleton_self y)⟩, hℓy⟩
  obtain ⟨g, rfl⟩ := hx
  have h := basePointsRepresentation_eq_smul_of_finite (H := Q) (M := W)
    (IsGroupLikeElem.one (R := k) (A := Q)) hAfin hact hyA g
  rw [map_one, one_smul,
    TauCeti.Comodule.basePointsRepresentation_corestrict (φ := πJ) (g := g)] at h
  rw [TauCeti.CommHopfAlgCat.quotientPointsHom_apply]
  exact h

end Main

section Reductive

theorem isNilpotent_basePointsRepresentation_sub_one {M : Type u} [CommRing M] [HopfAlgebra k M]
    {V : Type u} [AddCommGroup V] [Module k V] [TauCeti.Comodule k M V] [Module.Finite k V]
    {g : WithConv (M →ₐ[k] k)} (hg : TauCeti.HopfAlgebra.IsUnipotentPoint g) :
    IsNilpotent (basePointsRepresentation (H := M) V g - 1) := by
  have hρ : basePointsRepresentation (H := M) V g =
      (TensorProduct.lid k V).conjAlgEquiv k (TauCeti.Comodule.endOfPoint V g.ofConv) := by
    ext m
    rw [LinearEquiv.conjAlgEquiv_apply, TauCeti.Comodule.basePointsRepresentation_apply]
    simp
  obtain ⟨N, hN⟩ :=
    (TauCeti.HopfAlgebra.isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one g).mp
      hg (TauCeti.FGComoduleCat.of (R := k) (C := M) V)
  refine ⟨N, ?_⟩
  have h := congrArg ((TensorProduct.lid k V).conjAlgEquiv k) hN
  rw [map_pow, map_zero] at h
  rw [hρ, ← h]
  congr 1
  ext v
  simp [LinearEquiv.conjAlgEquiv_apply]

theorem sub_mem_of_sub_smul_mem {V : Type u} [AddCommGroup V] [Module k V]
    {A : Module.End k V} (hA : IsNilpotent (A - 1)) {F₀ F₁ : Submodule k V}
    (hA₀ : ∀ v ∈ F₀, A v ∈ F₀) (hA₁ : ∀ v ∈ F₁, A v ∈ F₁) {c : k}
    (hc : ∀ v ∈ F₁, A v - c • v ∈ F₀) : ∀ v ∈ F₁, A v - v ∈ F₀ := by
  by_cases hc1 : c = 1
  · subst hc1
    simpa only [one_smul] using hc
  have hle : ∀ w ∈ F₁, w ∈ F₀ := by
    intro w hw
    have hpow : ∀ j : ℕ, ((A - 1) ^ j) w - (c - 1) ^ j • w ∈ F₀ := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hstep : ((A - 1) ^ (j + 1)) w - (c - 1) ^ (j + 1) • w =
            (A - 1) (((A - 1) ^ j) w - (c - 1) ^ j • w) + (c - 1) ^ j • (A w - c • w) := by
          rw [pow_succ', Module.End.mul_apply, map_sub, map_smul, pow_succ, mul_smul]
          simp only [LinearMap.sub_apply, Module.End.one_apply, smul_sub, sub_smul, one_smul]
          abel
        rw [hstep]
        refine F₀.add_mem ?_ (F₀.smul_mem _ (hc w hw))
        rw [LinearMap.sub_apply, Module.End.one_apply]
        exact F₀.sub_mem (hA₀ _ ih) ih
    obtain ⟨N, hN⟩ := hA
    have h := hpow N
    rw [hN, LinearMap.zero_apply, zero_sub, neg_mem_iff] at h
    have := F₀.smul_mem ((c - 1) ^ N)⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero N (sub_ne_zero.mpr hc1)), one_smul] at this
  intro v hv
  exact F₀.sub_mem (hle _ (hA₁ v hv)) (hle v hv)

variable [IsAlgClosed k]

theorem basePointsRepresentation_eq_self_of_forall_eq_bot_or_eq_top
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsDomain M]
    {I : TauCeti.HopfIdeal k M} (hI : TauCeti.HopfIdeal.IsMaximalTorus k M.obj I)
    (J : TauCeti.HopfIdeal k M) [IsDomain (TauCeti.FiniteTypeCommHopfAlgCat.quotient M J)]
    (hJu : ∀ x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k),
      TauCeti.HopfAlgebra.IsUnipotentPoint x)
    (hJT : ∀ x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k),
      ∀ s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k),
        Commute x s)
    (hJN : ∀ g ∈ Subgroup.normalizer
        (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
          Set (WithConv (M →ₐ[k] k))),
      ∀ x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k),
        g * x * g⁻¹ ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k))
    (W : Type u) [AddCommGroup W] [Module k W] [TauCeti.Comodule k M W] [FiniteDimensional k W]
    (hW : ∀ N : TauCeti.Subcomodule k M W, N = ⊥ ∨ N = ⊤) {x : WithConv (M →ₐ[k] k)}
    (hx : x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k))
    (v : W) : basePointsRepresentation (H := M) W x v = v := by
  by_cases hW0 : ∃ v : W, v ≠ 0
  swap
  · simp only [ne_eq, not_exists, not_not] at hW0
    rw [hW0 v, map_zero]
  obtain ⟨v₀, hv₀⟩ := hW0
  have hC : IsZariskiClosed k (Set.univ : Set W) := ⟨∅, by ext v; simp [zeroSet]⟩
  obtain ⟨w, -, hw0, hclosed⟩ := exists_isZariskiClosed_orbitCone (k := k) (H := M) (M := W)
    hC (fun _ _ _ => Set.mem_univ _) (fun _ _ _ => Set.mem_univ _) ⟨v₀, Set.mem_univ _, hv₀⟩
  let E : Submodule k W := Submodule.span k (orbitCone k M w)
  have hfix : ∀ e ∈ E, basePointsRepresentation (H := M) W x e = e := by
    intro e he
    induction he using Submodule.span_induction with
    | mem e he =>
      exact basePointsRepresentation_eq_self_of_mem_orbitCone M hI J (W := W)
        (fun x' hx' => isNilpotent_basePointsRepresentation_sub_one (hJu x' hx')) hJT hJN
        hclosed hx he
    | zero => rw [map_zero]
    | add e e' _ _ h h' => rw [map_add, h, h']
    | smul a e _ h => rw [map_smul, h]
  have hEstab : ∀ (g : WithConv (M →ₐ[k] k)) {m : W}, m ∈ E →
      basePointsRepresentation (H := M) W g m ∈ E := by
    intro g m hm
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨h, d, rfl⟩ := hm
      exact Submodule.subset_span ⟨g * h, d, by rw [map_smul, map_mul, Module.End.mul_apply]⟩
    | zero => rw [map_zero]; exact E.zero_mem
    | add m m' _ _ h h' => rw [map_add]; exact E.add_mem h h'
    | smul a m _ h => rw [map_smul]; exact E.smul_mem a h
  have hstable : ∀ (g : M →ₐ[k] k) {m : W}, m ∈ E →
      TauCeti.Comodule.endOfPoint W g ((1 : k) ⊗ₜ[k] m) ∈ E.baseChange k := by
    intro g m hm
    rw [endOfPoint_tmul, one_smul, endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation]
    exact Submodule.tmul_mem_baseChange_of_mem _ (hEstab (toConv g) hm)
  have hE : E = ⊤ := by
    rw [← TauCeti.Subcomodule.ofEndOfPointStable_toSubmodule (K := k) E hstable]
    refine TauCeti.Subcomodule.toSubmodule_eq_top.mpr
      ((hW (TauCeti.Subcomodule.ofEndOfPointStable (K := k) E hstable)).resolve_left fun h => ?_)
    have hbot := TauCeti.Subcomodule.toSubmodule_eq_bot.mpr h
    rw [TauCeti.Subcomodule.ofEndOfPointStable_toSubmodule] at hbot
    have hwE : w ∈ E := Submodule.subset_span ⟨1, 1, by simp⟩
    rw [hbot, Submodule.mem_bot] at hwE
    exact hw0 hwE
  exact hfix v (hE ▸ Submodule.mem_top)

theorem eq_one_of_reductive
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hM : TauCeti.reductiveCommHopfAlgProperty k M)
    {I : TauCeti.HopfIdeal k M} (hI : TauCeti.HopfIdeal.IsMaximalTorus k M.obj I)
    (J : TauCeti.HopfIdeal k M) [IsDomain (TauCeti.FiniteTypeCommHopfAlgCat.quotient M J)]
    (hJu : ∀ x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k),
      TauCeti.HopfAlgebra.IsUnipotentPoint x)
    (hJT : ∀ x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k),
      ∀ s ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k),
        Commute x s)
    (hJN : ∀ g ∈ Subgroup.normalizer
        (TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
          Set (WithConv (M →ₐ[k] k))),
      ∀ x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k),
        g * x * g⁻¹ ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k))
    {x : WithConv (M →ₐ[k] k)}
    (hx : x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k)) :
    x = 1 := by
  let : Algebra.Smooth k M := hM.smooth
  let : ConnectedSpace (PrimeSpectrum M) :=
    TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace k M.obj
      hM.geometricallyConnected
  let : IsDomain M := CFSG.isDomain_of_smooth_of_connected (k := k) M
  let : IsReduced M := inferInstance
  obtain ⟨V, n, b, hb⟩ := TauCeti.Comodule.exists_coordinateBialgHom_surjective (k := k) (H := M)
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  let : Module.Finite k V := Module.Finite.of_basis b
  have hV : TauCeti.Comodule.IsFaithful (k := k) (H := M) (V := V) := by
    rw [TauCeti.Comodule.isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom b,
      TauCeti.Comodule.isClosedImmersion_coordinateGroupSchemeHom_iff]
    exact hb
  obtain ⟨d, F, hF0, hFd, hstab, hscalar⟩ :=
    ScalarFiltration.exists_scalar_filtration_of_family M
      (fun y : TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k) =>
        (y : WithConv (M →ₐ[k] k)))
      (fun W hW y => ⟨1, fun v => by
        let : AddCommGroup W := Module.addCommMonoidToAddCommGroup k
        rw [one_smul]
        exact basePointsRepresentation_eq_self_of_forall_eq_bot_or_eq_top M hI J hJu hJT hJN W
          hW y.2 v⟩) V
  let S := GradedKernel.pointKernel (TauCeti.Comodule.basePointsRepresentation V) F hstab
  have hJS : ∀ y ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k),
      y ∈ S := by
    intro y hy
    refine (GradedKernel.mem_pointKernel _ F hstab).mpr fun i => ?_
    obtain ⟨c, hc⟩ := hscalar ⟨y, hy⟩ i
    exact sub_mem_of_sub_smul_mem (isNilpotent_basePointsRepresentation_sub_one (hJu y hy))
      (fun v hv => hstab y i v hv) (fun v hv => hstab y (i + 1) v hv) hc
  let : S.Normal := GradedKernel.pointKernel_normal _ F hstab
  let J' := TauCeti.HopfIdeal.vanishingIdeal S
  have hSJ' : S ≤ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J' (CommAlgCat.of k k) :=
    (TauCeti.HopfIdeal.le_vanishingIdeal_iff S J').mp le_rfl
  have hJ'u : ∀ y ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J' (CommAlgCat.of k k),
      TauCeti.HopfAlgebra.IsUnipotentPoint y := by
    intro y hy
    have hyS : y ∈ S := GradedKernel.quotientPointsSubgroup_vanishing_pointKernel_le M V F hstab hy
    apply GradedKernel.isUnipotentPoint_of_isNilpotent_basePointsRepresentation_sub_one M V hV y
    exact GradedKernel.pointKernel_isNilpotent_sub_one _ F hstab d hF0 hFd y hyS
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient M J
  let πJ : M →ₐc[k] Q := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient M J)
  have hQU : ∀ g : WithConv (Q →ₐ[k] k), TauCeti.AlgHom.mapDomain (A := k) πJ g ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj J (CommAlgCat.of k k) := fun g =>
    ⟨g, by rw [TauCeti.CommHopfAlgCat.quotientPointsHom_apply]; rfl⟩
  have : ConnectedSpace (PrimeSpectrum Q) :=
    connectedSpace_iff_univ.mpr (IrreducibleSpace.isIrreducible_univ _).isConnected
  have hconst := CanonicalReductive.eq_const_of_reductive_normal_unipotent_image M hM J'
    (GradedKernel.isNormal_vanishingIdeal M S) hJ'u Q (πJ : M →ₐ[k] Q)
    (Bialgebra.counitAlgHom k Q) (by
      apply WithConv.ofConv_injective
      ext a
      change Bialgebra.counitAlgHom k Q (πJ a) = _
      simp [AlgHom.convOne_apply, CoalgHomClass.counit_comp_apply])
    (fun p => hSJ' (hJS _ (hQU (toConv p))))
  obtain ⟨g, rfl⟩ := hx
  rw [TauCeti.CommHopfAlgCat.quotientPointsHom_apply]
  apply WithConv.ofConv_injective
  ext a
  change g.ofConv (πJ a) = _
  rw [show πJ a = (πJ : M →ₐ[k] Q) a from rfl, hconst, AlgHom.comp_apply,
    Bialgebra.counitAlgHom_apply, Algebra.ofId_apply]
  exact (g.ofConv.commutes _).trans (AlgHom.convOne_apply a).symm

end Reductive

end CFSG.LieType.AlgebraicGroups.CentralizerUnipotent
