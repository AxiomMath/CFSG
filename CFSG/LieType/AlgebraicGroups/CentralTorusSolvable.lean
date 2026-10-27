module

public import CFSG.LieType.AlgebraicGroups.CartanCentralizer
public import CFSG.LieType.AlgebraicGroups.ClosedOrbitFixed

public noncomputable section

open WithConv TauCeti TauCeti.Comodule CategoryTheory
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.CentralTorus

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem conj_mem_of_mem_conjugate (H : FiniteTypeCommHopfAlgCat.{u,u} k) {I : HopfIdeal k H}
    (c : WithConv (H →ₐ[k] k)) {s : WithConv (H →ₐ[k] k)}
    (hs : s ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj (I.conjugate c) (CommAlgCat.of k k)) :
    c⁻¹ * s * c ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) := by
  have hmv : TauCeti.AlgHom.mapValue (H := H) (Algebra.ofId k k) c = c := by
    ext h
    simp
  refine (CommHopfAlgCat.pointConjugation_mem_conjugate_iff I c (CommAlgCat.of k k)
    (c⁻¹ * s * c)).mp ?_
  rw [hmv, show c * (c⁻¹ * s * c) * c⁻¹ = s by group]
  exact hs

theorem exists_mul_isUnipotentPoint_of_isSolvable (H : FiniteTypeCommHopfAlgCat.{u,u} k)
    [IsDomain H] [Group.IsSolvable (WithConv (H →ₐ[k] k))] {I : HopfIdeal k H}
    (hI : HopfIdeal.IsMaximalTorus k H.obj I) (g : WithConv (H →ₐ[k] k)) :
    ∃ t ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      ∃ v : WithConv (H →ₐ[k] k), HopfAlgebra.IsUnipotentPoint v ∧ g = t * v := by
  have : ConnectedSpace (PrimeSpectrum H) :=
    connectedSpace_iff_univ.mpr (IrreducibleSpace.isIrreducible_univ _).isConnected
  obtain ⟨T, p, j, hT, -, hker, hj, -⟩ := exists_torus_quotient_section_of_solvable H
  let π := AlgHom.mapDomain (A := k) p
  let σ := AlgHom.mapDomain (A := k) j
  have hsec : π.comp σ = MonoidHom.id _ := by
    rw [← AlgHom.mapDomain_comp, hj]
    rfl
  have hjs : Function.Surjective j := by
    intro t
    exact ⟨p t, congrArg (fun f : T →ₐc[k] T => f t) hj⟩
  have hunip : ∀ x, π x = 1 → HopfAlgebra.IsUnipotentPoint x := by
    intro x hx
    have hU := CommHopfAlgCat.quotientPointsSubgroup_kernelHopfIdeal_eq_ker_mapPointsFunctor
      (_root_.CommHopfAlgCat.ofHom p) (CommAlgCat.of k k)
    change CommHopfAlgCat.quotientPointsSubgroup H.obj
      (CommHopfAlgCat.kernelHopfIdeal (_root_.CommHopfAlgCat.ofHom p))
      (CommAlgCat.of k k) = π.ker at hU
    rw [hker] at hU
    have hmem : x ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H) (CommAlgCat.of k k) := by
      rw [hU]
      exact hx
    obtain ⟨q, hq⟩ := hmem
    have hiq : CommHopfAlgCat.quotientPointsHom H.obj
        (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H) (CommAlgCat.of k k) q =
        unipotentRadicalPointsHom H q := by
      rw [unipotentRadicalPointsHom, FiniteTypeCommHopfAlgCat.unipotentRadicalCoordinateMap_def]
      exact CommHopfAlgCat.quotientPointsHom_apply _ _ _ q
    rw [← hq, hiq]
    exact (unipotentRadical_points_unipotent H q).mapDomain _
  let I' := HopfIdeal.kerOfSurjective j hjs
  have hI' : torusCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient H I') := by
    let e := CommHopfAlgCat.quotientKerOfSurjectiveIso (_root_.CommHopfAlgCat.ofHom j) hjs
    exact (torusCommHopfAlgProperty k).prop_of_iso
      (ObjectProperty.isoMk (finiteTypeCommHopfAlgProperty k) e.symm) hT
  obtain ⟨J, hJI', hJ⟩ := HopfIdeal.exists_isMaximalTorus_le H hI'
  obtain ⟨c, hc⟩ := TorusConjugacy.exists_conjugate_eq_of_isMaximalTorus H hI hJ
  set s := σ (π (c * g * c⁻¹))
  have hsJ : s ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj J (CommAlgCat.of k k) := by
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro x hx
    have hxj : j x = 0 := (HopfIdeal.mem_kerOfSurjective j hjs).mp (hJI' hx)
    change (π (c * g * c⁻¹)).ofConv (j x) = 0
    rw [hxj, map_zero]
  rw [← hc] at hsJ
  have hπv : π (s⁻¹ * (c * g * c⁻¹)) = 1 := by
    rw [map_mul, map_inv, show π s = π (c * g * c⁻¹) from
      congrArg (fun f => f (π (c * g * c⁻¹))) hsec, inv_mul_cancel]
  have hπv' : π (c⁻¹ * (s⁻¹ * (c * g * c⁻¹)) * c) = 1 := by
    rw [map_mul, map_mul, hπv, mul_one, map_inv, inv_mul_cancel]
  exact ⟨c⁻¹ * s * c, conj_mem_of_mem_conjugate H c hsJ, c⁻¹ * (s⁻¹ * (c * g * c⁻¹)) * c,
    hunip _ hπv', by group⟩

theorem mem_of_isSemisimplePoint_of_commute_of_isSolvable (H : FiniteTypeCommHopfAlgCat.{u,u} k)
    [IsDomain H] [Group.IsSolvable (WithConv (H →ₐ[k] k))] {I : HopfIdeal k H}
    (hI : HopfIdeal.IsMaximalTorus k H.obj I) {g : WithConv (H →ₐ[k] k)}
    (hg : HopfAlgebra.IsSemisimplePoint g)
    (hcomm : ∀ t ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      Commute t g) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) := by
  obtain ⟨t, ht, v, hv, rfl⟩ := exists_mul_isUnipotentPoint_of_isSolvable H hI g
  have htv : Commute t v := mul_left_cancel (a := t) (by rw [(hcomm t ht).eq, mul_assoc])
  have hts : HopfAlgebra.IsSemisimplePoint t := by
    obtain ⟨t', rfl⟩ := ht
    have hT : torusCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient H I) :=
      ((HopfIdeal.isMaximalTorus_iff k H.obj I).mp hI).1
    exact (isSemisimplePoint_of_torus _ hT t').mapDomain _
  have huniq := HopfAlgebra.Point.isSemisimple_isUnipotent_unique k H k (t * v) t v
    htv rfl ((HopfAlgebra.isSemisimplePoint_def t).mp hts) hv
  have hv1 : v = 1 := by
    rw [huniq.2]
    exact HopfAlgebra.Point.unipotentPart_eq_one_of_isSemisimple k H k
      ((HopfAlgebra.isSemisimplePoint_def _).mp hg)
  rw [hv1, mul_one]
  exact ht

theorem mem_of_isSemisimplePoint_of_isSolvable (H : FiniteTypeCommHopfAlgCat.{u,u} k)
    [IsDomain H] [Group.IsSolvable (WithConv (H →ₐ[k] k))] {I : HopfIdeal k H}
    (hI : HopfIdeal.IsMaximalTorus k H.obj I)
    (hcent : ∀ t ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      ∀ g : WithConv (H →ₐ[k] k), Commute t g)
    {g : WithConv (H →ₐ[k] k)} (hg : HopfAlgebra.IsSemisimplePoint g) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) :=
  mem_of_isSemisimplePoint_of_commute_of_isSolvable H hI hg fun t ht => hcent t ht g


section Tools

omit [IsAlgClosed k] in
theorem basePointsRepresentation_dual_apply {H : Type u} [CommRing H] [HopfAlgebra k H]
    {W : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k H W] [FiniteDimensional k W]
    (g : WithConv (H →ₐ[k] k)) (φ : Module.Dual k W) (w : W) :
    letI := TauCeti.Comodule.dual (R := k) (H := H) (M := W)
    basePointsRepresentation (H := H) (Module.Dual k W) g φ w =
      φ (basePointsRepresentation (H := H) W g⁻¹ w) := by
  let := TauCeti.Comodule.dual (R := k) (H := H) (M := W)
  have h1 := Comodule.apply_matrixCoefficient (H := H) g (Module.Dual.eval k W w) φ
  rw [Module.Dual.eval_apply] at h1
  rw [← h1]
  have h2 : Comodule.matrixCoefficient (C := H) (Module.Dual.eval k W w) φ =
      HopfAlgebra.antipode k (Comodule.matrixCoefficient (C := H) φ w) := by
    rw [← Comodule.dualTensorHom_dualCoact_apply, Comodule.matrixCoefficient_def,
      Comodule.dual_coact]
    generalize Comodule.dualCoact (R := k) (H := H) (M := W) φ = x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul ψ h => simp [dualTensorHom_apply]
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  rw [h2, show g.ofConv (HopfAlgebra.antipode k (Comodule.matrixCoefficient (C := H) φ w)) =
    (g⁻¹).ofConv (Comodule.matrixCoefficient (C := H) φ w) from
      (AlgHom.antipodeComp_apply g.ofConv _).symm, Comodule.apply_matrixCoefficient]

omit [IsAlgClosed k] in
theorem eq_one_of_isUnipotentPoint {M : Type u} [CommRing M] [HopfAlgebra k M]
    {V : Type u} [AddCommGroup V] [Module k V] [TauCeti.Comodule k M V] [Module.Finite k V]
    {v : WithConv (M →ₐ[k] k)} (hv : HopfAlgebra.IsUnipotentPoint v) {x : V} (hx : x ≠ 0)
    {a : k} (ha : basePointsRepresentation (H := M) V v x = a • x) : a = 1 := by
  obtain ⟨N, hN⟩ := CentralizerUnipotent.isNilpotent_basePointsRepresentation_sub_one (V := V) hv
  have h1 : ∀ j : ℕ, ((basePointsRepresentation (H := M) V v - 1) ^ j) x = (a - 1) ^ j • x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, ha,
        Module.End.one_apply, pow_succ, mul_smul, sub_smul, one_smul]
  have h2 := h1 N
  rw [hN, LinearMap.zero_apply, eq_comm, smul_eq_zero] at h2
  rcases h2 with h | h
  · exact sub_eq_zero.mp (IsNilpotent.eq_zero ⟨N, h⟩)
  · exact absurd h hx

end Tools


section Induction

omit [IsAlgClosed k] in
theorem quotientPointsHom_mem_of_mem_map (H : FiniteTypeCommHopfAlgCat.{u,u} k)
    {J I : HopfIdeal k H} (hJI : J ≤ I)
    {q : WithConv (FiniteTypeCommHopfAlgCat.quotient H J →ₐ[k] k)}
    (hq : q ∈ CommHopfAlgCat.quotientPointsSubgroup (FiniteTypeCommHopfAlgCat.quotient H J).obj
      (I.map (FiniteTypeCommHopfAlgCat.toBialgHom (FiniteTypeCommHopfAlgCat.mkQuotient H J)))
      (CommAlgCat.of k k)) :
    CommHopfAlgCat.quotientPointsHom H.obj J (CommAlgCat.of k k) q ∈
      CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) := by
  let π := FiniteTypeCommHopfAlgCat.toBialgHom (FiniteTypeCommHopfAlgCat.mkQuotient H J)
  have hπ : Function.Surjective π := CommHopfAlgCat.mkQuotient_surjective H.obj J
  have hker : HopfIdeal.kerOfSurjective π hπ = J :=
    HopfIdeal.kerOfSurjective_mkBialgHom (R := k) (H := H.obj) J
  have hcomap : (I.map π).comapOfSurjective π hπ = I := by
    rw [HopfIdeal.comapOfSurjective_map I π hπ, hker, sup_eq_left.mpr hJI]
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  intro f hf
  have hπf : π f ∈ I.map π := by
    rw [← hcomap] at hf
    exact HopfIdeal.mem_comapOfSurjective.mp hf
  have h0 := (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ (I.map π) _ _).mp hq _ hπf
  rw [CommHopfAlgCat.quotientPointsHom_apply_apply]
  exact h0

theorem exists_ne_zero_mem_forall_eq_smul_of_isSolvable (H : FiniteTypeCommHopfAlgCat.{u,u} k)
    {J : HopfIdeal k H} [IsDomain (FiniteTypeCommHopfAlgCat.quotient H J)]
    [Group.IsSolvable (WithConv (FiniteTypeCommHopfAlgCat.quotient H J →ₐ[k] k))]
    {W : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k H W] [FiniteDimensional k W]
    {C : Set W} (hC : ClosedCone.IsZariskiClosed k C) (hcone : ClosedCone.IsCone k C)
    (hT : ∀ s ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj J (CommAlgCat.of k k),
      ∀ v ∈ C, basePointsRepresentation (H := H) W s v ∈ C)
    (hne : ∃ v ∈ C, v ≠ 0) :
    ∃ x ∈ C, x ≠ 0 ∧ ∀ t ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj J (CommAlgCat.of k k),
      ∃ a : k, basePointsRepresentation (H := H) W t x = a • x := by
  let Q := FiniteTypeCommHopfAlgCat.quotient H J
  let π : H →ₐc[k] Q := FiniteTypeCommHopfAlgCat.toBialgHom (FiniteTypeCommHopfAlgCat.mkQuotient H J)
  let : TauCeti.Comodule k Q W := TauCeti.Comodule.Corestrict π.toCoalgHom
  have hG' : ∀ g : WithConv (Q →ₐ[k] k), ∀ v ∈ C,
      basePointsRepresentation (H := Q) W g v ∈ C := by
    intro g v hv
    rw [TauCeti.Comodule.basePointsRepresentation_corestrict (φ := π) (g := g)]
    exact hT _ ⟨g, rfl⟩ v hv
  obtain ⟨x, hxC, hx0, χ, -, hxχ⟩ :=
    ClosedCone.exists_ne_zero_mem_forall_eq_smul (k := k) (H := Q) (M := W) hC hcone hG' hne
  refine ⟨x, hxC, hx0, ?_⟩
  rintro _ ⟨g, rfl⟩
  refine ⟨g.ofConv χ, ?_⟩
  have h2 : CommHopfAlgCat.quotientPointsHom H.obj J (CommAlgCat.of k k) g =
      TauCeti.AlgHom.mapDomain (A := k) π g := by
    rw [CommHopfAlgCat.quotientPointsHom_apply]
    rfl
  rw [h2, ← TauCeti.Comodule.basePointsRepresentation_corestrict (φ := π) (g := g), hxχ g]

attribute [local instance] TauCeti.Comodule.tensor TauCeti.Comodule.dual

theorem isSolvable_of_central_of_ringKrullDim_le (n : ℕ) :
    ∀ (H : FiniteTypeCommHopfAlgCat.{u,u} k) [IsDomain H], ringKrullDim H ≤ n →
      ∀ {I : HopfIdeal k H}, HopfIdeal.IsMaximalTorus k H.obj I →
        (∀ t ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
          ∀ g : WithConv (H →ₐ[k] k), Commute t g) →
          Group.IsSolvable (WithConv (H →ₐ[k] k)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ hdim I hI hcent
  classical
  by_contra hsol
  have hnot := mt (ClosedCone.isSolvable_of_forall_isZariskiClosed_orbitCone (k := k) (H := H))
    hsol
  simp only [not_forall, exists_prop] at hnot
  obtain ⟨W, _, _, _, _, w₀, hw₀, hclosed, g₀, hg₀⟩ := hnot
  set T := CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) with hT_def
  have hinj : ∀ g : WithConv (H →ₐ[k] k),
      Function.Injective (basePointsRepresentation (H := H) W g) := by
    intro g x y hxy
    have := congrArg (basePointsRepresentation (H := H) W g⁻¹) hxy
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using this
  have hcone : ClosedCone.IsCone k (ClosedCone.orbitCone k H w₀) := by
    rintro c _ ⟨g, d, rfl⟩
    exact ⟨g, c * d, by rw [smul_smul]⟩
  have hG : ∀ g : WithConv (H →ₐ[k] k), ∀ v ∈ ClosedCone.orbitCone k H w₀,
      basePointsRepresentation (H := H) W g v ∈ ClosedCone.orbitCone k H w₀ := by
    rintro g _ ⟨h, d, rfl⟩
    exact ⟨g * h, d, by rw [map_smul, map_mul, Module.End.mul_apply]⟩
  obtain ⟨x, ⟨g, c, rfl⟩, hx0, hxT⟩ :=
    TorusConjugacy.exists_ne_zero_mem_forall_mem_span_of_isMaximalTorus H hI hclosed hcone
      (fun s _ => hG s) ⟨w₀, ⟨1, 1, by simp⟩, hw₀⟩
  have hc : c ≠ 0 := by
    rintro rfl
    exact hx0 (zero_smul k _)
  have hTw : ∀ t ∈ T, ∃ a : k, basePointsRepresentation (H := H) W t w₀ = a • w₀ := by
    intro t ht
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hxT t ht)
    refine ⟨a, hinj g ?_⟩
    have h2 : basePointsRepresentation (H := H) W t (basePointsRepresentation (H := H) W g w₀) =
        a • basePointsRepresentation (H := H) W g w₀ := by
      have h1 := ha.symm
      rw [map_smul, smul_comm a c] at h1
      exact smul_right_injective W hc h1
    rw [map_smul, ← h2, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      (hcent t ht g).eq]
  choose χ hχ using hTw
  have hχmul : ∀ t (ht : t ∈ T), χ t ht * χ t⁻¹ (inv_mem ht) = 1 := by
    intro t ht
    have h1 : basePointsRepresentation (H := H) W (t * t⁻¹) w₀ =
        (χ t ht * χ t⁻¹ (inv_mem ht)) • w₀ := by
      rw [map_mul, Module.End.mul_apply, hχ t⁻¹ (inv_mem ht), map_smul, hχ t ht, smul_smul,
        mul_comm]
    rw [mul_inv_cancel, map_one, Module.End.one_apply] at h1
    have h2 : (χ t ht * χ t⁻¹ (inv_mem ht) - 1) • w₀ = 0 := by
      rw [sub_smul, one_smul, ← h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hw₀)
  have hχne : ∀ t (ht : t ∈ T), χ t ht ≠ 0 := fun t ht h0 => by
    have := hχmul t ht
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have hχinv : ∀ t (ht : t ∈ T), χ t⁻¹ (inv_mem ht) = (χ t ht)⁻¹ :=
    fun t ht => eq_inv_of_mul_eq_one_right (hχmul t ht)
  set S := TorusConjugacy.lineStabilizer k H w₀ with hS_def
  set J := TorusConjugacy.closureIdentityComponent H S with hJ_def
  have : IsDomain (FiniteTypeCommHopfAlgCat.quotient H J) :=
    TorusConjugacy.isDomain_quotient_closureIdentityComponent H S
  have : IsDomain (FiniteTypeCommHopfAlgCat.quotient H I) :=
    TorusConjugacy.isDomain_quotient_of_isMaximalTorus H hI
  have : ConnectedSpace (PrimeSpectrum (FiniteTypeCommHopfAlgCat.quotient H I)) :=
    connectedSpace_iff_univ.mpr (IrreducibleSpace.isIrreducible_univ _).isConnected
  have hTS : T ≤ S := fun t ht => (TorusConjugacy.mem_lineStabilizer_iff hw₀ t).mpr (by
    rw [hχ t ht]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w₀))
  have hJI : J ≤ I := TorusConjugacy.closureIdentityComponent_le H hTS
  have hJbot : J ≠ ⊥ := by
    intro hJ0
    apply hg₀
    have hmem : g₀ ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj J (CommAlgCat.of k k) := by
      rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff, hJ0]
      intro x hx
      rw [(HopfIdeal.mem_bot).mp hx, map_zero]
    have hmem' := TorusConjugacy.quotientPointsSubgroup_closureIdentityComponent_le H S hmem
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hmem'
    exact (TorusConjugacy.mem_lineStabilizer_iff hw₀ g₀).mp
      (TorusConjugacy.mem_lineStabilizer_of_forall_mem_vanishingIdeal hw₀ hmem')
  have hlt := (TorusConjugacy.ringKrullDim_quotient_lt H hJbot).trans_le hdim
  obtain ⟨m, hm, hdim'⟩ : ∃ m < n,
      ringKrullDim (FiniteTypeCommHopfAlgCat.quotient H J) ≤ (m : WithBot ℕ∞) := by
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (FiniteTypeCommHopfAlgCat.quotient H J) :=
      ringKrullDim_nonneg_of_nontrivial
    generalize ringKrullDim (FiniteTypeCommHopfAlgCat.quotient H J) = x at hlt h0 ⊢
    induction x using WithBot.recBotCoe with
    | bot => exact absurd h0 (by simp)
    | coe y =>
      induction y using ENat.recTopCoe with
      | top => exact absurd hlt (by simp)
      | coe a =>
        refine ⟨a, ?_, le_rfl⟩
        exact_mod_cast hlt
  let ψ := CommHopfAlgCat.quotientPointsHom H.obj J (CommAlgCat.of k k)
  have hψinj : Function.Injective ψ :=
    CommHopfAlgCat.quotientPointsHom_injective H.obj J (CommAlgCat.of k k)
  have hTQ := TorusConjugacy.isMaximalTorus_map H hJI hI
  have hcentQ : ∀ t ∈ CommHopfAlgCat.quotientPointsSubgroup
      (FiniteTypeCommHopfAlgCat.quotient H J).obj
      (I.map (FiniteTypeCommHopfAlgCat.toBialgHom (FiniteTypeCommHopfAlgCat.mkQuotient H J)))
      (CommAlgCat.of k k), ∀ q, Commute t q := by
    intro t ht q
    have h1 := quotientPointsHom_mem_of_mem_map H hJI ht
    apply hψinj
    rw [map_mul, map_mul]
    exact (hcent _ h1 (ψ q)).eq
  have : Group.IsSolvable (WithConv (FiniteTypeCommHopfAlgCat.quotient H J →ₐ[k] k)) :=
    ih m hm _ hdim' hTQ hcentQ
  set P0 := CommHopfAlgCat.quotientPointsSubgroup H.obj J (CommAlgCat.of k k) with hP0_def
  have hP0S : P0 ≤ S := by
    intro p hp
    have hp' := TorusConjugacy.quotientPointsSubgroup_closureIdentityComponent_le H S hp
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hp'
    exact TorusConjugacy.mem_lineStabilizer_of_forall_mem_vanishingIdeal hw₀ hp'
  have hdec : ∀ p ∈ P0, ∃ t ∈ T, ∃ v ∈ P0, HopfAlgebra.IsUnipotentPoint v ∧ p = t * v := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨t', ht', v', hv', rfl⟩ := exists_mul_isUnipotentPoint_of_isSolvable _ hTQ q
    refine ⟨ψ t', quotientPointsHom_mem_of_mem_map H hJI ht', ψ v', ⟨v', rfl⟩, ?_, map_mul _ _ _⟩
    rw [CommHopfAlgCat.quotientPointsHom_apply]
    exact hv'.mapDomain _
  obtain ⟨mm, pr, cc, -, -, hsum, hcomm, hscal⟩ := CartanComponent.exists_weight_projections H hI W
  obtain ⟨i₀, hi₀⟩ : ∃ i, pr i w₀ ≠ 0 := by
    by_contra h
    push Not at h
    apply hw₀
    rw [← hsum w₀]
    exact Finset.sum_eq_zero fun i _ => h i
  have hcommT : ∀ t ∈ T, ∀ i, Commute (basePointsRepresentation (H := H) W t) (pr i) :=
    fun t ht i => hcomm t (fun s hs => (hcent s hs t).symm) i
  have hcc : ∀ t (ht : t ∈ T), cc i₀ t = χ t ht := by
    intro t ht
    have h1 : basePointsRepresentation (H := H) W t (pr i₀ w₀) = cc i₀ t • pr i₀ w₀ := by
      have := congrArg (fun f : Module.End k W => f w₀) (hscal t ht i₀)
      simpa only [Module.End.mul_apply, LinearMap.smul_apply] using this
    have h2 : basePointsRepresentation (H := H) W t (pr i₀ w₀) = χ t ht • pr i₀ w₀ := by
      rw [← Module.End.mul_apply, (hcommT t ht i₀).eq, Module.End.mul_apply, hχ t ht, map_smul]
    exact smul_left_injective k hi₀ (h1.symm.trans h2)
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ : Module.Dual k W, φ (pr i₀ w₀) ≠ 0 := by
    by_contra h
    push Not at h
    exact hi₀ ((Module.forall_dual_apply_eq_zero_iff k _).mp h)
  let K : Submodule k (Module.Dual k W) :=
    ⨅ (t : WithConv (H →ₐ[k] k)) (ht : t ∈ T),
      LinearMap.ker (basePointsRepresentation (H := H) (Module.Dual k W) t -
        (χ t ht)⁻¹ • LinearMap.id)
  have hmemK : ∀ φ, φ ∈ K ↔ ∀ t (ht : t ∈ T),
      basePointsRepresentation (H := H) (Module.Dual k W) t φ = (χ t ht)⁻¹ • φ := by
    intro φ
    simp only [K, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  have hφK : φ₀ ∘ₗ pr i₀ ∈ K := by
    rw [hmemK]
    intro t ht
    ext w
    have hpr : pr i₀ (basePointsRepresentation (H := H) W t⁻¹ w) = cc i₀ t⁻¹ • pr i₀ w := by
      rw [← Module.End.mul_apply, ← (hcommT t⁻¹ (inv_mem ht) i₀).eq,
        hscal t⁻¹ (inv_mem ht) i₀, LinearMap.smul_apply]
    rw [basePointsRepresentation_dual_apply, LinearMap.comp_apply, hpr, map_smul,
      hcc t⁻¹ (inv_mem ht), hχinv t ht, LinearMap.smul_apply, LinearMap.comp_apply]
  have hKstable : ∀ s ∈ P0, ∀ φ ∈ (K : Set (Module.Dual k W)),
      basePointsRepresentation (H := H) (Module.Dual k W) s φ ∈ (K : Set (Module.Dual k W)) := by
    intro s _ φ hφ
    rw [SetLike.mem_coe, hmemK] at hφ ⊢
    intro t ht
    rw [← Module.End.mul_apply, ← map_mul, (hcent t ht s).eq, map_mul, Module.End.mul_apply,
      hφ t ht, map_smul]
  have hφne : φ₀ ∘ₗ pr i₀ ≠ 0 := fun h => hφ₀ (by
    have := congrArg (fun f : Module.Dual k W => f w₀) h
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using this)
  obtain ⟨φ₁, hφ₁K, hφ₁0, hφ₁⟩ := exists_ne_zero_mem_forall_eq_smul_of_isSolvable H (J := J)
    (ClosedCone.isZariskiClosed_submodule K) (fun c φ hφ => K.smul_mem c hφ) hKstable
    ⟨_, hφK, hφne⟩
  set u : W ⊗[k] Module.Dual k W := w₀ ⊗ₜ φ₁ with hu_def
  obtain ⟨w₁, hw₁⟩ : ∃ w₁, φ₁ w₁ ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ₁0 (LinearMap.ext h)
  have hu0 : u ≠ 0 := by
    intro h0
    have := congrArg (ClosedCone.contract (W := W) (Module.Dual.eval k W w₁)) h0
    rw [hu_def, ClosedCone.contract_tmul, map_zero, Module.Dual.eval_apply] at this
    exact (smul_eq_zero.mp this).elim hw₁ hw₀
  have hTu : ∀ t ∈ T, basePointsRepresentation (H := H) (W ⊗[k] Module.Dual k W) t u = u := by
    intro t ht
    rw [hu_def, ClosedCone.basePointsRepresentation_tmul, hχ t ht, (hmemK φ₁).mp hφ₁K t ht,
      TensorProduct.smul_tmul_smul, mul_inv_cancel₀ (hχne t ht), one_smul]
  have hP0u : ∀ p ∈ P0, basePointsRepresentation (H := H) (W ⊗[k] Module.Dual k W) p u = u := by
    intro p hp
    obtain ⟨t, ht, v, hv, hvu, rfl⟩ := hdec p hp
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      ((TorusConjugacy.mem_lineStabilizer_iff hw₀ v).mp (hP0S hv))
    obtain ⟨b, hb⟩ := hφ₁ v hv
    have hvu' : basePointsRepresentation (H := H) (W ⊗[k] Module.Dual k W) v u = (a * b) • u := by
      rw [hu_def, ClosedCone.basePointsRepresentation_tmul, ← ha, hb,
        TensorProduct.smul_tmul_smul]
    have hab := eq_one_of_isUnipotentPoint hvu hu0 hvu'
    rw [map_mul, Module.End.mul_apply, hvu', hab, one_smul, hTu t ht]
  have hfin : {y | ∃ g : WithConv (H →ₐ[k] k), basePointsRepresentation (H := H) W g w₀ ∈ k ∙ w₀ ∧
      y = basePointsRepresentation (H := H) (W ⊗[k] Module.Dual k W) g u}.Finite := by
    have : (P0.subgroupOf S).FiniteIndex := ⟨TorusConjugacy.relIndex_closureIdentityComponent_ne_zero H S⟩
    refine (Set.finite_range fun q : S ⧸ P0.subgroupOf S =>
      basePointsRepresentation (H := H) (W ⊗[k] Module.Dual k W) (q.out : WithConv (H →ₐ[k] k)) u).subset ?_
    rintro _ ⟨g, hg, rfl⟩
    have hgS : g ∈ S := (TorusConjugacy.mem_lineStabilizer_iff hw₀ g).mpr hg
    refine ⟨QuotientGroup.mk ⟨g, hgS⟩, ?_⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (P0.subgroupOf S) ⟨g, hgS⟩
    simp only [hh, Subgroup.coe_mul, map_mul, Module.End.mul_apply,
      hP0u _ (Subgroup.mem_subgroupOf.mp h.2)]
  have hfix := ClosedCone.basePointsRepresentation_eq_of_finite hw₀ hclosed hfin g₀
  apply hg₀
  rw [hu_def, ClosedCone.basePointsRepresentation_tmul] at hfix
  have h1 := congrArg (ClosedCone.contract (W := W) (Module.Dual.eval k W w₁)) hfix
  rw [ClosedCone.contract_tmul, ClosedCone.contract_tmul, Module.Dual.eval_apply,
    Module.Dual.eval_apply] at h1
  by_cases h0 : basePointsRepresentation (H := H) (Module.Dual k W) g₀ φ₁ w₁ = 0
  · rw [h0, zero_smul, eq_comm, smul_eq_zero] at h1
    exact (h1.elim hw₁ hw₀).elim
  · refine Submodule.mem_span_singleton.mpr ⟨φ₁ w₁ / basePointsRepresentation (H := H)
      (Module.Dual k W) g₀ φ₁ w₁, ?_⟩
    rw [div_eq_inv_mul, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ h0, one_smul]

theorem isSolvable_of_central (H : FiniteTypeCommHopfAlgCat.{u,u} k) [IsDomain H]
    {I : HopfIdeal k H} (hI : HopfIdeal.IsMaximalTorus k H.obj I)
    (hcent : ∀ t ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      ∀ g : WithConv (H →ₐ[k] k), Commute t g) :
    Group.IsSolvable (WithConv (H →ₐ[k] k)) := by
  have : FiniteRingKrullDim H := TauCeti.finiteRingKrullDim_of_finiteType k H
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim H ≤ (n : WithBot ℕ∞) := by
    have htop : ringKrullDim H < ⊤ := ringKrullDim_lt_top
    generalize ringKrullDim H = x at htop ⊢
    induction x using WithBot.recBotCoe with
    | bot => exact ⟨0, bot_le⟩
    | coe y =>
      induction y using ENat.recTopCoe with
      | top => exact absurd htop (by simp)
      | coe a => exact ⟨a, le_rfl⟩
  exact isSolvable_of_central_of_ringKrullDim_le n H hn hI hcent

theorem mem_of_isSemisimplePoint_of_central (H : FiniteTypeCommHopfAlgCat.{u,u} k) [IsDomain H]
    {I : HopfIdeal k H} (hI : HopfIdeal.IsMaximalTorus k H.obj I)
    (hcent : ∀ t ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k),
      ∀ g : WithConv (H →ₐ[k] k), Commute t g)
    {g : WithConv (H →ₐ[k] k)} (hg : HopfAlgebra.IsSemisimplePoint g) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) := by
  have := isSolvable_of_central H hI hcent
  exact mem_of_isSemisimplePoint_of_isSolvable H hI hcent hg

end Induction

end CFSG.LieType.AlgebraicGroups.CentralTorus

namespace CFSG.LieType.AlgebraicGroups.CartanComponent

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem mem_of_mem_cartan_of_isSemisimplePoint (M : FiniteTypeCommHopfAlgCat.{u,u} k)
    {I : HopfIdeal k M} (hI : HopfIdeal.IsMaximalTorus k M.obj I)
    {x : WithConv (M →ₐ[k] k)}
    (hx : x ∈ CommHopfAlgCat.quotientPointsSubgroup M.obj
      (TorusConjugacy.closureIdentityComponent M (Subgroup.centralizer
        (CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
          Set (WithConv (M →ₐ[k] k))))) (CommAlgCat.of k k))
    (hs : HopfAlgebra.IsSemisimplePoint x) :
    x ∈ CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) := by
  let T := CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k)
  let C := Subgroup.centralizer (T : Set (WithConv (M →ₐ[k] k)))
  let J₀ := TorusConjugacy.closureIdentityComponent M C
  let Q := FiniteTypeCommHopfAlgCat.quotient M J₀
  have : IsDomain Q := TorusConjugacy.isDomain_quotient_closureIdentityComponent M C
  let π : M →ₐc[k] Q :=
    FiniteTypeCommHopfAlgCat.toBialgHom (FiniteTypeCommHopfAlgCat.mkQuotient M J₀)
  have hπ : Function.Surjective π := CommHopfAlgCat.mkQuotient_surjective M.obj J₀
  have : IsDomain (FiniteTypeCommHopfAlgCat.quotient M I) :=
    TorusConjugacy.isDomain_quotient_of_isMaximalTorus M hI
  have : ConnectedSpace (PrimeSpectrum (FiniteTypeCommHopfAlgCat.quotient M I)) :=
    connectedSpace_iff_univ.mpr (IrreducibleSpace.isIrreducible_univ _).isConnected
  have hTC : T ≤ C := fun t ht => Subgroup.mem_centralizer_iff.mpr fun s hs =>
    (TorusConjugacy.commute_of_mem_quotientPointsSubgroup_of_isMaximalTorus M hI hs ht).eq
  have hJI : J₀ ≤ I := TorusConjugacy.closureIdentityComponent_le M hTC
  have hTQ := TorusConjugacy.isMaximalTorus_map M hJI hI
  have hC0C : CommHopfAlgCat.quotientPointsSubgroup M.obj J₀ (CommAlgCat.of k k) ≤ C := by
    have h := TorusConjugacy.quotientPointsSubgroup_closureIdentityComponent_le M C
    rwa [CFSG.LieType.AlgebraicGroups.quotientPointsSubgroup_vanishingIdeal_centralizer] at h
  let ψ := CommHopfAlgCat.quotientPointsHom M.obj J₀ (CommAlgCat.of k k)
  have hψinj : Function.Injective ψ :=
    CommHopfAlgCat.quotientPointsHom_injective M.obj J₀ (CommAlgCat.of k k)
  obtain ⟨q, rfl⟩ := hx
  have hq : HopfAlgebra.IsSemisimplePoint q := by
    refine (HopfAlgebra.isSemisimplePoint_mapDomain_iff_of_surjective π hπ q).mp ?_
    change HopfAlgebra.IsSemisimplePoint (ψ q) at hs
    rw [CommHopfAlgCat.quotientPointsHom_apply] at hs
    exact hs
  have hcentQ : ∀ t ∈ CommHopfAlgCat.quotientPointsSubgroup Q.obj (I.map π) (CommAlgCat.of k k),
      ∀ g : WithConv (Q →ₐ[k] k), Commute t g := by
    intro t ht g
    apply hψinj
    rw [map_mul, map_mul]
    exact (Subgroup.mem_centralizer_iff.mp (hC0C ⟨g, rfl⟩)) _
      (CentralTorus.quotientPointsHom_mem_of_mem_map M hJI ht)
  exact CentralTorus.quotientPointsHom_mem_of_mem_map M hJI
    (CentralTorus.mem_of_isSemisimplePoint_of_central Q hTQ hcentQ hq)

theorem quotientPointsSubgroup_cartan_le (M : FiniteTypeCommHopfAlgCat.{u,u} k)
    (hM : reductiveCommHopfAlgProperty k M)
    {I : HopfIdeal k M} (hI : HopfIdeal.IsMaximalTorus k M.obj I) :
    CommHopfAlgCat.quotientPointsSubgroup M.obj
        (TorusConjugacy.closureIdentityComponent M (Subgroup.centralizer
          (CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :
            Set (WithConv (M →ₐ[k] k))))) (CommAlgCat.of k k) ≤
      CommHopfAlgCat.quotientPointsSubgroup M.obj I (CommAlgCat.of k k) :=
  quotientPointsSubgroup_cartan_le_of_semisimple M hM hI fun _ hs hss =>
    mem_of_mem_cartan_of_isSemisimplePoint M hI hs hss

end CFSG.LieType.AlgebraicGroups.CartanComponent
