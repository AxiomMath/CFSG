module

public import CFSG.LieType.AlgebraicGroups.SolvableTorusSection

public noncomputable section

open WithConv TauCeti CategoryTheory

namespace CFSG.LieType.AlgebraicGroups.SolvableSemisimple

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

theorem exists_unipotentRadical_conj_of_pow_eq_one_of_torus_section
    (H T : FiniteTypeCommHopfAlgCat.{u,u} k)
    (p : T →ₐc[k] H) (j : H →ₐc[k] T)
    (hp : CommHopfAlgCat.kernelHopfIdeal (_root_.CommHopfAlgCat.ofHom p) =
      FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H)
    (hj : j.comp p = BialgHom.id k T)
    {n : ℕ} (hn : (n : k) ≠ 0) (s : WithConv (H →ₐ[k] k)) (hs : s ^ n = 1) :
    ∃ u : WithConv (FiniteTypeCommHopfAlgCat.unipotentRadical H →ₐ[k] k),
      unipotentRadicalPointsHom H u * s * (unipotentRadicalPointsHom H u)⁻¹ =
        AlgHom.mapDomain j (AlgHom.mapDomain p s) := by
  let U := CommHopfAlgCat.quotientPointsSubgroup H.obj
    (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H) (CommAlgCat.of k k)
  let π := AlgHom.mapDomain (A := k) p
  let σ := AlgHom.mapDomain (A := k) j
  have hsec : π.comp σ = MonoidHom.id _ := by
    rw [← AlgHom.mapDomain_comp, hj]
    rfl
  have hker : U = π.ker := by
    have h := CommHopfAlgCat.quotientPointsSubgroup_kernelHopfIdeal_eq_ker_mapPointsFunctor
      (_root_.CommHopfAlgCat.ofHom p) (CommAlgCat.of k k)
    change CommHopfAlgCat.quotientPointsSubgroup H.obj
      (CommHopfAlgCat.kernelHopfIdeal (_root_.CommHopfAlgCat.ofHom p))
      (CommAlgCat.of k k) = π.ker at h
    rw [hp] at h
    exact h
  let : U.Normal := hker ▸ inferInstance
  let UE := Iso.groupIsoToMulEquiv (CommHopfAlgCat.quotientPointsSubgroupIso H.obj
    (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H) (CommAlgCat.of k k))
  let Uc := FiniteTypeCommHopfAlgCat.unipotentRadical H
  let : IsReduced Uc := unipotentRadical_isReduced H
  let : Group.IsNilpotent (WithConv (Uc →ₐ[k] k)) :=
    isNilpotent_points_of_forall_isUnipotentPoint Uc (unipotentRadical_points_unipotent H)
  let : Group.IsNilpotent U := Group.nilpotent_of_surjective UE.toMonoidHom UE.surjective
  have hnpos : 0 < n := by
    by_contra! h
    have hnzero : n = 0 := Nat.eq_zero_of_le_zero h
    exact hn (by rw [hnzero]; simp)
  let F := Subgroup.zpowers s
  let : Finite F := finite_zpowers.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hnpos, hs⟩)
  have hFcard : (Nat.card F : k) ≠ 0 := by
    obtain ⟨a, ha⟩ := orderOf_dvd_of_pow_eq_one hs
    have hcast : (n : k) = (orderOf s : k) * (a : k) := by
      rw [ha, Nat.cast_mul]
    rw [show Nat.card F = orderOf s from Nat.card_zpowers s]
    exact fun hz => hn (by rw [hcast, hz, zero_mul])
  have hpow : Function.Bijective (fun u : U => u ^ Nat.card F) := by
    have h := pow_bijective_of_unipotent Uc (unipotentRadical_points_unipotent H) hFcard
    constructor
    · intro u v huv
      apply UE.symm.injective
      exact h.1 (by simpa using congrArg UE.symm huv)
    · intro u
      obtain ⟨v,hv⟩ := h.2 (UE.symm u)
      exact ⟨UE v,by simpa using congrArg UE hv⟩
  let φ : F →* WithConv (H →ₐ[k] k) := F.subtype
  let ψ : F →* WithConv (H →ₐ[k] k) := σ.comp (π.comp φ)
  have hcong : ∀ a : F, φ a * (ψ a)⁻¹ ∈ U := by
    intro a
    rw [hker, MonoidHom.mem_ker, map_mul, map_inv]
    have hψ : π (ψ a) = π (φ a) := congrArg (fun f => f (π (φ a))) hsec
    rw [hψ, mul_inv_cancel]
  obtain ⟨u, hu⟩ := CFSG.GroupTheory.exists_conj_of_mul_inv_mem_of_finite_actor U hpow φ ψ hcong
  have h := hu ⟨s, Subgroup.mem_zpowers s⟩
  change (u : WithConv (H →ₐ[k] k)) * s * (u : WithConv (H →ₐ[k] k))⁻¹ =
    AlgHom.mapDomain j (AlgHom.mapDomain p s) at h
  obtain ⟨q,hq⟩ := u.2
  have hiq : CommHopfAlgCat.quotientPointsHom H.obj
      (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H) (CommAlgCat.of k k) q =
      unipotentRadicalPointsHom H q := by
    rw [unipotentRadicalPointsHom, FiniteTypeCommHopfAlgCat.unipotentRadicalCoordinateMap_def]
    exact CommHopfAlgCat.quotientPointsHom_apply _ _ _ q
  exact ⟨q,by simpa only [← hq, hiq] using h⟩

theorem exists_unipotentRadical_conj_of_pow_eq_one_of_solvable
    (H : FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced H]
    [ConnectedSpace (PrimeSpectrum H)] [Group.IsSolvable (WithConv (H →ₐ[k] k))]
    {n : ℕ} (hn : (n : k) ≠ 0) (s : WithConv (H →ₐ[k] k)) (hs : s ^ n = 1) :
    ∃ (T : FiniteTypeCommHopfAlgCat.{u,u} k) (j : H →ₐc[k] T),
      torusCommHopfAlgProperty k T ∧ Function.Surjective j ∧
      ∃ (u : WithConv (FiniteTypeCommHopfAlgCat.unipotentRadical H →ₐ[k] k))
        (t : WithConv (T →ₐ[k] k)),
        unipotentRadicalPointsHom H u * s * (unipotentRadicalPointsHom H u)⁻¹ =
          AlgHom.mapDomain j t := by
  obtain ⟨T,p,j,hT,hp,hker,hj,-⟩ := exists_torus_quotient_section_of_solvable H
  have hjs : Function.Surjective j := by
    intro t
    refine ⟨p t, ?_⟩
    exact congrArg (fun f : T →ₐc[k] T => f t) hj
  obtain ⟨u,hu⟩ := exists_unipotentRadical_conj_of_pow_eq_one_of_torus_section H T p j hker hj hn s hs
  exact ⟨T,j,hT,hjs,u,AlgHom.mapDomain p s,hu⟩

theorem exists_isMaximalTorus_of_pow_eq_one_of_solvable
    (H : FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced H]
    [ConnectedSpace (PrimeSpectrum H)] [Group.IsSolvable (WithConv (H →ₐ[k] k))]
    {n : ℕ} (hn : (n : k) ≠ 0) (s : WithConv (H →ₐ[k] k)) (hs : s ^ n = 1) :
    ∃ I : HopfIdeal k H,
      HopfIdeal.IsMaximalTorus k H.obj I ∧
        s ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) := by
  obtain ⟨T,j,hT,hjs,u,t,hu⟩ := exists_unipotentRadical_conj_of_pow_eq_one_of_solvable H hn s hs
  let I := HopfIdeal.kerOfSurjective j hjs
  have hI : torusCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient H I) := by
    let e := CommHopfAlgCat.quotientKerOfSurjectiveIso (_root_.CommHopfAlgCat.ofHom j) hjs
    exact (torusCommHopfAlgProperty k).prop_of_iso
      (ObjectProperty.isoMk (finiteTypeCommHopfAlgProperty k) e.symm) hT
  have htI : AlgHom.mapDomain j t ∈
      CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) := by
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro x hx
    have hxj : j x = 0 := (HopfIdeal.mem_kerOfSurjective j hjs).mp hx
    change t.ofConv (j x) = 0
    rw [hxj, map_zero]
  let v := unipotentRadicalPointsHom H u
  obtain ⟨J,hJI,hJ⟩ := HopfIdeal.exists_isMaximalTorus_le H hI
  have htJ : AlgHom.mapDomain j t ∈
      CommHopfAlgCat.quotientPointsSubgroup H.obj J (CommAlgCat.of k k) := by
    rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at htI ⊢
    exact fun x hx => htI x (hJI hx)
  refine ⟨J.conjugate v⁻¹,hJ.conjugate v⁻¹,?_⟩
  have hconj := (CommHopfAlgCat.pointConjugation_mem_conjugate_iff J v⁻¹
    (CommAlgCat.of k k) (AlgHom.mapDomain j t)).mpr htJ
  have hmv (x : WithConv (H →ₐ[k] k)) : AlgHom.mapValue (H := H) (Algebra.ofId k k) x = x := by
    ext a
    simp
  simp only [hmv, inv_inv] at hconj
  have heq : v⁻¹ * AlgHom.mapDomain j t * v = s := by
    rw [← hu]
    dsimp only [v]
    group
  exact heq ▸ hconj

end CFSG.LieType.AlgebraicGroups.SolvableSemisimple
