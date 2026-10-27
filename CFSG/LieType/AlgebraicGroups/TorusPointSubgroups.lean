module

public import CFSG.LieType.AlgebraicGroups.IdentityComponentTangent
public import CFSG.LieType.AlgebraicGroups.SplitTorusTwoTorsion
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LieType.AlgebraicGroups.CoordinateConjugation
public import CFSG.LieType.AlgebraicGroups.ClosedIdentityComponentFunctorial
public import CFSG.LieType.AlgebraicGroups.DiagonalSubgroupTorus
public import CFSG.LieType.AlgebraicGroups.ZariskiClosureFrobenius
import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Basic
import TauCeti.Algebra.AlgebraicGroup.Hopf.Map

public noncomputable section
namespace CFSG.LieType.AlgebraicGroups
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv CategoryTheory Subgroup
open scoped CFSG.ConvolutionPoints

section Matrix
variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k]
  {Z : Subgroup (ModGL τ k)}

abbrev closedIdentityCoordinateRing (Z : Subgroup (ModGL τ k)) : Type _ :=
  GLCoord k (Label τ) ⧸
    subgroupIdeal ((closedIdentityComponent Z).map (modGLPoint τ k).toMonoidHom)

theorem exists_finrank_tangent_primeTorsion_range_modGL
    {p : ℕ} (hp : p.Prime) (hpk : (p : k) ≠ 0)
    (hZ : IsPointClosed k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k))))
    (htor : TauCeti.torusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.of k (closedIdentityCoordinateRing (τ := τ) Z))) :
    ∃ d : ℕ, Module.finrank k (TangentSpace k
        (closedIdentityCoordinateRing (τ := τ) Z)
        (Bialgebra.counitAlgHom k _)) = d ∧
      ∃ ι : Multiplicative (Fin d → ZMod p) →* ModGL τ k,
        Function.Injective ι ∧ ∀ x : ModGL τ k,
          x ∈ ι.range ↔ x ∈ closedIdentityComponent Z ∧ x ^ p = 1 := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  let C : Subgroup (ModGL τ k) := closedIdentityComponent Z
  let H : Subgroup (WithConv (GLCoord k (Label τ) →ₐ[k] k)) :=
    C.map (modGLPoint τ k).toMonoidHom
  let Q : Type _ := GLCoord k (Label τ) ⧸ subgroupIdeal H
  have hpts : pointsZero k (subgroupIdeal H) = subgroupPoints H :=
    (isConnectedAlgebraicSubgroup_closedIdentityComponent (Z := Z) hZ).pointsZero_eq
  obtain ⟨d, hd, ι', hι', hrange'⟩ :=
    exists_finrank_tangent_primeTorsion_range_of_torus (R := Q) hp hpk htor
  let ψ : WithConv (Q →ₐ[k] k) ≃* H := subgroupQuotientPointsEquiv H hpts
  let ι : Multiplicative (Fin d → ZMod p) →* ModGL τ k :=
    (modGLPoint τ k).symm.toMonoidHom.comp (H.subtype.comp (ψ.toMonoidHom.comp ι'))
  have hι : Function.Injective ι :=
    (modGLPoint τ k).symm.injective.comp
      ((Subgroup.subtype_injective H).comp (ψ.injective.comp hι'))
  refine ⟨d, hd, ι, hι, ?_⟩
  intro x
  constructor
  · rintro ⟨e, rfl⟩
    have hι'pow : (ι' e) ^ p = 1 :=
      (hrange'.1 (ι' e)).mp (MonoidHom.mem_range.mpr ⟨e, rfl⟩)
    have hψpow : (ψ (ι' e)) ^ p = 1 := by
      rw [← map_pow, hι'pow, map_one]
    have hHpow : (H.subtype (ψ (ι' e))) ^ p = 1 := by
      rw [← map_pow, hψpow, map_one]
    have hxpow : ((modGLPoint τ k).symm (H.subtype (ψ (ι' e)))) ^ p = 1 := by
      rw [← map_pow, hHpow, map_one]
    have hxC : (modGLPoint τ k).symm (H.subtype (ψ (ι' e))) ∈ C := by
      have hmemH : H.subtype (ψ (ι' e)) ∈ H := (ψ (ι' e)).2
      obtain ⟨z, hzC, hzφ⟩ := Subgroup.mem_map.1 hmemH
      have hx_eq : (modGLPoint τ k).symm (H.subtype (ψ (ι' e))) = z := by
        rw [← hzφ]
        simp
      rwa [hx_eq]
    change (modGLPoint τ k).symm (H.subtype (ψ (ι' e))) ∈ C ∧
      ((modGLPoint τ k).symm (H.subtype (ψ (ι' e)))) ^ p = 1
    exact ⟨hxC, hxpow⟩
  · rintro ⟨hxC, hxpow⟩
    have hxH : (modGLPoint τ k) x ∈ H :=
      Subgroup.mem_map_of_mem (modGLPoint τ k).toMonoidHom hxC
    let y : H := ⟨(modGLPoint τ k) x, hxH⟩
    have hyp : ((modGLPoint τ k) x) ^ p = 1 := by
      rw [← map_pow, hxpow, map_one]
    have hypH : (y : H) ^ p = 1 := by
      apply Subtype.ext
      simpa [y] using hyp
    have hψp : (ψ.symm y) ^ p = 1 := by
      apply ψ.injective
      rw [map_pow, ψ.apply_symm_apply, hypH, map_one]
    obtain ⟨e, he⟩ := MonoidHom.mem_range.1 ((hrange'.1 (ψ.symm y)).mpr hψp)
    refine ⟨e, ?_⟩
    change (modGLPoint τ k).symm (H.subtype (ψ (ι' e))) = x
    rw [he, ψ.apply_symm_apply]
    simp [y]

omit [IsAlgClosed k] in
theorem isPointClosed_map_conj {Z : Subgroup (ModGL τ k)}
    (hZ : IsPointClosed k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k))))
    (g : ModGL τ k) :
    IsPointClosed k (transportPoints (modGLPoint τ k)
      (Z.map (MulAut.conj g).toMonoidHom : Set (ModGL τ k))) := by
  have h := isPointClosed_preimage_mul_mul g⁻¹ g hZ
  have hs : (Z.map (MulAut.conj g).toMonoidHom : Set (ModGL τ k)) =
      (fun x => g⁻¹ * x * g) ⁻¹' (Z : Set (ModGL τ k)) := by
    ext x
    change x ∈ Z.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ Z
    rw [Subgroup.mem_map_equiv]
    rfl
  rwa [hs]

omit [IsAlgClosed k] in
theorem map_conj_modGLPoint (Z : Subgroup (ModGL τ k)) (g : ModGL τ k) :
    (Z.map (MulAut.conj g).toMonoidHom).map (modGLPoint τ k).toMonoidHom =
      (Z.map (modGLPoint τ k).toMonoidHom).map
        (MulAut.conj (modGLPoint τ k g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    map_mul, map_inv]

theorem torus_closedIdentityComponent_of_conj_le_torus
    {Z : Subgroup (ModGL τ k)}
    (hZ : IsPointClosed k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k))))
    (g : ModGL τ k)
    (hconj : (closedIdentityComponent Z).map (MulAut.conj g).toMonoidHom ≤ torusGroup τ k) :
    TauCeti.torusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.of k (closedIdentityCoordinateRing Z)) := by
  let H := (closedIdentityComponent Z).map (modGLPoint τ k).toMonoidHom
  let Z' := Z.map (MulAut.conj g).toMonoidHom
  have hZ' := isPointClosed_map_conj hZ g
  have hH' := isConnectedAlgebraicSubgroup_closedIdentityComponent (Z := Z') hZ'
  have hmap : (closedIdentityComponent Z').map (modGLPoint τ k).toMonoidHom =
      H.map (MulAut.conj (modGLPoint τ k g)).toMonoidHom := by
    rw [closedIdentityComponent_map_conj, map_conj_modGLPoint]
  have hdiag : ∀ x ∈ (closedIdentityComponent Z').map (modGLPoint τ k).toMonoidHom,
      ∀ i j : Label τ, i ≠ j → x.ofConv (glEntry k (Label τ) i j) = 0 := by
    rintro _ ⟨x, hx, rfl⟩ i j hij
    rw [closedIdentityComponent_map_conj] at hx
    have hxT := hconj hx
    obtain ⟨c, hc⟩ := exists_apply_single_of_mem_diagonalGroup
      (torusGroup_le_diagonalGroup hxT) j
    change (modGLPoint τ k x).ofConv (glEntry k (Label τ) i j) = 0
    rw [modGLPoint_apply_glEntry, hc]
    simp [hij]
  have ht := torusCommHopfAlgProperty_of_diagonal_points _ hH' hdiag
  rw [hmap] at ht
  exact (torusCommHopfAlgProperty_conjugate_iff H (modGLPoint τ k g)).mp ht

end Matrix

section GeneralPower
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
 {R : Type u} [CommRing R] [HopfAlgebra k R] [Algebra.FiniteType k R]

theorem surjective_pow_of_torus
    (hR : TauCeti.torusCommHopfAlgProperty k (TauCeti.FiniteTypeCommHopfAlgCat.of k R))
    {m : ℕ} (hm : 0 < m) : Function.Surjective (fun x : WithConv (R →ₐ[k] k) => x ^ m) := by
  classical
  let T := TauCeti.FiniteTypeCommHopfAlgCat.of k R

  have hs := hR.split
  obtain ⟨r,⟨i⟩⟩ := (TauCeti.splitTorusCommHopfAlgProperty_iff k T).mp hs
  let C : Type u := (TauCeti.DiagonalizableGroup.coordinateRing k
    (TauCeti.SplitTorus.characterGroup (ULift.{u} (Fin r)))).obj
  let e : C ≃ₐc[k] R := CommHopfAlgCat.ofIso
    ((forget₂ (TauCeti.FiniteTypeCommHopfAlgCat k) (CommHopfAlgCat k)).mapIso i)
  let ψ : WithConv (R →ₐ[k] k) ≃* (ULift.{u} (Fin r) → kˣ) :=
    (TauCeti.AlgHom.mapDomainMulEquiv (A := k) e).trans
      (TauCeti.SplitTorus.pointsMulEquiv (R := k) (A := k) (σ := ULift.{u} (Fin r)))
  intro x
  have hy : ∀ j : ULift.{u} (Fin r), ∃ u : kˣ, u ^ m = ψ x j := by
    intro j
    obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (k := k) (ψ x j : k) hm
    have hz0 : z ≠ 0 := by
      intro h0
      have h : (ψ x j : k)=0 := by rw [← hz,h0,zero_pow (Nat.ne_of_gt hm)]
      exact (ψ x j).ne_zero h
    exact ⟨Units.mk0 z hz0,Units.ext hz⟩
  choose y hy using hy
  refine ⟨ψ.symm y,ψ.injective ?_⟩
  rw [map_pow,ψ.apply_symm_apply]
  exact funext hy

end GeneralPower

section Power
variable {k : Type} [Field k] [IsAlgClosed k]
 {R : Type} [CommRing R] [HopfAlgebra k R] [Algebra.FiniteType k R]

variable {A : Type} [CommRing A] [HopfAlgebra k A] [Algebra.FiniteType k A]

theorem exists_pow_mem_of_torus
    (H : Subgroup (WithConv (A →ₐ[k] k)))
    (hH : pointsZero k (subgroupIdeal H) = subgroupPoints H)
    (htor : TauCeti.torusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.of k (A ⧸ subgroupIdeal H)))
    {m : ℕ} (hm : 0 < m) {x : WithConv (A →ₐ[k] k)} (hx : x ∈ H) :
    ∃ y ∈ H, y ^ m = x := by
  let e := subgroupQuotientPointsEquiv H hH
  obtain ⟨y, hy⟩ := surjective_pow_of_torus htor hm (e.symm ⟨x, hx⟩)
  refine ⟨e y, (e y).2, ?_⟩
  have h := congrArg e hy
  rw [map_pow, e.apply_symm_apply] at h
  exact congrArg (fun z : H => (z : WithConv (A →ₐ[k] k))) h

theorem mul_comm_of_torus_points
    (H : Subgroup (WithConv (A →ₐ[k] k)))
    (hH : pointsZero k (subgroupIdeal H) = subgroupPoints H)
    (htor : TauCeti.torusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.of k (A ⧸ subgroupIdeal H)))
    {x y : WithConv (A →ₐ[k] k)} (hx : x ∈ H) (hy : y ∈ H) : x * y = y * x := by
  obtain ⟨d, hd, ⟨e⟩⟩ := exists_finrank_tangent_pointsMulEquiv_of_torus htor
  let ψ := subgroupQuotientPointsEquiv H hH
  have : (⟨x,hx⟩ : H) * ⟨y,hy⟩ = ⟨y,hy⟩ * ⟨x,hx⟩ := by
    apply ψ.symm.injective
    apply e.injective
    rw [map_mul, map_mul, map_mul, map_mul]
    exact mul_comm _ _
  exact congrArg (fun z : H => (z : WithConv (A →ₐ[k] k))) this

theorem not_torus_of_inverted_odd
    (H : Subgroup (WithConv (A →ₐ[k] k)))
    (hH : pointsZero k (subgroupIdeal H) = subgroupPoints H)
    {g e : WithConv (A →ₐ[k] k)} (hg : g ∈ H) (he : e ∈ H)
    {n : ℕ} (hn : Odd n) (hen : e ^ n = 1) (he1 : e ≠ 1) (hinv : g * e * g⁻¹ = e⁻¹) :
    ¬ TauCeti.torusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.of k (A ⧸ subgroupIdeal H)) := by
  intro htor
  have hcomm := mul_comm_of_torus_points H hH htor hg he
  have hei : e = e⁻¹ := by
    simpa only [hcomm, mul_assoc, mul_inv_cancel, mul_one] using hinv
  have he2 : e ^ 2 = 1 := by
    simpa only [pow_two, mul_inv_cancel] using congrArg (fun x => e * x) hei
  apply he1
  obtain ⟨m, rfl⟩ := hn
  rw [pow_succ, pow_mul, he2, one_pow, one_mul] at hen
  exact hen

theorem finrank_tangent_pos_of_torus_point_ne_one
    (H : Subgroup (WithConv (A →ₐ[k] k)))
    (hH : pointsZero k (subgroupIdeal H) = subgroupPoints H)
    (htor : TauCeti.torusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.of k (A ⧸ subgroupIdeal H)))
    {x : WithConv (A →ₐ[k] k)} (hx : x ∈ H) (hx1 : x ≠ 1) :
    0 < Module.finrank k (TangentSpace k (A ⧸ subgroupIdeal H)
      (Bialgebra.counitAlgHom k _)) := by
  obtain ⟨d, hd, ⟨e⟩⟩ := exists_finrank_tangent_pointsMulEquiv_of_torus htor
  by_contra h
  have hd0 : d = 0 := by omega
  subst d
  let ψ := subgroupQuotientPointsEquiv H hH
  have he : e (ψ.symm ⟨x, hx⟩) = e 1 := by
    funext j
    have : Fin 0 := hd0 ▸ j.down
    exact Fin.elim0 this
  have hp : ψ.symm ⟨x, hx⟩ = 1 := e.injective he
  have hxH : (⟨x, hx⟩ : H) = 1 := by
    have h := congrArg ψ hp
    simpa using h
  exact hx1 (congrArg (fun z : H => (z : WithConv (A →ₐ[k] k))) hxH)

variable {τ : Tag}

theorem mul_comm_of_matrix_torus
    (T : Subgroup (ModGL τ k))
    (hT : IsConnectedAlgebraicSubgroup k (T.map (modGLPoint τ k).toMonoidHom))
    (htor : TauCeti.torusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.of k
        (GLCoord k (Label τ) ⧸ subgroupIdeal (T.map (modGLPoint τ k).toMonoidHom))))
    {x y : ModGL τ k} (hx : x ∈ T) (hy : y ∈ T) : x * y = y * x := by
  apply (modGLPoint τ k).injective
  rw [map_mul, map_mul]
  exact mul_comm_of_torus_points _ hT.pointsZero_eq htor
    (mem_map_of_mem (modGLPoint τ k).toMonoidHom hx)
    (mem_map_of_mem (modGLPoint τ k).toMonoidHom hy)

end Power

end CFSG.LieType.AlgebraicGroups
