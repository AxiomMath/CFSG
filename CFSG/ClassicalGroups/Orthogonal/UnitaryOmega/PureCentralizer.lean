module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureBlockDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportCharts
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusEightLeviBasic
public import CFSG.ClassicalGroups.SpecialLinear.TvModLinAlg
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

set_option linter.style.haveILetI false

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open Module QuadraticMap
open scoped commutatorElement
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

private noncomputable def planeEquiv {n : ℕ} (i : Fin n) :
    K ≃ₗ[F] ↥(coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) i) where
  toFun z := ⟨((0, 0), Pi.single i z), mem_coordPlane.mpr ⟨z, rfl⟩⟩
  invFun u := u.1.2 i
  map_add' z w := by
    apply Subtype.ext
    simp [Pi.single_add]
  map_smul' c z := by
    apply Subtype.ext
    simp [Pi.single_smul]
  left_inv z := by
    show (((0, 0), Pi.single i z) : (F × F) × (Fin n → K)).2 i = z
    simp
  right_inv u := by
    obtain ⟨z, hz⟩ := mem_coordPlane.mp u.2
    have hz' : ((0, 0), Pi.single i z) = (u : (F × F) × (Fin n → K)) := hz
    have hzi : u.1.2 i = z := by rw [← hz']; simp
    apply Subtype.ext
    show ((0, 0), Pi.single i (u.1.2 i)) = (u : (F × F) × (Fin n → K))
    rw [hzi]
    exact hz'

private theorem planeEquiv_isometry {n : ℕ} (i : Fin n) (z : K) :
    ((normHypForm E n).comp
        (coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) i).subtype)
      (planeEquiv i z) = normQuad E z := by
  rw [QuadraticMap.comp_apply, normHypForm_apply_coord]
  change (hypPlane F) (0, 0) + ∑ j, (normQuad E) ((Pi.single i z : Fin n → K) j) =
    (normQuad E) z
  rw [hypPlane_apply]
  simp
  refine (Finset.sum_eq_single i ?_ ?_).trans ?_
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, QuadraticMap.map_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi
  · rw [Pi.single_eq_same]

private noncomputable def planeIsometry {n : ℕ} (i : Fin n) :
    (normQuad E).IsometryEquiv
      ((normHypForm E n).comp
        (coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) i).subtype) where
  toLinearEquiv := planeEquiv i
  map_app' := planeEquiv_isometry E i

omit [Finite K] [CharP K 2] in
private theorem coordPlane_inf_coordPlane {n : ℕ} {j k : Fin n} (hjk : j ≠ k) :
    coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) j ⊓
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) k = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hj, hk⟩ := Submodule.mem_inf.mp hv
  obtain ⟨z : K, hz⟩ := mem_coordPlane.mp hj
  obtain ⟨w : K, hw⟩ := mem_coordPlane.mp hk
  change ((0, Pi.single j z) : (F × F) × (Fin n → K)) = v at hz
  change ((0, Pi.single k w) : (F × F) × (Fin n → K)) = v at hw
  have hcoord : (Pi.single j z : Fin n → K) = Pi.single k w :=
    congrArg Prod.snd (hz.trans hw.symm)
  have hz0 : z = 0 := by
    have h := congrFun hcoord j
    simpa [Pi.single_eq_same, Pi.single_eq_of_ne hjk] using h
  rw [← hz, hz0]
  simp

private noncomputable def pairLinear (F K : Type) [Field F] [Field K] [Algebra F K]
    {n : ℕ} (j k : Fin n) : K →ₗ[F] ((F × F) × (Fin n → K)) :=
  (coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) j).subtype.comp
      (planeEquiv (n := n) j).toLinearMap +
    (coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) k).subtype.comp
      (planeEquiv (n := n) k).toLinearMap

private noncomputable def pairDiagonal (F K : Type) [Field F] [Field K] [Algebra F K]
    {n : ℕ} (j k : Fin n) :
    K →ₗ[F] ↥(coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) j ⊔
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) k) :=
  LinearMap.codRestrict
    (coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) j ⊔
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) k)
    (pairLinear F K j k)
    fun z => Submodule.add_mem_sup (planeEquiv (n := n) j z).2 (planeEquiv (n := n) k z).2

private theorem pairDiagonal_apply (F K : Type) [Field F] [Field K] [Algebra F K]
    {n : ℕ} (j k : Fin n) (z : K) :
    (pairDiagonal F K j k z : (F × F) × (Fin n → K)) =
      ((0, 0), (Pi.single j z : Fin n → K) + (Pi.single k z : Fin n → K)) := by
  rw [show (pairDiagonal F K j k z : (F × F) × (Fin n → K)) =
      (pairLinear F K j k z : (F × F) × (Fin n → K)) from rfl]
  simp only [pairLinear, LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply]
  simp [planeEquiv, Prod.mk_add_mk]

private theorem pairDiagonal_injective (F K : Type) [Field F] [Field K] [Algebra F K]
    {n : ℕ} {j k : Fin n} (hjk : j ≠ k) :
    Function.Injective (pairDiagonal F K j k) := by
  intro a b hab
  have hval : (pairDiagonal F K j k a : (F × F) × (Fin n → K)) =
      (pairDiagonal F K j k b : (F × F) × (Fin n → K)) := congrArg Subtype.val hab
  have h := congrFun (congrArg (fun u : (F × F) × (Fin n → K) => u.2) hval) j
  rw [pairDiagonal_apply F K j k a, pairDiagonal_apply F K j k b] at h
  simp only [Pi.add_apply] at h
  simpa [Pi.single_eq_same, Pi.single_eq_of_ne hjk] using h

private theorem pairDiagonal_singular (E : QuadExt F K (unitaryInvolution K 2 f)) [CharP F 2]
    {n : ℕ} {j k : Fin n} (hjk : j ≠ k) (z : K) :
    (normHypForm E n) (pairDiagonal F K j k z : (F × F) × (Fin n → K)) = 0 := by
  have h1 : (normHypForm E n) (((0, 0), (Pi.single j z : Fin n → K)) :
      (F × F) × (Fin n → K)) = normQuad E z := by
    change ((normHypForm E n).comp
      (coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) j).subtype)
      (planeEquiv (n := n) j z) = normQuad E z
    exact planeEquiv_isometry E j z
  have h2 : (normHypForm E n) (((0, 0), (Pi.single k z : Fin n → K)) :
      (F × F) × (Fin n → K)) = normQuad E z := by
    change ((normHypForm E n).comp
      (coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) k).subtype)
      (planeEquiv (n := n) k z) = normQuad E z
    exact planeEquiv_isometry E k z
  have h3 : polar (normHypForm E n)
      (((0, 0), (Pi.single j z : Fin n → K)) : (F × F) × (Fin n → K))
      (((0, 0), (Pi.single k z : Fin n → K)) : (F × F) × (Fin n → K)) = 0 :=
    polar_coordPlane_plane (LinearEquiv.refl F ((F × F) × (Fin n → K)))
      (normHypForm_apply_coord E n) hjk (mem_coordPlane.mpr ⟨z, rfl⟩)
      (mem_coordPlane.mpr ⟨z, rfl⟩)
  have hdecomp : (pairDiagonal F K j k z : (F × F) × (Fin n → K)) =
      (((0, 0), (Pi.single j z : Fin n → K)) : (F × F) × (Fin n → K)) +
        (((0, 0), (Pi.single k z : Fin n → K)) : (F × F) × (Fin n → K)) := by
    rw [pairDiagonal_apply F K j k z, Prod.mk_add_mk]
    simp
  rw [hdecomp, QuadraticMap.map_add (normHypForm E n), h1, h2, h3, add_zero]
  exact CharTwo.add_self_eq_zero (normQuad E z)

private theorem exists_totallySingular_coordPlane_sup
    (E : QuadExt F K (unitaryInvolution K 2 f)) [CharP F 2]
    {n : ℕ} {j k : Fin n} (hjk : j ≠ k) :
    ∃ S : Submodule F ↥(coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) j ⊔
        coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) k),
      Module.finrank F S = 2 ∧
        ∀ x ∈ S, ((normHypForm E n).comp
          (coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) j ⊔
            coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) k).subtype) x = 0 := by
  refine ⟨LinearMap.range (pairDiagonal F K j k), ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj (pairDiagonal_injective F K hjk), E.finrank_eq]
  · rintro _ ⟨z, rfl⟩
    exact pairDiagonal_singular E hjk z

private theorem nondegenerate_coordPlane_sup_pair
    (E : QuadExt F K (unitaryInvolution K 2 f)) {n : ℕ} (j k : Fin n) :
    (polarBilin ((normHypForm E n).comp
      (coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) j ⊔
        coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) k).subtype)).Nondegenerate := by
  classical
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  let V := (F × F) × (Fin n → K)
  let Q : QuadraticForm F V := normHypForm E n
  let U : Fin n → Submodule F V := fun i => coordPlane (LinearEquiv.refl F V) i
  have hψ : ∀ v : V, Q v = hypPlane F v.1 + ∑ i, normQuad E (v.2 i) :=
    normHypForm_apply_coord E n
  have hQE : (polarBilin (normQuad E)).Nondegenerate := normQuad_polarBilin_nondegenerate E
  have hUreg : ∀ i, PolarNondegOn Q (U i) := fun i =>
    coordPlane_polarNondegOn (LinearEquiv.refl F V) hψ hQE i
  have horth : ∀ i t, i ≠ t → ∀ x ∈ U i, ∀ y ∈ U t, polar Q x y = 0 := fun i t hit x hx y hy =>
    polar_coordPlane_plane (LinearEquiv.refl F V) hψ hit hx hy
  have h := CFSG.RankThree.PartOne.KCOrthogonal.nondegenerate_finset_sup U hUreg horth
    ({j, k} : Finset (Fin n))
  have hsup : ({j, k} : Finset (Fin n)).sup U = U j ⊔ U k := by
    rw [Finset.sup_insert, Finset.sup_singleton]
  rwa [hsup] at h

private theorem finrank_coordPlane_sup_pair
    (E : QuadExt F K (unitaryInvolution K 2 f)) {n : ℕ} {j k : Fin n} (hjk : j ≠ k) :
    Module.finrank F ↥(coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) j ⊔
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) k) = 2 * 2 := by
  classical
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  let V := (F × F) × (Fin n → K)
  let U : Fin n → Submodule F V := fun i => coordPlane (LinearEquiv.refl F V) i
  have hUdim : ∀ i, Module.finrank F (U i) = 2 := fun i =>
    (LinearEquiv.finrank_eq (planeEquiv (n := n) i)).symm.trans E.finrank_eq
  have hdisj : U j ⊓ U k = ⊥ := coordPlane_inf_coordPlane hjk
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (U j) (U k)
  rw [hdisj, finrank_bot, hUdim j, hUdim k] at hsum
  omega

private theorem isPerfect_supportedDerived_pair {n : ℕ} {j k : Fin n} (hjk : j ≠ k)
    (hq : 4 ≤ Nat.card F) :
    Group.IsPerfect ↥(supportedDerived (normHypForm E n)
      (coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) j ⊔
        coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) k)) := by
  classical
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  let V := (F × F) × (Fin n → K)
  let Q : QuadraticForm F V := normHypForm E n
  let Y : Submodule F V :=
    coordPlane (LinearEquiv.refl F V) j ⊔ coordPlane (LinearEquiv.refl F V) k
  have hYnd : (polarBilin (Q.comp Y.subtype)).Nondegenerate :=
    nondegenerate_coordPlane_sup_pair E j k
  have hYdim : Module.finrank F ↥Y = 2 * 2 :=
    finrank_coordPlane_sup_pair E hjk
  obtain ⟨S, hSdim, hSsing⟩ := exists_totallySingular_coordPlane_sup E hjk
  have hsplit : ∃ S : Submodule F ↥Y, Module.finrank F S = 2 ∧
      ∀ x ∈ S, (Q.comp Y.subtype) x = 0 := ⟨S, hSdim, hSsing⟩
  haveI : Group.IsPerfect ↥(orthDerived (Q.comp Y.subtype)) :=
    Subgroup.isPerfect_iff.mpr
      (CFSG.SeitzReduction.OmegaPilot.commutator_orthDerived_of_splitFour hYnd hYdim hsplit hq)
  exact Group.IsPerfect.ofSurjective
    (f := (orthDerivedSupportedEquiv hYnd).toMonoidHom)
    (orthDerivedSupportedEquiv hYnd).surjective

private theorem nondegenerate_coordPlane (E : QuadExt F K (unitaryInvolution K 2 f))
    {n : ℕ} (i : Fin n) :
    (polarBilin ((normHypForm E n).comp
      (coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) i).subtype)).Nondegenerate := by
  classical
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  exact CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn
    (coordPlane_polarNondegOn (LinearEquiv.refl F ((F × F) × (Fin n → K)))
      (normHypForm_apply_coord E n) (normQuad_polarBilin_nondegenerate E) i)

private theorem finrank_coordPlane (E : QuadExt F K (unitaryInvolution K 2 f))
    {n : ℕ} (i : Fin n) :
    Module.finrank F ↥(coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) i) = 2 :=
  (LinearEquiv.finrank_eq (planeEquiv (n := n) i)).symm.trans E.finrank_eq

private theorem orthogonal_coordPlane_of_ne (E : QuadExt F K (unitaryInvolution K 2 f))
    {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    ∀ x ∈ coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) i,
      ∀ y ∈ coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) j,
        polar (normHypForm E n) x y = 0 := by
  intro x hx y hy
  exact polar_coordPlane_plane (LinearEquiv.refl F ((F × F) × (Fin n → K)))
    (normHypForm_apply_coord E n) hij hx hy

private theorem supportedDerived_coordSupport_le_omega
    (E : QuadExt F K (unitaryInvolution K 2 f)) (n : ℕ) (S : Finset (Fin n)) :
    supportedDerived (normHypForm E n)
      (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S) ≤ normOmega E n := by
  classical
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  exact supportedDerived_le_orthDerived_of_regular
    (coordSupport_nondegenerate (LinearEquiv.refl F ((F × F) × (Fin n → K)))
      (normHypForm_apply_coord E n) (normHypForm_polarBilin_nondegenerate E n)
      (normQuad_polarBilin_nondegenerate E) S)

private theorem supportedDerived_coordPlane_sup_le_omega
    (E : QuadExt F K (unitaryInvolution K 2 f)) (n : ℕ) (S : Finset (Fin n)) :
    supportedDerived (normHypForm E n)
      (S.sup (fun t => coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) t)) ≤
        normOmega E n := by
  classical
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  let V := (F × F) × (Fin n → K)
  let U : Fin n → Submodule F V := fun t => coordPlane (LinearEquiv.refl F V) t
  have hψ : ∀ v : V, normHypForm E n v = hypPlane F v.1 + ∑ t, normQuad E (v.2 t) :=
    normHypForm_apply_coord E n
  have hQE : (polarBilin (normQuad E)).Nondegenerate := normQuad_polarBilin_nondegenerate E
  have hUreg : ∀ t, PolarNondegOn (normHypForm E n) (U t) := fun t =>
    coordPlane_polarNondegOn (LinearEquiv.refl F V) hψ hQE t
  have horth : ∀ a b, a ≠ b → ∀ x ∈ U a, ∀ y ∈ U b,
      polar (normHypForm E n) x y = 0 := fun a b hab x hx y hy =>
    polar_coordPlane_plane (LinearEquiv.refl F V) hψ hab hx hy
  exact supportedDerived_le_orthDerived_of_regular
    (CFSG.RankThree.PartOne.KCOrthogonal.nondegenerate_finset_sup U hUreg horth S)

private theorem isPerfect_subgroupOf {G : Type*} [Group G] {H K : Subgroup G} (hHK : H ≤ K)
    [Group.IsPerfect ↥H] : Group.IsPerfect ↥(H.subgroupOf K) :=
  Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hHK).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hHK).symm.surjective

theorem isPerfect_normPureBlock_pair {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (hq : 4 ≤ Nat.card F) :
    Group.IsPerfect ↥(normPureBlock E n {i, j}) := by
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  let V := (F × F) × (Fin n → K)
  let Q : QuadraticForm F V := normHypForm E n
  let U : Fin n → Submodule F V := fun i => coordPlane (LinearEquiv.refl F V) i
  have hψ : ∀ v : V, Q v = hypPlane F v.1 + ∑ i, normQuad E (v.2 i) :=
    normHypForm_apply_coord E n
  have hQE : (polarBilin (normQuad E)).Nondegenerate := normQuad_polarBilin_nondegenerate E
  have hUreg : ∀ i, PolarNondegOn Q (U i) := fun i =>
    coordPlane_polarNondegOn (LinearEquiv.refl F V) hψ hQE i
  have horth : ∀ i t, i ≠ t → ∀ x ∈ U i, ∀ y ∈ U t, polar Q x y = 0 := fun i t hit x hx y hy =>
    polar_coordPlane_plane (LinearEquiv.refl F V) hψ hit hx hy
  have hYnd : (polarBilin (Q.comp (({i, j} : Finset (Fin n)).sup U).subtype)).Nondegenerate :=
    CFSG.RankThree.PartOne.KCOrthogonal.nondegenerate_finset_sup U hUreg horth
      ({i, j} : Finset (Fin n))
  have hle : supportedDerived Q (({i, j} : Finset (Fin n)).sup U) ≤ normOmega E n :=
    supportedDerived_le_orthDerived_of_regular hYnd
  have hsup : (({i, j} : Finset (Fin n)).sup U) = U i ⊔ U j := by
    rw [Finset.sup_insert, Finset.sup_singleton]
  haveI : Group.IsPerfect ↥(supportedDerived Q (({i, j} : Finset (Fin n)).sup U)) := by
    rw [hsup]
    exact isPerfect_supportedDerived_pair E hij hq
  exact isPerfect_subgroupOf hle

section General

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [CharP K 2] {Q : QuadraticForm K V} {X Y : Submodule K V}

omit [Finite K] [FiniteDimensional K V] [CharP K 2] in
private theorem commutatorElement_apply_eq_self_of_commute_on
    {g h : V ≃ₗ[K] V} {U : Submodule K V}
    (hgU' : ∀ u ∈ U, g⁻¹ u ∈ U) (hhU' : ∀ u ∈ U, h⁻¹ u ∈ U)
    (hcomm : ∀ u ∈ U, g (h u) = h (g u)) {u : V} (hu : u ∈ U) :
    (⁅g, h⁆ : V ≃ₗ[K] V) u = u := by
  rw [commutatorElement_def]
  simp only [LinearEquiv.mul_apply]
  have h1 : g⁻¹ (h⁻¹ u) ∈ U := hgU' (h⁻¹ u) (hhU' u hu)
  have h2 := hcomm (g⁻¹ (h⁻¹ u)) h1
  rw [show g (g⁻¹ (h⁻¹ u)) = h⁻¹ u from LinearEquiv.apply_symm_apply g (h⁻¹ u)] at h2
  rw [h2]
  exact LinearEquiv.apply_symm_apply h u

omit [Finite K] [CharP K 2] in
private theorem sub_one_mapsTo_of_fixedFree
    (hX : (polarBilin (Q.comp X.subtype)).Nondegenerate)
    {ρ g : V ≃ₗ[K] V} (hρ : ρ ∈ supportedDerived Q X)
    (hρfix : ∀ z ∈ X, ρ z = z → z = 0) (hgcomm : Commute g ρ) :
    ∀ x ∈ X, g x ∈ X := by
  classical
  have hXr : PolarNondegOn Q X := polarNondegOn_of_nondegenerate hX
  have hdisp : ∀ x : V, ρ x - x ∈ X := by
    intro x
    obtain ⟨w, hw, p, hp, hwpx⟩ := suppExists_add_of_isCompl (isCompl_suppPerp hXr) x
    have hρp : ρ p = p := supportedDerived_apply_perp hρ hp
    have hx : ρ x - x = ρ w - w := by
      rw [← hwpx, map_add, hρp]
      abel
    rw [hx]
    exact Submodule.sub_mem X (supportedDerived_apply_mem hρ hw) hw
  let d : X →ₗ[K] X :=
    ((ρ : V →ₗ[K] V) - 1).restrict (p := X) (q := X) fun x _ => hdisp x
  have hdker : ∀ x : X, d x = 0 → x = 0 := by
    intro x hx
    have hval : ρ (x : V) - (x : V) = 0 := by
      have h := congrArg Subtype.val hx
      simpa [d] using h
    exact Subtype.ext (hρfix (x : V) x.2 (sub_eq_zero.mp hval))
  have hdinj : Function.Injective d := by
    intro x y hxy
    exact sub_eq_zero.mp (hdker (x - y) (by rw [map_sub, hxy, sub_self]))
  have hdsurj : Function.Surjective d := LinearMap.surjective_of_injective hdinj
  intro w hw
  obtain ⟨y, hy⟩ := hdsurj ⟨w, hw⟩
  have hyval : ρ (y : V) - (y : V) = w := by
    have h := congrArg Subtype.val hy
    simpa [d] using h
  have hρcomm : g (ρ (y : V)) = ρ (g (y : V)) :=
    congrArg (fun e : V ≃ₗ[K] V => e (y : V)) hgcomm.eq
  have hstep : g w = ρ (g (y : V)) - g (y : V) := by
    rw [← hyval, map_sub, hρcomm]
  rw [hstep]
  exact hdisp (g (y : V))

omit [Finite K] [CharP K 2] in
private theorem suppPerp_eq_sup_suppPerp_sup
    {A B : Submodule K V}
    (hA : (polarBilin (Q.comp A.subtype)).Nondegenerate)
    (hB : (polarBilin (Q.comp B.subtype)).Nondegenerate)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, polar Q a b = 0) :
    suppPerp Q A = B ⊔ suppPerp Q (A ⊔ B) := by
  classical
  have hAr : PolarNondegOn Q A := polarNondegOn_of_nondegenerate hA
  have hBr : PolarNondegOn Q B := polarNondegOn_of_nondegenerate hB
  have hMr : PolarNondegOn Q (A ⊔ B) :=
    CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup hAr hBr hAB
  have hcompl : IsCompl (A ⊔ B) (suppPerp Q (A ⊔ B)) := isCompl_suppPerp hMr
  refine le_antisymm ?_ ?_
  · intro v hv
    obtain ⟨m, hm, z, hz, rfl⟩ := suppExists_add_of_isCompl hcompl v
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
    have ha0 : a = 0 := by
      have h := hA.1 ⟨a, ha⟩ fun w => by
        rw [polarBilin_apply_apply, polar_comp_subtype_eq]
        have h1 : polar Q (w : V) (a + b + z) = 0 := mem_suppPerp.mp hv (w : V) w.2
        rw [polar_add_right, polar_add_right, hAB (w : V) w.2 b hb,
          mem_suppPerp.mp hz (w : V) (Submodule.mem_sup_left w.2), add_zero,
          add_zero] at h1
        rwa [polar_comm]
      exact congrArg Subtype.val h
    rw [ha0, zero_add]
    exact Submodule.add_mem_sup hb (mem_suppPerp.mpr fun m hm' => mem_suppPerp.mp hz m hm')
  · intro v hv
    obtain ⟨b, hb, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
    refine mem_suppPerp.mpr fun a ha => ?_
    rw [polar_add_right, hAB a ha b hb,
      mem_suppPerp.mp hz a (Submodule.mem_sup_left ha), add_zero]

omit [Finite K] [CharP K 2] in
private theorem fixedSpace_supportedDerived_eq
    (hX : (polarBilin (Q.comp X.subtype)).Nondegenerate)
    (hY : (polarBilin (Q.comp Y.subtype)).Nondegenerate)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, polar Q x y = 0)
    {ρ : V ≃ₗ[K] V} (hρ : ρ ∈ supportedDerived Q X)
    (hρfix : ∀ z ∈ X, ρ z = z → z = 0) :
    ∀ v : V, (∀ s ∈ supportedDerived Q X, s v = v) →
      v ∈ Y ⊔ suppPerp Q (X ⊔ Y) := by
  intro v hv
  rw [← suppPerp_eq_sup_suppPerp_sup hX hY hXY]
  obtain ⟨x, hx, w, hw, rfl⟩ :=
    suppExists_add_of_isCompl (isCompl_suppPerp (polarNondegOn_of_nondegenerate hX)) v
  have hxfix : ∀ s ∈ supportedDerived Q X, s x = x := by
    intro s hs
    have h1 := hv s hs
    rw [map_add s x w, supportedDerived_apply_perp hs hw] at h1
    exact add_right_cancel h1
  have hx0 : x = 0 := hρfix x hx (hxfix ρ hρ)
  rw [hx0, zero_add]
  exact hw

omit [Finite K] [CharP K 2] in
private theorem centralizer_mapsTo_sup
    (hQ : (polarBilin Q).Nondegenerate)
    (hX : (polarBilin (Q.comp X.subtype)).Nondegenerate)
    (hY : (polarBilin (Q.comp Y.subtype)).Nondegenerate)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, polar Q x y = 0)
    {ρ : V ≃ₗ[K] V} (hρ : ρ ∈ supportedDerived Q X)
    (hρfix : ∀ z ∈ X, ρ z = z → z = 0) :
    ∀ g ∈ Subgroup.centralizer (supportedDerived Q X : Set (V ≃ₗ[K] V)) ⊓
        supportedDerived Q (X ⊔ Y), ∀ y ∈ Y, g y ∈ Y := by
  have hMr : PolarNondegOn Q (X ⊔ Y) :=
    CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup
      (polarNondegOn_of_nondegenerate hX) (polarNondegOn_of_nondegenerate hY) hXY
  have hZnd : (polarBilin (Q.comp (suppPerp Q (X ⊔ Y)).subtype)).Nondegenerate := by
    apply CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn
    intro z hz hzp
    apply CFSG.ClassicalGroups.Orthogonal.eq_zero_of_polar_eq_zero hQ
    intro v
    obtain ⟨m, hm, z', hz', rfl⟩ :=
      suppExists_add_of_isCompl (isCompl_suppPerp hMr) v
    rw [polar_add_right, polar_comm, mem_suppPerp.mp hz m hm, hzp z' hz', add_zero]
  intro g hg y hy
  have hgyfix : ∀ s ∈ supportedDerived Q X, s (g y) = g y := by
    intro s hs
    obtain ⟨hgC, -⟩ := Subgroup.mem_inf.mp hg
    have hcomm : s * g = g * s := Subgroup.mem_centralizer_iff.mp hgC s hs
    have h1 : g (s y) = s (g y) :=
      (congrFun (congrArg (fun e : V ≃ₗ[K] V => (e : V → V)) hcomm) y).symm
    rw [← h1, supportedDerived_apply_perp hs (mem_suppPerp.mpr fun x hx => hXY x hx y hy)]
  obtain ⟨y', hy', z', hz', heq⟩ := Submodule.mem_sup.mp
    (fixedSpace_supportedDerived_eq hX hY hXY hρ hρfix (g y) hgyfix)
  have hz'0 : z' = 0 := by
    obtain ⟨-, hgM⟩ := Subgroup.mem_inf.mp hg
    have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      supportedDerived_le_orthogonalGroup hMr hgM
    have h := hZnd.1 ⟨z', hz'⟩ fun z => by
      rw [polarBilin_apply_apply, polar_comp_subtype_eq]
      have h3 : polar Q (g y) (z : V) = 0 := by
        have hzfix : g⁻¹ (z : V) = z := supportedDerived_apply_perp (inv_mem hgM) z.2
        have hpol := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO y (g⁻¹ (z : V))
        rw [show g (g⁻¹ (z : V)) = (z : V) from LinearEquiv.apply_symm_apply g (z : V),
          hzfix] at hpol
        rw [hpol]
        exact mem_suppPerp.mp z.2 y (Submodule.mem_sup_right hy)
      have h2 : polar Q y' (z : V) = 0 :=
        mem_suppPerp.mp z.2 y' (Submodule.mem_sup_right hy')
      have h5 : polar Q (y' + z') (z : V) = 0 := by rw [heq]; exact h3
      rwa [polar_add_left, h2, zero_add] at h5
    exact congrArg Subtype.val h
  rw [← heq, hz'0, add_zero]
  exact hy'

omit [Finite K] [CharP K 2] in
private theorem centralizer_mapsTo_left
    (hQ : (polarBilin Q).Nondegenerate)
    (hX : (polarBilin (Q.comp X.subtype)).Nondegenerate)
    (hY : (polarBilin (Q.comp Y.subtype)).Nondegenerate)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, polar Q x y = 0)
    {ρ : V ≃ₗ[K] V} (hρ : ρ ∈ supportedDerived Q X)
    (hρfix : ∀ z ∈ X, ρ z = z → z = 0) :
    ∀ g ∈ Subgroup.centralizer (supportedDerived Q X : Set (V ≃ₗ[K] V)) ⊓
        supportedDerived Q (X ⊔ Y), ∀ x ∈ X, g x ∈ X := by
  have hXr : PolarNondegOn Q X := polarNondegOn_of_nondegenerate hX
  have hYr : PolarNondegOn Q Y := polarNondegOn_of_nondegenerate hY
  have hMr : PolarNondegOn Q (X ⊔ Y) :=
    CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup hXr hYr hXY
  have hpresY := centralizer_mapsTo_sup hQ hX hY hXY hρ hρfix
  intro g hg x hx
  obtain ⟨-, hgM⟩ := Subgroup.mem_inf.mp hg
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    supportedDerived_le_orthogonalGroup hMr hgM
  obtain ⟨x', hx', y', hy', heq⟩ :=
    Submodule.mem_sup.mp (supportedDerived_apply_mem hgM (Submodule.mem_sup_left hx))
  have hy'0 : y' = 0 := by
    have h := hY.1 ⟨y', hy'⟩ fun y => by
      rw [polarBilin_apply_apply, polar_comp_subtype_eq]
      have hgoy : g⁻¹ (y : V) ∈ Y := hpresY g⁻¹ (inv_mem hg) (y : V) y.2
      have h1 : polar Q (g x) (y : V) = 0 := by
        have hpol :=
          TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO x (g⁻¹ (y : V))
        have hgy : g (g⁻¹ (y : V)) = (y : V) := LinearEquiv.apply_symm_apply g (y : V)
        rw [hgy] at hpol
        rw [hpol]
        exact hXY x hx (g⁻¹ (y : V)) hgoy
      have h2 : polar Q x' (y : V) = 0 := hXY x' hx' (y : V) y.2
      have h3 : polar Q (x' + y') (y : V) = 0 := by rw [heq]; exact h1
      rwa [polar_add_left, h2, zero_add] at h3
    exact congrArg Subtype.val h
  rw [← heq, hy'0, add_zero]
  exact hx'

omit [Finite K] [CharP K 2] in
private theorem commute_on_of_fixedFree
    (hX : (polarBilin (Q.comp X.subtype)).Nondegenerate)
    (hXdim : Module.finrank K X = 2)
    {ρ : V ≃ₗ[K] V} (hρ : ρ ∈ supportedDerived Q X)
    (hρfix : ∀ z ∈ X, ρ z = z → z = 0)
    (hρns : ∀ c : K, ∃ x : X, ρ (x : V) ≠ c • (x : V))
    {u v : V ≃ₗ[K] V}
    (hu : ∀ s ∈ supportedDerived Q X, Commute u s)
    (hv : ∀ s ∈ supportedDerived Q X, Commute v s) :
    ∀ x ∈ X, u (v x) = v (u x) := by
  have hupres : ∀ x ∈ X, u x ∈ X :=
    sub_one_mapsTo_of_fixedFree hX hρ hρfix (hu ρ hρ)
  have hvpres : ∀ x ∈ X, v x ∈ X :=
    sub_one_mapsTo_of_fixedFree hX hρ hρfix (hv ρ hρ)
  have hρpres : ∀ x ∈ X, ρ x ∈ X := fun x hx => supportedDerived_apply_mem hρ hx
  let uX : Module.End K X := (u : V →ₗ[K] V).restrict (p := X) (q := X) hupres
  let vX : Module.End K X := (v : V →ₗ[K] V).restrict (p := X) (q := X) hvpres
  let ρX : Module.End K X := (ρ : V →ₗ[K] V).restrict (p := X) (q := X) hρpres
  have hρXns : ∀ c : K, ρX ≠ c • (1 : Module.End K X) := by
    intro c h
    obtain ⟨x, hx⟩ := hρns c
    apply hx
    have h1 := congrArg (fun f : Module.End K X => f x) h
    have h2 : ρ (x : V) = c • (x : V) := by
      have := congrArg Subtype.val h1
      simpa [ρX] using this
    exact h2
  have hcommρu : Commute ρX uX := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ρ (u (x : V)) = u (ρ (x : V))
    exact congrArg (fun e : V ≃ₗ[K] V => e (x : V)) (hu ρ hρ).symm.eq
  have hcommρv : Commute ρX vX := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ρ (v (x : V)) = v (ρ (x : V))
    exact congrArg (fun e : V ≃ₗ[K] V => e (x : V)) (hv ρ hρ).symm.eq
  have hcommUV : Commute uX vX :=
    CFSG.ClassicalGroups.SpecialLinear.TvMod.commute_of_commute_of_finrank_eq_two
      hXdim hρXns hcommρu hcommρv
  intro x hx
  have h := congrArg (fun f : Module.End K X => f ⟨x, hx⟩) hcommUV.eq
  have h2 : (uX (vX ⟨x, hx⟩) : X) = vX (uX ⟨x, hx⟩) := by
    simpa only [Module.End.mul_apply] using h
  calc u (v x) = ((uX (vX ⟨x, hx⟩) : X) : V) := by
        simp [uX, vX, LinearMap.restrict_apply]
    _ = ((vX (uX ⟨x, hx⟩) : X) : V) := by rw [h2]
    _ = v (u x) := by simp [uX, vX, LinearMap.restrict_apply]

omit [Finite K] [FiniteDimensional K V] [CharP K 2] in
private theorem map_eq_of_mapsTo_of_inv_mapsTo {T : Submodule K V} {t : V ≃ₗ[K] V}
    (ht : ∀ x ∈ T, t x ∈ T) (hti : ∀ x ∈ T, t⁻¹ x ∈ T) :
    Submodule.map (t : V →ₗ[K] V) T = T := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact ht x hx
  · intro x hx
    exact ⟨t⁻¹ x, hti x hx, t.apply_symm_apply x⟩

omit [Finite K] [CharP K 2] in
private theorem commutator_fixes_suppPerp
    (hQ : (polarBilin Q).Nondegenerate)
    (hX : (polarBilin (Q.comp X.subtype)).Nondegenerate)
    (hY : (polarBilin (Q.comp Y.subtype)).Nondegenerate)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, polar Q x y = 0)
    (hXdim : Module.finrank K X = 2)
    {ρ : V ≃ₗ[K] V} (hρ : ρ ∈ supportedDerived Q X)
    (hρfix : ∀ z ∈ X, ρ z = z → z = 0)
    (hρns : ∀ c : K, ∃ x : X, ρ (x : V) ≠ c • (x : V))
    {g h : V ≃ₗ[K] V}
    (hg : g ∈ Subgroup.centralizer (supportedDerived Q X : Set (V ≃ₗ[K] V)) ⊓
        supportedDerived Q (X ⊔ Y))
    (hh : h ∈ Subgroup.centralizer (supportedDerived Q X : Set (V ≃ₗ[K] V)) ⊓
        supportedDerived Q (X ⊔ Y)) :
    ∀ v ∈ suppPerp Q Y, (⁅g, h⁆ : V ≃ₗ[K] V) v = v := by
  have hpresX := centralizer_mapsTo_left hQ hX hY hXY hρ hρfix
  obtain ⟨hgC, hgM⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨hhC, hhM⟩ := Subgroup.mem_inf.mp hh
  have hgcomm : ∀ s ∈ supportedDerived Q X, Commute g s := fun s hs =>
    (Subgroup.mem_centralizer_iff.mp hgC s hs).symm
  have hhcomm : ∀ s ∈ supportedDerived Q X, Commute h s := fun s hs =>
    (Subgroup.mem_centralizer_iff.mp hhC s hs).symm
  have hcomm : ∀ x ∈ X, g (h x) = h (g x) :=
    commute_on_of_fixedFree hX hXdim hρ hρfix hρns hgcomm hhcomm
  have hYeq : suppPerp Q Y = X ⊔ suppPerp Q (X ⊔ Y) := by
    rw [suppPerp_eq_sup_suppPerp_sup hY hX
      (fun y hy x hx => by rw [polar_comm]; exact hXY x hx y hy)]
    rw [sup_comm Y X]
  intro v hv
  rw [hYeq] at hv
  obtain ⟨x, hx, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  have hxfix : (⁅g, h⁆ : V ≃ₗ[K] V) x = x :=
    commutatorElement_apply_eq_self_of_commute_on (g := g) (h := h)
      (hpresX g⁻¹ (inv_mem hg)) (hpresX h⁻¹ (inv_mem hh)) hcomm hx
  have hzfix : (⁅g, h⁆ : V ≃ₗ[K] V) z = z := by
    rw [commutatorElement_def]
    simp only [LinearEquiv.mul_apply]
    rw [supportedDerived_apply_perp (inv_mem hhM) hz,
      supportedDerived_apply_perp (inv_mem hgM) hz,
      supportedDerived_apply_perp hhM hz, supportedDerived_apply_perp hgM hz]
  rw [map_add, hxfix, hzfix]

omit [Finite K] [FiniteDimensional K V] [CharP K 2] in
private theorem ofSubmodules_mem_orthogonalGroup {T : Submodule K V} {t : V ≃ₗ[K] V}
    (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hmap : Submodule.map (t : V →ₗ[K] V) T = T) :
    LinearEquiv.ofSubmodules t T T hmap ∈
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp T.subtype) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro y
  change Q ((LinearEquiv.ofSubmodules t T T hmap y : T) : V) = Q (y : V)
  rw [LinearEquiv.ofSubmodules_apply]
  exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup htO (y : V)

omit [Finite K] [CharP K 2] in
private theorem commutator_restricts
    (hQ : (polarBilin Q).Nondegenerate)
    (hX : (polarBilin (Q.comp X.subtype)).Nondegenerate)
    (hY : (polarBilin (Q.comp Y.subtype)).Nondegenerate)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, polar Q x y = 0)
    {ρ : V ≃ₗ[K] V} (hρ : ρ ∈ supportedDerived Q X)
    (hρfix : ∀ z ∈ X, ρ z = z → z = 0)
    {g h : V ≃ₗ[K] V}
    (hg : g ∈ Subgroup.centralizer (supportedDerived Q X : Set (V ≃ₗ[K] V)) ⊓
        supportedDerived Q (X ⊔ Y))
    (hh : h ∈ Subgroup.centralizer (supportedDerived Q X : Set (V ≃ₗ[K] V)) ⊓
        supportedDerived Q (X ⊔ Y)) :
    ∃ k ∈ orthDerived (Q.comp Y.subtype),
      ∀ y : Y, ((k y : Y) : V) = (⁅g, h⁆ : V ≃ₗ[K] V) (y : V) := by
  have hpresY := centralizer_mapsTo_sup hQ hX hY hXY hρ hρfix
  have hXr : PolarNondegOn Q X := polarNondegOn_of_nondegenerate hX
  have hYr : PolarNondegOn Q Y := polarNondegOn_of_nondegenerate hY
  have hMr : PolarNondegOn Q (X ⊔ Y) :=
    CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup hXr hYr hXY
  obtain ⟨-, hgM⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨-, hhM⟩ := Subgroup.mem_inf.mp hh
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    supportedDerived_le_orthogonalGroup hMr hgM
  have hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    supportedDerived_le_orthogonalGroup hMr hhM
  have hmapg : Submodule.map (g : V →ₗ[K] V) Y = Y :=
    map_eq_of_mapsTo_of_inv_mapsTo (hpresY g hg) (hpresY g⁻¹ (inv_mem hg))
  have hmaph : Submodule.map (h : V →ₗ[K] V) Y = Y :=
    map_eq_of_mapsTo_of_inv_mapsTo (hpresY h hh) (hpresY h⁻¹ (inv_mem hh))
  let gY : Y ≃ₗ[K] Y := LinearEquiv.ofSubmodules g Y Y hmapg
  let hY' : Y ≃ₗ[K] Y := LinearEquiv.ofSubmodules h Y Y hmaph
  have hgYO : gY ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp Y.subtype) :=
    ofSubmodules_mem_orthogonalGroup hgO hmapg
  have hhYO : hY' ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp Y.subtype) :=
    ofSubmodules_mem_orthogonalGroup hhO hmaph
  refine ⟨⁅gY, hY'⁆, Subgroup.commutator_mem_commutator hgYO hhYO, fun y => ?_⟩
  have hcoeG : ∀ u : Y, ((gY u : Y) : V) = g (u : V) := fun u =>
    LinearEquiv.ofSubmodules_apply g hmapg u
  have hcoeH : ∀ u : Y, ((hY' u : Y) : V) = h (u : V) := fun u =>
    LinearEquiv.ofSubmodules_apply h hmaph u
  have hcoeGinv : ∀ u : Y, ((gY⁻¹ u : Y) : V) = g⁻¹ (u : V) := fun u =>
    LinearEquiv.ofSubmodules_symm_apply (e := g) hmapg u
  have hcoeHinv : ∀ u : Y, ((hY'⁻¹ u : Y) : V) = h⁻¹ (u : V) := fun u =>
    LinearEquiv.ofSubmodules_symm_apply (e := h) hmaph u
  change ((⁅gY, hY'⁆ y : Y) : V) = (⁅g, h⁆ : V ≃ₗ[K] V) (y : V)
  rw [commutatorElement_def, commutatorElement_def]
  simp only [LinearEquiv.mul_apply, hcoeG, hcoeH, hcoeGinv, hcoeHinv]

omit [Finite K] [CharP K 2] in
private theorem commutator_mem_supportedDerived
    (hQ : (polarBilin Q).Nondegenerate)
    (hX : (polarBilin (Q.comp X.subtype)).Nondegenerate)
    (hY : (polarBilin (Q.comp Y.subtype)).Nondegenerate)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, polar Q x y = 0)
    (hXdim : Module.finrank K X = 2)
    {ρ : V ≃ₗ[K] V} (hρ : ρ ∈ supportedDerived Q X)
    (hρfix : ∀ z ∈ X, ρ z = z → z = 0)
    (hρns : ∀ c : K, ∃ x : X, ρ (x : V) ≠ c • (x : V))
    {g h : V ≃ₗ[K] V}
    (hg : g ∈ Subgroup.centralizer (supportedDerived Q X : Set (V ≃ₗ[K] V)) ⊓
        supportedDerived Q (X ⊔ Y))
    (hh : h ∈ Subgroup.centralizer (supportedDerived Q X : Set (V ≃ₗ[K] V)) ⊓
        supportedDerived Q (X ⊔ Y)) :
    ⁅g, h⁆ ∈ supportedDerived Q Y := by
  refine mem_supportedDerived.mpr ⟨?_, ?_⟩
  · exact commutator_fixes_suppPerp hQ hX hY hXY hXdim hρ hρfix hρns hg hh
  · exact commutator_restricts hQ hX hY hXY hρ hρfix hg hh

private theorem supportedDerived_le_commutator_centralizer
    (hX : (polarBilin (Q.comp X.subtype)).Nondegenerate)
    (hY : (polarBilin (Q.comp Y.subtype)).Nondegenerate)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, polar Q x y = 0)
    (hperf : Group.IsPerfect ↥(supportedDerived Q Y)) :
    supportedDerived Q Y ≤
      ⁅Subgroup.centralizer (supportedDerived Q X : Set (V ≃ₗ[K] V)) ⊓
          supportedDerived Q (X ⊔ Y),
        Subgroup.centralizer (supportedDerived Q X : Set (V ≃ₗ[K] V)) ⊓
          supportedDerived Q (X ⊔ Y)⁆ := by
  have hXr : PolarNondegOn Q X := polarNondegOn_of_nondegenerate hX
  have hYr : PolarNondegOn Q Y := polarNondegOn_of_nondegenerate hY
  have hMr : PolarNondegOn Q (X ⊔ Y) :=
    CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup hXr hYr hXY
  have hMnd : (polarBilin (Q.comp (X ⊔ Y).subtype)).Nondegenerate :=
    CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn hMr
  have hYleM : Y ≤ X ⊔ Y := fun _ hy => Submodule.mem_sup_right hy
  have hcent : ∀ y ∈ supportedDerived Q Y,
      y ∈ Subgroup.centralizer (supportedDerived Q X : Set (V ≃ₗ[K] V)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (supportedDerived_commute_of_orthogonal_supports hX hY hXY hs hy).eq
  have hMY : ∀ y ∈ supportedDerived Q Y,
      y ∈ Subgroup.centralizer (supportedDerived Q X : Set (V ≃ₗ[K] V)) ⊓
        supportedDerived Q (X ⊔ Y) := fun y hy =>
    Subgroup.mem_inf.mpr ⟨hcent y hy,
      supportedDerived_le_supportedDerived_of_le hYleM hY hMnd hy⟩
  calc supportedDerived Q Y = ⁅supportedDerived Q Y, supportedDerived Q Y⁆ :=
        (Subgroup.isPerfect_iff.mp hperf).symm
    _ ≤ ⁅Subgroup.centralizer (supportedDerived Q X : Set (V ≃ₗ[K] V)) ⊓
          supportedDerived Q (X ⊔ Y),
        Subgroup.centralizer (supportedDerived Q X : Set (V ≃ₗ[K] V)) ⊓
          supportedDerived Q (X ⊔ Y)⁆ :=
        Subgroup.commutator_mono (fun y hy => hMY y hy) (fun y hy => hMY y hy)

theorem commutator_centralizer_supportedDerived_eq
    (hQ : (polarBilin Q).Nondegenerate)
    (hX : (polarBilin (Q.comp X.subtype)).Nondegenerate)
    (hY : (polarBilin (Q.comp Y.subtype)).Nondegenerate)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, polar Q x y = 0)
    (hXdim : Module.finrank K X = 2)
    {ρ : V ≃ₗ[K] V} (hρ : ρ ∈ supportedDerived Q X)
    (hρfix : ∀ z ∈ X, ρ z = z → z = 0)
    (hρns : ∀ c : K, ∃ x : X, ρ (x : V) ≠ c • (x : V))
    (hperf : Group.IsPerfect ↥(supportedDerived Q Y)) :
    ⁅(Subgroup.centralizer (supportedDerived Q X : Set (V ≃ₗ[K] V)) ⊓
        supportedDerived Q (X ⊔ Y)),
      (Subgroup.centralizer (supportedDerived Q X : Set (V ≃ₗ[K] V)) ⊓
        supportedDerived Q (X ⊔ Y))⁆ = supportedDerived Q Y := by
  refine le_antisymm ?_ ?_
  · refine Subgroup.commutator_le.mpr ?_
    intro g hg h hh
    exact commutator_mem_supportedDerived hQ hX hY hXY hXdim hρ hρfix hρns hg hh
  · exact supportedDerived_le_commutator_centralizer hX hY hXY hperf

end General




section Reduction

variable {V : Type*} [AddCommGroup V] [Module K V]

omit [Finite K] [CharP K 2] in
private theorem centralizer_subgroupOf_eq (A G : Subgroup (V ≃ₗ[K] V)) (hAG : A ≤ G) :
    Subgroup.centralizer ((A.subgroupOf G : Subgroup G) : Set G) =
      (Subgroup.centralizer (A : Set (V ≃ₗ[K] V))).subgroupOf G := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro a ha
    have h := hx ⟨a, hAG ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
    exact Subtype.ext_iff.mp h
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro a ha
    exact Subtype.ext (hx a (Subgroup.mem_subgroupOf.mp ha))

omit [Finite K] [CharP K 2] in
private theorem commutator_centralizer_subgroupOf_eq {G A B P : Subgroup (V ≃ₗ[K] V)}
    (hAG : A ≤ G) (hBG : B ≤ G) (hPG : P ≤ G)
    (hmain : ⁅Subgroup.centralizer (A : Set (V ≃ₗ[K] V)) ⊓ B,
      Subgroup.centralizer (A : Set (V ≃ₗ[K] V)) ⊓ B⁆ = P) :
    ⁅Subgroup.centralizer ((A.subgroupOf G : Subgroup G) : Set G) ⊓ B.subgroupOf G,
      Subgroup.centralizer ((A.subgroupOf G : Subgroup G) : Set G) ⊓ B.subgroupOf G⁆ =
      P.subgroupOf G := by
  apply Subgroup.map_injective (f := G.subtype) G.subtype_injective
  rw [Subgroup.map_commutator]
  have h1 : (Subgroup.centralizer ((A.subgroupOf G : Subgroup G) : Set G) ⊓
      B.subgroupOf G).map G.subtype =
      Subgroup.centralizer (A : Set (V ≃ₗ[K] V)) ⊓ B := by
    rw [centralizer_subgroupOf_eq A G hAG]
    change Subgroup.map G.subtype
      (Subgroup.comap G.subtype (Subgroup.centralizer (A : Set (V ≃ₗ[K] V))) ⊓
        Subgroup.comap G.subtype B) = Subgroup.centralizer (A : Set (V ≃ₗ[K] V)) ⊓ B
    rw [← Subgroup.comap_inf]
    change Subgroup.map G.subtype
      (((Subgroup.centralizer (A : Set (V ≃ₗ[K] V))) ⊓ B).subgroupOf G) =
      Subgroup.centralizer (A : Set (V ≃ₗ[K] V)) ⊓ B
    exact Subgroup.map_subgroupOf_eq_of_le (le_trans inf_le_right hBG)
  rw [h1, hmain, Subgroup.map_subgroupOf_eq_of_le hPG]

end Reduction

section Transport

variable {P : Type} [AddCommGroup P] [Module K P] {QP : QuadraticForm K P}

omit [Finite K] [CharP K 2] in
private theorem exists_supportedDerived_conj
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {X : Submodule K V}
    (hX : (polarBilin (Q.comp X.subtype)).Nondegenerate)
    (e : QP.IsometryEquiv (Q.comp X.subtype))
    {d : P ≃ₗ[K] P} (hd : d ∈ orthDerived QP) :
    ∃ ρ : V ≃ₗ[K] V, ρ ∈ supportedDerived Q X ∧
      ∀ p : P, ρ ((e p : X) : V) = ((e (d p) : X) : V) := by
  classical
  have hdX : CFSG.RankThree.PartOne.linConj e.toLinearEquiv d ∈
      orthDerived (Q.comp X.subtype) := by
    rw [← CFSG.RankThree.PartOne.map_orthDerived_linConj e]
    exact Subgroup.mem_map_of_mem _ hd
  let g : orthDerived (Q.comp X.subtype) := ⟨_, hdX⟩
  let ρg : supportedDerived Q X := orthDerivedSupportedEquiv hX g
  have hρval : ((ρg : supportedDerived Q X) : V ≃ₗ[K] V) =
      orthExtend (isCompl_suppPerp (polarNondegOn_of_nondegenerate hX))
        (CFSG.RankThree.PartOne.linConj e.toLinearEquiv d) :=
    orthDerivedSupportedEquiv_apply hX g
  refine ⟨(ρg : supportedDerived Q X), ρg.2, fun p => ?_⟩
  rw [hρval]
  rw [show ((e p : X) : V) = ((e p : X) : V) + (0 : suppPerp Q X) from
    (add_zero _).symm, orthExtend_apply]
  rw [CFSG.RankThree.PartOne.linConj_apply]
  simp

omit [Finite K] [CharP K 2] in
private theorem exists_supportedDerived_fixedFree_nonscalar
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {X : Submodule K V}
    (hX : (polarBilin (Q.comp X.subtype)).Nondegenerate)
    (e : QP.IsometryEquiv (Q.comp X.subtype))
    {d : P ≃ₗ[K] P} (hd : d ∈ orthDerived QP)
    (hdfix : ∀ p : P, d p = p → p = 0)
    (hdns : ∀ c : K, ∃ p : P, d p ≠ c • p) :
    ∃ ρ : V ≃ₗ[K] V, ρ ∈ supportedDerived Q X ∧
      (∀ z ∈ X, ρ z = z → z = 0) ∧
      (∀ c : K, ∃ x : X, ρ (x : V) ≠ c • (x : V)) := by
  obtain ⟨ρ, hρ, hact⟩ := exists_supportedDerived_conj hX e hd
  refine ⟨ρ, hρ, ?_, ?_⟩
  · intro z hz hzfix
    obtain ⟨p, hp⟩ := e.surjective ⟨z, hz⟩
    have hz' : z = ((e p : X) : V) := congrArg Subtype.val hp.symm
    rw [hz'] at hzfix ⊢
    have hdp : d p = p := by
      apply e.injective
      have h1 : ((e (d p) : X) : V) = ((e p : X) : V) := (hact p).symm.trans hzfix
      exact Subtype.ext h1
    have hp0 : p = 0 := hdfix p hdp
    rw [hp0, map_zero]
    rfl
  · intro c
    obtain ⟨p, hp⟩ := hdns c
    refine ⟨⟨e p, (e p).2⟩, ?_⟩
    intro h
    apply hp
    have h1 : ((e (d p) : X) : V) = c • ((e p : X) : V) := by
      calc ((e (d p) : X) : V) = ρ ((e p : X) : V) := (hact p).symm
        _ = c • ((e p : X) : V) := h
    have h2 : e (d p) = c • e p := Subtype.ext h1
    have h3 : d p = c • p := by
      have := congrArg e.symm h2
      simpa using this
    exact h3

end Transport


section Anchor

private noncomputable def hpSwap : (F × F) ≃ₗ[F] (F × F) where
  toFun p := (p.2, p.1)
  invFun p := (p.2, p.1)
  map_add' _ _ := Prod.ext rfl rfl
  map_smul' _ _ := Prod.ext rfl rfl
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def hpDiag (mu : Fˣ) : (F × F) ≃ₗ[F] (F × F) where
  toFun p := ((mu : F) * p.1, ((mu : F)⁻¹) * p.2)
  invFun p := (((mu : F)⁻¹) * p.1, (mu : F) * p.2)
  map_add' p q := by
    refine Prod.ext ?_ ?_ <;> simp [mul_add]
  map_smul' c p := by
    refine Prod.ext ?_ ?_
    · show (mu : F) * (c * p.1) = c * ((mu : F) * p.1)
      ring
    · show ((mu : F)⁻¹) * (c * p.2) = c * (((mu : F)⁻¹) * p.2)
      ring
  left_inv p := by
    refine Prod.ext ?_ ?_
    · show ((mu : F)⁻¹) * ((mu : F) * p.1) = p.1
      rw [← mul_assoc, inv_mul_cancel₀ mu.ne_zero, one_mul]
    · show (mu : F) * (((mu : F)⁻¹) * p.2) = p.2
      rw [← mul_assoc, mul_inv_cancel₀ mu.ne_zero, one_mul]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · show (mu : F) * (((mu : F)⁻¹) * p.1) = p.1
      rw [← mul_assoc, mul_inv_cancel₀ mu.ne_zero, one_mul]
    · show ((mu : F)⁻¹) * ((mu : F) * p.2) = p.2
      rw [← mul_assoc, inv_mul_cancel₀ mu.ne_zero, one_mul]

private theorem hpSwap_isometry (p : F × F) : hypPlane F (hpSwap p) = hypPlane F p := by
  simp [hpSwap, hypPlane_apply, mul_comm]

private theorem hpDiag_isometry (mu : Fˣ) (p : F × F) :
    hypPlane F (hpDiag mu p) = hypPlane F p := by
  simp only [hpDiag, hypPlane_apply]
  calc ((mu : F) * p.1) * (((mu : F)⁻¹) * p.2)
      = ((mu : F) * ((mu : F)⁻¹)) * (p.1 * p.2) := by rw [mul_mul_mul_comm]
    _ = p.1 * p.2 := by rw [mul_inv_cancel₀ mu.ne_zero, one_mul]

private theorem hpDiag_inv (mu : Fˣ) : (hpDiag mu)⁻¹ = hpDiag mu⁻¹ := by
  apply LinearEquiv.ext
  intro p
  show (hpDiag mu).symm p = hpDiag mu⁻¹ p
  apply (hpDiag mu).injective
  rw [LinearEquiv.apply_symm_apply]
  refine Prod.ext ?_ ?_ <;> simp [hpDiag]

private noncomputable def hpRho (mu : Fˣ) : (F × F) ≃ₗ[F] (F × F) :=
  hpSwap * hpDiag mu * hpSwap⁻¹ * (hpDiag mu)⁻¹

private theorem hpRho_eq_commutator (mu : Fˣ) :
    hpRho mu = ⁅(hpSwap : (F × F) ≃ₗ[F] (F × F)),
      (hpDiag mu : (F × F) ≃ₗ[F] (F × F))⁆ := by
  rw [commutatorElement_def]
  rfl

private theorem hpRho_mem (mu : Fˣ) : hpRho mu ∈ orthDerived (hypPlane F) := by
  have h : ⁅(hpSwap : (F × F) ≃ₗ[F] (F × F)),
      (hpDiag mu : (F × F) ≃ₗ[F] (F × F))⁆ ∈ orthDerived (hypPlane F) :=
    Subgroup.commutator_mem_commutator
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hpSwap_isometry)
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hpDiag_isometry mu))
  rwa [hpRho_eq_commutator]

private theorem hpRho_apply (mu : Fˣ) (p : F × F) :
    hpRho mu p = (((mu : F)⁻¹ * (mu : F)⁻¹) * p.1, ((mu : F) * (mu : F)) * p.2) := by
  have hA : ∀ q : F × F, hpSwap q = (q.2, q.1) := fun q => rfl
  have hB : ∀ q : F × F, hpDiag mu q =
      ((mu : F) * q.1, ((mu : F)⁻¹) * q.2) := fun q => rfl
  have hAi : ∀ q : F × F, hpSwap⁻¹ q = (q.2, q.1) := fun q => rfl
  have hBinv : ∀ q : F × F, hpDiag mu⁻¹ q =
      (((mu : F)⁻¹) * q.1, (((mu : F)⁻¹)⁻¹) * q.2) := fun q => by simp [hpDiag]
  rw [hpRho]
  simp only [LinearEquiv.mul_apply, hA, hB, hAi]
  rw [hpDiag_inv, hBinv, inv_inv]
  refine Prod.ext ?_ ?_ <;> simp [mul_assoc]

private theorem hpRho_fixedFree (mu : Fˣ) (hmu : (mu : F) ≠ 1) [CharP F 2] :
    ∀ p : F × F, hpRho mu p = p → p = 0 := by
  intro p hp
  have hlam : ((mu : F)⁻¹ * (mu : F)⁻¹) ≠ 1 := by
    intro h
    apply hmu
    have h2 : ((mu : F)⁻¹) ^ 2 = 1 := by simpa [pow_two] using h
    have h3 : (mu : F)⁻¹ = 1 := CharTwo.sq_inj.mp (by simpa using h2)
    have h4 : mu⁻¹ = 1 := by
      apply Units.ext
      simpa using h3
    have h5 : mu = 1 := inv_eq_one.mp h4
    simpa using congrArg (fun u : Fˣ => (u : F)) h5
  have hmu2 : ((mu : F) * (mu : F)) ≠ 1 := by
    intro h
    apply hmu
    have h2 : (mu : F) ^ 2 = 1 := by simpa [pow_two] using h
    exact CharTwo.sq_inj.mp (by simpa using h2)
  have hp1 : p.1 = 0 := by
    by_contra h
    apply hlam
    refine mul_right_cancel₀ h ?_
    have hh := congrArg Prod.fst hp
    rw [hpRho_apply] at hh
    simpa using hh
  have hp2 : p.2 = 0 := by
    by_contra h
    apply hmu2
    refine mul_right_cancel₀ h ?_
    have hh := congrArg Prod.snd hp
    rw [hpRho_apply] at hh
    simpa using hh
  refine Prod.ext hp1 hp2

private theorem hpRho_mem_orthogonal (mu : Fˣ) :
    hpRho mu ∈ TauCeti.QuadraticMap.orthogonalGroup (hypPlane F) := by
  have hS : hpSwap ∈ TauCeti.QuadraticMap.orthogonalGroup (hypPlane F) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hpSwap_isometry
  have hD : hpDiag mu ∈ TauCeti.QuadraticMap.orthogonalGroup (hypPlane F) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hpDiag_isometry mu)
  rw [hpRho]
  exact mul_mem (mul_mem (mul_mem hS hD) (inv_mem hS)) (inv_mem hD)

private theorem hpRho_nonscalar (mu : Fˣ) (hmu : (mu : F) ≠ 1) [CharP F 2] :
    ∀ c : F, ∃ p : F × F, hpRho mu p ≠ c • p := by
  intro c
  by_contra h
  push Not at h
  have hq1 : hypPlane F ((1, 1) : F × F) = 1 := by simp [hypPlane_apply]
  have h1 := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
    (hpRho_mem_orthogonal mu) ((1, 1) : F × F)
  rw [h ((1, 1) : F × F)] at h1
  have hcc : c * c = 1 := by
    simpa [hypPlane_apply, hq1, mul_assoc] using h1
  have hc : c = 1 := CharTwo.sq_inj.mp (by simpa [pow_two] using hcc)
  have hp0 : hpRho mu (1, 0) = (1, 0) := by
    rw [h (1, 0), hc]
    simp
  have hz := hpRho_fixedFree mu hmu (1, 0) hp0
  simp at hz

private noncomputable def anchorIso (n : ℕ) :
    (hypPlane F).IsometryEquiv
      ((normHypForm E n).comp
        (coordAnchor (LinearEquiv.refl F ((F × F) × (Fin n → K)))).subtype) where
  toLinearEquiv :=
    { toFun p := ⟨((p.1, p.2), (0 : Fin n → K)),
        mem_coordAnchor.mpr ⟨p, rfl⟩⟩
      invFun v := (v : (F × F) × (Fin n → K)).1
      map_add' p q := by
        apply Subtype.ext
        refine Prod.ext ?_ (funext fun t => ?_)
        · refine Prod.ext ?_ ?_ <;> simp
        · simp
      map_smul' c p := by
        apply Subtype.ext
        refine Prod.ext ?_ (funext fun t => ?_)
        · refine Prod.ext ?_ ?_ <;> simp
        · simp
      left_inv p := rfl
      right_inv v := by
        obtain ⟨r, hr⟩ := mem_coordAnchor.mp v.2
        have hr1 : r = (v : (F × F) × (Fin n → K)).1 := congrArg Prod.fst hr
        apply Subtype.ext
        calc (((v : (F × F) × (Fin n → K)).1, 0) :
              (F × F) × (Fin n → K)) = ((r, 0) : (F × F) × (Fin n → K)) := by rw [hr1]
          _ = v := hr }
  map_app' p := by
    change (normHypForm E n) (((p.1, p.2), (0 : Fin n → K)) :
      (F × F) × (Fin n → K)) = hypPlane F p
    rw [normHypForm_apply_coord]
    simp [hypPlane_apply]

private theorem nondegenerate_coordAnchor (E : QuadExt F K (unitaryInvolution K 2 f)) (n : ℕ) :
    (polarBilin ((normHypForm E n).comp
      (coordAnchor (LinearEquiv.refl F ((F × F) × (Fin n → K)))).subtype)).Nondegenerate := by
  classical
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  exact coordAnchor_nondegenerate (LinearEquiv.refl F ((F × F) × (Fin n → K)))
    (normHypForm_apply_coord E n) (normHypForm_polarBilin_nondegenerate E n)
    (normQuad_polarBilin_nondegenerate E)

private theorem orthogonal_coordAnchor_coordPlane
    (E : QuadExt F K (unitaryInvolution K 2 f)) (n : ℕ) {i : Fin n} :
    ∀ x ∈ coordAnchor (LinearEquiv.refl F ((F × F) × (Fin n → K))),
      ∀ y ∈ coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) i,
        polar (normHypForm E n) x y = 0 := by
  intro x hx y hy
  exact polar_coordAnchor_plane (LinearEquiv.refl F ((F × F) × (Fin n → K)))
    (normHypForm_apply_coord E n) hx hy

private theorem finrank_coordAnchor (E : QuadExt F K (unitaryInvolution K 2 f)) (n : ℕ) :
    Module.finrank F ↥(coordAnchor (LinearEquiv.refl F ((F × F) × (Fin n → K)))) = 2 := by
  have h := LinearEquiv.finrank_eq (anchorIso E n).toLinearEquiv
  rw [← h]
  simp [Module.finrank_prod]

private theorem exists_anchor_fixedFree_nonscalar
    (E : QuadExt F K (unitaryInvolution K 2 f)) [Finite F] [CharP F 2] {n : ℕ}
    (hq : 4 ≤ Nat.card F) :
    ∃ ρ : ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K)),
      ρ ∈ supportedDerived (normHypForm E n)
        (coordAnchor (LinearEquiv.refl F ((F × F) × (Fin n → K)))) ∧
      (∀ z ∈ coordAnchor (LinearEquiv.refl F ((F × F) × (Fin n → K))),
        ρ z = z → z = 0) ∧
      (∀ c : F, ∃ x : ↥(coordAnchor (LinearEquiv.refl F ((F × F) × (Fin n → K)))),
        ρ (x : (F × F) × (Fin n → K)) ≠ c • (x : (F × F) × (Fin n → K))) := by
  classical
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  obtain ⟨mu, hmu⟩ : ∃ mu : Fˣ, (mu : F) ≠ 1 := by
    have hunits : 1 < Nat.card Fˣ := by
      rw [Nat.card_units]
      omega
    haveI : Fintype Fˣ := Fintype.ofFinite Fˣ
    have hunits' : 1 < Fintype.card Fˣ := by
      rw [← Nat.card_eq_fintype_card]
      exact hunits
    obtain ⟨mu, hmu⟩ := Fintype.exists_ne_of_one_lt_card hunits' (1 : Fˣ)
    exact ⟨mu, fun h => hmu (Units.ext h)⟩
  exact exists_supportedDerived_fixedFree_nonscalar (nondegenerate_coordAnchor E n) (anchorIso E n)
    (hpRho_mem mu) (hpRho_fixedFree mu hmu) (hpRho_nonscalar mu hmu)


end Anchor


theorem commutator_centralizer_normBlock_empty_inf_pair (hq : 4 ≤ Nat.card F) {n : ℕ}
    {i j : Fin n} (hij : i ≠ j) :
    ⁅Subgroup.centralizer (normBlock E n ∅ : Set (normOmega E n)) ⊓ normBlock E n {i, j},
      Subgroup.centralizer (normBlock E n ∅ : Set (normOmega E n)) ⊓ normBlock E n {i, j}⁆ =
      normPureBlock E n {i, j} := by
  classical
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  let V := (F × F) × (Fin n → K)
  let Q : QuadraticForm F V := normHypForm E n
  let W : Submodule F V := coordAnchor (LinearEquiv.refl F V)
  let U : Fin n → Submodule F V := fun t => coordPlane (LinearEquiv.refl F V) t
  let S : Finset (Fin n) := {i, j}
  let Y : Submodule F V := S.sup U
  have hYeq : Y = U i ⊔ U j := by simp [Y, S]
  have hQ : (polarBilin Q).Nondegenerate := normHypForm_polarBilin_nondegenerate E n
  have hWnd : (polarBilin (Q.comp W.subtype)).Nondegenerate := nondegenerate_coordAnchor E n
  have hYnd : (polarBilin (Q.comp Y.subtype)).Nondegenerate := by
    rw [hYeq]
    exact nondegenerate_coordPlane_sup_pair E i j
  have hWY : ∀ x ∈ W, ∀ y ∈ Y, polar Q x y = 0 := by
    intro x hx y hy
    have hy' : y ∈ coordPlane (LinearEquiv.refl F V) i ⊔
        coordPlane (LinearEquiv.refl F V) j := by simpa [Y, S, U] using hy
    obtain ⟨yi, hyi, yj, hyj, rfl⟩ := Submodule.mem_sup.mp hy'
    rw [polar_add_right, orthogonal_coordAnchor_coordPlane E n x hx yi hyi,
      orthogonal_coordAnchor_coordPlane E n x hx yj hyj, add_zero]
  have hWdim : Module.finrank F W = 2 := finrank_coordAnchor E n
  obtain ⟨ρ, hρ, hρfix, hρns⟩ := exists_anchor_fixedFree_nonscalar E hq
  have hperf : Group.IsPerfect ↥(supportedDerived Q Y) := by
    rw [hYeq]
    exact isPerfect_supportedDerived_pair E hij hq
  have hmain := commutator_centralizer_supportedDerived_eq (Q := Q) hQ hWnd hYnd hWY
    hWdim hρ hρfix hρns hperf
  let G : Subgroup (V ≃ₗ[F] V) := normOmega E n
  have hA : supportedDerived Q W ≤ G := supportedDerived_le_orthDerived_of_regular hWnd
  have hB : supportedDerived Q (W ⊔ Y) ≤ G := by
    have hblock : W ⊔ Y = coordSupport (LinearEquiv.refl F V) S := rfl
    rw [hblock]
    exact supportedDerived_coordSupport_le_omega E n S
  have hP : supportedDerived Q Y ≤ G := supportedDerived_le_orthDerived_of_regular hYnd
  have htarget := commutator_centralizer_subgroupOf_eq (G := G) hA hB hP hmain
  have hAblock : normBlock E n ∅ = (supportedDerived Q W).subgroupOf G := by
    simp only [normBlock, G, Q, W, coordSupport_empty]
    rfl
  have hBblock : normBlock E n {i, j} = (supportedDerived Q (W ⊔ Y)).subgroupOf G := rfl
  have hPblock : normPureBlock E n {i, j} = (supportedDerived Q Y).subgroupOf G := rfl
  rw [hAblock, hBblock, hPblock]
  exact htarget


section PureModel

private noncomputable def frobK (E : QuadExt F K (unitaryInvolution K 2 f)) :
    K ≃ₗ[F] K where
  toFun := unitaryInvolution K 2 f
  invFun := unitaryInvolution K 2 f
  map_add' := map_add (unitaryInvolution K 2 f)
  map_smul' c z := by
    simp only [Algebra.smul_def, map_mul, E.fix, RingHom.id_apply]
  left_inv z := E.isUnitary.invol z
  right_inv z := E.isUnitary.invol z

private theorem frobK_isometry (E : QuadExt F K (unitaryInvolution K 2 f)) (z : K) :
    normQuad E (frobK E z) = normQuad E z := by
  apply (algebraMap F K).injective
  rw [algebraMap_normQuad, algebraMap_normQuad]
  show unitaryInvolution K 2 f z *
      unitaryInvolution K 2 f (unitaryInvolution K 2 f z) =
    z * unitaryInvolution K 2 f z
  rw [E.isUnitary.invol, mul_comm]

private noncomputable def rotHom (u : Kˣ) : K ≃ₗ[F] K where
  toFun z := (u : K) * z
  invFun z := (u : K)⁻¹ * z
  map_add' x y := by ring
  map_smul' c x := by
    simp only [Algebra.smul_def, RingHom.id_apply]
    ring
  left_inv x := by
    show (u : K)⁻¹ * ((u : K) * x) = x
    rw [← mul_assoc, inv_mul_cancel₀ u.ne_zero, one_mul]
  right_inv x := by
    show (u : K) * ((u : K)⁻¹ * x) = x
    rw [← mul_assoc, mul_inv_cancel₀ u.ne_zero, one_mul]

omit [Finite K] [CharP K 2] in
private theorem rotHom_inv (u : Kˣ) :
    (rotHom (F := F) u)⁻¹ = rotHom (F := F) u⁻¹ := by
  apply LinearEquiv.ext
  intro z
  change (u : K)⁻¹ * z = ((u⁻¹ : Kˣ) : K) * z
  rw [Units.val_inv_eq_inv_val]

private theorem rotHom_isometry (u : Kˣ)
    (hu : (u : K) * unitaryInvolution K 2 f (u : K) = 1) (z : K) :
    normQuad E (rotHom (F := F) u z) = normQuad E z := by
  apply (algebraMap F K).injective
  rw [algebraMap_normQuad, algebraMap_normQuad]
  show ((u : K) * z) * unitaryInvolution K 2 f ((u : K) * z) =
    z * unitaryInvolution K 2 f z
  rw [map_mul]
  calc (u : K) * z * (unitaryInvolution K 2 f (u : K) * unitaryInvolution K 2 f z)
      = ((u : K) * unitaryInvolution K 2 f (u : K)) *
          (z * unitaryInvolution K 2 f z) := by ring
    _ = z * unitaryInvolution K 2 f z := by rw [hu, one_mul]

private noncomputable def planeRho (E : QuadExt F K (unitaryInvolution K 2 f))
    (u : Kˣ) : K ≃ₗ[F] K :=
  frobK E * rotHom u * (frobK E)⁻¹ * (rotHom u)⁻¹

private theorem planeRho_eq_commutator (E : QuadExt F K (unitaryInvolution K 2 f))
    (u : Kˣ) : planeRho E u = ⁅(frobK E : K ≃ₗ[F] K), (rotHom u : K ≃ₗ[F] K)⁆ := by
  rw [commutatorElement_def]
  rfl

private theorem planeRho_mem_O (E : QuadExt F K (unitaryInvolution K 2 f)) (u : Kˣ)
    (hu : (u : K) * unitaryInvolution K 2 f (u : K) = 1) :
    planeRho E u ∈ TauCeti.QuadraticMap.orthogonalGroup (normQuad E) := by
  have hF : frobK E ∈ TauCeti.QuadraticMap.orthogonalGroup (normQuad E) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (frobK_isometry E)
  have hR : rotHom u ∈ TauCeti.QuadraticMap.orthogonalGroup (normQuad E) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (rotHom_isometry E u hu)
  rw [planeRho]
  exact mul_mem (mul_mem (mul_mem hF hR) (inv_mem hF)) (inv_mem hR)

private theorem planeRho_mem (E : QuadExt F K (unitaryInvolution K 2 f)) (u : Kˣ)
    (hu : (u : K) * unitaryInvolution K 2 f (u : K) = 1) :
    planeRho E u ∈ orthDerived (normQuad E) := by
  have h : ⁅(frobK E : K ≃ₗ[F] K), (rotHom u : K ≃ₗ[F] K)⁆ ∈
      orthDerived (normQuad E) :=
    Subgroup.commutator_mem_commutator
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (frobK_isometry E))
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (rotHom_isometry E u hu))
  rwa [planeRho_eq_commutator]

private theorem planeRho_apply (E : QuadExt F K (unitaryInvolution K 2 f)) (u : Kˣ)
    (z : K) :
    planeRho E u z = (unitaryInvolution K 2 f (u : K) * ((u : K)⁻¹)) * z := by
  have hF : ∀ w : K, frobK E w = unitaryInvolution K 2 f w := fun w => rfl
  have hFinv_eq : (frobK E)⁻¹ = frobK E := by
    apply LinearEquiv.ext
    intro w
    change (frobK E).symm w = frobK E w
    apply (frobK E).injective
    rw [LinearEquiv.apply_symm_apply]
    show w = unitaryInvolution K 2 f (unitaryInvolution K 2 f w)
    rw [E.isUnitary.invol]
  have hFi : ∀ w : K, (frobK E)⁻¹ w = unitaryInvolution K 2 f w := by
    intro w
    rw [hFinv_eq]
    rfl
  have hR : ∀ v : Kˣ, ∀ w : K, rotHom (F := F) v w = (v : K) * w := fun v w => rfl
  have hRi : ∀ v : Kˣ, ∀ w : K, (rotHom (F := F) v)⁻¹ w = (v : K)⁻¹ * w := by
    intro v w
    rw [rotHom_inv (F := F)]
    change ((v⁻¹ : Kˣ) : K) * w = (v : K)⁻¹ * w
    rw [Units.val_inv_eq_inv_val]
  rw [planeRho]
  simp only [LinearEquiv.mul_apply, hF, hFinv_eq, hR, hRi, map_mul, map_inv₀,
    E.isUnitary.invol]
  ring

private theorem exists_unitary_moved_element (E : QuadExt F K (unitaryInvolution K 2 f)) :
    ∃ α : K, unitaryInvolution K 2 f α ≠ α := by
  let φ : F →ₗ[F] K := Algebra.linearMap F K
  have hfr : Module.finrank F (LinearMap.range φ) = 1 := by
    rw [LinearMap.finrank_range_of_inj (f := φ) (by
      intro x y hxy
      exact (algebraMap F K).injective (by simpa [φ] using hxy))]
    exact Module.finrank_self F
  have hnot : LinearMap.range φ ≠ ⊤ := by
    intro h
    have h2 : Module.finrank F (⊤ : Submodule F K) = 2 := by
      rw [finrank_top, E.finrank_eq]
    rw [h] at hfr
    omega
  have hdim : Module.finrank F K = 2 := E.finrank_eq
  obtain ⟨α, hα⟩ := Submodule.exists_of_finrank_lt (LinearMap.range φ) (by omega)
  refine ⟨α, ?_⟩
  intro hfix
  obtain ⟨a, ha⟩ := E.exists_of_fix α hfix
  have hmem : α ∈ LinearMap.range φ := LinearMap.mem_range.mpr ⟨a, by simpa [φ] using ha⟩
  have hnotmem : α ∉ LinearMap.range φ := by simpa using hα 1 one_ne_zero
  exact hnotmem hmem

private theorem exists_pure_rotation (E : QuadExt F K (unitaryInvolution K 2 f)) [CharP F 2]
    {α : K} (hα : unitaryInvolution K 2 f α ≠ α) :
    ∃ nu : Kˣ, (nu : K) * unitaryInvolution K 2 f (nu : K) = 1 ∧
      unitaryInvolution K 2 f (nu : K) * ((nu : K)⁻¹) ≠ 1 := by
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact hα (by simp)
  have hσα0 : unitaryInvolution K 2 f α ≠ 0 := by
    intro h
    exact hα0 ((unitaryInvolution K 2 f).injective (by simpa using h))
  let nu : Kˣ := Units.mk0 (unitaryInvolution K 2 f α / α) (div_ne_zero hσα0 hα0)
  have hnu_val : (nu : K) = unitaryInvolution K 2 f α / α := rfl
  have hnu : (nu : K) * unitaryInvolution K 2 f (nu : K) = 1 := by
    have hσnu : unitaryInvolution K 2 f (nu : K) = ((nu : K))⁻¹ := by
      rw [hnu_val, map_div₀, E.isUnitary.invol]
      field_simp
    rw [hσnu, mul_inv_cancel₀ nu.ne_zero]
  have hc : unitaryInvolution K 2 f (nu : K) * ((nu : K)⁻¹) ≠ 1 := by
    intro h
    have hfix : unitaryInvolution K 2 f (nu : K) = (nu : K) := by
      have h' := congrArg (fun x : K => x * (nu : K)) h
      simpa [mul_assoc, mul_inv_cancel₀ nu.ne_zero] using h'
    obtain ⟨a, ha⟩ := E.exists_of_fix (nu : K) hfix
    have hnu_eq : (nu : K) = algebraMap F K a := ha.symm
    rw [hnu_val, div_eq_iff hα0] at hnu_eq
    have h1 : unitaryInvolution K 2 f α = algebraMap F K a * α := hnu_eq
    have h2 : α = (algebraMap F K a) * (algebraMap F K a) * α := by
      have h3 := congrArg (unitaryInvolution K 2 f) h1
      rw [map_mul, E.fix, E.isUnitary.invol] at h3
      calc α = (algebraMap F K a) * unitaryInvolution K 2 f α := h3
        _ = (algebraMap F K a) * ((algebraMap F K a) * α) := by rw [h1]
        _ = (algebraMap F K a) * (algebraMap F K a) * α := by ring
    have ha2 : (algebraMap F K a) * (algebraMap F K a) = 1 := by
      have h4 : ((algebraMap F K a) * (algebraMap F K a)) * α = 1 * α := by
        rw [one_mul, ← h2]
      exact mul_right_cancel₀ hα0 h4
    have ha2' : a * a = 1 := by
      apply (algebraMap F K).injective
      rw [map_mul, map_one]
      exact ha2
    have ha1 : a = 1 := CharTwo.sq_inj.mp (by simpa [pow_two] using ha2')
    apply hα
    rw [h1, ha1, map_one, one_mul]
  exact ⟨nu, hnu, hc⟩

private theorem planeRho_fixedFree (E : QuadExt F K (unitaryInvolution K 2 f)) {nu : Kˣ}
    (hc : unitaryInvolution K 2 f (nu : K) * ((nu : K)⁻¹) ≠ 1) :
    ∀ z : K, planeRho E nu z = z → z = 0 := by
  intro z hz
  rw [planeRho_apply E] at hz
  by_contra hz0
  apply hc
  refine mul_right_cancel₀ hz0 ?_
  simpa using hz

private theorem planeRho_nonscalar (E : QuadExt F K (unitaryInvolution K 2 f)) [CharP F 2]
    {nu : Kˣ} (hnu : (nu : K) * unitaryInvolution K 2 f (nu : K) = 1)
    (hc : unitaryInvolution K 2 f (nu : K) * ((nu : K)⁻¹) ≠ 1) :
    ∀ c : F, ∃ z : K, planeRho E nu z ≠ c • z := by
  intro c
  by_contra h
  push Not at h
  have h1 := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
    (planeRho_mem_O E nu hnu) (1 : K)
  rw [h (1 : K)] at h1
  have hc1 : c = 1 := by
    have h1' : (algebraMap F K c) * algebraMap F K c = 1 := by
      have h2 := congrArg (algebraMap F K) h1
      rw [algebraMap_normQuad, algebraMap_normQuad] at h2
      simpa [Algebra.smul_def, map_mul, E.fix] using h2
    have hcc : c * c = 1 := by
      apply (algebraMap F K).injective
      rw [map_mul, map_one]
      exact h1'
    exact CharTwo.sq_inj.mp (by simpa [pow_two] using hcc)
  have h11 : planeRho E nu 1 = 1 := by
    rw [h (1 : K), hc1]
    simp
  have hz := planeRho_fixedFree E hc 1 h11
  simp at hz

private theorem exists_pure_fixedFree_nonscalar
    (E : QuadExt F K (unitaryInvolution K 2 f)) [CharP F 2] {n : ℕ} (i : Fin n) {nu : Kˣ}
    (hnu : (nu : K) * unitaryInvolution K 2 f (nu : K) = 1)
    (hc : unitaryInvolution K 2 f (nu : K) * ((nu : K)⁻¹) ≠ 1) :
    ∃ ρ : ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K)),
      ρ ∈ supportedDerived (normHypForm E n)
        (coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) i) ∧
      (∀ z ∈ coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) i,
        ρ z = z → z = 0) ∧
      (∀ c : F, ∃ x : ↥(coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) i),
        ρ (x : (F × F) × (Fin n → K)) ≠ c • (x : (F × F) × (Fin n → K))) := by
  classical
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  exact exists_supportedDerived_fixedFree_nonscalar (nondegenerate_coordPlane E i)
    (planeIsometry E i) (planeRho_mem E nu hnu) (planeRho_fixedFree E hc)
    (planeRho_nonscalar E hnu hc)


end PureModel

theorem commutator_centralizer_normPureBlock_singleton_inf_triple (hq : 4 ≤ Nat.card F)
    {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅Subgroup.centralizer (normPureBlock E n {i} : Set (normOmega E n)) ⊓
        normPureBlock E n {i, j, k},
      Subgroup.centralizer (normPureBlock E n {i} : Set (normOmega E n)) ⊓
        normPureBlock E n {i, j, k}⁆ =
      normPureBlock E n {j, k} := by
  classical
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  haveI : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  haveI : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  let V := (F × F) × (Fin n → K)
  let Q : QuadraticForm F V := normHypForm E n
  let U : Fin n → Submodule F V := fun t => coordPlane (LinearEquiv.refl F V) t
  let X : Submodule F V := U i
  let Y : Submodule F V := U j ⊔ U k
  let S : Finset (Fin n) := {i, j, k}
  have hQ : (polarBilin Q).Nondegenerate := normHypForm_polarBilin_nondegenerate E n
  have hXnd : (polarBilin (Q.comp X.subtype)).Nondegenerate := by
    simpa [X, U, Q] using nondegenerate_coordPlane E i
  have hYnd : (polarBilin (Q.comp Y.subtype)).Nondegenerate :=
    nondegenerate_coordPlane_sup_pair E j k
  have hXY : ∀ x ∈ X, ∀ y ∈ Y, polar Q x y = 0 := by
    intro x hx y hy
    have hx' : x ∈ coordPlane (LinearEquiv.refl F V) i := by simpa [X, U] using hx
    obtain ⟨yj, hyj, yk, hyk, rfl⟩ := Submodule.mem_sup.mp hy
    rw [polar_add_right, orthogonal_coordPlane_of_ne E hij x hx' yj hyj,
      orthogonal_coordPlane_of_ne E hik x hx' yk hyk, add_zero]
  have hXdim : Module.finrank F X = 2 := by
    simpa [X, U] using finrank_coordPlane E i
  obtain ⟨α, hα⟩ := exists_unitary_moved_element E
  obtain ⟨nu, hnu, hc⟩ := exists_pure_rotation E hα
  obtain ⟨ρ, hρ, hρfix, hρns⟩ := exists_pure_fixedFree_nonscalar E i hnu hc
  have hperf : Group.IsPerfect ↥(supportedDerived Q Y) :=
    isPerfect_supportedDerived_pair E hjk hq
  have hmain := commutator_centralizer_supportedDerived_eq (Q := Q) hQ hXnd hYnd hXY
    hXdim hρ hρfix hρns hperf
  let G : Subgroup (V ≃ₗ[F] V) := normOmega E n
  have hA : supportedDerived Q X ≤ G := supportedDerived_le_orthDerived_of_regular hXnd
  have hB : supportedDerived Q (X ⊔ Y) ≤ G := by
    have hblock : X ⊔ Y = S.sup U := by
      simp [X, Y, S, U, Finset.sup_insert, Finset.sup_singleton]
    rw [hblock]
    exact supportedDerived_coordPlane_sup_le_omega E n S
  have hP : supportedDerived Q Y ≤ G := supportedDerived_le_orthDerived_of_regular hYnd
  have htarget := commutator_centralizer_subgroupOf_eq (G := G) hA hB hP hmain
  simpa [normPureBlock, normOmega, X, Y, U, G, Q, S, Finset.sup_insert,
    Finset.sup_singleton] using htarget


end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

end
