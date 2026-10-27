module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.CompletionThreeFar
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.D5Frame
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.D5Nodes
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureEmbed
import CFSG.RankThree.PartOne.KC.OrthogonalHypPlaneGeneration

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
open QuadraticMap

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

include E in
private theorem cross_finrank_coordPlane (i : Fin 4) :
    Module.finrank F (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) i) = 2 := by
  have hdim : Module.finrank F (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) i) =
      Module.finrank F K := by
    let L : K →ₗ[F] (Fin 4 → K) := LinearMap.single F (fun _ => K) i
    have hL : Function.Injective L := by
      intro x y hxy
      have h := congrFun hxy i
      simpa [L] using h
    have hinj : Function.Injective
        ((LinearMap.inr F (F × F) (Fin 4 → K)).comp L) :=
      LinearMap.inr_injective.comp hL
    dsimp only [coordPlane]
    exact LinearMap.finrank_range_of_inj hinj
  rw [hdim, E.finrank_eq]

private theorem cross_coordPlane_anisotropic (i : Fin 4) :
    ∀ u ∈ coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) i,
      normHypForm E 4 u = 0 → u = 0 := by
  intro u hu hQu
  obtain ⟨x, rfl⟩ := mem_coordPlane.mp hu
  change normHypForm E 4 (((0, 0), Pi.single i x) : (F × F) × (Fin 4 → K)) = 0 at hQu
  have hsum : (∑ j : Fin 4, normQuad E ((Pi.single i x : Fin 4 → K) j)) = normQuad E x := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [Pi.single_eq_of_ne hji, map_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hQx : normQuad E x = 0 := by
    rw [normHypForm_apply_coord] at hQu
    simpa [hypPlane_apply, hsum] using hQu
  have hx : x = 0 := (normQuad_eq_zero_iff E).1 hQx
  subst hx
  simp

private theorem cross_coord_two_three {w : (F × F) × (Fin 4 → K)}
    (hw : w ∈ coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 0 ⊔
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 1) :
    w.2 2 = 0 ∧ w.2 3 = 0 := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
  obtain ⟨a, rfl⟩ := mem_coordPlane.mp hy
  obtain ⟨b, rfl⟩ := mem_coordPlane.mp hz
  refine ⟨?_, ?_⟩ <;> simp [Pi.single_apply]

private theorem cross_hypH2_le :
    hypH2 E ≤ coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 0 ⊔
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 1 :=
  le_sup_right.trans (hypH1_sup_hypH2 E).le

private theorem cross_hypH1_le :
    hypH1 E ≤ coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 0 ⊔
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 1 :=
  le_sup_left.trans (hypH1_sup_hypH2 E).le

private theorem cross_polar_hypH2_coordPlane {c : Fin 4} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    {w u : (F × F) × (Fin 4 → K)} (hw : w ∈ hypH2 E)
    (hu : u ∈ coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) c) :
    polar (normHypForm E 4) w u = 0 := by
  have hψ := normHypForm_apply_coord E 4
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (cross_hypH2_le E hw)
  rw [polar_add_left, polar_coordPlane_plane _ hψ (Ne.symm hc0) hy hu,
    polar_coordPlane_plane _ hψ (Ne.symm hc1) hz hu, add_zero]

private theorem cross_swap_apply_of_mem_hypH2 (h34 : 3 ≤ 4) {w : (F × F) × (Fin 4 → K)}
    (hw : w ∈ hypH2 E) :
    ((normPerm E h34 (Equiv.swap (2 : Fin 4) 3) : normOmega E 4) :
      ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) w = w := by
  obtain ⟨h2, h3⟩ := cross_coord_two_three (cross_hypH2_le E hw)
  rw [normPerm_apply]
  refine Prod.ext rfl (funext fun j => ?_)
  show w.2 ((Equiv.swap (2 : Fin 4) 3)⁻¹ j) = w.2 j
  rw [Equiv.swap_inv]
  by_cases hj2 : j = 2
  · subst hj2
    rw [Equiv.swap_apply_left, h3, h2]
  · by_cases hj3 : j = 3
    · subst hj3
      rw [Equiv.swap_apply_right, h2, h3]
    · rw [Equiv.swap_apply_of_ne_of_ne hj2 hj3]

private theorem cross_swap_map_coordPlane (h34 : 3 ≤ 4) :
    (coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 2).map
        ((normPerm E h34 (Equiv.swap (2 : Fin 4) 3) : normOmega E 4) :
          ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))).toLinearMap =
      coordPlane (LinearEquiv.refl F ((F × F) × (Fin 4 → K))) 3 := by
  have key : ∀ e : K,
      ((normPerm E h34 (Equiv.swap (2 : Fin 4) 3) : normOmega E 4) :
        ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) ((0 : F × F), Pi.single 2 e) =
        ((0 : F × F), Pi.single 3 e) := by
    intro e
    rw [normPerm_apply]
    refine Prod.ext rfl (funext fun j => ?_)
    show (Pi.single (2 : Fin 4) e : Fin 4 → K) ((Equiv.swap (2 : Fin 4) 3)⁻¹ j) =
      (Pi.single (3 : Fin 4) e : Fin 4 → K) j
    rw [Equiv.swap_inv]
    by_cases hj3 : j = 3
    · subst hj3
      simp
    · by_cases hj2 : j = 2
      · subst hj2
        simp
      · rw [Equiv.swap_apply_of_ne_of_ne hj2 hj3, Pi.single_eq_of_ne hj2,
          Pi.single_eq_of_ne hj3]
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨e, rfl⟩ := mem_coordPlane.mp hv
    exact mem_coordPlane.mpr ⟨e, (key e).symm⟩
  · intro v hv
    obtain ⟨e, rfl⟩ := mem_coordPlane.mp hv
    exact ⟨((0 : F × F), Pi.single 2 e), mem_coordPlane.mpr ⟨e, rfl⟩, key e⟩

variable {E}

theorem commute_crossAnchor_crossPure (hq : 4 ≤ Nat.card F) {G : Type} [Group G]
    {a : Fin 4 → (normOmega E 3 →* G)} (ha : ∀ i, Function.Injective (a i))
    {R : Finset (Fin 4) → Subgroup G}
    (hR : ∀ (i : Fin 4) (S : Finset (Fin 3)), S.Nonempty → S.card ≤ 2 →
      (normBlock E 3 S).map (a i) = R (S.image i.succAbove))
    {φ : normPureBlock E 4 Finset.univ →* G}
    (hagree : ∀ (x : normOmega E 3)
      (hx : normOmegaCast E (by norm_num : 3 ≤ 4) x ∈ normPureBlock E 4 Finset.univ),
      φ ⟨_, hx⟩ = a 3 x)
    (h23 : ∀ y : normPureBlock E 4 Finset.univ, (y : normOmega E 4) ∈ normPureBlock E 4 {2, 3} →
      φ y ∈ (normPureBlock E 3 {1, 2}).map (a 0))
    (x : normOmega E 3) (y : normPureBlock E 4 Finset.univ)
    (hx : normOmegaCast E (by norm_num : 3 ≤ 4) x ∈
      (supportedDerived (normHypForm E 4) (crossAnchor E)).subgroupOf (normOmega E 4))
    (hy : (y : normOmega E 4) ∈
      (supportedDerived (normHypForm E 4) (crossPure E)).subgroupOf (normOmega E 4)) :
    Commute (a 3 x) (φ y) := by
  classical
  have : FiniteDimensional F K := finiteDimensional_of_quadExt E
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  have h34 : (3 : ℕ) ≤ 4 := by norm_num
  have hψ := normHypForm_apply_coord E 4
  have hQ := normHypForm_polarBilin_nondegenerate E 4
  have hQE := normQuad_polarBilin_nondegenerate E
  have hq2 : 2 < Nat.card F := by omega
  have : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  set ψ := LinearEquiv.refl F ((F × F) × (Fin 4 → K)) with hψdef
  set Q := normHypForm E 4 with hQdef
  have hUpoly : ∀ i, PolarNondegOn Q (coordPlane ψ i) :=
    fun i => coordPlane_polarNondegOn ψ hψ hQE i
  have hUorth : ∀ i j, i ≠ j → ∀ x ∈ coordPlane ψ i, ∀ y ∈ coordPlane ψ j, polar Q x y = 0 :=
    fun i j hij x hx y hy => polar_coordPlane_plane ψ hψ hij hx hy
  have hH2poly : PolarNondegOn Q (hypH2 E) := by
    change PolarNondegOn Q (Submodule.span F {(hypPairH2 E).e, (hypPairH2 E).f})
    exact polarNondegOn_span_pair_of_polar_eq_one (hypPairH2 E).polar_ef
  have hH2U2 : (polarBilin (Q.comp (hypH2 E ⊔ coordPlane ψ 2).subtype)).Nondegenerate :=
    CFSG.LieType.SeitzGeneration.OrthBlk.nondegenerate_of_polarNondegOn
      (CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup hH2poly (hUpoly 2)
        (fun w hw u hu => cross_polar_hypH2_coordPlane E (by decide) (by decide) hw hu))
  have hTriple : (polarBilin (Q.comp
      (({0, 1, 2} : Finset (Fin 4)).sup (coordPlane ψ)).subtype)).Nondegenerate :=
    nondegenerate_finset_sup (coordPlane ψ) hUpoly hUorth _
  have hPair23 : (({2, 3} : Finset (Fin 4)).sup (coordPlane ψ)) =
      coordPlane ψ 2 ⊔ coordPlane ψ 3 := by
    simp
  have hPairReg :
      (polarBilin (Q.comp (coordPlane ψ 2 ⊔ coordPlane ψ 3).subtype)).Nondegenerate := by
    rw [← hPair23]
    exact nondegenerate_finset_sup (coordPlane ψ) hUpoly hUorth _
  let P := normPureBlock E 4 Finset.univ
  let T : Subgroup (((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) :=
    (((Subgroup.centralizer ({a 3 x} : Set G)).comap φ).map P.subtype).map
      (normOmega E 4).subtype
  have hmemT : ∀ (g : ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K)))
      (hgΩ : g ∈ normOmega E 4) (hgP : (⟨g, hgΩ⟩ : normOmega E 4) ∈ P),
      Commute (a 3 x) (φ ⟨⟨g, hgΩ⟩, hgP⟩) → g ∈ T := by
    intro g hgΩ hgP hc
    refine ⟨⟨g, hgΩ⟩, ⟨⟨⟨g, hgΩ⟩, hgP⟩, ?_, rfl⟩, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr hc.eq.symm
  have hX : supportedDerived Q (hypH2 E ⊔ coordPlane ψ 2) ≤ T := by
    intro g hg
    have hgΩ : g ∈ normOmega E 4 := supportedDerived_le_orthDerived_of_regular hH2U2 hg
    have hle : hypH2 E ⊔ coordPlane ψ 2 ≤ ({0, 1, 2} : Finset (Fin 4)).sup (coordPlane ψ) := by
      refine sup_le ((cross_hypH2_le E).trans (sup_le ?_ ?_)) ?_
      · exact Finset.le_sup (f := coordPlane ψ) (by decide)
      · exact Finset.le_sup (f := coordPlane ψ) (by decide)
      · exact Finset.le_sup (f := coordPlane ψ) (by decide)
    have hg3 : (⟨g, hgΩ⟩ : normOmega E 4) ∈ normPureBlock E 4 {0, 1, 2} :=
      Subgroup.mem_subgroupOf.mpr (supportedDerived_le_supportedDerived_of_le hle hH2U2 hTriple hg)
    have hcast : (normPureBlock E 3 Finset.univ).map (normOmegaCast E h34) =
        normPureBlock E 4 {0, 1, 2} := by
      rw [map_normPureBlock_normOmegaCast]
      congr 1
    have hgP : (⟨g, hgΩ⟩ : normOmega E 4) ∈ P :=
      normPureBlock_mono E 4 (Finset.subset_univ _) hg3
    rw [← hcast] at hg3
    obtain ⟨x', -, hx'g⟩ := hg3
    refine hmemT g hgΩ hgP ?_
    have hφ : φ ⟨⟨g, hgΩ⟩, hgP⟩ = a 3 x' := by
      have h := hagree x' (by rw [hx'g]; exact hgP)
      rw [← h]
      exact congrArg φ (Subtype.ext hx'g.symm)
    rw [hφ]
    have hxA : ((normOmegaCast E h34 x : normOmega E 4) :
        ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) ∈
          supportedDerived Q (crossAnchor E) := Subgroup.mem_subgroupOf.mp hx
    have hx'B : ((normOmegaCast E h34 x' : normOmega E 4) :
        ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) ∈
          supportedDerived Q (hypH2 E ⊔ coordPlane ψ 2) := by
      rw [hx'g]
      exact hg
    have hlin := supportedDerived_commute_of_orthogonal_supports (nondegenerate_crossAnchor E)
      hH2U2 (fun u hu v hv => polar_crossAnchor_crossPure E hu
        ((sup_le_sup_left (le_sup_left : coordPlane ψ 2 ≤ coordPlane ψ 2 ⊔ coordPlane ψ 3)
          (hypH2 E)) hv)) hxA hx'B
    have hc : normOmegaCast E h34 x * normOmegaCast E h34 x' =
        normOmegaCast E h34 x' * normOmegaCast E h34 x :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact hlin.eq)
    have hcx : x * x' = x' * x := by
      apply normOmegaCast_injective E h34
      rw [map_mul, map_mul]
      exact hc
    exact Commute.map hcx (a 3)
  have hZ : supportedDerived Q (coordPlane ψ 2 ⊔ coordPlane ψ 3) ≤ T := by
    intro g hg
    have hgΩ : g ∈ normOmega E 4 := supportedDerived_le_orthDerived_of_regular hPairReg hg
    have hg23 : (⟨g, hgΩ⟩ : normOmega E 4) ∈ normPureBlock E 4 {2, 3} := by
      refine Subgroup.mem_subgroupOf.mpr ?_
      show g ∈ supportedDerived Q (({2, 3} : Finset (Fin 4)).sup (coordPlane ψ))
      rw [hPair23]
      exact hg
    have hgP : (⟨g, hgΩ⟩ : normOmega E 4) ∈ P := normPureBlock_mono E 4 (Finset.subset_univ _) hg23
    refine hmemT g hgΩ hgP ?_
    have hφ := h23 ⟨⟨g, hgΩ⟩, hgP⟩ hg23
    rw [← rangePurePair_eq_map E hq ha hR (i := 2) (j := 3) (l := 0) (by decide) (by decide)
      (by decide) (i' := 1) (j' := 2) (by decide) (by decide)] at hφ
    have hxB4 : normOmegaCast E h34 x ∈ normBlock E 4 {0, 1} := by
      refine Subgroup.mem_subgroupOf.mpr ?_
      have hle : crossAnchor E ≤ coordSupport ψ {0, 1} := by
        refine sup_le_sup_left ((cross_hypH1_le E).trans (sup_le ?_ ?_)) _
        · exact Finset.le_sup (f := coordPlane ψ) (by decide)
        · exact Finset.le_sup (f := coordPlane ψ) (by decide)
      exact supportedDerived_le_supportedDerived_of_le hle (nondegenerate_crossAnchor E)
        (coordSupport_nondegenerate ψ hψ hQ hQE {0, 1}) (Subgroup.mem_subgroupOf.mp hx)
    have hmap := map_normBlock_normOmegaCast E h34 ({0, 1} : Finset (Fin 3))
    have hS : ({0, 1} : Finset (Fin 3)).map (Fin.castLEEmb h34) = {0, 1} := by
      rw [Finset.map_insert, Finset.map_singleton]
      rfl
    rw [hS] at hmap
    rw [← hmap] at hxB4
    obtain ⟨x0, hx0, hx0x⟩ := hxB4
    have hx0eq : x0 = x := normOmegaCast_injective E h34 hx0x
    subst hx0eq
    have hR3 := hR 3 {0, 1} (by decide) (by decide)
    have himg : ({0, 1} : Finset (Fin 3)).image (3 : Fin 4).succAbove = {0, 1} := by decide
    rw [himg] at hR3
    have hx01 : a 3 x0 ∈ R {0, 1} := hR3 ▸ Subgroup.mem_map_of_mem _ hx0
    exact (commute_of_mem_rangePurePair_of_mem_pair E hq ha hR (i := 2) (j := 3) (k := 0) (l := 1)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hφ hx01).symm
  have hg := normPerm_swap_mem_normPureBlock E hq2 h34 (2 : Fin 4) 3
  have hgS : ((normPerm E h34 (Equiv.swap (2 : Fin 4) 3) : normOmega E 4) :
      ((F × F) × (Fin 4 → K)) ≃ₗ[F] ((F × F) × (Fin 4 → K))) ∈
        supportedDerived Q (coordPlane ψ 2 ⊔ coordPlane ψ 3) := by
    have h := Subgroup.mem_subgroupOf.mp hg
    rw [← hPair23]
    exact h
  have hsplit : supportedDerived Q (crossPure E) ≤
      supportedDerived Q (hypH2 E ⊔ coordPlane ψ 2) ⊔
        supportedDerived Q (coordPlane ψ 2 ⊔ coordPlane ψ 3) :=
    supportedDerived_hypPlane_sup_le (hypPairH2 E) (cross_finrank_coordPlane E 2)
      (cross_finrank_coordPlane E 3) (cross_coordPlane_anisotropic E 2)
      (cross_coordPlane_anisotropic E 3)
      (fun w hw u hu => cross_polar_hypH2_coordPlane E (by decide) (by decide) hw hu)
      (fun w hw u hu => cross_polar_hypH2_coordPlane E (by decide) (by decide) hw hu)
      (fun u hu v hv => polar_coordPlane_plane ψ hψ (by decide) hu hv) hgS
      (fun w hw => cross_swap_apply_of_mem_hypH2 E h34 hw) (cross_swap_map_coordPlane E h34)
  obtain ⟨u, ⟨z, hz, hzu⟩, hug⟩ := (hsplit.trans (sup_le hX hZ)) (Subgroup.mem_subgroupOf.mp hy)
  have hzy : z = y := by
    apply Subtype.ext
    apply Subtype.ext
    rw [← hug, ← hzu]
    rfl
  subst hzy
  exact (Subgroup.mem_centralizer_singleton_iff.mp hz).symm

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

end
