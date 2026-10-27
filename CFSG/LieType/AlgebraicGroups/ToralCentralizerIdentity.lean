module

public import CFSG.LieType.AlgebraicGroups.ToralCentralizerComponent
public import CFSG.LieType.AlgebraicGroups.ToralRootCover
public import CFSG.LieType.AlgebraicGroups.ExactAffineRealization
public import CFSG.LieType.Chevalley.OddToralInvolutionComponents
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley WithConv Topology

open scoped CFSG.ConvolutionPoints

theorem exists_toralCoverData
    {τ : Tag} {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) :
    ∃ (nI : ℕ) (κ : Fin nI → KernelComponent χ) (m : Fin nI → ℕ)
      (α : (l : Fin nI) → Fin (m l) → Fin τ.rank → ℤ) (v : (Fin τ.rank → ℤ) → WeylGroup τ)
      (j : (Fin τ.rank → ℤ) → Fin τ.rank)
      (ω : KernelComponent χ → WeylGroup τ → List (Fin τ.rank → ℤ)),
      Function.Bijective κ ∧ (∀ l, Function.Injective (α l)) ∧
      (∀ l, Set.range (α l) = posRoots (componentRoots χ (κ l))) ∧
      (∀ i, ∀ β ∈ simpleRoots (componentRoots χ i),
        v β • (Pi.single (j β) 1 : Fin τ.rank → ℤ) = β) ∧
      ∀ i, ∀ w ∈ componentWeylGroup (componentRoots χ i),
        IsComponentWord (componentRoots χ i) (ω i w) ∧ reflectionWordProd (ω i w) = w := by
  classical
  have : Finite (kernelRoots χ) := ((finite_setOf_isRoot τ).subset fun α h => h.1).to_subtype
  obtain ⟨nI, ⟨e⟩⟩ := Finite.exists_equiv_fin (KernelComponent χ)
  have hfin : ∀ i : KernelComponent χ, Finite (posRoots (componentRoots χ i)) := fun i =>
    ((finite_setOf_isRoot τ).subset fun β hβ => by
      obtain ⟨⟨hβk, -⟩, -⟩ := hβ
      exact hβk.1).to_subtype
  have hvj : ∀ β : Fin τ.rank → ℤ, ∃ (w : WeylGroup τ) (i : Fin τ.rank),
      IsRoot τ β → w • (Pi.single i 1 : Fin τ.rank → ℤ) = β := fun β => by
    by_cases hβ : IsRoot τ β
    · obtain ⟨w, i, h⟩ := isRoot_iff_exists_smul_single.1 hβ
      exact ⟨w, i, fun _ => h⟩
    · exact ⟨1, ⟨0, τ.rank_pos⟩, fun h => absurd h hβ⟩
  choose v j hvj using hvj
  have hω : ∀ (i : KernelComponent χ) (w : WeylGroup τ), ∃ l : List (Fin τ.rank → ℤ),
      w ∈ componentWeylGroup (componentRoots χ i) →
        IsComponentWord (componentRoots χ i) l ∧ reflectionWordProd l = w := fun i w => by
    by_cases hw : w ∈ componentWeylGroup (componentRoots χ i)
    · obtain ⟨l, hl, e⟩ := mem_componentWeylGroup_iff.1 hw
      exact ⟨l, fun _ => ⟨hl, e⟩⟩
    · exact ⟨[], fun h => absurd h hw⟩
  choose ω hω using hω
  refine ⟨nI, e.symm, fun l => Nat.card (posRoots (componentRoots χ (e.symm l))),
    fun l p => ((Finite.equivFin (posRoots (componentRoots χ (e.symm l)))).symm p :
      Fin τ.rank → ℤ), v, j, ω, e.symm.bijective,
    fun l => Subtype.val_injective.comp (Equiv.injective _), fun l => ?_,
    fun i β hβ => hvj β (simpleRoots_isRoot hβ), hω⟩
  ext β
  constructor
  · rintro ⟨p, rfl⟩
    exact ((Finite.equivFin _).symm p).2
  · intro hβ
    exact ⟨Finite.equivFin _ ⟨β, hβ⟩,
      congrArg Subtype.val ((Finite.equivFin _).symm_apply_apply _)⟩

variable {τ : Tag} {k : Type} [Field k]

variable (τ k) in
abbrev toralCentralizerPointSubgroup
    (a : Fin τ.rank → kˣ) :
    Subgroup (WithConv (GLCoord k (Label τ) →ₐ[k] k)) :=
  (toralCentralizer τ k a).map (modGLPoint τ k).toMonoidHom

variable (τ k) in
abbrev toralRootPointSubgroup
    (a : Fin τ.rank → kˣ) :
    Subgroup (WithConv (GLCoord k (Label τ) →ₐ[k] k)) :=
  (toralRootGroup τ k a).map (modGLPoint τ k).toMonoidHom

theorem transportPoints_toralCentralizer
    (a : Fin τ.rank → kˣ) :
    transportPoints (modGLPoint τ k) (toralCentralizer τ k a) =
      groupPoints τ k ∩ {y | y.comp (innerCo (modGLPoint τ k (rootDiagUnit τ a))) = y} := by
  ext y
  rw [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨hgG, hgc⟩ := mem_toralCentralizer.1 hg
    refine ⟨by rwa [groupPoints, Set.mem_ofPred_eq, toConv_ofConv, MulEquiv.symm_apply_apply], ?_⟩
    have h := point_comp_innerCo (modGLPoint τ k g) (modGLPoint τ k (rootDiagUnit τ a))
    rw [← map_inv, ← map_mul, ← map_mul, hgc] at h
    exact congrArg ofConv h
  · rintro ⟨hG, hc⟩
    refine ⟨(modGLPoint τ k).symm (toConv y), mem_toralCentralizer.2 ⟨hG, ?_⟩, ?_⟩
    · have h := point_comp_innerCo (toConv y) (modGLPoint τ k (rootDiagUnit τ a))
      rw [ofConv_toConv, hc] at h
      apply (modGLPoint τ k).injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact h.symm
    · simp only [MulEquiv.apply_symm_apply, ofConv_toConv]

theorem isPointClosed_toralCentralizer
    [IsAlgClosed k] (a : Fin τ.rank → kˣ) :
    IsPointClosed k (subgroupPoints (toralCentralizerPointSubgroup τ k a)) := by
  rw [subgroupPoints_map, transportPoints_toralCentralizer]
  exact (exceptional_Lang_exact_affine_group_realization k τ).1.1.inter
    (isPointClosed_setOf_comp_eq _)

theorem kernelReflectionGroup_eq_kernelWeylGroup_rootCharHom
    (a : Fin τ.rank → kˣ) :
    kernelReflectionGroup a = kernelWeylGroup (rootCharHom a) :=
  rfl

theorem mem_kernelReflectionGroup_of_canonicalRep_mem
    [IsAlgClosed k] (hk : ringChar k ≠ 2)
    {a : Fin τ.rank → kˣ} (ha : ∀ i, a i = 1 ∨ a i = -1) {w : WeylGroup τ}
    (hw : canonicalRep (coxeterSystem τ) k w ∈ toralRootGroup τ k a) :
    w ∈ kernelReflectionGroup a := by
  obtain ⟨nI, κ, m, α, v, j, ω, hκ, hα, hαr, hvj, hω⟩ := exists_toralCoverData (rootCharHom a)
  obtain ⟨-, -, -, -, -, -, -, -, hidx, -, -⟩ :=
    exceptional_toral_root_subgroup_regular_cover τ k hk a ha κ hκ α hα hαr v j hvj ω hω
  obtain ⟨u, hu, hnu⟩ := hidx _ hw
  have huw : u = w := by
    by_contra hne
    exact Set.disjoint_left.1 (disjoint_bruhatCell hne) hnu (canonicalRep_mem_bruhatCell w)
  rw [kernelReflectionGroup_eq_kernelWeylGroup_rootCharHom, kernelWeylGroup_eq_closure, ← huw]
  exact hu

theorem nonempty_quotient_subgroupOf_mulEquiv {G : Type*} [Group G] {H H' N N' : Subgroup G}
    [(N.subgroupOf H).Normal] [(N'.subgroupOf H').Normal] (hH : H = H') (hN : N = N') :
    Nonempty (H ⧸ N.subgroupOf H ≃* H' ⧸ N'.subgroupOf H') := by
  subst hH hN
  exact ⟨MulEquiv.refl _⟩

theorem nonempty_weylQuotient_mulEquiv_charQuotient
    (hk : ringChar k ≠ 2) {a : Fin τ.rank → kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) :
    Nonempty (rootCharStabilizerSubgroup a ⧸
        (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a) ≃*
      CharQuotient (maskChar (signTupleBits a))) :=
  have := (sign_character_Weyl_stabilizer_quotients τ (maskChar (signTupleBits a))).2.1
  nonempty_quotient_subgroupOf_mulEquiv
    (Subgroup.ext fun _ => mem_rootCharStabilizer_iff hk ha)
    (kernelReflectionGroup_eq_kernelWeylGroup hk ha)

variable (τ k) in
theorem exceptional_toral_centralizer_identity_component
    [IsAlgClosed k] (hk : ringChar k ≠ 2)
    (a : Fin τ.rank → kˣ) (ha : ∀ i, a i = 1 ∨ a i = -1) :
    (IsPointClosed k (subgroupPoints (toralCentralizerPointSubgroup τ k a)) ∧
      subgroupIdeal (adjointPointSubgroup τ k) ≤
        subgroupIdeal (toralCentralizerPointSubgroup τ k a) ∧
      pointsZero k (subgroupIdeal (toralCentralizerPointSubgroup τ k a)) =
        subgroupPoints (toralCentralizerPointSubgroup τ k a) ∧
      (subgroupIdeal (toralCentralizerPointSubgroup τ k a)).IsHopfIdeal k ∧
      (subgroupIdeal (toralCentralizerPointSubgroup τ k a)).IsRadical ∧
      IsReduced (GLCoord k (Label τ) ⧸ subgroupIdeal (toralCentralizerPointSubgroup τ k a)) ∧
      (∀ J : Ideal (GLCoord k (Label τ)), J.IsRadical →
        pointsZero k J = subgroupPoints (toralCentralizerPointSubgroup τ k a) →
          J = subgroupIdeal (toralCentralizerPointSubgroup τ k a)) ∧
      (∃ e : WithConv ((GLCoord k (Label τ) ⧸
          subgroupIdeal (toralCentralizerPointSubgroup τ k a)) →ₐ[k] k) ≃*
            toralCentralizer τ k a, ∀ φ,
        ((e φ : toralCentralizer τ k a) : ModGL τ k) =
          (modGLPoint τ k).symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k _)))) ∧
      Algebra.Smooth k
        (GLCoord k (Label τ) ⧸ subgroupIdeal (toralCentralizerPointSubgroup τ k a))) ∧
    (IsConnectedAlgebraicSubgroup k (toralRootPointSubgroup τ k a) ∧
      connectedComponentIn (PrimeSpectrum.zeroLocus
          (subgroupIdeal (toralCentralizerPointSubgroup τ k a) : Set (GLCoord k (Label τ))))
          (pointSpec (1 : WithConv (GLCoord k (Label τ) →ₐ[k] k)).ofConv) =
        PrimeSpectrum.zeroLocus
          (subgroupIdeal (toralRootPointSubgroup τ k a) : Set (GLCoord k (Label τ))) ∧
      Algebra.Smooth k (GLCoord k (Label τ) ⧸ subgroupIdeal (toralRootPointSubgroup τ k a)) ∧
      IrreducibleSpace
        (PrimeSpectrum (GLCoord k (Label τ) ⧸ subgroupIdeal (toralRootPointSubgroup τ k a))) ∧
      ∃ e : WithConv ((GLCoord k (Label τ) ⧸ subgroupIdeal (toralRootPointSubgroup τ k a)) →ₐ[k]
          k) ≃* toralRootGroup τ k a, ∀ φ,
        ((e φ : toralRootGroup τ k a) : ModGL τ k) =
          (modGLPoint τ k).symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k _)))) ∧
    (toralRootGroup τ k a ≤ toralCentralizer τ k a ∧
      ((toralRootGroup τ k a).subgroupOf (toralCentralizer τ k a)).Normal ∧
      kernelReflectionGroup a ≤ rootCharStabilizerSubgroup a ∧
      ((kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)).Normal ∧
      ∃ e : rootCharStabilizerSubgroup a ⧸
          (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a) ≃*
            toralCentralizer τ k a ⧸ (toralRootGroup τ k a).subgroupOf (toralCentralizer τ k a),
        ∀ w : rootCharStabilizerSubgroup a, e (QuotientGroup.mk w) =
          QuotientGroup.mk ⟨canonicalRep (coxeterSystem τ) k w,
            canonicalRep_mem_toralCentralizer w.2⟩) ∧
    Finite (toralCentralizer τ k a ⧸ (toralRootGroup τ k a).subgroupOf (toralCentralizer τ k a)) ∧
    ((τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) → toralRootGroup τ k a = toralCentralizer τ k a) ∧
    (τ = .E7 → Nat.card (toralCentralizer τ k a ⧸
      (toralRootGroup τ k a).subgroupOf (toralCentralizer τ k a)) ∣ 2) ∧
    (τ = .D4 → Nat.card (toralCentralizer τ k a ⧸
        (toralRootGroup τ k a).subgroupOf (toralCentralizer τ k a)) ∣ 4 ∧
      CFSG.IsElementaryAbelian 2 (toralCentralizer τ k a ⧸
        (toralRootGroup τ k a).subgroupOf (toralCentralizer τ k a))) := by
  classical
  set Zp := toralCentralizerPointSubgroup τ k a with hZp
  set Mp := toralRootPointSubgroup τ k a with hMp
  have hZcl : IsPointClosed k (subgroupPoints Zp) := isPointClosed_toralCentralizer a
  have hZ : pointsZero k (subgroupIdeal Zp) = subgroupPoints Zp :=
    pointsZero_pointsIdeal_of_isPointClosed hZcl
  have hZrad : (subgroupIdeal Zp).IsRadical := isRadical_pointsIdeal _
  have hZred : IsReduced (GLCoord k (Label τ) ⧸ subgroupIdeal Zp) :=
    (Ideal.isRadical_iff_quotient_reduced _).1 hZrad
  have hZG : Zp ≤ adjointPointSubgroup τ k := Subgroup.map_mono inf_le_left
  have hGZ : subgroupIdeal (adjointPointSubgroup τ k) ≤ subgroupIdeal Zp := fun f hf =>
    mem_pointsIdeal.2 fun y hy => mem_pointsIdeal.1 hf y (hZG hy)
  obtain ⟨nI, κ, m, α, v, j, ω, hκ, hα, hαr, hvj, hω⟩ := exists_toralCoverData (rootCharHom a)
  obtain ⟨-, -, -, -, -, -, -, -, -, hirr, hcons⟩ :=
    exceptional_toral_root_subgroup_regular_cover τ k hk a ha κ hκ α hα hαr v j hvj ω hω
  obtain ⟨-, hM, hMe⟩ := isConnectedAlgebraicSubgroup_map (modGLPoint τ k)
    (toralRootGroup τ k a) hcons hirr
  obtain ⟨hMsm, -, hMirr⟩ := hM.smooth
  obtain ⟨hMX, hMn, hWS, hWn, φ, hφs, hφ⟩ :=
    Chevalley_toral_centralizer_root_generated_quotient τ k a
  have hφi : Function.Injective φ := by
    refine (injective_iff_map_eq_one φ).2 fun q hq => ?_
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hφ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact mem_kernelReflectionGroup_of_canonicalRep_mem hk ha hq
  set e := MulEquiv.ofBijective φ ⟨hφi, hφs⟩ with he
  have hfinQ : Finite (toralCentralizer τ k a ⧸
      (toralRootGroup τ k a).subgroupOf (toralCentralizer τ k a)) := Finite.of_surjective φ hφs
  have hMZ : Mp ≤ Zp := Subgroup.map_mono hMX
  have hdiff : IsPointClosed k (subgroupPoints Zp \ subgroupPoints Mp) := by
    refine isPointClosed_subgroupPoints_diff hMZ hM.isPointClosed (Set.finite_range fun
      q : toralCentralizer τ k a ⧸ (toralRootGroup τ k a).subgroupOf (toralCentralizer τ k a) =>
        modGLPoint τ k (q.out : ModGL τ k)) ?_ ?_
    · rintro _ ⟨q, rfl⟩
      exact ⟨q.out, q.out.2, rfl⟩
    · rintro _ ⟨g, hg, rfl⟩
      refine ⟨_, ⟨QuotientGroup.mk ⟨g, hg⟩, rfl⟩, ?_⟩
      have h1 := QuotientGroup.out_eq' (QuotientGroup.mk ⟨g, hg⟩ : toralCentralizer τ k a ⧸
        (toralRootGroup τ k a).subgroupOf (toralCentralizer τ k a))
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
      refine ⟨_, h1, ?_⟩
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, Subgroup.coe_mul,
        Subgroup.coe_inv, map_mul, map_inv]
  refine ⟨⟨hZcl, hGZ, hZ, inferInstance, hZrad, hZred,
    fun J hJ hJZ => eq_subgroupIdeal_of_pointsZero_eq Zp hJ hJZ,
    ⟨(subgroupQuotientPointsEquiv Zp hZ).trans
      ((modGLPoint τ k).subgroupMap (toralCentralizer τ k a)).symm, fun _ => rfl⟩,
    (smooth_of_hopfAlgebra_of_isReduced k _).1⟩,
    ⟨hM, connectedComponentIn_zeroLocus_eq hMZ hM hdiff, hMsm, hMirr, hMe⟩,
    ⟨hMX, hMn, hWS, hWn, e, fun w => hφ w⟩, hfinQ, ?_, ?_, ?_⟩
  ·
    intro hτ
    have hW := (sign_character_Weyl_stabilizer_quotients τ (maskChar (signTupleBits a))).2.2.1 hτ
    refine le_antisymm hMX fun g hg => ?_
    obtain ⟨q, hq⟩ := hφs (QuotientGroup.mk ⟨g, hg⟩)
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    have hw : (w : WeylGroup τ) ∈ kernelReflectionGroup a := by
      rw [kernelReflectionGroup_eq_kernelWeylGroup hk ha, ← hW]
      exact (mem_rootCharStabilizer_iff hk ha).1 w.2
    have h1 : (QuotientGroup.mk w : rootCharStabilizerSubgroup a ⧸
        (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hw
    rw [h1, map_one, eq_comm, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq
    exact hq
  · intro hτ
    obtain ⟨e'⟩ := nonempty_weylQuotient_mulEquiv_charQuotient hk ha
    rw [Nat.card_congr (e.symm.trans e').toEquiv]
    exact (sign_character_Weyl_stabilizer_quotients τ _).2.2.2.1 hτ
  · intro hτ
    obtain ⟨e'⟩ := nonempty_weylQuotient_mulEquiv_charQuotient hk ha
    obtain ⟨h4, hEA⟩ := (sign_character_Weyl_stabilizer_quotients τ _).2.2.2.2 hτ
    exact ⟨by rw [Nat.card_congr (e.symm.trans e').toEquiv]; exact h4,
      isElementaryAbelian_of_mulEquiv (e.symm.trans e') hEA⟩

end CFSG.LieType.AlgebraicGroups
