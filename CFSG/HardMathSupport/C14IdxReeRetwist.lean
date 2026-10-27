module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcIdxRee
public import CFSG.RankThree.PartOne.KLR.TwistPerm
public import CFSG.HardMathSupport.C14IdxReeLang
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KernelPosNormalize
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5SpinCoords
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5TorusGen
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyConjNormalizer
public import CFSG.LieType.AlgebraicGroups.KernelRootBruhat
public import CFSG.LieType.Chevalley.CharTwoWeylLifts
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR
  CFSG.RankThree.PartOne.TCX.Ree CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.SeitzReduction
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen (coordTuple)


private theorem kernelWeylGroup_eq_unionWeylGroup
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} :
    kernelWeylGroup χ = unionWeylGroup χ (Set.univ : Set (KernelComponent χ)) := by
  refine le_antisymm ?_ ?_
  · rw [kernelWeylGroup_eq_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, rfl⟩
    have hα' : α ∈ unionRoots χ (Set.univ : Set (KernelComponent χ)) := by
      rwa [CFSG.LieType.AlgebraicGroups.unionRoots_univ_eq_kernelRoots]
    obtain ⟨u, hu, β, hβ, rfl⟩ := exists_smul_unionSimpleRoot (J := Set.univ) hα'
    rw [rootReflection_smul_root u (isRoot_of_mem_unionSimpleRoots hβ)]
    exact mul_mem (mul_mem hu (rootReflection_mem_unionWeylGroup hβ)) (inv_mem hu)
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβ, rfl⟩
    have hβ' : β ∈ kernelRoots χ := by
      rw [← CFSG.LieType.AlgebraicGroups.unionRoots_univ_eq_kernelRoots]
      exact mem_unionRoots_of_mem_unionSimpleRoots hβ
    exact rootReflection_mem_kernelWeylGroup hβ'

private theorem exists_mul_smul_mem_posRoots_of_bijOn
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {S : Set (Fin τ.rank → ℤ)} {x : WeylGroup τ}
    (hx : Set.BijOn (fun α => x • α) S (kernelRoots χ)) :
    ∃ ρ ∈ kernelWeylGroup χ, ∀ α ∈ S, 0 < height α → (ρ * x) • α ∈ posRoots (kernelRoots χ) := by
  classical
  let f : (Fin τ.rank → ℤ) →+ ℤ :=
    { toFun := fun μ => height (x⁻¹ • μ)
      map_zero' := by simp [height]
      map_add' := fun u v => by rw [smul_add, height_add] }
  have hf : ∀ γ ∈ kernelRoots χ, f γ ≠ 0 := fun γ hγ =>
    (IsRoot.smul hγ.1 x⁻¹).height_ne_zero
  obtain ⟨ρ₀, hρ₀, hpos⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KernelPos.exists_kernelWeyl_smul_pos
      (χ := χ) f hf
  refine ⟨ρ₀⁻¹, inv_mem hρ₀, fun α hα hαpos => ?_⟩
  have hxα : x • α ∈ kernelRoots χ := hx.mapsTo hα
  have hδα : ρ₀⁻¹ • (x • α) ∈ kernelRoots χ :=
    smul_mem_kernelRoots (kernelWeylGroup_le (inv_mem hρ₀)) hxα
  change (ρ₀⁻¹ * x) • α ∈ posRoots (kernelRoots χ)
  rw [mul_smul]
  by_contra hnot
  have hδneg : ¬ 0 < height (ρ₀⁻¹ • (x • α)) := fun h => hnot ⟨hδα, h⟩
  have hneg := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KernelPos.mem_posRoots_of_neg
    hδα hδneg
  have h1 := hpos _ hneg
  have h2 : f (ρ₀ • (-(ρ₀⁻¹ • (x • α)))) = -height α := by
    dsimp [f]
    rw [smul_neg, smul_inv_smul]; rw [smul_neg, inv_smul_smul, height_neg]
  rw [h2] at h1
  omega

theorem exists_pinned_reeRetwist {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] {ι : Type} {a : ι → Fin ReeTag.F4.tag.rank → Lˣ}
    {hf : ReeTag.F4.ShortFaithful L} {a₀ : ℕ} {h : adjointGroup ReeTag.F4.tag L}
    {F' : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L}
    (hF' : IsReeConj hf a₀ h F') (hM : ∀ g ∈ famM a, F' g ∈ famM a) :
    ∃ m ∈ famM a, ∃ w : WeylGroup ReeTag.F4.tag,
      (∀ g, m⁻¹ * F' (m * g * m⁻¹) * m =
        nrep ReeTag.F4.tag L w * ReeTag.F4.reeEndo L hf a₀ g * (nrep ReeTag.F4.tag L w)⁻¹) ∧
      Set.BijOn (fun α => w • ReeTag.F4.dualRoot α) (familyKernel a) (familyKernel a) ∧
      Set.BijOn (fun α => w • ReeTag.F4.dualRoot α) (posRoots (familyKernel a))
        (posRoots (familyKernel a)) := by
  classical
  have hPerf : PerfectRing L 2 := IsAlgClosed.perfectRing L 2
  have hPerfF4 : PerfectRing L ReeTag.F4.prime := hPerf
  let F : MulAut (adjointGroup ReeTag.F4.tag L) :=
    MulEquiv.ofBijective (ReeTag.F4.reeEndo L hf a₀)
      (reeEndo_bijective (t := ReeTag.F4) (K := L) hf a₀)
  have hF_ree : ∀ g, F g = ReeTag.F4.reeEndo L hf a₀ g := fun g => rfl
  have hFrob : IsReeFrob a₀ F := isReeFrob_of_reeEndo hF_ree
  let Q : adjointGroup ReeTag.F4.tag L := h * (F h)⁻¹
  have hF'_eq : ∀ g, F' g = Q * F g * Q⁻¹ := by
    intro g
    rw [hF' g]
    have hree : ReeTag.F4.reeEndo L hf a₀ (h⁻¹ * g * h) = F (h⁻¹ * g * h) :=
      (hF_ree _).symm
    rw [hree, map_mul, map_mul, map_inv]
    dsimp [Q]
    group
  let MG : Subgroup (ModGL ReeTag.F4.tag L) := familyGroup a
  have hTadj : ∀ t : Fin ReeTag.F4.tag.rank → Lˣ,
      rootDiagUnit ReeTag.F4.tag t ∈ adjointGroup ReeTag.F4.tag L := fun t =>
    CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup (rootDiagUnit_mem_torusGroup t)
  have hF_diag : ∀ t : Fin ReeTag.F4.tag.rank → Lˣ,
      ((F ⟨rootDiagUnit ReeTag.F4.tag t, hTadj t⟩ : adjointGroup ReeTag.F4.tag L) :
        ModGL ReeTag.F4.tag L) = rootDiagUnit ReeTag.F4.tag (reeTuple (L := L) a₀ t) := by
    intro t
    have h := hFrob.fext_rootDiagUnit (L := L) t
    rwa [Fext_of_mem F (hTadj t)] at h
  have hQTor : ∀ t : Fin ReeTag.F4.tag.rank → Lˣ,
      (Q : ModGL ReeTag.F4.tag L) * rootDiagUnit ReeTag.F4.tag t *
        (Q : ModGL ReeTag.F4.tag L)⁻¹ ∈ MG := by
    intro t
    obtain ⟨s, hs⟩ := reeTuple_surjective (L := L) a₀ t
    let ds : adjointGroup ReeTag.F4.tag L := ⟨rootDiagUnit ReeTag.F4.tag s, hTadj s⟩
    have hdsM : ds ∈ famM a :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup s))
    have hFM : F' ds ∈ famM a := hM ds hdsM
    have hcoe : ((F' ds : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
        (Q : ModGL ReeTag.F4.tag L) * rootDiagUnit ReeTag.F4.tag t *
          (Q : ModGL ReeTag.F4.tag L)⁻¹ := by
      rw [hF'_eq ds]
      change (Q : ModGL ReeTag.F4.tag L) *
        ((F ds : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) *
        (Q : ModGL ReeTag.F4.tag L)⁻¹ = _
      rw [hF_diag s, hs]
    rw [← hcoe]
    exact Subgroup.mem_subgroupOf.mp hFM
  let di : ∀ i, ModGL ReeTag.F4.tag L := fun i => rootDiagUnit ReeTag.F4.tag (a i)
  have hdi_mem : ∀ i, di i ∈ MG := fun i =>
    Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup (a i))
  have hdi_central : ∀ i (m : ModGL ReeTag.F4.tag L), m ∈ MG → di i * m * (di i)⁻¹ = m := by
    intro i m hm
    exact (mem_familyCentralizer.1 (familyGroup_le_familyCentralizer (K := L) a hm)).2 i
  have hQinv_adj : ∀ i, (Q : ModGL ReeTag.F4.tag L)⁻¹ * di i * (Q : ModGL ReeTag.F4.tag L) ∈
      adjointGroup ReeTag.F4.tag L := by
    intro i
    exact mul_mem (mul_mem (inv_mem Q.2)
      (CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup
        (rootDiagUnit_mem_torusGroup (a i)))) Q.2
  have hcomm : ∀ i (t : Fin ReeTag.F4.tag.rank → Lˣ),
      Commute ((Q : ModGL ReeTag.F4.tag L)⁻¹ * di i * (Q : ModGL ReeTag.F4.tag L))
        (rootDiagUnit ReeTag.F4.tag t) := by
    intro i t
    have hm : (Q : ModGL ReeTag.F4.tag L) * rootDiagUnit ReeTag.F4.tag t *
        (Q : ModGL ReeTag.F4.tag L)⁻¹ ∈ MG := hQTor t
    have hcent := hdi_central i _ hm
    have hcomm_di : di i * ((Q : ModGL ReeTag.F4.tag L) * rootDiagUnit ReeTag.F4.tag t *
        (Q : ModGL ReeTag.F4.tag L)⁻¹) =
        ((Q : ModGL ReeTag.F4.tag L) * rootDiagUnit ReeTag.F4.tag t *
          (Q : ModGL ReeTag.F4.tag L)⁻¹) * di i := by
      calc di i * ((Q : ModGL ReeTag.F4.tag L) * rootDiagUnit ReeTag.F4.tag t *
            (Q : ModGL ReeTag.F4.tag L)⁻¹)
          = (di i * ((Q : ModGL ReeTag.F4.tag L) * rootDiagUnit ReeTag.F4.tag t *
              (Q : ModGL ReeTag.F4.tag L)⁻¹) * (di i)⁻¹) * di i := by group
        _ = ((Q : ModGL ReeTag.F4.tag L) * rootDiagUnit ReeTag.F4.tag t *
              (Q : ModGL ReeTag.F4.tag L)⁻¹) * di i := by rw [hcent]
    rw [Commute]
    calc ((Q : ModGL ReeTag.F4.tag L)⁻¹ * di i * (Q : ModGL ReeTag.F4.tag L)) *
          rootDiagUnit ReeTag.F4.tag t
        = (Q : ModGL ReeTag.F4.tag L)⁻¹ *
            (di i * ((Q : ModGL ReeTag.F4.tag L) * rootDiagUnit ReeTag.F4.tag t *
              (Q : ModGL ReeTag.F4.tag L)⁻¹)) * (Q : ModGL ReeTag.F4.tag L) := by group
      _ = (Q : ModGL ReeTag.F4.tag L)⁻¹ *
            (((Q : ModGL ReeTag.F4.tag L) * rootDiagUnit ReeTag.F4.tag t *
              (Q : ModGL ReeTag.F4.tag L)⁻¹) * di i) * (Q : ModGL ReeTag.F4.tag L) := by
            rw [hcomm_di]
      _ = rootDiagUnit ReeTag.F4.tag t *
            ((Q : ModGL ReeTag.F4.tag L)⁻¹ * di i * (Q : ModGL ReeTag.F4.tag L)) := by group
  have hQtorus : ∀ i, (Q : ModGL ReeTag.F4.tag L)⁻¹ * di i * (Q : ModGL ReeTag.F4.tag L) ∈
      torusGroup ReeTag.F4.tag L := fun i =>
    mem_torusGroup_of_forall_commute_rootDiagUnit (hQinv_adj i) (hcomm i)
  choose b hb using fun i =>
    CFSG.LieType.Chevalley.exists_rootDiagUnit_eq_of_mem_torusGroup (hQtorus i)
  have hconj_b : ∀ i, (Q : ModGL ReeTag.F4.tag L) * rootDiagUnit ReeTag.F4.tag (b i) *
      (Q : ModGL ReeTag.F4.tag L)⁻¹ = di i := by
    intro i
    rw [← hb i]
    group
  obtain ⟨w₀, hw₀⟩ := exists_weyl_of_conj_family ReeTag.F4.tag L a b Q.2 hconj_b
  let nw₀ : ModGL ReeTag.F4.tag L := canonicalRep (coxeterSystem ReeTag.F4.tag) L w₀
  have hnw₀_adj : nw₀ ∈ adjointGroup ReeTag.F4.tag L :=
    canonicalRep_mem_adjointGroup _ L w₀
  have hQnw_adj : (Q : ModGL ReeTag.F4.tag L) * nw₀⁻¹ ∈ adjointGroup ReeTag.F4.tag L :=
    mul_mem Q.2 (inv_mem hnw₀_adj)
  have hQnw_cent : (Q : ModGL ReeTag.F4.tag L) * nw₀⁻¹ ∈ familyCentralizer ReeTag.F4.tag L a := by
    rw [mem_familyCentralizer]
    refine ⟨hQnw_adj, fun i => ?_⟩
    have h1 : (Q : ModGL ReeTag.F4.tag L)⁻¹ * di i * (Q : ModGL ReeTag.F4.tag L) =
        nw₀⁻¹ * di i * nw₀ := by
      calc (Q : ModGL ReeTag.F4.tag L)⁻¹ * di i * (Q : ModGL ReeTag.F4.tag L)
          = rootDiagUnit ReeTag.F4.tag (b i) := hb i
        _ = nw₀⁻¹ * di i * nw₀ := by
            rw [show di i = rootDiagUnit ReeTag.F4.tag (a i) from rfl]
            dsimp [nw₀]
            rw [hw₀ i]
            group
    have hcomm1 : di i * (Q : ModGL ReeTag.F4.tag L) * nw₀⁻¹ =
        (Q : ModGL ReeTag.F4.tag L) * nw₀⁻¹ * di i := by
      calc di i * (Q : ModGL ReeTag.F4.tag L) * nw₀⁻¹
          = (Q : ModGL ReeTag.F4.tag L) *
              ((Q : ModGL ReeTag.F4.tag L)⁻¹ * di i * (Q : ModGL ReeTag.F4.tag L)) * nw₀⁻¹ := by
              group
        _ = (Q : ModGL ReeTag.F4.tag L) * (nw₀⁻¹ * di i * nw₀) * nw₀⁻¹ := by rw [h1]
        _ = (Q : ModGL ReeTag.F4.tag L) * nw₀⁻¹ * di i := by group
    calc di i * ((Q : ModGL ReeTag.F4.tag L) * nw₀⁻¹) * (di i)⁻¹
        = di i * (Q : ModGL ReeTag.F4.tag L) * nw₀⁻¹ * (di i)⁻¹ := by group
      _ = ((Q : ModGL ReeTag.F4.tag L) * nw₀⁻¹ * di i) * (di i)⁻¹ := by rw [hcomm1]
      _ = (Q : ModGL ReeTag.F4.tag L) * nw₀⁻¹ := by group
  obtain ⟨u, hu, m₀, hm₀, hQeq⟩ := familyCentralizer_le_mul ReeTag.F4.tag L a hQnw_cent
  let v : WeylGroup ReeTag.F4.tag := u * w₀
  let nv : ModGL ReeTag.F4.tag L := canonicalRep (coxeterSystem ReeTag.F4.tag) L v
  have hnv_eq : nv = canonicalRep (coxeterSystem ReeTag.F4.tag) L u * nw₀ := by
    dsimp [nv, v, nw₀]
    rw [CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_charTwo]
  have hQeq' : (Q : ModGL ReeTag.F4.tag L) =
      (m₀ * canonicalRep (coxeterSystem ReeTag.F4.tag) L u) * nw₀ := by
    calc (Q : ModGL ReeTag.F4.tag L)
        = ((Q : ModGL ReeTag.F4.tag L) * nw₀⁻¹) * nw₀ := by group
      _ = (m₀ * canonicalRep (coxeterSystem ReeTag.F4.tag) L u) * nw₀ := by rw [hQeq]
  have hQeq_v : (Q : ModGL ReeTag.F4.tag L) = m₀ * nv := by
    rw [hQeq', hnv_eq]
    group
  have hm₀_adj : m₀ ∈ adjointGroup ReeTag.F4.tag L := by
    have hle : familyGroup a ≤ adjointGroup ReeTag.F4.tag L := by
      rw [familyGroup]
      exact sup_le (CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup)
        (rootSpan_le_adjointGroup L (familyKernel a))
    exact hle hm₀
  let mG : adjointGroup ReeTag.F4.tag L := ⟨m₀, hm₀_adj⟩
  have hmG : mG ∈ famM a := Subgroup.mem_subgroupOf.mpr hm₀
  let nvG : adjointGroup ReeTag.F4.tag L := nrep ReeTag.F4.tag L v
  have hnvG_coe : (nvG : ModGL ReeTag.F4.tag L) = nv := rfl
  have hQeq_G : Q = mG * nvG := by
    apply Subtype.ext
    change (Q : ModGL ReeTag.F4.tag L) = m₀ * nv
    exact hQeq_v
  have hsigma_eq : ∀ g : adjointGroup ReeTag.F4.tag L,
      nvG * F g * nvG⁻¹ = mG⁻¹ * F' g * mG := by
    intro g
    rw [hF'_eq g, hQeq_G]
    group
  have hM_u : ∀ g ∈ famM a, nvG * F g * nvG⁻¹ ∈ famM a := by
    intro g hg
    rw [hsigma_eq g]
    exact mul_mem (mul_mem (inv_mem hmG) (hM g hg)) hmG
  have hM_u_ree : ∀ g ∈ famM a,
      nvG * ReeTag.F4.reeEndo L hf a₀ g * nvG⁻¹ ∈ famM a := by
    intro g hg
    rw [← hF_ree g]
    exact hM_u g hg
  obtain ⟨z, hzM, hz⟩ := exists_reeLang_famM hf a₀ nvG hM_u_ree hmG
  rw [← hF_ree z] at hz
  have hvDual : ∀ α ∈ familyKernel a, v • ReeTag.F4.dualRoot α ∈ familyKernel a := by
    intro α hα
    let X : adjointGroup ReeTag.F4.tag L :=
      ⟨pinnedX ReeTag.F4.tag L α 1, pinnedX_mem_adjointGroup α 1⟩
    have hXM : X ∈ famM a := Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_sup_right (pinnedX_mem_rootSpan hα 1))
    have hFXM : nvG * F X * nvG⁻¹ ∈ famM a := by
      rw [hsigma_eq X]
      exact mul_mem (mul_mem (inv_mem hmG) (hM X hXM)) hmG
    have hconjX : nvG * F X * nvG⁻¹ =
        ⟨pinnedX ReeTag.F4.tag L (v • ReeTag.F4.dualRoot α) 1,
          pinnedX_mem_adjointGroup _ 1⟩ := by
      apply Subtype.ext
      change (nv : ModGL ReeTag.F4.tag L) *
        ((F X : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) * nv⁻¹ =
        pinnedX ReeTag.F4.tag L (v • ReeTag.F4.dualRoot α) 1
      have hXcoe : ((F X : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
          Fext F (pinnedX ReeTag.F4.tag L α 1) := by
        rw [Fext_of_mem F (pinnedX_mem_adjointGroup α 1)]
      rw [hXcoe]
      simpa using hFrob.twist_pinnedX (L := L) (a := a₀) (n := nv) (w := v)
        (permAct_canonicalRep v) hα.1 1
    have hXfam : (⟨pinnedX ReeTag.F4.tag L (v • ReeTag.F4.dualRoot α) 1,
        pinnedX_mem_adjointGroup _ 1⟩ : adjointGroup ReeTag.F4.tag L) ∈ famM a := by
      rw [← hconjX]
      exact hFXM
    have hroot : IsRoot ReeTag.F4.tag (v • ReeTag.F4.dualRoot α) :=
      IsRoot.smul (ReeTag.isRoot_dualRoot hα.1) v
    refine ⟨hroot, fun i => ?_⟩
    have hcomm_i : Commute (di i) (pinnedX ReeTag.F4.tag L (v • ReeTag.F4.dualRoot α) 1) := by
      have hcent := hdi_central i _ (Subgroup.mem_subgroupOf.mp hXfam)
      rw [Commute]
      calc di i * pinnedX ReeTag.F4.tag L (v • ReeTag.F4.dualRoot α) 1
          = (di i * pinnedX ReeTag.F4.tag L (v • ReeTag.F4.dualRoot α) 1 * (di i)⁻¹) * di i := by
              group
        _ = pinnedX ReeTag.F4.tag L (v • ReeTag.F4.dualRoot α) 1 * di i := by rw [hcent]
    exact rootChar_eq_one_of_commute_rootDiagUnit_pinnedX (a i) hroot hcomm_i
  let S : Set (Fin ReeTag.F4.tag.rank → ℤ) := ReeTag.F4.dualRoot '' familyKernel a
  have hfin : (familyKernel a).Finite :=
    (finite_setOf_isRoot ReeTag.F4.tag).subset fun α hα => hα.1
  have hSfin : S.Finite := hfin.image _
  have hmapv : Set.MapsTo (fun α => v • α) S (familyKernel a) := by
    rintro _ ⟨β, hβ, rfl⟩
    exact hvDual β hβ
  have hinjv : Set.InjOn (fun α => v • α) S := fun a _ b _ h => smul_left_cancel v h
  have hcardS : S.ncard = (familyKernel a).ncard := by
    refine Set.ncard_congr (fun α _ => ReeTag.F4.dualRoot α) ?_ ?_ ?_
    · rintro _ ⟨β, hβ, rfl⟩
      rw [ReeTag.dualRoot_dualRoot hβ.1]
      exact hβ
    · intro a b ha hb h
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      rw [ReeTag.dualRoot_dualRoot ha'.1, ReeTag.dualRoot_dualRoot hb'.1] at h
      rw [h]
    · intro β hβ
      exact ⟨ReeTag.F4.dualRoot β, ⟨β, hβ, rfl⟩, ReeTag.dualRoot_dualRoot hβ.1⟩
  have himage : (fun α => v • α) '' S = familyKernel a := by
    have hsub : (fun α => v • α) '' S ⊆ familyKernel a := by
      rintro _ ⟨α, hα, rfl⟩
      exact hmapv hα
    refine Set.eq_of_subset_of_ncard_le hsub ?_ hfin
    rw [Set.ncard_image_of_injective S (MulAction.injective v), hcardS]
  have hx_bij : Set.BijOn (fun α => v • α) S (familyKernel a) := by
    refine ⟨hmapv, hinjv, ?_⟩
    intro β hβ
    have hβ' : β ∈ (fun α => v • α) '' S := by rw [himage]; exact hβ
    exact hβ'
  have hx_bij' : Set.BijOn (fun α => v • α) S (kernelRoots (familyChar a)) := by
    simpa [kernelRoots_familyChar] using hx_bij
  obtain ⟨ρ, hρW, hρpos⟩ := exists_mul_smul_mem_posRoots_of_bijOn (χ := familyChar a) hx_bij'
  have hρchar : ρ ∈ charStabilizer (familyChar a) := kernelWeylGroup_le hρW
  let nρ : ModGL ReeTag.F4.tag L := canonicalRep (coxeterSystem ReeTag.F4.tag) L ρ
  have hnρ_adj : nρ ∈ adjointGroup ReeTag.F4.tag L := canonicalRep_mem_adjointGroup _ L ρ
  let nρG : adjointGroup ReeTag.F4.tag L := nrep ReeTag.F4.tag L ρ
  have hnρG_coe : (nρG : ModGL ReeTag.F4.tag L) = nρ := rfl
  have hnρM : nρG ∈ famM a := by
    have hρU : ρ ∈ unionWeylGroup (familyChar a)
        (Set.univ : Set (KernelComponent (familyChar a))) := by
      rw [← kernelWeylGroup_eq_unionWeylGroup]
      exact hρW
    have hnρ_span : nρ ∈ rootSpan ReeTag.F4.tag L
        (unionRoots (familyChar a) Set.univ) := canonicalRep_mem_rootSpan_unionRoots hρU
    have hroot : nρ ∈ rootSpan ReeTag.F4.tag L (familyKernel a) := by
      rw [CFSG.LieType.AlgebraicGroups.unionRoots_univ_eq_kernelRoots (χ := familyChar a),
        kernelRoots_familyChar] at hnρ_span
      exact hnρ_span
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right hroot)
  obtain ⟨z', hz'M, hz'⟩ := exists_reeLang_famM hf a₀ nvG hM_u_ree hnρM
  rw [← hF_ree z'] at hz'
  let m : adjointGroup ReeTag.F4.tag L := z⁻¹ * z'
  have hmM : m ∈ famM a := mul_mem (inv_mem hzM) hz'M
  let σ : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L :=
    (MulAut.conj nvG).toMonoidHom.comp F.toMonoidHom
  have hσ_apply : ∀ g, σ g = nvG * F g * nvG⁻¹ := fun g => rfl
  have hzσ : z⁻¹ * σ z = mG := by simpa [σ] using hz
  have hz'σ : z'⁻¹ * σ z' = nρG := by simpa [σ] using hz'
  have hσz : σ z = z * mG := by
    calc σ z = z * (z⁻¹ * σ z) := by group
      _ = z * mG := by rw [hzσ]
  have hσz' : σ z' = z' * nρG := by
    calc σ z' = z' * (z'⁻¹ * σ z') := by group
      _ = z' * nρG := by rw [hz'σ]
  have hF'_σ : ∀ g, F' g = mG * σ g * mG⁻¹ := by
    intro g
    rw [hF'_eq g, hQeq_G]
    rfl
  have hF'_C : ∀ g, F' g = z⁻¹ * σ (z * g * z⁻¹) * z := by
    intro g
    rw [hF'_σ g]
    calc mG * σ g * mG⁻¹
        = (z⁻¹ * σ z) * σ g * (z⁻¹ * σ z)⁻¹ := by rw [← hzσ]
      _ = z⁻¹ * σ (z * g * z⁻¹) * z := by
          rw [map_mul, map_mul, map_inv]
          group
  have hmconj : ∀ g, m⁻¹ * F' (m * g * m⁻¹) * m =
      nρG * (nvG * F g * nvG⁻¹) * nρG⁻¹ := by
    intro g
    rw [hF'_C]
    have hstep : m⁻¹ * (z⁻¹ * σ (z * (m * g * m⁻¹) * z⁻¹) * z) * m =
        z'⁻¹ * σ (z' * g * z'⁻¹) * z' := by
      dsimp [m]
      group
    rw [hstep]
    calc z'⁻¹ * σ (z' * g * z'⁻¹) * z'
        = z'⁻¹ * (σ z' * σ g * (σ z')⁻¹) * z' := by rw [map_mul, map_mul, map_inv]
      _ = nρG * σ g * nρG⁻¹ := by rw [hσz']; group
      _ = nρG * (nvG * F g * nvG⁻¹) * nρG⁻¹ := rfl
  have hnρnv : nρG * nvG = nrep ReeTag.F4.tag L (ρ * v) := by
    apply Subtype.ext
    change nρ * nv = canonicalRep (coxeterSystem ReeTag.F4.tag) L (ρ * v)
    dsimp [nρ, nv, v]
    simp only [CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_charTwo]
  refine ⟨m, hmM, ρ * v, ?_, ?_, ?_⟩
  · intro g
    rw [hmconj g, ← hnρnv]
    simp only [hF_ree]
    group
  · have hmap : Set.MapsTo (fun α => (ρ * v) • ReeTag.F4.dualRoot α)
        (familyKernel a) (familyKernel a) := by
      intro α hα
      change (ρ * v) • ReeTag.F4.dualRoot α ∈ familyKernel a
      rw [mul_smul]
      have h : v • ReeTag.F4.dualRoot α ∈ kernelRoots (familyChar a) := by
        rw [kernelRoots_familyChar]
        exact hvDual α hα
      have h2 := smul_mem_kernelRoots hρchar h
      rwa [kernelRoots_familyChar] at h2
    have hinj : Set.InjOn (fun α => (ρ * v) • ReeTag.F4.dualRoot α) (familyKernel a) := by
      intro α hα β hβ h
      have h' : ReeTag.F4.dualRoot α = ReeTag.F4.dualRoot β := smul_left_cancel (ρ * v) h
      calc α = ReeTag.F4.dualRoot (ReeTag.F4.dualRoot α) := (ReeTag.dualRoot_dualRoot hα.1).symm
        _ = ReeTag.F4.dualRoot (ReeTag.F4.dualRoot β) := by rw [h']
        _ = β := ReeTag.dualRoot_dualRoot hβ.1
    exact (hfin.injOn_iff_bijOn_of_mapsTo hmap).1 hinj
  · have hmap : Set.MapsTo (fun α => (ρ * v) • ReeTag.F4.dualRoot α)
        (posRoots (familyKernel a)) (posRoots (familyKernel a)) := by
      intro α hα
      have hS : ReeTag.F4.dualRoot α ∈ S := ⟨α, hα.1, rfl⟩
      have hSpos : 0 < height (ReeTag.F4.dualRoot α) :=
        (ReeTag.height_dualRoot_pos_iff hα.1.1).2 hα.2
      have h := hρpos (ReeTag.F4.dualRoot α) hS hSpos
      rwa [kernelRoots_familyChar] at h
    have hinj : Set.InjOn (fun α => (ρ * v) • ReeTag.F4.dualRoot α)
        (posRoots (familyKernel a)) := by
      intro α hα β hβ h
      have h' : ReeTag.F4.dualRoot α = ReeTag.F4.dualRoot β := smul_left_cancel (ρ * v) h
      calc α = ReeTag.F4.dualRoot (ReeTag.F4.dualRoot α) :=
            (ReeTag.dualRoot_dualRoot hα.1.1).symm
        _ = ReeTag.F4.dualRoot (ReeTag.F4.dualRoot β) := by rw [h']
        _ = β := ReeTag.dualRoot_dualRoot hβ.1.1
    have hposfin : (posRoots (familyKernel a)).Finite := hfin.subset fun α hα => hα.1
    exact (hposfin.injOn_iff_bijOn_of_mapsTo hmap).1 hinj

end CFSG.HardMathSupport.C14Idx
