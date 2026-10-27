module

public import CFSG.RankThree.PartOne.KLR.TwistPerm
public import CFSG.RankThree.PartOne.TCX.Ree.Closure
public import CFSG.HardMathSupport.C14IdxReeSimple
public import CFSG.HardMathSupport.C14IdxFixedBruhat
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5SpinCoords
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5TorusGen
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover
public import CFSG.LieType.AlgebraicGroups.KernelRootBruhat
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR
  CFSG.RankThree.PartOne.TCX.Ree CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.SeitzReduction
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen (coordTuple)

open scoped Pointwise

private lemma canonicalRep_inv_charTwo
    {K : Type} [Field K] [CharP K 2]
    (w : WeylGroup ReeTag.F4.tag) :
    canonicalRep (coxeterSystem ReeTag.F4.tag) K w⁻¹ =
      (canonicalRep (coxeterSystem ReeTag.F4.tag) K w)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_charTwo,
    inv_mul_cancel, canonicalRep_one]

theorem exists_reeTwistFixed_bruhat_factor {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin ReeTag.F4.tag.rank → ℤ) →* M} {a₀ : ℕ}
    {F : MulAut (adjointGroup ReeTag.F4.tag L)} (hF : IsReeFrob a₀ F)
    {w : WeylGroup ReeTag.F4.tag}
    (hΨ : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α) (kernelRoots χ) (kernelRoots χ))
    (hΨp : Set.BijOn (fun α => w • ReeTag.F4.dualRoot α) (posRoots (kernelRoots χ))
      (posRoots (kernelRoots χ)))
    {s : ModGL ReeTag.F4.tag L} (hs : s ∈ unionRootSpan L χ Set.univ)
    (hσ : s ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) :
    ∃ x ∈ unionWeylGroup χ Set.univ,
      (∀ α ∈ kernelRoots χ, w • ReeTag.F4.dualRoot (x • α) = x • (w • ReeTag.F4.dualRoot α)) ∧
      ∃ t ∈ unionTorus L χ Set.univ,
        t ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
      ∃ u ∈ unionUnipotent L χ Set.univ,
        u ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
      ∃ v ∈ unionUnipotent L χ Set.univ,
        v ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
      s = t * u * canonicalRep (coxeterSystem ReeTag.F4.tag) L x * v := by
  classical
  let τ := ReeTag.F4.tag
  let θ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ := fun α => w • ReeTag.F4.dualRoot α
  have hθΨ : Set.BijOn θ (kernelRoots χ) (kernelRoots χ) := hΨ
  have hθΨp : Set.BijOn θ (posRoots (kernelRoots χ)) (posRoots (kernelRoots χ)) := hΨp
  have hθΔ : Set.BijOn θ (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ))
      (simpleRoots (kernelRoots χ) : Set (Fin τ.rank → ℤ)) :=
    bijOn_simpleRoots_of_reeTwist hΨ hΨp
  let n : (Fin τ.rank → ℤ) → ModGL τ L :=
    fun β => canonicalRep (coxeterSystem τ) L (rootReflection β)
  have hnmem : ∀ β ∈ unionSimpleRoots χ Set.univ,
      n β ∈ rootSubgroup τ L β ⊔ rootSubgroup τ L (-β) := by
    intro β hβ
    have hβr := isRoot_of_mem_unionSimpleRoots hβ
    dsimp only [n]
    rw [canonicalRep_rootReflection_eq_charTwo hβr]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (mem_rootSubgroup.2 ⟨1, rfl⟩))
      (Subgroup.mem_sup_right (mem_rootSubgroup.2 ⟨1, rfl⟩)))
      (Subgroup.mem_sup_left (mem_rootSubgroup.2 ⟨1, rfl⟩))
  have hn : ∀ β ∈ unionSimpleRoots χ Set.univ, n β ∈ rootSubgroup τ L β ⊔
      rootSubgroup τ L (-β) ∧ n β ∈ monomialSubgroup τ L ∧
      MapsRootLines (n β) (rootReflection β) :=
    fun β hβ => ⟨hnmem β hβ, canonicalRep_mem_monomialSubgroup L _,
      mapsRootLines_canonicalRep (R := L) (rootReflection β)⟩
  obtain ⟨-, hcellEq, hcover, hdisj, hbij, hB, huniq, -, -, -⟩ :=
    orthogonal_union_Bruhat_cell_factorization τ L χ Set.univ n hn
  have hsin : s ∈ ⋃ x ∈ unionWeylGroup χ Set.univ, unionCell L χ Set.univ n x := by
    rw [← hcover]
    exact hs
  rw [Set.mem_iUnion] at hsin
  obtain ⟨x, hsin⟩ := hsin
  rw [Set.mem_iUnion] at hsin
  obtain ⟨hx, hsx⟩ := hsin
  let nx : ModGL τ L := canonicalRep (coxeterSystem τ) L x
  have hmono : ∀ v ∈ unionWeylGroup χ Set.univ,
      canonicalRep (coxeterSystem τ) L v ∈ unionMonomial L χ Set.univ n := by
    intro v hv
    induction hv using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨β, hβ, rfl⟩ := hy
      exact lift_mem_unionMonomial hβ
    | one =>
      rw [canonicalRep_one]
      exact one_mem _
    | mul y z _ _ hy hz =>
      rw [CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_charTwo]
      exact mul_mem hy hz
    | inv y _ hy =>
      rw [canonicalRep_inv_charTwo]
      exact inv_mem hy
  have hliftx : nx ∈ unionLifts L χ Set.univ n x :=
    ⟨hmono x hx, mapsRootLines_canonicalRep (R := L) x⟩
  let nw : ModGL τ L := canonicalRep (coxeterSystem τ) L w
  have hnwAdj : nw ∈ adjointGroup τ L := canonicalRep_mem_adjointGroup _ L w
  let nwAdj : adjointGroup τ L := ⟨nw, hnwAdj⟩
  let σ : MulAut (adjointGroup τ L) := MulAut.conj nwAdj * F
  have hσ_coe : ∀ y : adjointGroup τ L,
      (σ y : ModGL τ L) = nw * Fext F y * nw⁻¹ := by
    rintro ⟨v, hv⟩
    dsimp only [σ, nwAdj]
    rw [MulAut.mul_apply, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Fext_of_mem F hv]
  let x' : WeylGroup τ := w * ReeTag.F4.weylPerm x * w⁻¹
  have hweyl_refl : ∀ {β : Fin τ.rank → ℤ}, IsRoot τ β →
      ReeTag.F4.weylPerm (rootReflection β) = rootReflection (ReeTag.F4.dualRoot β) := by
    intro β hβ
    obtain ⟨u, j, rfl⟩ := isRoot_iff_exists_smul_single.1 hβ
    rw [rootReflection_eq_conj (w := u) (j := j) rfl]
    rw [map_mul, map_mul, map_inv, ReeTag.weylPerm_simple]
    rw [ReeTag.dualRoot_smul u (isRoot_single τ j), ReeTag.dualRoot_single]
    rw [rootReflection_eq_conj (w := ReeTag.F4.weylPerm u) (j := ReeTag.F4.perm j) rfl]
  have hx' : x' ∈ unionWeylGroup χ Set.univ := by
    have hstep : ∀ v ∈ unionWeylGroup χ Set.univ,
        w * ReeTag.F4.weylPerm v * w⁻¹ ∈ unionWeylGroup χ Set.univ := by
      intro v hv
      induction hv using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨β, hβ, rfl⟩ := hy
        have hβs : β ∈ simpleRoots (kernelRoots χ) := by
          have h := (mem_simpleRoots_unionRoots_iff (J := Set.univ)).2 hβ
          rwa [unionRoots_univ_eq_kernelRoots] at h
        have hθβs : θ β ∈ simpleRoots (kernelRoots χ) := hθΔ.mapsTo hβs
        have hθβ : θ β ∈ unionSimpleRoots χ Set.univ := by
          refine (mem_simpleRoots_unionRoots_iff (J := Set.univ)).1 ?_
          rwa [unionRoots_univ_eq_kernelRoots]
        have hβr : IsRoot τ β := isRoot_of_mem_unionSimpleRoots hβ
        rw [hweyl_refl hβr]
        rw [← rootReflection_smul_root w (ReeTag.isRoot_dualRoot hβr)]
        exact rootReflection_mem_unionWeylGroup hθβ
      | one => simp
      | mul y z _ _ hy hz =>
        rw [map_mul]
        have e : w * (ReeTag.F4.weylPerm y * ReeTag.F4.weylPerm z) * w⁻¹ =
            (w * ReeTag.F4.weylPerm y * w⁻¹) * (w * ReeTag.F4.weylPerm z * w⁻¹) := by
          group
        rw [e]
        exact mul_mem hy hz
      | inv y _ hy =>
        rw [map_inv]
        have e : w * (ReeTag.F4.weylPerm y)⁻¹ * w⁻¹ =
            (w * ReeTag.F4.weylPerm y * w⁻¹)⁻¹ := by
          group
        rw [e]
        exact inv_mem hy
    exact hstep x hx
  have hσ_rootSpan : ∀ {S : Set (Fin τ.rank → ℤ)}, (∀ α ∈ S, IsRoot τ α) →
      ∀ y : adjointGroup τ L, (y : ModGL τ L) ∈ rootSpan τ L S →
        (σ y : ModGL τ L) ∈ rootSpan τ L (θ '' S) := by
    intro S hS y hy
    refine coe_mulAut_mem_rootSpan (F := σ) (S' := θ '' S) ?_ hy
    intro γ hγ x hx
    have hγr : IsRoot τ γ := hS γ hγ
    have hdγr : IsRoot τ (ReeTag.F4.dualRoot γ) := ReeTag.isRoot_dualRoot hγr
    have hFx : (F x : ModGL τ L) ∈ rootSubgroup τ L (ReeTag.F4.dualRoot γ) :=
      hF.mem_rootSubgroup hγr hx
    have hFx' : (F x : ModGL τ L) ∈ rootSpan τ L ({ReeTag.F4.dualRoot γ} : Set _) := by
      rwa [rootSpan_singleton]
    have hconj := conj_mem_rootSpan_of_mapsRootLines
      (canonicalRep_mem_monomialSubgroup L w) (mapsRootLines_canonicalRep (R := L) w)
      (S := {ReeTag.F4.dualRoot γ}) (fun α hα => by
        rw [Set.mem_singleton_iff.1 hα]; exact hdγr) hFx'
    have hconj' : nw * (F x : ModGL τ L) * nw⁻¹ ∈
        rootSubgroup τ L (w • ReeTag.F4.dualRoot γ) := by
      rwa [Set.image_singleton, rootSpan_singleton] at hconj
    have hσx : (σ x : ModGL τ L) = nw * (F x : ModGL τ L) * nw⁻¹ := by
      rw [hσ_coe x, Fext_of_mem F x.2]
    rw [hσx]
    exact le_iSup₂_of_le (f := fun β (_ : β ∈ θ '' S) => rootSubgroup τ L β)
      (θ γ) ⟨γ, hγ, rfl⟩ le_rfl hconj'
  have hmapS : ∀ y : adjointGroup τ L, (y : ModGL τ L) ∈ rootSpan τ L (kernelRoots χ) →
      (σ y : ModGL τ L) ∈ rootSpan τ L (kernelRoots χ) := by
    intro y hy
    have h := hσ_rootSpan (S := kernelRoots χ) (fun α hα => hα.1) y hy
    rwa [hθΨ.image_eq] at h
  have hmapU : ∀ y : adjointGroup τ L,
      (y : ModGL τ L) ∈ rootSpan τ L (posRoots (kernelRoots χ)) →
        (σ y : ModGL τ L) ∈ rootSpan τ L (posRoots (kernelRoots χ)) := by
    intro y hy
    have h := hσ_rootSpan (S := posRoots (kernelRoots χ)) (fun α hα => hα.1.1) y hy
    rwa [hθΨp.image_eq] at h
  have hθpos_iff : ∀ {γ : Fin τ.rank → ℤ}, γ ∈ kernelRoots χ →
      (θ γ ∈ posRoots (kernelRoots χ) ↔ γ ∈ posRoots (kernelRoots χ)) := by
    intro γ hγ
    constructor
    · intro h
      obtain ⟨δ, hδ, hδθ⟩ := hθΨp.surjOn h
      have hδγ : δ = γ := hθΨ.injOn hδ.1 hγ hδθ
      rwa [hδγ] at hδ
    · intro h
      exact hθΨp.mapsTo h
  have hneg_of_not_pos : ∀ {γ : Fin τ.rank → ℤ}, γ ∈ kernelRoots χ →
      γ ∉ posRoots (kernelRoots χ) → height γ < 0 := by
    intro γ hγ hnot
    rcases IsRoot.height_pos_or_neg hγ.1 with h | h
    · exact absurd ⟨hγ, h⟩ hnot
    · exact h
  have hθ_smul : ∀ {γ : Fin τ.rank → ℤ} (hγ : γ ∈ kernelRoots χ),
      θ (x • γ) = x' • θ γ := by
    intro γ hγ
    have h1 : θ (x • γ) = w • ReeTag.F4.dualRoot (x • γ) := rfl
    have h2 : ReeTag.F4.dualRoot (x • γ) = ReeTag.F4.weylPerm x • ReeTag.F4.dualRoot γ :=
      ReeTag.dualRoot_smul x hγ.1
    have h3 : w • (ReeTag.F4.weylPerm x • ReeTag.F4.dualRoot γ) =
        (w * ReeTag.F4.weylPerm x) • ReeTag.F4.dualRoot γ := (mul_smul w _ _).symm
    have h4 : x' • θ γ = (w * ReeTag.F4.weylPerm x) • ReeTag.F4.dualRoot γ := by
      dsimp only [x', θ]
      simp only [mul_smul, inv_smul_smul]
    rw [h1, h2, h3, h4]
  have hIeq : θ '' unionInversionRoots χ Set.univ x =
      unionInversionRoots χ Set.univ x' := by
    ext α
    constructor
    · rintro ⟨β, hβ, rfl⟩
      change β ∈ posRoots (unionRoots χ Set.univ) ∧ height (x • β) < 0 at hβ
      change θ β ∈ posRoots (unionRoots χ Set.univ) ∧ height (x' • θ β) < 0
      have hβΨp : β ∈ posRoots (kernelRoots χ) := by
        have h := hβ.1
        rwa [unionRoots_univ_eq_kernelRoots] at h
      have hβroot : β ∈ kernelRoots χ := hβΨp.1
      have hxβroot : x • β ∈ kernelRoots χ := by
        rw [← unionRoots_univ_eq_kernelRoots]
        exact smul_mem_unionRoots hx hβ.1.1
      have hxβnot : x • β ∉ posRoots (kernelRoots χ) := fun hp => (not_lt.mpr hβ.2.le) hp.2
      have hθxβnot : θ (x • β) ∉ posRoots (kernelRoots χ) :=
        fun h => hxβnot ((hθpos_iff hxβroot).1 h)
      have hneg : height (θ (x • β)) < 0 :=
        hneg_of_not_pos (hθΨ.mapsTo hxβroot) hθxβnot
      refine ⟨?_, ?_⟩
      · rw [unionRoots_univ_eq_kernelRoots]
        exact hθΨp.mapsTo hβΨp
      · rwa [← hθ_smul hβroot]
    · intro hα
      change α ∈ posRoots (unionRoots χ Set.univ) ∧ height (x' • α) < 0 at hα
      have hαΨp : α ∈ posRoots (kernelRoots χ) := by
        have h := hα.1
        rwa [unionRoots_univ_eq_kernelRoots] at h
      obtain ⟨β, hβp, hβα⟩ := hθΨp.surjOn hαΨp
      have hβroot : β ∈ kernelRoots χ := hβp.1
      have hxβroot : x • β ∈ kernelRoots χ := by
        rw [← unionRoots_univ_eq_kernelRoots]
        exact smul_mem_unionRoots hx (by
          rw [unionRoots_univ_eq_kernelRoots]
          exact hβp.1)
      have hθxβ : θ (x • β) = x' • α := by rw [hθ_smul hβroot, hβα]
      have hnot : θ (x • β) ∉ posRoots (kernelRoots χ) := by
        intro hp
        have hp' : 0 < height (x' • α) := by rw [← hθxβ]; exact hp.2
        exact (not_lt.mpr hα.2.le) hp'
      have hxβnot : x • β ∉ posRoots (kernelRoots χ) :=
        fun h => hnot ((hθpos_iff hxβroot).2 h)
      have hneg : height (x • β) < 0 := hneg_of_not_pos hxβroot hxβnot
      refine ⟨β, ?_, hβα⟩
      change β ∈ posRoots (unionRoots χ Set.univ) ∧ height (x • β) < 0
      exact ⟨by rwa [unionRoots_univ_eq_kernelRoots], hneg⟩
  have hmapI : ∀ y : adjointGroup τ L,
      (y : ModGL τ L) ∈ rootSpan τ L (unionInversionRoots χ Set.univ x) →
        (σ y : ModGL τ L) ∈ rootSpan τ L (unionInversionRoots χ Set.univ x') := by
    intro y hy
    have h := hσ_rootSpan (S := unionInversionRoots χ Set.univ x)
      (fun α hα => isRoot_of_mem_unionRoots hα.1.1) y hy
    rwa [hIeq] at h
  have hσT : ∀ y : adjointGroup τ L, (y : ModGL τ L) ∈ unionTorus L χ Set.univ →
      (σ y : ModGL τ L) ∈ unionTorus L χ Set.univ := by
    intro y hy
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have hyS : (y : ModGL τ L) ∈ rootSpan τ L (kernelRoots χ) := by
        rw [← unionRoots_univ_eq_kernelRoots]
        exact hy.1
      have h := hmapS y hyS
      rwa [← unionRoots_univ_eq_kernelRoots] at h
    · obtain ⟨a, hya⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy.2
      have hFy : Fext F (y : ModGL τ L) = rootDiagUnit ReeTag.F4.tag (reeTuple a₀ a) := by
        rw [hya]
        exact hF.fext_rootDiagUnit a
      rw [hσ_coe y, hFy]
      exact (Subgroup.mem_normalizer_iff.1
        (mem_normalizer_torusGroup_of_mem_monomialSubgroup
          (canonicalRep_mem_monomialSubgroup L w))
        (rootDiagUnit ReeTag.F4.tag (reeTuple a₀ a))).1
        (rootDiagUnit_mem_torusGroup _)
  have hσU : ∀ y : adjointGroup τ L, (y : ModGL τ L) ∈ unionUnipotent L χ Set.univ →
      (σ y : ModGL τ L) ∈ unionUnipotent L χ Set.univ := by
    intro y hy
    change (y : ModGL τ L) ∈ rootSpan τ L (posRoots (unionRoots χ Set.univ)) at hy
    rw [unionRoots_univ_eq_kernelRoots] at hy
    change (σ y : ModGL τ L) ∈ rootSpan τ L (posRoots (unionRoots χ Set.univ))
    rw [unionRoots_univ_eq_kernelRoots]
    exact hmapU y hy
  have hσs : (σ ⟨s, unionRootSpan_le_adjointGroup hs⟩ : ModGL τ L) = s := by
    rw [hσ_coe]
    exact hσ.2
  obtain ⟨⟨b, u⟩, ⟨hb, hu⟩, hbu⟩ := (hbij x hx nx hliftx).surjOn
    (by rw [hcellEq x hx nx hliftx]; exact hsx)
  have hbAdj : b ∈ adjointGroup τ L :=
    sup_le (unionTorus_le_unionRootSpan.trans unionRootSpan_le_adjointGroup)
      (unionUnipotent_le_unionRootSpan.trans unionRootSpan_le_adjointGroup) hb
  have huAdj : u ∈ adjointGroup τ L :=
    CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L
      (unionInversionRoots χ Set.univ x) hu
  let b' : adjointGroup τ L := ⟨b, hbAdj⟩
  let u' : adjointGroup τ L := ⟨u, huAdj⟩
  have hσuI : (σ u' : ModGL τ L) ∈ rootSpan τ L (unionInversionRoots χ Set.univ x') :=
    hmapI u' hu
  have hσbB : (σ b' : ModGL τ L) ∈ unionBorel L χ Set.univ := by
    have hbTU : b ∈ (unionTorus L χ Set.univ : Set (ModGL τ L)) *
        (unionUnipotent L χ Set.univ : Set (ModGL τ L)) := by
      rw [← hB]
      exact hb
    obtain ⟨t, ht, u1, hu1, htu⟩ := Set.mem_mul.1 hbTU
    have htAdj : t ∈ adjointGroup τ L :=
      unionTorus_le_unionRootSpan.trans unionRootSpan_le_adjointGroup ht
    have hu1Adj : u1 ∈ adjointGroup τ L :=
      unionUnipotent_le_unionRootSpan.trans unionRootSpan_le_adjointGroup hu1
    let t' : adjointGroup τ L := ⟨t, htAdj⟩
    let u1' : adjointGroup τ L := ⟨u1, hu1Adj⟩
    have hσt : (σ t' : ModGL τ L) ∈ unionTorus L χ Set.univ := hσT t' ht
    have hσu1 : (σ u1' : ModGL τ L) ∈ unionUnipotent L χ Set.univ := hσU u1' hu1
    have hσb_eq : (σ b' : ModGL τ L) = (σ t' : ModGL τ L) * (σ u1' : ModGL τ L) := by
      have hb' : b' = t' * u1' := Subtype.ext (by simpa [t', u1'] using htu.symm)
      rw [hb', map_mul]
      rfl
    rw [hσb_eq]
    exact mul_mem (Subgroup.mem_sup_left hσt) (Subgroup.mem_sup_right hσu1)
  have hσnx : (σ ⟨nx, canonicalRep_mem_adjointGroup _ L x⟩ : ModGL τ L) =
      canonicalRep (coxeterSystem τ) L x' := by
    rw [hσ_coe, hF.fext_canonicalRep]
    dsimp only [nw]
    rw [← CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_charTwo w (ReeTag.F4.weylPerm x),
      ← canonicalRep_inv_charTwo w,
      ← CFSG.QuasithinUnique.Setup.X6.canonicalRep_mul_charTwo
        (w * ReeTag.F4.weylPerm x) w⁻¹]
  have hs_eq : (σ b' : ModGL τ L) * canonicalRep (coxeterSystem τ) L x' *
      (σ u' : ModGL τ L) = s := by
    have hσprod : (σ b' : ModGL τ L) * (σ ⟨nx, canonicalRep_mem_adjointGroup _ L x⟩ :
        ModGL τ L) * (σ u' : ModGL τ L) =
        (σ (⟨b * nx * u, by
          rw [show b * nx * u = s from hbu]
          exact unionRootSpan_le_adjointGroup hs⟩ : adjointGroup τ L) : ModGL τ L) := by
      have e : (⟨b * nx * u, by
          rw [show b * nx * u = s from hbu]
          exact unionRootSpan_le_adjointGroup hs⟩ : adjointGroup τ L) =
          b' * ⟨nx, canonicalRep_mem_adjointGroup _ L x⟩ * u' := rfl
      rw [e, map_mul, map_mul]
      rfl
    rw [← hσnx, hσprod]
    rw [show (⟨b * nx * u, by
        rw [show b * nx * u = s from hbu]
        exact unionRootSpan_le_adjointGroup hs⟩ : adjointGroup τ L) =
        ⟨s, unionRootSpan_le_adjointGroup hs⟩ from Subtype.ext hbu]
    exact hσs
  have hsCell' : s ∈ unionCell L χ Set.univ n x' := by
    rw [← hcellEq x' hx' (canonicalRep (coxeterSystem τ) L x')
      ⟨hmono x' hx', mapsRootLines_canonicalRep (R := L) x'⟩]
    refine Set.mem_mul.2 ⟨(σ b' : ModGL τ L) * canonicalRep (coxeterSystem τ) L x', ?_,
      (σ u' : ModGL τ L), ?_, hs_eq⟩
    · exact Set.mem_mul.2 ⟨(σ b' : ModGL τ L), hσbB,
        canonicalRep (coxeterSystem τ) L x', by simp, rfl⟩
    · exact (le_sup_right : unionUnipotent L χ Set.univ ≤ unionBorel L χ Set.univ)
        (rootSpan_mono (fun α hα => hα.1) hσuI)
  have hxx' : x' = x := by
    by_contra hne
    exact (Set.disjoint_left.1 (hdisj x hx x' hx' (fun h => hne h.symm)) hsx) hsCell'
  rw [hxx'] at hs_eq
  rw [hxx'] at hσuI
  have hσnx' : (σ ⟨nx, canonicalRep_mem_adjointGroup _ L x⟩ : ModGL τ L) = nx := by
    rw [hσnx, hxx']
  have hpair : ((σ b' : ModGL τ L), (σ u' : ModGL τ L)) = (b, u) :=
    (hbij x hx nx hliftx).injOn ⟨hσbB, hσuI⟩ ⟨hb, hu⟩
      (hs_eq.trans hbu.symm)
  have hbfix : (σ b' : ModGL τ L) = b := congrArg Prod.fst hpair
  have hufix : (σ u' : ModGL τ L) = u := congrArg Prod.snd hpair
  have hbTU : b ∈ (unionTorus L χ Set.univ : Set (ModGL τ L)) *
      (unionUnipotent L χ Set.univ : Set (ModGL τ L)) := by
    rw [← hB]
    exact hb
  obtain ⟨t, ht, u1, hu1, htu⟩ := Set.mem_mul.1 hbTU
  have htAdj : t ∈ adjointGroup τ L :=
    unionTorus_le_unionRootSpan.trans unionRootSpan_le_adjointGroup ht
  have hu1Adj : u1 ∈ adjointGroup τ L :=
    unionUnipotent_le_unionRootSpan.trans unionRootSpan_le_adjointGroup hu1
  let t' : adjointGroup τ L := ⟨t, htAdj⟩
  let u1' : adjointGroup τ L := ⟨u1, hu1Adj⟩
  have hσt : (σ t' : ModGL τ L) ∈ unionTorus L χ Set.univ := hσT t' ht
  have hσu1 : (σ u1' : ModGL τ L) ∈ unionUnipotent L χ Set.univ := hσU u1' hu1
  have hσb_eq : (σ b' : ModGL τ L) = (σ t' : ModGL τ L) * (σ u1' : ModGL τ L) := by
    have hb' : b' = t' * u1' := Subtype.ext (by simpa [t', u1'] using htu.symm)
    rw [hb', map_mul]
    rfl
  have hEq : t * u1 = (σ t' : ModGL τ L) * (σ u1' : ModGL τ L) := by
    rw [htu]
    rw [← hbfix]
    exact hσb_eq
  obtain ⟨htfix, hu1fix⟩ := huniq t ht (σ t' : ModGL τ L) hσt u1 hu1
    (σ u1' : ModGL τ L) hσu1 hEq
  have hcomm : ∀ α ∈ kernelRoots χ, w • ReeTag.F4.dualRoot (x • α) =
      x • (w • ReeTag.F4.dualRoot α) := by
    intro α hα
    have h := hθ_smul hα
    rwa [hxx'] at h
  have htuU : u ∈ unionUnipotent L χ Set.univ :=
    rootSpan_mono (fun α hα => hα.1) hu
  refine ⟨x, hx, hcomm, t, ht, ?_, u1, hu1, ?_, u, htuU, ?_, ?_⟩
  · exact ⟨htAdj, by rw [← hσ_coe t']; exact htfix.symm⟩
  · exact ⟨hu1Adj, by rw [← hσ_coe u1']; exact hu1fix.symm⟩
  · exact ⟨huAdj, by rw [← hσ_coe u']; exact hufix⟩
  · rw [← hbu, ← htu]

end CFSG.HardMathSupport.C14Idx
