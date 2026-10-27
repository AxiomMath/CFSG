module

public import CFSG.RankThree.PartOne.KLR.TwistPerm
public import CFSG.HardMathSupport.C14IdxCorootConj
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicRootCenter
public import CFSG.LieType.Chevalley.CharTwoWeylLifts
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.SeitzReduction
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen (coordTuple)


private theorem relExp_perm_eq (a : ℕ) (k : Fin ReeTag.F4.tag.rank) :
    (ReeTag.F4.relationExponent a (ReeTag.F4.perm k) : ℤ) =
      2 ^ a * (if k ∈ ReeTag.F4.longSet then 2 else 1) := by
  have h0 : (0 : Fin ReeTag.F4.tag.rank) ∈ ReeTag.F4.longSet := by decide
  have h1 : (1 : Fin ReeTag.F4.tag.rank) ∈ ReeTag.F4.longSet := by decide
  have h2 : (2 : Fin ReeTag.F4.tag.rank) ∉ ReeTag.F4.longSet := by decide
  have h3 : (3 : Fin ReeTag.F4.tag.rank) ∉ ReeTag.F4.longSet := by decide
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
    fin_cases k <;> decide
  rcases hk with rfl | rfl | rfl | rfl
  · have hp : ReeTag.F4.perm (0 : Fin ReeTag.F4.tag.rank) = 3 := by decide
    have hr : ReeTag.F4.relationExponent a (3 : Fin ReeTag.F4.tag.rank) = 2 ^ (a + 1) :=
      rfl
    rw [hp, hr, if_pos h0, pow_succ]
    push_cast
    ring
  · have hp : ReeTag.F4.perm (1 : Fin ReeTag.F4.tag.rank) = 2 := by decide
    have hr : ReeTag.F4.relationExponent a (2 : Fin ReeTag.F4.tag.rank) = 2 ^ (a + 1) :=
      rfl
    rw [hp, hr, if_pos h1, pow_succ]
    push_cast
    ring
  · have hp : ReeTag.F4.perm (2 : Fin ReeTag.F4.tag.rank) = 1 := by decide
    have hr : ReeTag.F4.relationExponent a (1 : Fin ReeTag.F4.tag.rank) = 2 ^ a := rfl
    rw [hp, hr, if_neg h2]
    push_cast
    ring
  · have hp : ReeTag.F4.perm (3 : Fin ReeTag.F4.tag.rank) = 0 := by decide
    have hr : ReeTag.F4.relationExponent a (0 : Fin ReeTag.F4.tag.rank) = 2 ^ a := rfl
    rw [hp, hr, if_neg h3]
    push_cast
    ring

private theorem rootExp_eq_two_pow_mul (a : ℕ) (β : Fin ReeTag.F4.tag.rank → ℤ) :
    (rootExp a β : ℤ) =
      2 ^ a * (if ReeTag.F4.quadForm β = 2 then 2 else 1) := by
  unfold rootExp
  split_ifs with h
  · rw [pow_succ]
    push_cast
    ring
  · push_cast
    ring

private theorem ree_corootPair_single_aux :
    ∀ v ∈ rootFinset ReeTag.F4.tag, ∀ k : Fin ReeTag.F4.tag.rank,
      (if k ∈ ReeTag.F4.longSet then (2 : ℤ) else 1) *
          corootPair v (Pi.single (ReeTag.F4.perm k) 1) =
        (if ReeTag.F4.quadForm v = 2 then (2 : ℤ) else 1) *
          corootPair (ReeTag.F4.dualRoot v) (Pi.single k 1) := by
  decide +kernel

private theorem ree_corootPair_single (a : ℕ)
    {β : Fin ReeTag.F4.tag.rank → ℤ} (hβ : IsRoot ReeTag.F4.tag β)
    (k : Fin ReeTag.F4.tag.rank) :
    (ReeTag.F4.relationExponent a (ReeTag.F4.perm k) : ℤ) *
        corootPair β (Pi.single (ReeTag.F4.perm k) 1) =
      (rootExp a β : ℤ) * corootPair (ReeTag.F4.dualRoot β) (Pi.single k 1) := by
  have hnum := ree_corootPair_single_aux β (mem_rootFinset.2 hβ) k
  rw [relExp_perm_eq a k, rootExp_eq_two_pow_mul a β, mul_assoc, mul_assoc, hnum]

theorem corootPair_reePsi
    (a : ℕ) {β : Fin ReeTag.F4.tag.rank → ℤ}
    (hβ : IsRoot ReeTag.F4.tag β) (v : Fin ReeTag.F4.tag.rank → ℤ) :
    corootPair β (reePsi a v) =
      (rootExp a β : ℤ) * corootPair (ReeTag.F4.dualRoot β) v := by
  rw [CFSG.StandardType.LayerCycRoot.corootPair_eq_sum_single hβ (reePsi a v)]
  have hsum : (∑ i : Fin ReeTag.F4.tag.rank,
        reePsi a v i * corootPair β (Pi.single i 1)) =
      ∑ k : Fin ReeTag.F4.tag.rank,
        ((ReeTag.F4.relationExponent a (ReeTag.F4.perm k) : ℤ) * v k) *
          corootPair β (Pi.single (ReeTag.F4.perm k) 1) := by
    simp only [reePsi]
    rw [← Equiv.sum_comp ReeTag.F4.perm
      (fun i => (ReeTag.F4.relationExponent a i : ℤ) * v (ReeTag.F4.perm i) *
        corootPair β (Pi.single i 1))]
    exact Finset.sum_congr rfl fun k _ => by rw [ReeTag.perm_perm]
  rw [hsum]
  calc (∑ k : Fin ReeTag.F4.tag.rank,
        ((ReeTag.F4.relationExponent a (ReeTag.F4.perm k) : ℤ) * v k) *
          corootPair β (Pi.single (ReeTag.F4.perm k) 1))
      = ∑ k : Fin ReeTag.F4.tag.rank, v k * ((rootExp a β : ℤ) *
          corootPair (ReeTag.F4.dualRoot β) (Pi.single k 1)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show ((ReeTag.F4.relationExponent a (ReeTag.F4.perm k) : ℤ) * v k) *
              corootPair β (Pi.single (ReeTag.F4.perm k) 1) =
            v k * ((ReeTag.F4.relationExponent a (ReeTag.F4.perm k) : ℤ) *
              corootPair β (Pi.single (ReeTag.F4.perm k) 1)) by ring]
        rw [ree_corootPair_single a hβ k]
    _ = (rootExp a β : ℤ) * ∑ k : Fin ReeTag.F4.tag.rank,
          v k * corootPair (ReeTag.F4.dualRoot β) (Pi.single k 1) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = (rootExp a β : ℤ) * corootPair (ReeTag.F4.dualRoot β) v := by
        rw [CFSG.StandardType.LayerCycRoot.corootPair_eq_sum_single
          (ReeTag.isRoot_dualRoot hβ) v]

private theorem rootChar_coordTuple
    {L : Type} [Field L] {O : Finset (Fin ReeTag.F4.tag.rank → ℤ)}
    (hOroot : ∀ β ∈ O, IsRoot ReeTag.F4.tag β)
    (c : (Fin ReeTag.F4.tag.rank → ℤ) → Lˣ)
    (γ : Fin ReeTag.F4.tag.rank → ℤ) :
    rootChar (coordTuple O c) γ = ∏ β ∈ O, c β ^ corootPair β γ := by
  unfold rootChar
  simp only [coordTuple]
  rw [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.prod_zpow_prod_comm
    O Finset.univ c (fun β i => corootPair β (Pi.single i 1)) γ]
  refine Finset.prod_congr rfl fun β hβ => ?_
  rw [CFSG.StandardType.LayerCycRoot.corootPair_eq_sum_single (hOroot β hβ) γ]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem rootChar_coordTuple_ree
    {L : Type} [Field L]
    {a : ℕ} {w : WeylGroup ReeTag.F4.tag}
    {O : Finset (Fin ReeTag.F4.tag.rank → ℤ)}
    {c : (Fin ReeTag.F4.tag.rank → ℤ) → Lˣ}
    (hOroot : ∀ β ∈ O, IsRoot ReeTag.F4.tag β)
    (hOθ : ∀ β ∈ O, w • ReeTag.F4.dualRoot β ∈ O)
    (hc : ∀ β ∈ O, c (w • ReeTag.F4.dualRoot β) = c β ^ rootExp a β)
    (v : Fin ReeTag.F4.tag.rank → ℤ) :
    rootChar (coordTuple O c) (w • v) = rootChar (coordTuple O c) (reePsi a v) := by
  classical
  rw [rootChar_coordTuple hOroot c (w • v),
    rootChar_coordTuple hOroot c (reePsi a v)]
  have hR : (∏ β ∈ O, c β ^ corootPair β (reePsi a v)) =
      ∏ β ∈ O, c (w • ReeTag.F4.dualRoot β) ^
        corootPair (ReeTag.F4.dualRoot β) v := by
    refine Finset.prod_congr rfl fun β hβ => ?_
    rw [corootPair_reePsi a (hOroot β hβ) v, zpow_mul, zpow_natCast, hc β hβ]
  have hθinj : ∀ β ∈ O, ∀ γ ∈ O,
      w • ReeTag.F4.dualRoot β = w • ReeTag.F4.dualRoot γ → β = γ := by
    intro β hβ γ hγ h
    have h1 : ReeTag.F4.dualRoot β = ReeTag.F4.dualRoot γ := MulAction.injective w h
    have h2 := congrArg ReeTag.F4.dualRoot h1
    rwa [ReeTag.dualRoot_dualRoot (hOroot β hβ),
      ReeTag.dualRoot_dualRoot (hOroot γ hγ)] at h2
  have hθimage : O.image (fun β => w • ReeTag.F4.dualRoot β) = O := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro γ hγ
      obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hγ
      exact hOθ β hβ
    · rw [Finset.card_image_of_injOn hθinj]
  have hR2 : (∏ β ∈ O, c (w • ReeTag.F4.dualRoot β) ^
        corootPair (ReeTag.F4.dualRoot β) v) =
      ∏ γ ∈ O, c γ ^ corootPair γ (w • v) := by
    have h1 : (∏ γ ∈ O.image (fun β => w • ReeTag.F4.dualRoot β),
          c γ ^ corootPair γ (w • v)) =
        ∏ β ∈ O, c (w • ReeTag.F4.dualRoot β) ^
          corootPair (w • ReeTag.F4.dualRoot β) (w • v) :=
      Finset.prod_image (s := O) (g := fun β => w • ReeTag.F4.dualRoot β)
        (f := fun γ => c γ ^ corootPair γ (w • v)) hθinj
    rw [hθimage] at h1
    rw [h1]
    refine Finset.prod_congr rfl fun β _ => ?_
    rw [CFSG.StandardType.LayerCycRoot.corootPair_smul_smul]
  rw [hR, hR2]

theorem rootDiagUnit_coordTuple_mem_closure_of_reeInvolution
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin ReeTag.F4.tag.rank → ℤ) →* M} {J : Set (KernelComponent χ)}
    {a₀ : ℕ} {F : MulAut (adjointGroup ReeTag.F4.tag L)} (hF : IsReeFrob a₀ F)
    {w : WeylGroup ReeTag.F4.tag} {O : Finset (Fin ReeTag.F4.tag.rank → ℤ)}
    (hOΨ : ∀ β ∈ O, β ∈ unionRoots χ J) (hOθ : ∀ β ∈ O, w • ReeTag.F4.dualRoot β ∈ O)
    {x : WeylGroup ReeTag.F4.tag} (hx : x ∈ unionWeylGroup χ J) (hx2 : x * x = 1)
    (hxO : ∀ β ∈ O, x • β = -β)
    (hxσ : canonicalRep (coxeterSystem ReeTag.F4.tag) L x ∈
      twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w))
    (c : (Fin ReeTag.F4.tag.rank → ℤ) → Lˣ)
    (hc : ∀ β ∈ O, c (w • ReeTag.F4.dualRoot β) = c β ^ rootExp a₀ β) :
    rootDiagUnit ReeTag.F4.tag (coordTuple O c) ∈ Subgroup.closure
      {y : ModGL ReeTag.F4.tag L | y ∈ unionRootSpan L χ J ∧
        y ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
          ∃ k : ℕ, y ^ 2 ^ k = 1} := by
  classical
  let n : ModGL ReeTag.F4.tag L := canonicalRep (coxeterSystem ReeTag.F4.tag) L w
  let m : ModGL ReeTag.F4.tag L := canonicalRep (coxeterSystem ReeTag.F4.tag) L x
  let d : ModGL ReeTag.F4.tag L := rootDiagUnit ReeTag.F4.tag (coordTuple O c)
  have hOroot : ∀ β ∈ O, IsRoot ReeTag.F4.tag β :=
    fun β hβ => isRoot_of_mem_unionRoots (hOΨ β hβ)
  have hdσ : d ∈ twistedFixed F n := by
    rw [rootDiagUnit_mem_twistedFixed_canonicalRep_iff (a := a₀) hF w (coordTuple O c)]
    intro v
    rw [rootChar_reeTuple]
    exact rootChar_coordTuple_ree hOroot hOθ hc v
  have hnd : m * d * m⁻¹ = d⁻¹ := by
    let π : (Fin ReeTag.F4.tag.rank → ℤ) ≃+ (Fin ReeTag.F4.tag.rank → ℤ) :=
      DistribMulAction.toAddEquiv (Fin ReeTag.F4.tag.rank → ℤ) x
    have hπ_apply : ∀ y, π y = x • y := fun y => DistribMulAction.toAddEquiv_apply _ _ _
    have hπ : ∀ y z, iform (π y) (π z) = iform y z := fun y z => by
      rw [hπ_apply, hπ_apply]
      exact iform_smul x y z
    have hπΦ : ∀ α, IsRoot ReeTag.F4.tag α → IsRoot ReeTag.F4.tag (π α) := by
      intro α hα
      rw [hπ_apply]
      exact IsRoot.smul hα x
    have hgX : ∀ α, IsRoot ReeTag.F4.tag α → ∃ ε : Lˣ, ∀ y : L,
        m * pinnedX ReeTag.F4.tag L α y * m⁻¹ =
          pinnedX ReeTag.F4.tag L (π α) (ε * y) := by
      intro α hα
      exact ⟨1, fun y => by
        rw [hπ_apply]
        simpa using canonicalRep_conj_pinnedX x hα y⟩
    have hgT : ∀ t, ∃ t', m * rootDiagUnit ReeTag.F4.tag t * m⁻¹ =
        rootDiagUnit ReeTag.F4.tag t' := fun t =>
      ⟨CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct x t,
        CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit x t⟩
    have hconj : m * d * m⁻¹ =
        rootDiagUnit ReeTag.F4.tag (coordTuple (O.image π) fun γ => c (π.symm γ)) := by
      rw [show d = rootDiagUnit ReeTag.F4.tag (coordTuple O c) from rfl]
      exact conj_rootDiagUnit_coordTuple (g := m) (π := π) hπ hπΦ hgX hgT hOroot c
    have hcoord : coordTuple (O.image π) (fun γ => c (π.symm γ)) =
        coordTuple O (fun β => (c β)⁻¹) := by
      funext i
      simp only [coordTuple]
      rw [Finset.prod_image (fun y _ z _ h => π.injective h)]
      refine Finset.prod_congr rfl fun β hβ => ?_
      rw [AddEquiv.symm_apply_apply, hπ_apply, hxO β hβ,
        CFSG.StandardType.LayerCycCoroot.corootPair_neg_root (hOroot β hβ)
          (Pi.single i 1),
        zpow_neg, inv_zpow]
    have hd_inv : rootDiagUnit ReeTag.F4.tag (coordTuple O (fun β => (c β)⁻¹)) = d⁻¹ := by
      rw [show d = rootDiagUnit ReeTag.F4.tag (coordTuple O c) from rfl, rootDiagUnit_inv]
      congr 1
      rw [← CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.coordHom_apply O c,
        ← map_inv (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.coordHom O) c,
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.coordHom_apply]
      rfl
    rw [hconj, hcoord, hd_inv]
  have hmS : m ∈ unionRootSpan L χ J := canonicalRep_mem_rootSpan_unionRoots hx
  have hm2 : m * m = 1 := by
    have h := CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo (R := L) x x
    rw [hx2, CFSG.LieType.Chevalley.canonicalRep_one] at h
    exact h.symm
  have hdS : d ∈ unionRootSpan L χ J :=
    unionTorus_le_unionRootSpan (rootDiagUnit_coordTuple_mem_unionTorus hOΨ c)
  let y : ModGL ReeTag.F4.tag L := d * m
  have hyS : y ∈ unionRootSpan L χ J := mul_mem hdS hmS
  have hyσ : y ∈ twistedFixed F n := mul_mem hdσ hxσ
  have hy2 : y * y = 1 := by
    change (d * m) * (d * m) = 1
    calc (d * m) * (d * m) = d * (m * d * m⁻¹) * (m * m) := by group
      _ = d * d⁻¹ * 1 := by rw [hnd, hm2]
      _ = 1 := by group
  let D : Subgroup (ModGL ReeTag.F4.tag L) := Subgroup.closure
    {y : ModGL ReeTag.F4.tag L | y ∈ unionRootSpan L χ J ∧
      y ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
        ∃ k : ℕ, y ^ 2 ^ k = 1}
  have hmD : m ∈ D := Subgroup.subset_closure ⟨hmS, hxσ, 1, by simpa [pow_two] using hm2⟩
  have hyD : y ∈ D := Subgroup.subset_closure ⟨hyS, hyσ, 1, by simpa [pow_two] using hy2⟩
  have hdD : d ∈ D := by
    have hdn : d = y * m⁻¹ := by
      change d = d * m * m⁻¹
      group
    rw [hdn]
    exact D.mul_mem hyD (D.inv_mem hmD)
  exact hdD

end CFSG.HardMathSupport.C14Idx
