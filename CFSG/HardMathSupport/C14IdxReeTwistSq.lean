module

public import CFSG.RankThree.PartOne.KLR.TwistClosure
public import CFSG.RankThree.PartOne.TCX.Ree.Closure
public import CFSG.HardMathSupport.C14IdxReeInvolution

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR
  CFSG.RankThree.PartOne.TCX.Ree CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial

theorem rootExp_mul_rootExp_dualRoot
    {a : ℕ} {γ : Fin ReeTag.F4.tag.rank → ℤ} (hγ : IsRoot ReeTag.F4.tag γ) :
    rootExp a γ * rootExp a (ReeTag.F4.dualRoot γ) = 2 ^ (2 * a + 1) := by
  have hprod := (ReeTag.rootDualityCheck_spec hγ).2.2.2.2.1
  have hp : ReeTag.F4.prime = 2 := rfl
  rw [hp] at hprod
  norm_num at hprod
  unfold rootExp
  rcases ReeTag.quadForm_eq (t := ReeTag.F4) hγ with h | h
  · rw [if_pos h]
    have hd : ReeTag.F4.quadForm (ReeTag.F4.dualRoot γ) = 4 := by
      rw [h] at hprod
      omega
    rw [if_neg (by rw [hd]; norm_num), ← pow_add]
    congr 1
    omega
  · have hne : ¬ ReeTag.F4.quadForm γ = 2 := by
      rw [h, hp]
      norm_num
    rw [if_neg hne]
    have h4 : ReeTag.F4.quadForm γ = 4 := by
      rw [h, hp]
      norm_num
    have hd : ReeTag.F4.quadForm (ReeTag.F4.dualRoot γ) = 2 := by
      rw [h4] at hprod
      omega
    rw [if_pos hd, ← pow_add]
    congr 1
    omega

private theorem rootChar_singleTuple {L : Type} [Field L]
    {γ : Fin ReeTag.F4.tag.rank → ℤ} (hγ : IsRoot ReeTag.F4.tag γ) (c : Lˣ)
    (u : Fin ReeTag.F4.tag.rank → ℤ) :
    rootChar (fun i => c ^ corootPair γ (Pi.single i 1)) u = c ^ corootPair γ u := by
  unfold rootChar
  calc ∏ i, (c ^ corootPair γ (Pi.single i 1)) ^ u i
      = ∏ i, c ^ (corootPair γ (Pi.single i 1) * u i) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← zpow_mul]
    _ = c ^ ∑ i, corootPair γ (Pi.single i 1) * u i :=
        Finset.prod_zpow_eq_zpow_sum Finset.univ c
          (fun i => corootPair γ (Pi.single i 1) * u i)
    _ = c ^ corootPair γ u := by
        congr 1
        rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.corootPair_eq_sum hγ]
        exact Finset.sum_congr rfl fun i _ => by ring

theorem twistMap_rootDiagUnit_single {L : Type}
    [Field L] [IsAlgClosed L] [CharP L 2] {a : ℕ}
    {F : MulAut (adjointGroup ReeTag.F4.tag L)} (hF : IsReeFrob a F)
    {w : WeylGroup ReeTag.F4.tag}
    {θ : (Fin ReeTag.F4.tag.rank → ℤ) → Fin ReeTag.F4.tag.rank → ℤ}
    (hθ : ∀ β, θ β = w • ReeTag.F4.dualRoot β) {γ : Fin ReeTag.F4.tag.rank → ℤ}
    (hγ : IsRoot ReeTag.F4.tag γ) (c : Lˣ) :
    twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)
        (rootDiagUnit ReeTag.F4.tag (fun i => c ^ corootPair γ (Pi.single i 1))) =
      rootDiagUnit ReeTag.F4.tag
        (fun i => (c ^ rootExp a γ) ^ corootPair (θ γ) (Pi.single i 1)) := by
  rw [twistMap, hF.fext_rootDiagUnit, canonicalRep_conj_rootDiagUnit]
  congr 1
  funext k
  unfold weylTuple
  rw [rootChar_reeTuple,
    rootChar_singleTuple hγ c (reePsi a (w⁻¹ • (Pi.single k 1))),
    corootPair_reePsi a hγ (w⁻¹ • (Pi.single k 1)),
    ← CFSG.StandardType.LayerCycRoot.corootPair_smul_smul w (ReeTag.F4.dualRoot γ), smul_inv_smul,
    hθ γ, zpow_mul, zpow_natCast]

private theorem reeFext_sq {L : Type} [Field L] [CharP L 2]
    {a : ℕ} {F : MulAut (adjointGroup ReeTag.F4.tag L)} (hF : IsReeFrob a F)
    {u : ModGL ReeTag.F4.tag L} (hu : u ∈ adjointGroup ReeTag.F4.tag L) :
    Fext F (Fext F u) = entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a + 1) u := by
  have hφ : (Subgroup.subtype (adjointGroup ReeTag.F4.tag L)).comp
        ((F * F).toMonoidHom) =
      (entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a + 1)).comp
        (Subgroup.subtype (adjointGroup ReeTag.F4.tag L)) := by
    refine adjointGroup_hom_ext ?_ ?_
    · intro i c
      change ((F * F) (xElement i c) : ModGL ReeTag.F4.tag L) =
        entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a + 1) (xElement i c)
      rw [MulAut.mul_apply]
      have h1 := (hF i c).1
      have h2 := (hF (ReeTag.F4.perm i) (c ^ ReeTag.F4.relationExponent a i)).1
      rw [h1, h2, ReeTag.perm_perm, ← pow_mul, ReeTag.relationExponent_mul_perm,
        ReeTag.prime]
      change xUnit ReeTag.F4.tag L i (c ^ 2 ^ (2 * a + 1)) =
        entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a + 1) (xElement i c)
      rw [show ((xElement i c : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
          xUnit ReeTag.F4.tag L i c from rfl, ← pinnedX_single (τ := ReeTag.F4.tag) (R := L) i c,
        entrywiseFrobGL_pinnedX, iterateFrobenius_def,
        ← pinnedX_single (τ := ReeTag.F4.tag) (R := L) i (c ^ 2 ^ (2 * a + 1))]
    · intro i c
      change ((F * F) (yElement i c) : ModGL ReeTag.F4.tag L) =
        entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a + 1) (yElement i c)
      rw [MulAut.mul_apply]
      have h1 := (hF i c).2
      have h2 := (hF (ReeTag.F4.perm i) (c ^ ReeTag.F4.relationExponent a i)).2
      rw [h1, h2, ReeTag.perm_perm, ← pow_mul, ReeTag.relationExponent_mul_perm,
        ReeTag.prime]
      change yUnit ReeTag.F4.tag L i (c ^ 2 ^ (2 * a + 1)) =
        entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a + 1) (yElement i c)
      rw [show ((yElement i c : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
          yUnit ReeTag.F4.tag L i c from rfl,
        ← pinnedX_neg_single (τ := ReeTag.F4.tag) (R := L) i c,
        entrywiseFrobGL_pinnedX, iterateFrobenius_def,
        ← pinnedX_neg_single (τ := ReeTag.F4.tag) (R := L) i (c ^ 2 ^ (2 * a + 1))]
  have h := congrArg (fun f : adjointGroup ReeTag.F4.tag L →* ModGL ReeTag.F4.tag L =>
    f ⟨u, hu⟩) hφ
  rw [Fext_of_mem F hu, Fext_of_mem F (F ⟨u, hu⟩).2]
  simpa [MulAut.mul_apply] using h

theorem reeTwistMap_sq {L : Type} [Field L]
    [CharP L 2] {a : ℕ} {F : MulAut (adjointGroup ReeTag.F4.tag L)} (hF : IsReeFrob a F)
    (w : WeylGroup ReeTag.F4.tag) {x : ModGL ReeTag.F4.tag L}
    (hx : x ∈ adjointGroup ReeTag.F4.tag L) :
    twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)
        (twistMap F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) x) =
      frobTwistGL ReeTag.F4.tag L 2 (2 * a + 1)
        (canonicalRep (coxeterSystem ReeTag.F4.tag) L (w * ReeTag.F4.weylPerm w)) x := by
  unfold twistMap
  have hn : canonicalRep (coxeterSystem ReeTag.F4.tag) L w ∈ adjointGroup ReeTag.F4.tag L :=
    canonicalRep_mem_adjointGroup _ L w
  have hFx : Fext F x ∈ adjointGroup ReeTag.F4.tag L := Fext_mem F hx
  rw [Fext_mul F (mul_mem hn hFx) (inv_mem hn), Fext_mul F hn hFx, Fext_inv F hn,
    hF.fext_canonicalRep, reeFext_sq hF hx]
  rw [show canonicalRep (coxeterSystem ReeTag.F4.tag) L w *
        (canonicalRep (coxeterSystem ReeTag.F4.tag) L (ReeTag.F4.weylPerm w) *
            entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a + 1) x *
          (canonicalRep (coxeterSystem ReeTag.F4.tag) L (ReeTag.F4.weylPerm w))⁻¹) *
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)⁻¹ =
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L w *
        canonicalRep (coxeterSystem ReeTag.F4.tag) L (ReeTag.F4.weylPerm w)) *
          entrywiseFrobGL ReeTag.F4.tag L 2 (2 * a + 1) x *
        (canonicalRep (coxeterSystem ReeTag.F4.tag) L w *
          canonicalRep (coxeterSystem ReeTag.F4.tag) L (ReeTag.F4.weylPerm w))⁻¹ by group]
  rw [← CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo w (ReeTag.F4.weylPerm w),
    frobTwistGL_apply]

end CFSG.HardMathSupport.C14Idx
