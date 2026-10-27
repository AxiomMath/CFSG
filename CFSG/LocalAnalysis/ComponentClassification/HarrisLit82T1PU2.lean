module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PSemi
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PFrame
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU3
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RC
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinear

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup QuadraticMap CFSG.LieType.Universal.Spin CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

section Model

variable {K : Type} [Field K] {n : ℕ}

@[expose] def spinOmega (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    spinGroup (quadOdd n K) →* orthDerived (quadOdd n K) :=
  (spinAction (quadOdd n K)).codRestrict _ fun x =>
    (range_spinAction_quadOdd_eq_commutator h2 hn).le ⟨x, rfl⟩

theorem coe_spinOmega (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) (x : spinGroup (quadOdd n K)) :
    (spinOmega h2 hn x : (Fin n ⊕ Fin n ⊕ Unit → K) ≃ₗ[K] (Fin n ⊕ Fin n ⊕ Unit → K)) =
      spinAction (quadOdd n K) x :=
  rfl

@[expose] def spinProj (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    spinGroup (quadOdd n K) →* ProjOrthDerived (quadOdd n K) :=
  (QuotientGroup.mk' _).comp (spinOmega h2 hn)

theorem spinProj_apply (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) (x : spinGroup (quadOdd n K)) :
    spinProj h2 hn x = QuotientGroup.mk (spinOmega h2 hn x) :=
  rfl

theorem spinProj_surjective (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    Function.Surjective (spinProj h2 hn) := by
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have hg : (g : (Fin n ⊕ Fin n ⊕ Unit → K) ≃ₗ[K] (Fin n ⊕ Fin n ⊕ Unit → K)) ∈
      (spinAction (quadOdd n K)).range := by
    rw [range_spinAction_quadOdd_eq_commutator h2 hn]
    exact g.2
  obtain ⟨x, hx⟩ := hg
  refine ⟨x, ?_⟩
  rw [spinProj_apply]
  exact congrArg QuotientGroup.mk (Subtype.ext hx : spinOmega h2 hn x = g)

theorem eq_one_of_mem_scalars_quadOdd
    {g : (Fin n ⊕ Fin n ⊕ Unit → K) ≃ₗ[K] (Fin n ⊕ Fin n ⊕ Unit → K)}
    (hg : g ∈ orthDerived (quadOdd n K)) (hs : g ∈ scalars K (Fin n ⊕ Fin n ⊕ Unit → K)) :
    g = 1 := by
  refine eq_one_of_mem_scalars_of_mem_orthDerived ?_ (v₀ := oddZ n K)
    (by rw [quadOdd_oddZ]; exact one_ne_zero) hg hs
  rw [Module.finrank_fintype_fun_eq_card]
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  exact ⟨n, by ring⟩

theorem ker_spinProj (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    (spinProj h2 hn).ker = center (spinGroup (quadOdd n K)) := by
  rw [center_spinGroup_quadOdd_eq_ker h2 hn]
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, spinProj_apply, QuotientGroup.eq_one_iff,
    mem_subgroupOf]
  constructor
  · intro hx
    exact eq_one_of_mem_scalars_quadOdd (spinOmega h2 hn x).2 hx
  · intro hx
    rw [coe_spinOmega, hx]
    exact one_mem _

end Model

theorem isTwoComponentIn_spinJ {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
    {J : Subgroup (spinGroup (quadOdd 3 K))}
    (hJ : J = spinJ₁ K ∨ J = spinJ₂ K ∨ J = spinJ₃ K) :
    IsTwoComponentIn J (centralizer {tSeven K}) := by
  obtain ⟨hJC, hJn, -, hO, hq⟩ := spinJ_props hp hp2 hK h5 hJ
  exact ⟨hJC, hJn.isSubnormal, hq.1, LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).symm hq⟩

theorem eq_one_or_eq_conj_of_fix {X : Type} [Group X] [Finite X] {p f : ℕ} (h5 : 5 ≤ p ^ f)
    (hX : IsCoverOf .POmegaOdd 3 p f 2 X) {t : X} (ht : orderOf t = 2) (htZ : t ∉ center X)
    {α : MulAut X}
    (hα : ∀ J : Subgroup X, IsTwoComponentIn J (centralizer {t}) → ∀ j ∈ J, α j = j) :
    α = 1 ∨ α = MulAut.conj t := by
  obtain ⟨K, _, _, e, hK, hp, hp2, het⟩ := exists_mulEquiv_spinSeven h5 hX ht htZ
  have h2 : (2 : K) ≠ 0 := two_ne_zero_spin hp hp2 hK
  have : Group.IsPerfect X := by
    obtain ⟨hq, -⟩ := hX
    exact hq.1
  have hfixJ : ∀ J : Subgroup (spinGroup (quadOdd 3 K)),
      (J = spinJ₁ K ∨ J = spinJ₂ K ∨ J = spinJ₃ K) → ∀ s ∈ J, α (e.symm s) = e.symm s := by
    intro J hJ s hs
    have hJX : IsTwoComponentIn (J.map e.symm.toMonoidHom) (centralizer {t}) := by
      have h := L35.isTwoComponentIn_map_of_injective e.symm.toMonoidHom e.symm.injective
        (isTwoComponentIn_spinJ hp hp2 hK h5 hJ)
      rwa [map_centralizer_singleton_mulEquiv e.symm, ← het, MulEquiv.symm_apply_apply] at h
    exact hα _ hJX _ ⟨s, hs, rfl⟩
  set κX : X →* ProjOrthDerived (quadOdd 3 K) := (spinProj h2 (le_refl 3)).comp e.toMonoidHom
    with hκX
  have hκXs : Function.Surjective κX := (spinProj_surjective h2 (le_refl 3)).comp e.surjective
  have hκXe : ∀ s, κX (e.symm s) = QuotientGroup.mk (spinOmega h2 (le_refl 3) s) := fun s => by
    rw [hκX, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      spinProj_apply]
  have hkerX : κX.ker = center X := by
    ext x
    rw [MonoidHom.mem_ker, hκX, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_spinProj,
      MulEquiv.coe_toMonoidHom, mem_center_mulEquiv_iff]
  set ε : X ⧸ center X ≃* ProjOrthDerived (quadOdd 3 K) :=
    (QuotientGroup.quotientMulEquivOfEq hkerX.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective κX hκXs)
  have hεmk : ∀ x : X, ε (QuotientGroup.mk x) = κX x := fun x => rfl
  set αb : MulAut (ProjOrthDerived (quadOdd 3 K)) :=
    MulAut.congr ε (PerfectAutomorphisms.onCenterQuotient α) with hαb
  have hαbκ : ∀ x : X, αb (κX x) = κX (α x) := by
    intro x
    rw [← hεmk, ← hεmk]
    simp only [hαb, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    exact congrArg ε (PerfectAutomorphisms.onCenterQuotient_apply_mk α x)
  have hdim : Module.finrank K (Fin 3 ⊕ Fin 3 ⊕ Unit → K) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  obtain ⟨σ, F, hF, μ, -, hQF, hind⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonalAut.orthogonal_aut_semilinear_of_seven_le
      (quadOdd 3 K) (nondegenerate_polarBilin_quadOdd 3 K h2) hdim.ge
      (fun h => absurd (hdim.symm.trans h) (by norm_num)) αb
  have hcomm : ∀ J : Subgroup (spinGroup (quadOdd 3 K)),
      (J = spinJ₁ K ∨ J = spinJ₂ K ∨ J = spinJ₃ K) → ∀ s ∈ J, ∀ v,
        F (spinAction (quadOdd 3 K) s v) = spinAction (quadOdd 3 K) s (F v) := by
    intro J hJ s hs v
    have hfixs : αb (QuotientGroup.mk (spinOmega h2 (le_refl 3) s)) =
        QuotientGroup.mk (spinOmega h2 (le_refl 3) s) := by
      have h1 := hαbκ (e.symm s)
      rwa [hfixJ J hJ s hs, hκXe] at h1
    exact commute_of_inducedBySemilinear (fun g hg hs => eq_one_of_mem_scalars_quadOdd hg hs)
      hF hQF hind hfixs v
  have hL : ∀ (A : SL(2, K)) v, F ((frame01 K).La A v) = (frame01 K).La A (F v) := by
    intro A v
    have h := hcomm _ (Or.inr (Or.inl rfl)) _ ⟨A, rfl⟩ v
    rwa [spinAction_longSL2] at h
  have hR : ∀ (A : SL(2, K)) v, F ((frame01 K).swap.La A v) = (frame01 K).swap.La A (F v) := by
    intro A v
    have h := hcomm _ (Or.inr (Or.inr rfl)) _ ⟨A, rfl⟩ v
    rwa [spinAction_longSL2, show (oddFrame 3 K).toHypFrame.toFrame fin3_zero_ne_one true false =
      (frame01 K).swap from toFrame_not _ fin3_zero_ne_one true true] at h
  have hS : ∀ (s : Bool) (c : K) v,
      F (spinAction (quadOdd 3 K) ((oddFrame 3 K).shortRoot 2 s (.ofAdd c)) v) =
        spinAction (quadOdd 3 K) ((oddFrame 3 K).shortRoot 2 s (.ofAdd c)) (F v) := by
    intro s c v
    have hmem : (oddFrame 3 K).shortRoot 2 s (.ofAdd c) ∈ spinJ₁ K := by
      cases s
      · refine ⟨lowerSL2 (-c), ?_⟩
        show (oddFrame 3 K).shortSL2 2 true (lowerSL2 (-c)) = _
        simp only [OddFrame.shortSL2_lowerSL2, neg_neg, Bool.not_true]
      · exact ⟨upperSL2 c, OddFrame.shortSL2_upperSL2 _ _ _ c⟩
    exact hcomm _ (Or.inl rfl) _ hmem v
  obtain ⟨-, c, hc0, hFc⟩ := eq_smul_or_eq_smul_La_of_commute h2 hF hQF hL hR hS
  rcases hFc with hFc | hFc
  ·
    left
    have h1 : αb = MulAut.conj (QuotientGroup.mk (1 : orthDerived (quadOdd 3 K))) :=
      eq_conj_of_inducedBySemilinear hind 1 hc0 fun v => (hFc v).trans rfl
    rw [QuotientGroup.mk_one, map_one] at h1
    have h3 : PerfectAutomorphisms.onCenterQuotient α = 1 := by
      have h4 := congrArg (MulAut.congr ε).symm h1
      rwa [hαb, MulEquiv.symm_apply_apply, map_one] at h4
    exact PerfectAutomorphisms.onCenterQuotient_eq_one_imp α h3
  ·
    right
    have h1 : αb = MulAut.conj (QuotientGroup.mk (spinOmega h2 (le_refl 3) (tSeven K))) :=
      eq_conj_of_inducedBySemilinear hind _ hc0 fun v => by
        rw [hFc, coe_spinOmega, spinAction_tSeven]
    have h3 : PerfectAutomorphisms.onCenterQuotient α =
        PerfectAutomorphisms.onCenterQuotient (MulAut.conj t) := by
      apply (MulAut.congr ε).injective
      rw [← hαb, h1, onCenterQuotient_conj, OuterAutomorphisms.congr_conj]
      congr 1
      rw [show QuotientGroup.mk' (center X) t = (QuotientGroup.mk t : X ⧸ center X) from rfl,
        hεmk, hκX, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, het, spinProj_apply]
    have h4 : PerfectAutomorphisms.centerQuotientHom X α =
        PerfectAutomorphisms.centerQuotientHom X (MulAut.conj t) := h3
    exact PerfectAutomorphisms.centerQuotientHom_injective X h4

theorem harris82Lemma411U2_holds : Harris82Lemma411U2 := by
  intro X _ _ p f hp hp2 h5 hX t ht htZ
  exact ⟨pPrimeCore_centralizer_of_isCoverOf h5 hX ht htZ,
    fun α hα => eq_one_or_eq_conj_of_fix h5 hX ht htZ hα⟩

end CFSG.ComponentClassification.HarrisLit.T1
