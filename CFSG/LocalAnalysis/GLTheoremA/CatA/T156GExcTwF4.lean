module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GKnown
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GExcBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFixGapTwF4
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4Diag
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownChevGeom
public import CFSG.LieType.Simplicity.TitsModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.LocalAnalysis.GLTheoremA.FP CFSG.LocalAnalysis.GLTheoremA.FQ
open CFSG.Assembly CFSG.StandardType CFSG.Blueprint CFSG.LieType.Ree CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open scoped commutatorElement


theorem sq_mem_commutator_reeFixed {k : Type} [Field k] [Finite k] [CharP k ReeTag.F4.prime]
    (hk : Nat.card k = 2)
    (g : reeFixed ReeTag.F4 k 0) : g ^ 2 ∈ commutator (reeFixed ReeTag.F4 k 0) := by
  set T := CFSG.LieType.Simplicity.titsData k hk
  set N := commutator (reeFixed ReeTag.F4 k 0) with hN
  have htop := T.commutator_sup_zpowers_eq_top hk
  set Q := QuotientGroup.mk' N with hQ
  have hzp : Q g ∈ Subgroup.zpowers (Q T.g₁) := by
    have h1 : Q g ∈ (N ⊔ Subgroup.zpowers T.g₁).map Q :=
      Subgroup.mem_map_of_mem Q (htop ▸ Subgroup.mem_top g)
    rwa [Subgroup.map_sup, hQ, QuotientGroup.map_mk'_self, bot_sup_eq,
      MonoidHom.map_zpowers] at h1
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hzp
  have hg1 : Q T.g₁ ^ 2 = 1 := by
    rw [← map_pow, hQ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact T.g₁_sq_mem
  have h2 : Q (g ^ 2) = 1 := by
    rw [map_pow, ← hz, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg1,
      one_zpow]
  rw [hQ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact h2

variable {p : ℕ}

theorem geomBody_twF4 (hp : p.Prime) (hp2 : p ≠ 2) {a : ℕ} (ha : 1 ≤ a) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    GeomBody p ⟨.twF4, 0, 2 * a + 1⟩ (LargeEvenCenterQuot (LargeEvenTwF4H a K))
      (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
      (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K)) := by
  haveI : CharP K ReeTag.F4.prime := charP_two_of_card hK
  refine geomBody_of_field (by simp) fun hS hna f hf hord => ?_
  have hF : FQ.InnFree p (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K)) :=
    innFree_of_ggRawInnField (RawAutReeF4.ggRawInnField_twF4_of_diag ha hK
      (ggTwistedF4DiagInput_holds a ha K hK hS) hp.one_lt.ne') hS hna
  obtain ⟨b, hbp, k, _, _, _, hk, ⟨φ⟩⟩ :=
    FR.exists_fixSub_equiv_reeGamma ha hK hp hp2 _ hF f hf hord
  have hdiv : (2 * a + 1) / p = 2 * b + 1 := by rw [← hbp, Nat.mul_div_cancel _ hp.pos]
  haveI := hS
  have hZ := center_eq_bot_of_simple_noncomm hna
  have hI : ∀ φ ∈ LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K), φ ^ p = 1 →
      φ ∈ Set.range (MulAut.conj : LargeEvenCenterQuot (LargeEvenTwF4H a K) →* _) := by
    intro φ hφ _
    obtain ⟨r, hr⟩ := chevIDImage_subset_inn_twF4 ha K hK hφ
    exact ⟨r, hr⟩
  rcases Nat.eq_zero_or_pos b with hb0 | hb1
  ·
    subst hb0
    have hk2 : Nat.card k = 2 := by simpa using hk
    obtain ⟨eT⟩ := nonempty_titsQuot_equiv hk2
    haveI : IsSimpleGroup ↥(commutator ↥(reeFixed ReeTag.F4 k 0)) := gff_isSimpleGroup_tits hk2
    haveI : Group.IsPerfect ↥(commutator ↥(reeFixed ReeTag.F4 k 0)) :=
      (CFSG.LieType.Simplicity.titsData k hk2).isPerfect hk2
    obtain ⟨x, y, hxy⟩ := exists_mul_ne_of_isPerfect ↥(commutator ↥(reeFixed ReeTag.F4 k 0))
    have hL : GGHasLabel ⟨.twF4der, 0, 1⟩ (LargeEvenCenterQuot (LargeEvenTwF4H 0 k)) := by
      unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
      exact ⟨k, inferInstance, inferInstance, hk, ⟨MulEquiv.refl _⟩⟩
    let ψ : ↥(FP.fixSub f) ≃* ↥(reeFixed ReeTag.F4 k 0) :=
      φ.trans (ReeTag.reeFixedEquivReeGamma k 0).symm
    have he : Nonempty (↥(ggFixDer f) ≃* LargeEvenCenterQuot (LargeEvenTwF4H 0 k)) := by
      unfold ggFixDer
      rw [ggFixSub_eq_fixSub]
      exact ⟨(((CFSG.LieType.BorelTits.commutatorSubgroupEquiv (FP.fixSub f)).trans
        (CFSG.LieType.BorelTits.commutatorEquiv φ)).trans
        (CFSG.LieType.BorelTits.commutatorEquiv (ReeTag.reeFixedEquivReeGamma k 0).symm)).trans
        eT.symm⟩
    have hpK : ∀ g ∈ ggFixSub f, g ^ p = 1 → g ∈ ggFixDer f := by
      refine pow_mem_ggFixDer_of_coprime fun g hg => ⟨2, ?_, ?_⟩
      · exact (Nat.coprime_two_right.2 (hp.odd_of_ne_two hp2))
      · have hg' : g ∈ FP.fixSub f := by rwa [← ggFixSub_eq_fixSub]
        have h1 := sq_mem_commutator_reeFixed hk2 (ψ ⟨g, hg'⟩)
        have hmap : (commutator ↥(FP.fixSub f)).map ψ.toMonoidHom =
            commutator ↥(reeFixed ReeTag.F4 k 0) := by
          rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
            MonoidHom.range_eq_top.2 ψ.surjective]
        rw [← map_pow, ← hmap] at h1
        obtain ⟨y, hy, hyeq⟩ := h1
        have hy' : y = ⟨g, hg'⟩ ^ 2 := ψ.injective hyeq
        rw [hy'] at hy
        have h2 : (((⟨g, hg'⟩ : ↥(FP.fixSub f)) ^ 2 : ↥(FP.fixSub f)) :
            LargeEvenCenterQuot (LargeEvenTwF4H a K)) ∈
            (commutator ↥(FP.fixSub f)).map (FP.fixSub f).subtype := ⟨_, hy, rfl⟩
        rw [Subgroup.map_subtype_commutator] at h2
        unfold ggFixDer
        rw [ggFixSub_eq_fixSub]
        simpa using h2
    exact fixAlt_of_hasLabel (lab₀ := ⟨.twF4der, 0, 1⟩) hp hp2 hZ hI hpK ⟨le_rfl, rfl, rfl⟩
      eT.isSimpleGroup
      ⟨eT.symm x, eT.symm y, fun h => hxy (by simpa using congrArg eT h)⟩ hL he
  ·
    obtain ⟨eR⟩ := gff_nonempty_centerQuot_equiv_reeGamma hb1 hk
    obtain ⟨hs₀, hna₀⟩ := twF4Quot_simple hb1 hk
    haveI := hs₀
    have hfix : FP.fixSub f = ggFixSub f := Subgroup.ext fun _ => Iff.rfl
    let e : LargeEvenCenterQuot (LargeEvenTwF4H b k) ≃* ↥(ggFixSub f) :=
      (eR.trans φ.symm).trans (MulEquiv.subgroupCongr hfix)
    have hder : ggFixDer f = ggFixSub f := ggFixDer_eq_ggFixSub hna₀ f e
    have hL : GGHasLabel ⟨.twF4, 0, 2 * b + 1⟩ (LargeEvenCenterQuot (LargeEvenTwF4H b k)) := by
      unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
      show LargeEvenRecipeTwF4 ((2 * b + 1 - 1) / 2) _
      rw [show (2 * b + 1 - 1) / 2 = b by omega]
      exact ⟨k, inferInstance, inferInstance, hk, ⟨MulEquiv.refl _⟩⟩
    have hlab₀ : LargeEvenInLambda2 ⟨.twF4, 0, 2 * b + 1⟩ := by
      refine ⟨?_, ?_⟩
      · show 1 ≤ 2 * b + 1
        omega
      · show (0 : ℕ) = 0 ∧ Odd (2 * b + 1) ∧ 3 ≤ 2 * b + 1
        exact ⟨rfl, ⟨b, rfl⟩, by omega⟩
    exact fixAlt_of_hasLabel hp hp2 hZ hI (pow_mem_ggFixDer_of_eq hder) hlab₀ hs₀ hna₀ hL
      ⟨(MulEquiv.subgroupCongr hder).trans e.symm⟩

theorem cAll_geomBody_twF4 (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    MI.CAll ⟨.twF4, 0, n⟩ (GeomBody p ⟨.twF4, 0, n⟩) := by
  obtain ⟨a, rfl⟩ := hodd
  have ha : 1 ≤ a := by omega
  have ha0 : a ≠ 0 := by omega
  intro Q hQ
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwF4Inherited] at hQ ⊢
  rw [show (2 * a + 1 - 1) / 2 = a by omega] at hQ ⊢
  simp only [ha0, ↓reduceIte] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  exact ⟨K, inferInstance, inferInstance, hK, hQ, geomBody_twF4 hp hp2 ha K hK⟩

end CFSG.LocalAnalysis.GLTheoremA.T156

end
