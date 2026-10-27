module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Datum
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Lang
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6Descent
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6Torus
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangSz
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6OddField
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LieType.Chevalley.DiagonalFieldActorData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPCyc
public import CFSG.GroupTheory.MulAutCongr
public import CFSG.LocalAnalysis.StandardType.GGFixSub
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.StandardType.RecipeExcLang CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ggFixSub_eq_of_zpowers_eq {G : Type*} [Group G] {x y : MulAut G}
    (h : Subgroup.zpowers x = Subgroup.zpowers y) : ggFixSub x = ggFixSub y := by
  have key : ∀ {x y : MulAut G}, y ∈ Subgroup.zpowers x → ggFixSub x ≤ ggFixSub y := by
    intro x y hy g hg
    have hle : Subgroup.zpowers x ≤ MulAction.stabilizer (MulAut G) g :=
      Subgroup.zpowers_le.2 (mem_ggFixSub.1 hg)
    exact mem_ggFixSub.2 (hle hy)
  exact le_antisymm (key (h ▸ Subgroup.mem_zpowers y)) (key (h.symm ▸ Subgroup.mem_zpowers x))

theorem pow_pow_eq_self_of_pow_eq {M : Type*} [Monoid M] {c : M} {m : ℕ} (h : c ^ m = c)
    (j : ℕ) : c ^ (m ^ j) = c := by
  induction j with
  | zero => rw [pow_zero, pow_one]
  | succ j ih => rw [pow_succ, pow_mul, ih, h]

section TwE6


variable {K : Type} [Field K] [Finite K]

theorem twE6_theta_eq_one_of_mem_markID (σ : K ≃+* K)
    (Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K)
    (hΘ : ∀ α g u δ, α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
      fieldActor σ δ → Θ α = δ)
    {φ : MulAut (LargeEvenCenterQuot (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))}
    (hφ : φ ∈ markIDImage (IsRoot TwistTag.E6.tag) K
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
    Θ (MulAut.congr (centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ))
      φ) = 1 := by
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hle : Subgroup.closure (LargeEvenInnSet _ ∪ markDiagImage (IsRoot TwistTag.E6.tag) K
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) ≤
        (Θ.comp (MulAut.congr (centerQuotEquivOfBot hZ)).toMonoidHom).ker := by
    rw [Subgroup.closure_le]
    rintro φ (⟨r, rfl⟩ | ⟨a, hN1, -, hrel⟩)
    · show Θ (MulAut.congr (centerQuotEquivOfBot hZ) (MulAut.conj r)) = 1
      rw [mulAut_congr_conj]
      exact hΘ _ (centerQuotEquivOfBot hZ r) 1 1 (by rw [map_one, fieldActor_one, mul_one, mul_one])
    · have hnorm : ∀ g ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
          rootDiagUnit TwistTag.E6.tag a * g * (rootDiagUnit TwistTag.E6.tag a)⁻¹ ∈
            graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
        intro g hg
        obtain ⟨h', hh'⟩ := hN1 ⟨g, hg⟩
        rw [markDiag_rel_iff] at hh'
        rw [← hh']
        exact h'.2
      obtain ⟨u, hu⟩ := exists_compatDiag_eq (t := TwistTag.E6) (σ := σ.toRingHom)
        (TableB.TwE6.compat_of_forall_conj_mem hnorm)
      have hΨφ : MulAut.congr (centerQuotEquivOfBot hZ) φ =
          compatDiagAutHom TwistTag.E6 K σ.toRingHom u := by
        refine MulEquiv.ext fun h => Subtype.ext ?_
        have h1 := congr_centerQuotEquivOfBot_mk hZ φ h
        have h2 := hrel h ⟨_, hnorm h h.2⟩ ((markDiag_rel_iff a _ _).2 rfl)
        have h3 : MulAut.congr (centerQuotEquivOfBot hZ) φ h = ⟨_, hnorm h h.2⟩ :=
          congrArg (centerQuotEquivOfBot hZ) (h1.symm.trans h2)
        rw [h3, coe_compatDiagAutHom, hu]
      show Θ (MulAut.congr (centerQuotEquivOfBot hZ) φ) = 1
      rw [hΨφ]
      exact hΘ _ 1 u 1 (by rw [map_one, fieldActor_one, one_mul, mul_one])
  exact hle hφ

theorem twE6_entrywise_eq_of_commute {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hq3 : 3 ≤ 2 ^ n) (ε : K ≃+* K)
    (w : twInndiagGroup K σ)
    (hc : twConj K σ w * fieldActor σ ε = fieldActor σ ε * twConj K σ w) :
    Units.map (entrywiseHom ε.toRingHom) (w : ModGL TwistTag.E6.tag K) = w := by
  have hw' : Units.map (entrywiseHom ε.toRingHom) (w : ModGL TwistTag.E6.tag K) ∈
      twInndiagGroup K σ := entrywise_mem_twInndiag ε w.2
  have hz : (Units.map (entrywiseHom ε.toRingHom) (w : ModGL TwistTag.E6.tag K))⁻¹ *
      (w : ModGL TwistTag.E6.tag K) ∈ twInndiagGroup K σ := mul_mem (inv_mem hw') w.2
  refine (inv_mul_eq_one.1 (eq_one_of_commute_C0 hn hK hσ hq3 hz fun c hcC => ?_))
  obtain ⟨h, hh⟩ := (fieldActor σ ε).surjective ⟨c, hcC⟩
  have e1 := congrArg (fun α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) =>
    ((α h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K)) hc
  simp only [MulAut.mul_apply, coe_twConj, coe_fieldActor] at e1
  rw [map_mul, map_mul, map_inv] at e1
  have hc' : c = Units.map (entrywiseHom ε.toRingHom) (h : ModGL TwistTag.E6.tag K) := by
    have := congrArg Subtype.val hh
    rw [coe_fieldActor] at this
    exact this.symm
  rw [hc']
  set x := Units.map (entrywiseHom ε.toRingHom) (h : ModGL TwistTag.E6.tag K)
  set w' := Units.map (entrywiseHom ε.toRingHom) (w : ModGL TwistTag.E6.tag K)
  calc w'⁻¹ * (w : ModGL TwistTag.E6.tag K) * x =
        w'⁻¹ * ((w : ModGL TwistTag.E6.tag K) * x * (w : ModGL TwistTag.E6.tag K)⁻¹) *
          (w : ModGL TwistTag.E6.tag K) := by group
    _ = w'⁻¹ * (w' * x * w'⁻¹) * (w : ModGL TwistTag.E6.tag K) := by rw [e1]
    _ = x * (w'⁻¹ * (w : ModGL TwistTag.E6.tag K)) := by group

theorem exists_twInndiag_of_fixed {n d : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K}
    (κ : K ≃+* K) (hd : 1 ≤ d) (hk : Nat.card (fixSubfield κ) = (2 ^ d) ^ 2)
    (σ₀ : fixSubfield κ ≃+* fixSubfield κ) (hσ₀ : ∀ c, σ₀ c = c ^ (2 ^ d))
    (hcomm : (fixSubfield κ).subtype.comp σ₀.toRingHom =
      σ.toRingHom.comp (fixSubfield κ).subtype)
    {w : ModGL TwistTag.E6.tag K} (hw : w ∈ twInndiagGroup K σ)
    (hfix : Units.map (entrywiseHom κ.toRingHom) w = w) :
    ∃ w₀ ∈ twInndiagGroup (fixSubfield κ) σ₀, baseChangeGL (fixSubfield κ).subtype w₀ = w := by
  have hle : twInndiagGroup K σ ≤ inndiagGroup TwistTag.E6.tag K := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (hc | ⟨b, -, rfl⟩)
    · exact adjointGroup_le_inndiagGroup (twistedFixedGroup_le_adjointGroup TwistTag.E6 K
        σ.toRingHom (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom hc))
    · exact rootDiagUnit_mem_inndiagGroup b
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  have hk' : Nat.card (fixSubfield κ) = 2 ^ (2 * d) := by rw [hk, ← pow_mul, mul_comm]
  obtain ⟨w₀, hw₀, hw₀w⟩ := E6FieldFix.exists_inndiagGroup_of_fixed hK' κ hk' (hle hw) hfix
  have htw : twistHom TwistTag.E6 (fixSubfield κ) σ₀.toRingHom w₀ = w₀ := by
    apply baseChangeGL_injective (fixSubfield κ).subtype
    rw [← twistHom_baseChangeGL (fixSubfield κ).subtype hcomm, hw₀w]
    exact twistHom_eq_of_mem_twInndiag hw
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [← Nat.card_eq_fintype_card]; exact hK')
  set L := AlgebraicClosure (fixSubfield κ)
  haveI : CharP L 2 :=
    charP_of_injective_algebraMap (algebraMap (fixSubfield κ) L).injective 2
  have hFr : ∀ c : L, iterateFrobenius L 2 d c = c ^ (2 ^ d) := fun c => iterateFrobenius_def 2 d c
  have hFrc : (algebraMap (fixSubfield κ) L).comp σ₀.toRingHom =
      (iterateFrobenius L 2 d).comp (algebraMap (fixSubfield κ) L) := RingHom.ext fun c => by
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσ₀, hFr,
      map_pow]
  have hmem : baseChangeGL (algebraMap (fixSubfield κ) L) w₀ ∈ adjointGroup TwistTag.E6.tag L :=
    baseChangeGL_mem_adjointGroup_of_mem_inndiag _ hw₀
  have hF : twistHom TwistTag.E6 L (iterateFrobenius L 2 d)
      (baseChangeGL (algebraMap (fixSubfield κ) L) w₀) =
        baseChangeGL (algebraMap (fixSubfield κ) L) w₀ := by
    rw [twistHom_baseChangeGL _ hFrc, htw]
  obtain ⟨w₁, hw₁, hw₁e⟩ :=
    exists_mem_twInndiag_of_twist_fixed (K := fixSubfield κ) hd hk hσ₀ hFr hmem hF
  have h01 : w₁ = w₀ := baseChangeGL_injective _ hw₁e
  exact ⟨w₀, h01 ▸ hw₁, hw₀w⟩

end TwE6

end CFSG.LocalAnalysis.GLTheoremA.T156

end
