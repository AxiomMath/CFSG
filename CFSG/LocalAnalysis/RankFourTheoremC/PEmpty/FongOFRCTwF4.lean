module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieTransfer
import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixedEmbed
import CFSG.RankThree.PartOne.K128.F4Syl
import CFSG.RankThree.PartOne.K128.SylowShapeRank
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieDefs
public import CFSG.RankThree.PartOne.RF4.Descent

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)
open CFSG.RankThree.PartOne

section


open CFSG.HardMathSupport.Lang.Coordinator in
theorem outerFixedRankCrossAt_twistedF4 : OuterFixedRankCrossAt .twistedF4 := by
  intro X _ _ n ℓ f hadm hmodel hT p hp hp5 hne hdiv α hαp hαin hrk
  obtain ⟨hn0, hℓ2, -, -⟩ := hadm.2.2
  subst hn0
  subst hℓ2
  have hp1 : 1 < p := hp.one_lt
  have hp2 : p ≠ 2 := by omega
  have hR : ReeTitsModel X .twistedF4 2 f :=
    ((CFSG.Blueprint.LieModel.reeTitsModel hmodel (by decide)).2)
  obtain ⟨a, F, _, _, _, ha, hfa, hFcard, ⟨e⟩⟩ := KEXC.exists_gamma_of_model hR
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hFcard
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ReeTag.F4.reeGamma F a) := Finite.of_equiv X e.toEquiv
  set α' : MulAut (ReeTag.F4.reeGamma F a) := MulAut.congr e α with hα'
  have hα'p : α' ^ p = 1 := by rw [hα', ← map_pow, hαp, map_one]
  have hα'inn : α' ∉ inner (ReeTag.F4.reeGamma F a) := fun h =>
    hαin ((congr_mem_inner_iff e α).mp h)
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha F hK
  obtain ⟨⟨x, β⟩, hxβ, -⟩ := hNF α'
  have hΨα : Ψ ⟨x, β⟩ = α' := by rw [hΨ x β]; exact hxβ.symm
  let Θ : MulAut (ReeTag.F4.reeGamma F a) →* (F ≃+* F) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘα : Θ α' = β := by
    show SemidirectProduct.rightHom (Ψ.symm α') = β
    rw [← hΨα, MulEquiv.symm_apply_apply]
    rfl
  have hβp : β ^ p = 1 := by
    rw [← hΘα, ← map_pow, hα'p, map_one]
  have hone : ReeTag.F4.reeGammaFieldAut F a 1 = 1 := by rw [← ReeTag.reeGammaFieldAutHom_apply, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hα'inn
    rw [h, hone, mul_one] at hxβ
    exact ⟨x, hxβ.symm⟩
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  obtain ⟨g, hg⟩ := RF4.largeRee_fieldAut_coset_conj a hK hp β hβord α' hα'p ⟨x, hxβ⟩
  obtain ⟨b, hchar, hbcard, hbp, ι, hιinj, hιfix⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.exists_fixedPoints_reeGammaFieldAut_odd hK hp hp2 β
      hβord
  have : Finite (fixSubfield β) := Subtype.finite
  have : Finite (ReeTag.F4.reeGamma (fixSubfield β) b) := Subtype.finite
  have hrkΓ : 2 ≤ CFSG.pRank p (ReeTag.F4.reeGamma F a) := by
    rw [← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.open_pRank_top_eq_pRank,
      ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 e]
    exact hrk
  obtain ⟨d, hd, hdvd⟩ := K128.ree_class hK hp hp5 hrkΓ
  have hqp : (2 : ℕ) ^ (2 * a + 1) = (2 ^ (2 * b + 1)) ^ p := by rw [← pow_mul, hbp]
  have hq₂ : 2 ≤ 2 ^ (2 * b + 1) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdvd₀ : p ∣ K128.phiF4 d (2 ^ (2 * b + 1)) :=
    K128.dvd_phiF4_of_dvd_pow hp (by omega) hd (by rw [← hqp]; exact hdvd)
  have hphi : K128.phiF4 d (2 ^ (2 * b + 1)) ≠ 0 := by
    rcases hd with rfl | rfl | rfl <;> simp [K128.phiF4] <;> omega
  have he : 1 ≤ (K128.phiF4 d (2 ^ (2 * b + 1))).factorization p :=
    hp.factorization_pos_of_dvd hphi hdvd₀
  have hshape := K128.sylowShape_ree (a := b) (K := fixSubfield β) hbcard hd hp hp5 hdvd₀
  have h2 : 2 ≤ CFSG.pRank p (ReeTag.F4.reeGamma (fixSubfield β) b) :=
    K1214.two_le_pRank_of_sylowShape_sq hp he hshape
  have h3 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (ReeTag.F4.reeGamma (fixSubfield β) b)) := by
    rw [CFSG.HardMathSupport.Timmesfeld.ComponentBalance.open_pRank_top_eq_pRank]
    exact h2
  have h4 := pRank_top_le_pRank_fixed_of_embedding hp1 ι hιinj
    (ReeTag.F4.reeGammaFieldAut F a β) fun z => (hιfix (ι z)).1 ⟨z, rfl⟩
  have h5 : CFSG.Open.pRank p (fixedSubgroup (ReeTag.F4.reeGammaFieldAut F a β)) ≤
      CFSG.Open.pRank p (fixedSubgroup α') :=
    pRank_fixed_le_of_intertwine hp1 (MulAut.conj g)⁻¹ α' (ReeTag.F4.reeGammaFieldAut F a β)
      fun y => by
        rw [hg]
        simp [MulAut.mul_apply]
        group
  have h6 : CFSG.Open.pRank p (fixedSubgroup α') ≤ CFSG.Open.pRank p (fixedSubgroup α) :=
    pRank_fixed_le_of_intertwine hp1 e α α' fun y => by
      rw [hα', MulAut.congr_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  omega

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
