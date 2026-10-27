module

public import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
public import CFSG.RankThree.PartOne.TCF.Ree
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain
import CFSG.RankThree.PartOne.KLC.Transport
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Simplicity.TitsModel
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixed

public section

namespace CFSG.HardMathSupport.Dickson.SuzukiReeB

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.Ree CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

private def NQS (X : Type*) [Group X] : Prop :=
  ∃ (M : Subgroup X) (_ : M.Normal), CFSG.IsQuasisimple ↥M ∧ Group.IsSolvable (X ⧸ M)

private theorem nqs_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : NQS X) :
    NQS Y := by
  obtain ⟨M, hMn, hMq, hMs⟩ := h
  have hn : (M.map e.toMonoidHom).Normal := hMn.map e.toMonoidHom e.surjective
  refine ⟨M.map e.toMonoidHom, hn, ?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective M e.toMonoidHom e.injective) hMq
  · exact Group.isSolvable_of_surjective
      (f := (QuotientGroup.congr M (M.map e.toMonoidHom) e rfl).toMonoidHom)
      (QuotientGroup.congr M (M.map e.toMonoidHom) e rfl).surjective

private theorem nqs_of_isQuasisimple {X : Type*} [Group X] (h : CFSG.IsQuasisimple X) :
    NQS X := by
  haveI : Subsingleton (X ⧸ (⊤ : Subgroup X)) := QuotientGroup.subsingleton_quotient_top
  exact ⟨⊤, inferInstance, CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm h,
    inferInstance⟩

private theorem perfectInLayer_of_nqs {S : Type*} [Group S] [Finite S] (β : MulAut S)
    (h : NQS ↥(fixSubgroup β)) : PerfectInLayer β := by
  obtain ⟨M, hMn, hMq, hMs⟩ := h
  have hN : (M.map (fixSubgroup β).subtype).subgroupOf (fixSubgroup β) = M :=
    Subgroup.comap_map_eq_self_of_injective (fixSubgroup β).subtype_injective M
  have hNn : ((M.map (fixSubgroup β).subtype).subgroupOf (fixSubgroup β)).Normal := by
    rw [hN]; exact hMn
  refine perfectInLayer_of_normal_quasisimple β (Subgroup.map_subtype_le M) hNn
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective M (fixSubgroup β).subtype
        (fixSubgroup β).subtype_injective) hMq) ?_
  exact Group.isSolvable_of_surjective
    (f := (QuotientGroup.quotientMulEquivOfEq hN).symm.toMonoidHom)
    (QuotientGroup.quotientMulEquivOfEq hN).symm.surjective

private theorem odd_index_of_two_elements {Γ : Type*} [Group Γ] [Finite Γ] (C N : Subgroup Γ)
    (hNC : N ≤ C) (hN2 : ∀ g ∈ C, (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ N) :
    Odd (N.subgroupOf C).index := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥C) := inferInstance
  have hPN : (P : Subgroup ↥C) ≤ N.subgroupOf C := by
    intro g hg
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 P.isPGroup' ⟨g, hg⟩
    refine hN2 (g : Γ) g.2 ⟨k, ?_⟩
    rw [Subgroup.orderOf_coe g, ← hk]
    exact (Subgroup.orderOf_mk g hg).symm
  have h1 : (N.subgroupOf C).index ∣ (P : Subgroup ↥C).index := Subgroup.index_dvd_of_le hPN
  have h2 : ¬ 2 ∣ (P : Subgroup ↥C).index := P.not_dvd_index
  exact (Nat.odd_iff.2 (by omega)).of_dvd_nat h1

private theorem nqs_reeGamma {b : ℕ} {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    NQS (ReeTag.F4.reeGamma k b) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have hk2 : Nat.card k = 2 := by simpa using hk
    refine nqs_congr (ReeTag.reeFixedEquivReeGamma k 0) ?_
    have hT := CFSG.LieType.Simplicity.titsData k hk2
    refine ⟨commutator (reeFixed ReeTag.F4 k 0), inferInstance, hT.isQuasisimple hk2, ?_⟩
    exact (inferInstance : Group.IsSolvable (Abelianization (reeFixed ReeTag.F4 k 0)))
  · have hs : IsSimpleGroup (ReeTag.F4.reeGamma k b) :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb hk
    have hperf : commutator (ReeTag.F4.reeGamma k b) = ⊤ :=
      ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb hk
    have hnc : ∃ x y : ReeTag.F4.reeGamma k b, x * y ≠ y * x := by
      by_contra hab
      push Not at hab
      have hc : commutator (ReeTag.F4.reeGamma k b) = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact hab y x
      rw [hperf] at hc
      exact top_ne_bot hc
    exact nqs_of_isQuasisimple (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1

private theorem nqs_fixSubgroup_fieldAut {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    NQS ↥(fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)) := by
  classical
  obtain ⟨b, -, hkcard, hfixed⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.largeRee_fixed_data_odd hK hp hp2 σ hσ
  have : Finite (fixSubfield σ) := Subtype.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP (fixSubfield σ) ReeTag.F4.prime := by
    have : Fintype (fixSubfield σ) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (f := 2 * b + 1) (by
      rw [← Nat.card_eq_fintype_card, hkcard]
      rfl)
  have hFix : fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ) =
      (ReeTag.F4.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _) := rfl
  let eC : fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ) ≃*
      ReeTag.F4.reeGamma (fixSubfield σ) b :=
    (((fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)).equivMapOfInjective
      (ReeTag.F4.reeGamma K a).subtype (ReeTag.F4.reeGamma K a).subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [hFix]; exact hfixed))).trans
    ((ReeTag.F4.reeGamma (fixSubfield σ) b).equivMapOfInjective _
      (baseChangeGL_injective (τ := ReeTag.F4.tag) (fixSubfield σ).subtype)).symm
  exact nqs_congr eC.symm (nqs_reeGamma hkcard)

private theorem nqs_of_component_data {Γ : Type} [Group Γ] [Finite Γ] (C N : Subgroup Γ)
    (hNC : N ≤ C) (hN2 : ∀ g ∈ C, (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ N)
    (hcomp : CFSG.RankThree.PartOne.IsComponentOf C N)
    (hall : ∀ D : Subgroup Γ, CFSG.RankThree.PartOne.IsComponentOf C D → D = N) :
    NQS ↥C := by
  have hconj : ∀ g ∈ C, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    have h1 := CFSG.RankThree.PartOne.KLC.isComponentOf_map_mulEquiv' (MulAut.conj g) hcomp
    have hC : C.map (MulAut.conj g).toMonoidHom = C := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact C.mul_mem (C.mul_mem hg hz) (C.inv_mem hg)
      · intro hy
        refine ⟨g⁻¹ * y * g, C.mul_mem (C.mul_mem (C.inv_mem hg) hy) hg, ?_⟩
        show g * (g⁻¹ * y * g) * g⁻¹ = y
        group
    rw [hC] at h1
    have h2 := hall _ h1
    rw [← h2]
    exact ⟨n, hn, rfl⟩
  have hNn : (N.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff hNC).2 fun h k hh hk => hconj k hk h hh
  refine ⟨N.subgroupOf C, hNn, ?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNC).symm
      hcomp.2.1
  · exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_index_of_two_elements C N hNC hN2)

private theorem perfectInLayer_inner_gt3
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (x : ReeTag.F4.reeGamma K a) (hx : orderOf x = p) :
    PerfectInLayer (MulAut.conj x) := by
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨N, hNC, hN2, hall, hcomp⟩ :=
    CFSG.RankThree.PartOne.TCF.largeRee_component_data ha hK hp hp3 x hx
  have hC := fixSubgroup_conj x
  by_cases hN : N = ⊥
  · apply perfectInLayer_of_isSolvable
    rw [hC]
    have h := odd_index_of_two_elements (Subgroup.centralizer ({x} : Set _)) N hNC hN2
    rw [hN, Subgroup.bot_subgroupOf, Subgroup.index_bot] at h
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ h
  · apply perfectInLayer_of_nqs
    rw [hC]
    exact nqs_of_component_data _ N hNC hN2 (hcomp hN) hall

private theorem perfectInLayer_inner_three {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K]
    [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (x : ReeTag.F4.reeGamma K a) (hx : orderOf x = 3) :
    PerfectInLayer (MulAut.conj x) := by
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU
    a K hK x hx
  have hK' : Nat.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]
  have hq := (CFSG.RankThree.PartTwo.Sec8.Item87Proof.isQuasisimple_statedSU_three
    (F := GaloisField 2 (2 * (2 * a + 1))) (f := 2 * a + 1) hK' (by omega)).1
  apply perfectInLayer_of_nqs
  rw [fixSubgroup_conj]
  exact nqs_congr e.symm (nqs_of_isQuasisimple hq)

private theorem perfectInLayer_reeGamma
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {β : MulAut (ReeTag.F4.reeGamma K a)} (hβ : β ^ p = 1) (hβ1 : β ≠ 1) :
    PerfectInLayer β := by
  classical
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF β
  have hΨα : Ψ ⟨x, σ⟩ = β := by rw [hΨ x σ]; exact hxσ.symm
  let Θ : MulAut (ReeTag.F4.reeGamma K a) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘ : Θ β = σ := by
    show SemidirectProduct.rightHom (Ψ.symm β) = σ
    rw [← hΨα, MulEquiv.symm_apply_apply]
    rfl
  have hσp : σ ^ p = 1 := by rw [← hΘ, ← map_pow, hβ, map_one]
  have hone : ReeTag.F4.reeGammaFieldAut K a 1 = 1 :=
    map_one (ReeTag.F4.reeGammaFieldAutHom K a)
  by_cases hσ1 : σ = 1
  · have hβx : β = MulAut.conj x := by
      rw [hxσ]
      change MulAut.conj x * ReeTag.F4.reeGammaFieldAut K a σ = _
      rw [hσ1, hone, mul_one]
    have hZ : Subgroup.center (ReeTag.F4.reeGamma K a) = ⊥ :=
      ReeTag.large_Ree_fixed_group_center_trivial a K hK
    obtain ⟨y, hy, hyp, hy1⟩ := exists_eq_conj_of_mem_range hZ ⟨x, hβx.symm⟩ hβ hβ1
    rw [hy]
    have hyo : orderOf y = p := orderOf_eq_prime hyp hy1
    by_cases hp3 : p = 3
    · subst hp3
      exact perfectInLayer_inner_three ha hK y hyo
    · have h4 : p ≠ 4 := by
        rintro rfl
        norm_num at hp
      have h2 := hp.two_le
      exact perfectInLayer_inner_gt3 ha hK hp (by omega) y hyo
  · have hσo : orderOf σ = p := orderOf_eq_prime hσp hσ1
    obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.RF4.largeRee_fieldAut_coset_conj a hK hp σ hσo β hβ
      ⟨x, hxσ⟩
    rw [hg]
    exact LieSemisimple.perfectInLayer_conj _ _
      (perfectInLayer_of_nqs _ (nqs_fixSubgroup_fieldAut hK hp hp2 σ hσo))

theorem perfectInLayer_reeF4
    (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {β : MulAut S} (hβ : β ^ p = 1) (hβ1 : β ≠ 1) :
    CFSG.HardMathSupport.Solomon.Coordinator.PerfectInLayer β := by
  obtain ⟨e0⟩ := he
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index m hv e0
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hR
  refine LieSemisimple.perfectInLayer_of_congr e β ?_
  refine perfectInLayer_reeGamma ha hK hp hp2 ?_ ?_
  · rw [← map_pow, hβ, map_one]
  · exact fun h => hβ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))

end CFSG.HardMathSupport.Dickson.SuzukiReeB
