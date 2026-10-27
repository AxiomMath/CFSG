module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveTwTheta
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSU
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUTwo
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructTwE6Levi
import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreOfFuse
import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2
import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldImages

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.SeitzReduction CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.SeitzReduction.TwistedE6Pilot CFSG.LieType.Chevalley.E6GraphLevi
open CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.LieType.Chevalley.E6GraphHighestRoot
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Chevalley.E6GraphRootSL2 CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.StandardType
open CFSG.StandardType.TwE6CorootCore
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.SectionRank.OddCover

local notation "Γ₂" F => ModGL TwistTag.E6.tag F


private lemma exists_isJUnitary_conj_of_mem_sup {f : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2]
    (hF : Nat.card F = (2 ^ f) ^ 2) {σ : F ≃+* F} (hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ f)
    {ψ₀ : ↥(SU (unitaryInvolution F 2 f) 6) →* Γ₂ F}
    (hψ₀ : ∀ u, ψ₀ u =
      ((KGTwE6.su6LeviHom hF hσ' u : ↥((su6Levi σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.E6 F σ.toRingHom))) : Γ₂ F))
    (hr₀ : ψ₀.range = su6Levi σ.toRingHom)
    (hTN : twistedE6DiagGL F σ ≤
      Subgroup.normalizer (su6Levi σ.toRingHom : Set (Γ₂ F))) :
    ∀ a ∈ su6Levi σ.toRingHom ⊔ twistedE6DiagGL F σ,
      ∃ (A : GL (Fin 6) F) (hA : InnerDiagSU.IsJUnitary (unitaryInvolution F 2 f) A),
        ∀ u, a * ψ₀ u * a⁻¹ = ψ₀ (InnerDiagSU.conjSU A hA u) := by
  intro a ha
  have ha' : a ∈ ((su6Levi σ.toRingHom ⊔ twistedE6DiagGL F σ : Subgroup (Γ₂ F)) :
      Set (Γ₂ F)) := ha
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hTN] at ha'
  obtain ⟨s, hs, t, ht, rfl⟩ := ha'
  obtain ⟨B₀, rfl⟩ : s ∈ ψ₀.range := hr₀ ▸ hs
  obtain ⟨b, hb, rfl⟩ := (mem_twistedE6DiagGL_iff F σ).1 ht
  obtain ⟨α, ⟨A, hA, hAα⟩, hα⟩ :=
    KGTwE6.exists_suConjSet_compatParamAut hF hσ' ⟨b, hb⟩
  refine ⟨(B₀ : GL (Fin 6) F) * A, (InnerDiagSU.isJUnitary_of_mem_SU B₀).mul hA,
    fun u => ?_⟩
  have htu : rootDiagUnit TwistTag.E6.tag b * ψ₀ u * (rootDiagUnit TwistTag.E6.tag b)⁻¹ =
      ψ₀ (InnerDiagSU.conjSU A hA u) := by
    have h1 := hα (KGTwE6.su6LeviHom hF hσ' u)
    rw [hAα] at h1
    have h2 := congrArg Subtype.val h1
    rw [RootCentExc.coe_compatParamAut_apply] at h2
    rw [hψ₀ u, hψ₀ (InnerDiagSU.conjSU A hA u)]
    exact h2.symm
  have hconj : InnerDiagSU.conjSU ((B₀ : GL (Fin 6) F) * A)
      ((InnerDiagSU.isJUnitary_of_mem_SU B₀).mul hA) u =
      B₀ * InnerDiagSU.conjSU A hA u * B₀⁻¹ := by
    apply Subtype.ext
    simp only [InnerDiagSU.coe_conjSU, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [hconj, map_mul, map_mul, map_inv, ← htu]
  group

theorem exists_unitarySU_hom_su6Levi {f : ℕ} {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 f F) {σ : F ≃+* F} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ ψ : ↥(unitarySU 2 f F 6) →* Γ₂ F,
      ψ.range = su6Levi σ.toRingHom ∧ ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f F 6) ∧
      ∀ a ∈ su6Levi σ.toRingHom ⊔ twistedE6DiagGL F σ,
        ∃ B ∈ primeFormUnitary h (idGram F 6), (a, B) ∈ SUTorus.suPairs ψ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := h.charP
  have hF : Nat.card F = (2 ^ f) ^ 2 := h.card_eq_sq
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ f := hσ
  set C₀ := graphFixedRootGroup TwistTag.E6 F σ.toRingHom with hC₀
  set φ := KGTwE6.su6LeviHom hF hσ' with hφ
  let ψ₀ : ↥(SU (unitaryInvolution F 2 f) 6) →* Γ₂ F :=
    C₀.subtype.comp (((su6Levi σ.toRingHom).subgroupOf C₀).subtype.comp φ)
  have hψ₀ : ∀ u, ψ₀ u = (((φ u : ↥((su6Levi σ.toRingHom).subgroupOf C₀)) : ↥C₀) : Γ₂ F) :=
    fun u => rfl
  have hr₀ : ψ₀.range = su6Levi σ.toRingHom := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (φ u).2
    · intro hy
      have hyC : y ∈ C₀ := su6Levi_le_graphFixedRootGroup σ.toRingHom hy
      obtain ⟨u, hu⟩ := KGTwE6.su6LeviHom_surjective hF hσ'
        ⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.2 hy⟩
      exact ⟨u, by rw [hψ₀, hu]⟩
  have hker₀ : ψ₀.ker ≤ Subgroup.center ↥(SU (unitaryInvolution F 2 f) 6) := by
    intro u hu
    apply KGTwE6.ker_su6LeviHom_le_center hF hσ'
    rw [MonoidHom.mem_ker] at hu ⊢
    exact Subtype.ext (Subtype.ext hu)
  have hTN : twistedE6DiagGL F σ ≤ Subgroup.normalizer (su6Levi σ.toRingHom : Set (Γ₂ F)) := by
    intro d hd
    obtain ⟨b, hb, rfl⟩ := (mem_twistedE6DiagGL_iff F σ).1 hd
    exact mem_normalizer_inf_of_mem_normalizer_twE6
      (rootDiagUnit_mem_normalizer_subsystemGroup setA b)
      (rootDiagUnit_mem_normalizer_graphFixedRootGroup hb)
  have hmat := exists_isJUnitary_conj_of_mem_sup hF hσ' hψ₀ hr₀ hTN
  obtain ⟨P, hP⟩ := exists_wittMatrix hF 6
  have hSU : SUid (unitaryInvolution F 2 f) 6 = unitarySU 2 f F 6 := SUid_eq_statedSU hF 6
  set Φ := (conjEquiv P hP).trans (MulEquiv.subgroupCongr hSU) with hΦ
  refine ⟨ψ₀.comp Φ.symm.toMonoidHom, by rw [SUTorus.range_comp_symm, hr₀],
    SUTorus.ker_comp_symm_le hker₀ Φ, fun a ha => ?_⟩
  obtain ⟨A, hA, hAc⟩ := hmat a ha
  exact ⟨P * A * P⁻¹,
    SUTorus.mem_primeFormUnitary_of_isIdUnitary h (InnerDiagSU.isIdUnitary_conj hP hA),
    SUTorus.mem_suPairs_transfer P hP hSU hA hAc⟩

theorem eq_one_of_mem_centralizer_thetaRankOneGroup_su6Levi {f : ℕ} (hf : 1 ≤ f) {k F : Type}
    [Field k] [Field F] [Algebra k F] [Finite F] (hk : Nat.card k = 2 ^ f)
    (hF : Nat.card F = (2 ^ f) ^ 2) {σ : F ≃+* F} (hσ : ∀ c, σ c = c ^ 2 ^ f) {x : Γ₂ F}
    (hx : x ∈ twistedE6InndiagGL F σ)
    (hxθ : x ∈ Subgroup.centralizer (thetaRankOneGroup (algebraMap k F) : Set (Γ₂ F)))
    (hxD : x ∈ Subgroup.centralizer (su6Levi σ.toRingHom : Set (Γ₂ F))) : x = 1 := by
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ f := hσ
  have hK2 : (2 : F) = 0 := two_eq_zero_of_card_sq hf hF
  haveI : CharP k 2 :=
    CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (two_eq_zero_of_card hf hk)
  obtain ⟨A, hA⟩ := CFSG.SeitzReduction.F4Pilot.exists_orderOf_eq_natCard_add_one (K := k)
  have hm : A ^ 1 ≠ 1 := by
    rw [pow_one]
    intro h1
    rw [h1, orderOf_one] at hA
    have : 0 < Nat.card k := Nat.card_pos
    omega
  set ρ := (thetaSL2 F).comp (Matrix.SpecialLinearGroup.map (algebraMap k F)) with hρdef
  have hρJ : ∀ B, ρ B ∈ thetaRankOneGroup (algebraMap k F) := fun B => by
    rw [thetaRankOneGroup_eq_range hK2]
    exact MonoidHom.mem_range.2 ⟨B, rfl⟩
  have hst : x * ρ (A ^ 1) = ρ (A ^ 1) * x :=
    (Subgroup.mem_centralizer_iff.1 hxθ (ρ (A ^ 1)) (hρJ _)).symm
  have hsD : ∀ d ∈ su6Levi σ.toRingHom, x * d = d * x := fun d hd =>
    (Subgroup.mem_centralizer_iff.1 hxD d hd).symm
  have hxJ : x ∈ thetaRankOneGroup (algebraMap k F) := by
    obtain ⟨c, hc, _, ⟨u, hu⟩, rfl⟩ := exists_mul_eq_of_mem_twistedE6InndiagGL σ hx
    subst hu
    have hc' := (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 F σ.toRingHom).1
      (graphFixedRootGroup_le TwistTag.E6 F σ.toRingHom hc)
    have hz := mem_zpowers_of_commute_su6Levi hf hk hF hσ' hA hm hc'.1
      (compatDiag TwistTag.E6 σ.toRingHom u) rfl
      (by rw [map_mul, hc'.2, twistHom_rootDiagUnit fun i => compatDiag_perm u i]) hst hsD
    exact (Subgroup.zpowers_le.2 (hρJ A)) hz
  have hbot := thetaRankOneGroup_inf_eq_bot hK2 (algebraMap k F)
    (C := Subgroup.centralizer (thetaRankOneGroup (algebraMap k F) : Set (Γ₂ F))) le_rfl
  have hmem : x ∈ thetaRankOneGroup (algebraMap k F) ⊓
      Subgroup.centralizer (thetaRankOneGroup (algebraMap k F) : Set (Γ₂ F)) := ⟨hxJ, hxθ⟩
  rw [hbot] at hmem
  exact hmem

theorem inf_centralizer_su6Levi_eq_bot {f : ℕ} (hf : 1 ≤ f) {k F : Type} [Field k] [Field F]
    [Algebra k F] [Finite F] (hk : Nat.card k = 2 ^ f) (hF : Nat.card F = (2 ^ f) ^ 2)
    {σ : F ≃+* F} (hσ : ∀ c, σ c = c ^ 2 ^ f) (h3 : 3 ∣ 2 ^ f + 1) {A : Subgroup (Γ₂ F)}
    (hA3 : IsPGroup 3 A)
    (hAL : A ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA5 ⊔
      twistedE6DiagGL F σ) :
    A ⊓ Subgroup.centralizer (su6Levi σ.toRingHom : Set (Γ₂ F)) = ⊥ := by
  have hAθ := le_centralizer_thetaRankOneGroup hf hk hF hσ h3 hA3 hAL
  have hLN : graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA5 ⊔
      twistedE6DiagGL F σ ≤ twistedE6InndiagGL F σ := by
    refine sup_le ?_ le_sup_right
    exact (graphFixedParabolicLevi_le (t := TwistTag.E6) (K := F) (σ := σ.toRingHom)
      (J := twE6MaxA5)).trans le_sup_left
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxA, hxD⟩ := Subgroup.mem_inf.1 hx
  exact (Subgroup.mem_bot).2 (eq_one_of_mem_centralizer_thetaRankOneGroup_su6Levi hf hk hF hσ
    (hLN (hAL hxA)) (hAθ hxA) hxD)

private lemma card_ne_six_of_diagHom_isBlockOn {F : Type} [Field F]
    {A : Subgroup (Γ₂ F)} {d : Γ₂ F}
    {ψ ψ₂ : ↥(unitarySU 2 1 F 6) →* Γ₂ F}
    (hAC : A ⊓ Subgroup.centralizer (ψ.range : Set (Γ₂ F)) = ⊥)
    (hr₂ : ψ₂.range = ψ.range) (hdA : d ∈ A) (hd1 : d ≠ 1)
    {δ : Fin 6 → Fˣ} (hδd : (d, diagHom 6 δ) ∈ SUTorus.suPairs ψ₂)
    {I : Finset (Fin 6)} (hIc : ∀ i ∈ I, ∀ j ∈ I, δ i = δ j) :
    I.card ≠ 6 := by
  intro h6
  have hIu : I = Finset.univ := Finset.eq_univ_of_card I (by simpa using h6)
  have hdc := SUTorus.mem_centralizer_map_blockSU hδd hIc
  rw [hIu, SUTorus.blockSU_univ, ← MonoidHom.range_eq_map] at hdc
  have hmem : d ∈ A ⊓ Subgroup.centralizer (ψ.range : Set (Γ₂ F)) :=
    ⟨hdA, by rw [← hr₂]; exact hdc⟩
  rw [hAC] at hmem
  exact hd1 hmem

theorem exists_su_of_le_levi_A5_two {k F : Type} [Field k] [Field F] [Algebra k F] [Finite F]
    (hk : Nat.card k = 2) (hF : Nat.card F = 2 ^ 2) {σ : F ≃+* F} (hσ : ∀ c, σ c = c ^ 2)
    {A : Subgroup (Γ₂ F)} (hAel : IsElemAbelian 3 A) (hA4 : 3 ^ 4 ≤ Nat.card A)
    (hAL : A ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA5 ⊔
      twistedE6DiagGL F σ)
    {d : Γ₂ F} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hKL : stdLayerD (twistedE6RootGroup F σ) d ≤
      CFSG.SeitzReduction.TwistedE6Pilot.su6Levi σ.toRingHom)
    (hcomp : IsComponentOf (stdLayerD (twistedE6RootGroup F σ) d)
      (twistedE6RootGroup F σ ⊓ Subgroup.centralizer ({d} : Set (Γ₂ F)))) :
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
      ∃ ρ : ↥(CFSG.Assembly.LargeEvenSUGroup (Fin n) F 2) →*
          ↥(stdLayerD (twistedE6RootGroup F σ) d),
        Function.Surjective ρ ∧ ρ.ker ≤ Subgroup.center _ := by
  classical
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  haveI : Finite (Γ₂ F) := finite_modGL
  have hU : UnitaryFieldData 2 1 F := ⟨Nat.prime_two, le_rfl, by simpa using hF⟩
  have hk' : Nat.card k = 2 ^ 1 := by simpa using hk
  have hF' : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF
  have hσ' : ∀ c, σ c = c ^ 2 ^ 1 := by simpa using hσ
  have hsup := (su6Levi_facts le_rfl hk' hF' (σ := σ.toRingHom) hσ').2.1
  have hW := thetaTorus_le_twistedE6DiagGL le_rfl hk' hF' hσ'
  have hL : graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA5 ≤
      su6Levi σ.toRingHom ⊔ twistedE6DiagGL F σ := by
    rw [graphFixedParabolicLevi, show twE6MaxA5 = foldedSetA from rfl, orbitUnion_foldedSetA,
      ← hsup]
    exact sup_le_sup le_rfl hW
  have hAK : A ≤ su6Levi σ.toRingHom ⊔ twistedE6DiagGL F σ :=
    hAL.trans (sup_le hL le_sup_right)
  have hA3 : IsPGroup 3 A := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hAel.2 x x.2)⟩
  obtain ⟨ψ, hψr, hψk, hψB⟩ := exists_unitarySU_hom_su6Levi hU hσ'
  have hAC : A ⊓ Subgroup.centralizer (ψ.range : Set (Γ₂ F)) = ⊥ := by
    rw [hψr]
    exact inf_centralizer_su6Levi_eq_bot le_rfl hk' hF' hσ' (by norm_num) hA3 hAL
  have hbig : 3 ^ (6 / 3 + 1) < Nat.card A := by
    have : (3 : ℕ) ^ (6 / 3 + 1) = 27 := by norm_num
    omega
  obtain ⟨ψ₂, hr₂, hk₂, hδ⟩ := SUTorus.exists_comp_conjSU_diag hU (n := 6) (by norm_num)
    (by decide) Nat.prime_three (by norm_num) (by norm_num) hψk hAel hbig
    (fun a ha => hψB a (hAK ha)) hAC
  obtain ⟨δ, hδd⟩ := hδ d hdA
  have hcompA := CFSG.Assembly.isComponentOf_iff_open.mpr hcomp
  have hr₂' : ψ₂.range = su6Levi σ.toRingHom := hr₂.trans hψr
  have hK2 : CFSG.Assembly.IsComponentOf (stdLayerD (twistedE6RootGroup F σ) d)
      (ψ₂.range ⊓ Subgroup.centralizer ({d} : Set (Γ₂ F))) := by
    refine hcompA.of_le_of_le (le_inf (by rw [hr₂']; exact hKL) (hcompA.1.trans inf_le_right))
      (inf_le_inf_right _ ?_)
    rw [hr₂']
    exact su6Levi_le_graphFixedRootGroup σ.toRingHom
  obtain ⟨I, hI4, hIc, hKI⟩ :=
    SUTorus.exists_blockSU_of_isComponentOf_two (m := 5) hU hk₂ hδd hK2
  have hI6 : I.card ≠ 6 :=
    card_ne_six_of_diagHom_isBlockOn hAC hr₂ hdA hd1 hδd hIc
  have hIle : I.card ≤ 6 := by simpa using Finset.card_le_univ I
  refine ⟨I.card, by omega, ?_⟩
  obtain ⟨ρ, hρ, hρk⟩ := SUTorus.exists_hom_of_eq_map_blockSU hU hk₂ hKI
  exact ⟨ρ, hρ, hρk⟩

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
