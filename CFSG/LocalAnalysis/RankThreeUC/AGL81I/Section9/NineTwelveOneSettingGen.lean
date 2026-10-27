module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineOne
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneComp
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneLayer
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneSolv
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKStar
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.Assembly.InCatalog
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.LocalCores.Components
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinTransport
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenLayer
import CFSG.LocalAnalysis.RankThreeUC.AGL81CStarImgEquiv
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.Main
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.Faithful
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.Lift
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneSection
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineElevenGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineSixStarEGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenOneIGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenLayerGen

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup CFSG.LocalAnalysis.RankThreeUC.S15

variable {G : Type} [Group G] [Finite G] {M Q H E : Subgroup G} {p : ℕ}

@[expose] def NineSixLowDimSectionGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G) (p : ℕ),
    NineSettingGen G M p Q H E 2 → H ∈ H2Fam M Q → p ∉ sigmaM G M → ¬ pLayerIn p H ≤ M →
    ∀ L : Subgroup G, IsPComponentIn p L (kSub p M H) →
    ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → q ≠ p →
      IsLowDimSimpleSection q
        ((↥L ⧸ CFSG.pPrimeCore p ↥L) ⧸ center (↥L ⧸ CFSG.pPrimeCore p ↥L)) →
      p = 3 ∧ Nonempty (((↥L ⧸ CFSG.pPrimeCore p ↥L) ⧸ center (↥L ⧸ CFSG.pPrimeCore p ↥L)) ≃*
        alternatingGroup (Fin 6))

@[expose] def NineSixAutSectionGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q H E : Subgroup G) (p : ℕ),
    NineSettingGen G M p Q H E 2 → H ∈ H2Fam M Q → p ∉ sigmaM G M → ¬ pLayerIn p H ≤ M →
    ∀ L : Subgroup G, IsPComponentIn p L (kSub p M H) →
    ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p →
    ∀ (V : Type) [Group V] [Finite V], IsPGroup q V → CFSG.Open.pRank q (⊤ : Subgroup V) ≤ 3 →
    ∀ (A : Subgroup (MulAut V))
      (φ : ↥A →* (↥L ⧸ CFSG.pPrimeCore p ↥L) ⧸ center (↥L ⧸ CFSG.pPrimeCore p ↥L)),
      Function.Surjective φ →
      p = 3 ∧ Nonempty (((↥L ⧸ CFSG.pPrimeCore p ↥L) ⧸ center (↥L ⧸ CFSG.pPrimeCore p ↥L)) ≃*
        alternatingGroup (Fin 6))

private lemma isElemAbelian_range_gen {X Y : Type*} [Group X] [Group Y] {p : ℕ}
    {D : Subgroup X} (hD : CFSG.Open.IsElemAbelian p D) (ψ : ↥D →* Y) :
    CFSG.Open.IsElemAbelian p ψ.range := by
  have h := (hD.subgroupOf D).map ψ
  simpa [Subgroup.subgroupOf_self, Subgroup.map_top] using h

private lemma injective_comp_inclusion_gen {X : Type*} [Group X] {C D Γ : Subgroup X}
    (hC : Group.IsPerfect ↥C) (hDN : D ≤ normalizer (C : Set X))
    (hΓ : (⨆ (e : X) (_ : e ∈ D) (_ : e ≠ 1), centralizer ({e} : Set X)) ≤ Γ)
    (hCΓ : ¬ C ≤ Γ) :
    Function.Injective ((normalizerQuotCenterHom C).comp (Subgroup.inclusion hDN)) := by
  rw [injective_iff_map_eq_one]
  intro d hd
  by_contra hne
  have hd' : (d : X) ≠ 1 := fun h => hne (Subtype.ext h)
  refine hCΓ ((le_centralizer_of_normalizerQuotCenterHom_eq_one hC hd).trans (le_trans ?_ hΓ))
  exact le_iSup_of_le (d : X) (le_iSup_of_le d.2 (le_iSup_of_le hd' le_rfl))

private lemma closure_eq_top_of_range_gen {X : Type*} [Group X] {C D : Subgroup X} {p : ℕ}
    (hDN : D ≤ normalizer (C : Set X))
    (hgen : closure {x : ↥C ⧸ center ↥C | ¬ p ∣ orderOf x ∧
      ∃ α ∈ ((normalizerQuotCenterHom C).comp (Subgroup.inclusion hDN)).range,
        α ≠ 1 ∧ α x = x} = ⊤) :
    closure {x : ↥C ⧸ center ↥C | ¬ p ∣ orderOf x ∧
      ∃ g : ↥(normalizer (C : Set X)), (g : X) ∈ D ∧
        normalizerQuotCenterHom C g ≠ 1 ∧ normalizerQuotCenterHom C g x = x} = ⊤ := by
  rw [eq_top_iff, ← hgen]
  refine closure_mono ?_
  rintro x ⟨hx, _, ⟨d, rfl⟩, hne, hfix⟩
  exact ⟨hx, Subgroup.inclusion hDN d, d.2, hne, hfix⟩

private lemma le_of_kFact_gen (hK : KFactLowDimPPrimeGen) {X : Type} [Group X] [Finite X]
    {q p : ℕ} [Fact q.Prime] (hp : p.Prime) (hq2 : q ≠ 2) (hp2 : p ≠ 2) (hqp : q ≠ p)
    {C D Γ : Subgroup X} (hC : CFSG.IsQuasisimple ↥C)
    (hS : IsLowDimSimpleSection q (↥C ⧸ center ↥C))
    (hA6 : ¬ (p = 3 ∧ Nonempty ((↥C ⧸ center ↥C) ≃* alternatingGroup (Fin 6))))
    (hD : CFSG.Open.IsElemAbelian p D) (hDcard : Nat.card D = p ^ 2)
    (hDN : D ≤ normalizer (C : Set X))
    (hΓ : (⨆ (e : X) (_ : e ∈ D) (_ : e ≠ 1), centralizer ({e} : Set X)) ≤ Γ) : C ≤ Γ := by
  by_contra hCΓ
  have : IsSimpleGroup (↥C ⧸ center ↥C) := hC.2.1
  have hnc : ¬ IsMulCommutative (↥C ⧸ center ↥C) := fun h =>
    let ⟨a, b, hab⟩ := hC.2.2
    hab (h.is_comm.comm a b)
  have hinj := injective_comp_inclusion_gen hC.1 hDN hΓ hCΓ
  have hcard : Nat.card ((normalizerQuotCenterHom C).comp (Subgroup.inclusion hDN)).range =
      p ^ 2 := by
    rw [← hDcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hgen := hK q p hp hq2 hp2 hqp (↥C ⧸ center ↥C) hnc hS _ (isElemAbelian_range_gen hD _)
    hcard hA6
  have hE : IsPGroup p D := fun g => ⟨1, Subtype.ext (by simpa using hD.2 g g.2)⟩
  exact hCΓ ((le_iSup_centralizer_of_closure_eq_top hC.1 hp hDN hE
    (closure_eq_top_of_range_gen hDN hgen)).trans hΓ)

private theorem mem_of_isComponent_le_sSup_gen {X : Type} [Group X] [Finite X] {C : Subgroup X}
    {S : Set (Subgroup X)} (hC : CFSG.IsComponent C) (hS : ∀ D ∈ S, CFSG.IsComponent D)
    (hle : C ≤ sSup S) : C ∈ S := by
  by_contra hCS
  have hcen : sSup S ≤ Subgroup.centralizer (C : Set X) := by
    refine sSup_le fun D hD => ?_
    have hDC : D ≠ C := fun hDC => hCS (hDC ▸ hD)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((CFSG.LocalCores.distinct_components_commute (hS D hD) hC).resolve_left hDC)
  have hbot : ⁅C, C⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hle.trans hcen)
  have hperf : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.mp hC.1.1
  rw [hbot] at hperf
  exact (Subgroup.nontrivial_iff_ne_bot C).mp (CFSG.LocalCores.isQuasisimple_nontrivial hC.1)
    hperf.symm

private theorem iSup_centralizer_starImgE_le_gen (h : NineSettingGen G M p Q H E 2) :
    (⨆ (e : StarGroup p H) (_ : e ∈ starImg p H E) (_ : e ≠ 1),
      Subgroup.centralizer ({e} : Set (StarGroup p H))) ≤ starImg p H M := by
  refine iSup_le fun e => iSup_le fun he => iSup_le fun he1 => ?_
  have : Fact p.Prime := ⟨h.prime⟩
  have hep : e ^ p = 1 := (NineSettingGen.isElemAbelian_starImg_E_gen h).2 e he
  have hcard : Nat.card (Subgroup.zpowers e) = p ^ 1 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hep he1, pow_one]
  have hrank : 1 ≤ CFSG.Open.pRank p (Subgroup.zpowers e) :=
    CFSG.SectionRank.le_pRank (p := p) h.prime.one_lt le_rfl
      (CFSG.Open.isElemAbelian_zpowers hep) hcard
  have hN := CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore
    (p := p) (k := 1) (Subgroup.zpowers_le.mpr he) hrank
  have hcent : Subgroup.centralizer ({e} : Set (StarGroup p H)) =
      Subgroup.centralizer (Subgroup.zpowers e : Set (StarGroup p H)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcent]
  exact (Subgroup.centralizer_le_normalizer (Subgroup.zpowers e : Set (StarGroup p H))).trans
    (hN.trans (NineSettingGen.rankThreeGamma_starImg_E_le_gen h))

private theorem isPComponentIn_and_not_le_of_kSub_gen (h : NineSettingGen G M p Q H E 2)
    (hL : ¬ pLayerIn p H ≤ M) {L : Subgroup G} (hLK : IsPComponentIn p L (kSub p M H)) :
    IsPComponentIn p L H ∧ ¬ L ≤ M := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hLH : L ≤ H := hLK.1.trans (kSub_le p M H)
  have hPC : IsPComponentIn p L H := ⟨hLH,
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff p L H hLH).mpr
      ⟨hLK.isSubnormal_of_kSub hL,
        ((CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_iff p L _
          hLK.1).mp hLK.2).2⟩⟩
  refine ⟨hPC, fun hLM => ?_⟩
  have hle : starImg p H L ≤ kStar p M H :=
    Subgroup.map_mono (Subgroup.comap_mono hLK.1)
  rw [h.kStar_eq_sSup_of_not_le hL] at hle
  exact (mem_of_isComponent_le_sSup_gen (isComponent_starImg hPC) (fun _ hD => hD.1) hle).2
    ((NineSettingGen.le_iff_starImg_le h hLH).mp hLM)

theorem nineSixLowDimSectionGen_of (hK : KFactLowDimPPrimeGen) : NineSixLowDimSectionGen := by
  intro G _ _ M Q H E p h _ _ hL L hLK q _ hq2 hqp hS
  by_contra hneg
  obtain ⟨hLH, hLM⟩ := isPComponentIn_and_not_le_of_kSub_gen h hL hLK
  have hp := h.prime
  obtain ⟨e₀⟩ := hLH.nonempty_quotEquiv_starImg hp
  let e := QuotientGroup.congr _ _ e₀ (Subgroup.map_center_eq e₀)
  have hC := isComponent_starImg hLH
  have hCM : ¬ starImg p H L ≤ starImg p H M :=
    fun h' => hLM ((NineSettingGen.le_iff_starImg_le h hLH.1).2 h')
  refine hCM (le_of_kFact_gen hK hp hq2 h.ne_two hqp hC.1
    (isLowDimSimpleSection_of_mulEquiv e.symm hS) ?_
    (NineSettingGen.isElemAbelian_starImg_E_gen h) (NineSettingGen.card_starImg_E_gen h)
    (NineSettingGen.starImg_E_le_normalizer_gen h hC hCM)
    (iSup_centralizer_starImgE_le_gen h))
  rintro ⟨hp3, ⟨f⟩⟩
  exact hneg ⟨hp3, ⟨e.trans f⟩⟩

theorem nineSixAutSectionGen_of (hB : LowDimMulAutSection) (h : NineSixLowDimSectionGen) :
    NineSixAutSectionGen := by
  intro G _ _ M Q H E p hset hH2 hp hL L hLK q hq hq2 hqp V _ _ hV hrk A φ hφ
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨-, hs, a, b, hab⟩ := IsPComponentIn.isQuasisimple_quot hset.prime hLK
  have hnc : ¬ IsMulCommutative
      ((↥L ⧸ CFSG.pPrimeCore p ↥L) ⧸ center (↥L ⧸ CFSG.pPrimeCore p ↥L)) :=
    fun hc => hab (hc.is_comm.comm a b)
  exact h G M Q H E p hset hH2 hp hL L hLK q hq2 hqp (hB q hq2 V hV hrk A _ hnc φ hφ)

namespace NineSettingGen

theorem nineTwelveOne (hsec : NineSixAutSectionGen) (hK3 : KFactAutRankThreeSolvable)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (h : NineSettingGen G M p Q H E 2) (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M)
    (hL : ¬ pLayerIn p H ≤ M) {L : Subgroup G} (hLK : IsPComponentIn p L (kSub p M H)) :
    IsTwoPrimeComponentIn L H ∨
      (p = 3 ∧ Nonempty (↥L ⧸ CFSG.solvableRadical ↥L ≃* alternatingGroup (Fin 6))) := by
  have hp' : p.Prime := h.prime
  have hp2 : p ≠ 2 := h.ne_two
  have hLH : L ≤ H := hLK.1.trans (kSub_le p M H)
  have hLs : (L.subgroupOf H).IsSubnormal := hLK.isSubnormal_of_kSub hL
  haveI : Group.IsPerfect ↥L := hLK.isPerfect hp'
  by_cases hc : CFSG.pPrimeCore p (↥L ⧸ CFSG.pCore 2 ↥L) ≤
      center (↥L ⧸ CFSG.pCore 2 ↥L)
  · exact Or.inl (isTwoPrimeComponentIn_of_le_center hp' hp2 hL hLK hc)
  · right
    have hgen :
        closure {y : ↥L ⧸ CFSG.pCore 2 ↥L | ∃ n : ℕ, orderOf y = p ^ n} = ⊤ :=
      closure_pElem_quot_eq_top (Y := ↥L) hp' (CFSG.pCore 2 ↥L)
        (IsPComponentIn.closure_pElem_eq_top hp' hLK)
    have h2 : CFSG.pCore 2 (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := pCore_two_quot_eq_bot (Y := ↥L)
    obtain ⟨e₀⟩ := nonempty_quot_pPrimeCore_quot_mulEquiv (Y := ↥L) hp' hp2
    have hq : CFSG.IsQuasisimple ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸
        CFSG.pPrimeCore p (↥L ⧸ CFSG.pCore 2 ↥L)) :=
      CFSG.IsQuasisimple.of_mulEquiv e₀ (IsPComponentIn.isQuasisimple_quot hp' hLK)
    have hrk : ∀ r : ℕ, r.Prime → r ≠ 2 →
        CFSG.Open.pRank r (CFSG.pPrimeCore p (↥L ⧸ CFSG.pCore 2 ↥L)) ≤ 3 :=
      fun r hr hr2 => (pRank_pPrimeCore_quot_le (Y := ↥L) hp' hp2 hr hr2).trans
        (NineSettingGen.pRank_pPrimeCore_le_three h hLH hLs hr hr2)
    have hK : CFSG.Open.IsKGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
      (NineSettingGen.isKGroup_of_le h hLH).quotient (CFSG.pCore 2 ↥L)
    have hE : CFSG.layer ↥(CFSG.pPrimeCore p (↥L ⧸ CFSG.pCore 2 ↥L)) = ⊥ :=
      layer_pPrimeCore_eq_bot (Y := ↥L ⧸ CFSG.pCore 2 ↥L) hp' hgen hK hS hrk
    obtain ⟨q, hq', hq2, hqp, V, hV, hrank, A, φ, hφ⟩ :=
      exists_mulAut_surjective_of_not_le_center (Y := ↥L ⧸ CFSG.pCore 2 ↥L)
        hp' hgen h2 hq hE hrk hc
    obtain ⟨e₁⟩ := nonempty_center_quot_mulEquiv e₀
    let φ' : ↥A →* (↥L ⧸ CFSG.pPrimeCore p ↥L) ⧸
        center (↥L ⧸ CFSG.pPrimeCore p ↥L) := e₁.toMonoidHom.comp φ
    have hφ' : Function.Surjective φ' := e₁.surjective.comp hφ
    obtain ⟨hp3, ⟨e₂⟩⟩ :=
      hsec G M Q H E p h hH2 hp hL L hLK q hq' hq2 hqp ↥V hV hrank A φ' hφ'
    cases hp3
    have hN : Group.IsSolvable ↥(CFSG.pPrimeCore 3 (↥L ⧸ CFSG.pCore 2 ↥L)) :=
      isSolvable_pPrimeCore_three hK3 h2 hE hrk
    have hN' : Group.IsSolvable ↥(CFSG.pPrimeCore 3 ↥L) :=
      isSolvable_pPrimeCore_of_quot (Y := ↥L) hp' hp2 hN
    exact ⟨rfl, nonempty_quot_solvableRadical_mulEquiv hN'
      (IsPComponentIn.isQuasisimple_quot hp' hLK) e₂⟩

end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
