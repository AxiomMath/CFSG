module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallResidues
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallCentralizer
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeK
import CFSG.LocalAnalysis.SectionRank.TwoGenerators
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

private theorem pRank_le_one_of_isCyclic_subgroup {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {C : Subgroup X} (hC : IsCyclic C) : Open.pRank p C ≤ 1 :=
  CFSG.SectionRank.pRank_le_one_of_isCyclic hp hC

namespace ReducedNongeneration

variable {p : ℕ} {X : Type} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem false_of_alphaFive_of_mem (h : ReducedNongeneration p X R X₀)
    (hR4 : 4 ≤ Open.pRank p (R : Subgroup X)) (hX : CatalogSimpleSections X) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∈ K) (hK9 : KFactAlphaFive)
    (hp5 : 5 ≤ p) : False := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hnc := h.not_isCyclic_inf_of_mem hz hzp hK hzK
  obtain ⟨T, hT⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal R hKn.isSubnormal
  rcases hK9 K hK.2.2 (hX.isCatalogGroup_center_quotient hK) p hp hp5
      (center_ne_bot_of_mem hp hz hzp hzK) (isPGroup_center_of_isComponentOf hp h.core_eq_bot hK)
      (h.isCyclic_center hK hKn) T with ⟨hgen, h3 | hout⟩ | hb | ⟨hc, h3⟩
  · exact h.false_of_three_le_pRank_of_le hKn (h.le_of_kGenThree hR4 hz hzp hK hKn hzK hgen) h3
  · exact h.false_of_kOutNormalSylow (h.le_of_kGenThree hR4 hz hzp hK hKn hzK hgen)
      (h.centralizer_le_of_not_isCyclic hKn hnc) hout
  · exact h.false_of_pRank_mulAut_le_two hR4 hz hzp hK hKn hzK hb
  · exact h.false_of_three_le_pRank_of_le hKn (h.le_of_glbCore_eq_top hT hc) h3

theorem exists_sylow_of_not_mem (h : ReducedNongeneration p X R X₀)
    (hR4 : 4 ≤ Open.pRank p (R : Subgroup X)) (hX : CatalogSimpleSections X) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∉ K) (hβ : KFactBeta) :
    IsSimpleGroup K ∧ (∃ a b : K, a * b ≠ b * a) ∧ IsCatalogGroup K ∧
      3 ≤ Open.pRank p (⊤ : Subgroup (MulAut K)) ∧
      ∃ T : Sylow p K, ¬ IsCyclic (T : Subgroup K) ∧ GLBCore p 1 (T : Subgroup K) ≠ ⊤ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hZ, hcycC, hfacts⟩ := h.rankOneLieAutFacts_of_not_mem hR4 hX hz hzp hK hKn hzK hβ
  let e : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
  have hsimple : IsSimpleGroup K := e.isSimpleGroup
  have hnonab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.2.2
    refine ⟨e.symm a, e.symm b, fun hba => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hba
  have hcat : IsCatalogGroup K :=
    IsCatalogGroup.of_mulEquiv e (hX.isCatalogGroup_center_quotient hK)
  obtain ⟨T, hT⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal R hKn.isSubnormal
  have hAut : 3 ≤ Open.pRank p (⊤ : Subgroup (MulAut K)) := by
    have hineq := pRank_le_pRank_inf_centralizer_add_pRank_map_conjNormal hp K (R : Subgroup X)
    have h1 := pRank_le_one_of_isCyclic_subgroup hp hcycC
    have h2 := pRank_mono p hp
      (le_top : (R : Subgroup X).map (MulAut.conjNormal (H := K)) ≤ ⊤)
    omega
  have hTnc : ¬ IsCyclic (T : Subgroup K) := fun hTc => by
    have := pRank_mulAut_le_two_of_kOutRankLeOne hp hZ
      (fun B hB => card_le_of_isElemAbelian_of_isCyclic_sylow T hTc hB) hfacts.1
    omega
  have hnc : ¬ IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X) := fun hc => hTnc (by
    rw [← hT] at hc
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective _ _ K.subtype_injective).symm (MulEquiv.surjective _))
  obtain ⟨hN, hKX₀⟩ := (h.center_eq_bot_and_rankOne_of_not_mem hz hzp hK hzK).2 hnc
  exact ⟨hsimple, hnonab, hcat, hAut, T, hTnc, h.glbCore_ne_top_of_rankOne hN hKX₀ hT⟩

end ReducedNongeneration

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1ComponentConfig.exists_surjective_of_reducedCentralizer
    (hcfg : D1ComponentConfig p P M H R Rbar) {L : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hLp : Group.IsPerfect L) (hLs : IsSimpleGroup L) {x : L} (hx : x ≠ 1) {k : ℕ}
    (hxk : x ^ p ^ k = 1) {z : G} (hzH : z ∈ H) (hzp : orderOf z = p)
    (hzL : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩ ∈
      Subgroup.centralizer (L : Set (H ⧸ primeComplementCore (G := H) p)))
    {P' : Sylow p G} {Pbar : Sylow p (D1CzQuot p z)} {KC : Subgroup (D1CzQuot p z)}
    (hRC : D1ReducedCentralizer p P' M z Pbar KC) (hSch : KFactCatalogSchreier) :
    ∃ (A : Subgroup KC) (f : A →* L), Function.Surjective f := by
  have hp := hcfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hO := primeComplementCore_coprime (G := H) p
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set W : Subgroup G := Subgroup.centralizer ({z} : Set G) ⊓ (L.comap π).map H.subtype
  have hWH : W ≤ H := inf_le_right.trans (Subgroup.map_subtype_le _)
  have hWC : W ≤ Subgroup.centralizer ({z} : Set G) := inf_le_left
  have hφ₀ : ∀ w : W, π (Subgroup.inclusion hWH w) ∈ L := by
    rintro ⟨w, -, h, hh, rfl⟩
    exact hh
  set φ : W →* L := (π.comp (Subgroup.inclusion hWH)).codRestrict L hφ₀
  have hzH' : orderOf (⟨z, hzH⟩ : H) = p := (Subgroup.orderOf_coe _).symm.trans hzp
  have hφ : Function.Surjective φ := by
    intro l
    obtain ⟨g, hg, hgl⟩ := exists_mem_centralizer_mk_eq hp _ hO
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzH', pow_one]))
      (Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzL l l.2))
    have hgC : (g : G) ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg))
    have hgL : g ∈ L.comap π := by
      rw [Subgroup.mem_comap, hgl]
      exact l.2
    exact ⟨⟨g, hgC, g, hgL, rfl⟩, Subtype.ext hgl⟩
  exact hRC.exists_surjective_of_isSimpleGroup hSch hWC hLp φ hφ hx hxk

theorem D1OneSmallData.exists_surjective_of_reducedCentralizer
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    {P' : Sylow p G} {Pbar : Sylow p (D1CzQuot p z)} {KC : Subgroup (D1CzQuot p z)}
    (hRC : D1ReducedCentralizer p P' M z Pbar KC) (hSch : KFactCatalogSchreier) :
    ∃ (A : Subgroup KC) (f : A →* K), Function.Surjective f := by
  obtain ⟨-, hzp, hzH, hzC⟩ := hz
  obtain ⟨T₁, -, -, -, -, hT₁nc, -⟩ := hd.exists_sylow
  obtain ⟨x, hx⟩ : ∃ x : (T₁ : Subgroup K), x ≠ 1 :=
    (Subgroup.ne_bot_iff_exists_ne_one).mp fun h => hT₁nc (h ▸ inferInstance)
  obtain ⟨k, hk⟩ := T₁.isPGroup' x
  exact hd.cfg.exists_surjective_of_reducedCentralizer ⟨hd.comp.2.2.1⟩ hd.isSimpleGroup.1
    (x := (x : K)) (fun h1 => hx (Subtype.ext h1)) (k := k)
    (by rw [← Subgroup.coe_pow, hk, Subgroup.coe_one]) hzH hzp hzC hRC hSch

end Config

theorem stmtSmallSPIn_of (hK9 : KFactAlphaFive) : StmtSmallSPIn := by
  intro G _ _ p P M H R Rbar K hd _ z hz _ hp5 hSP hin
  obtain ⟨P', Pbar, KC, -, -, -, hRC⟩ := hd.exists_reducedCentralizer hz hSP
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨hzZ, hzp⟩ := hRC.center ⟨z, hzC⟩ rfl
  have hzK : d1CzElt p z ∈ KC := by
    by_contra hzK
    refine hin fun L hL => ?_
    rw [hRC.unique L hL]
    exact hzK
  exact hRC.red.false_of_alphaFive_of_mem hRC.four_le_pRank hRC.catalog hzZ hzp hRC.comp
    hRC.normal hzK hK9 hp5

theorem stmtSmallSPOut_of (hβ : KFactBeta) (hK10 : KFactSmallInvolve)
    (hSch : KFactCatalogSchreier) : StmtSmallSPOut := by
  intro G _ _ p P M H R Rbar K hd _ z hz _ hSP hout hnSPL
  obtain ⟨P', Pbar, KC, -, -, -, hRC⟩ := hd.exists_reducedCentralizer hz hSP
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨hzZ, hzp⟩ := hRC.center ⟨z, hzC⟩ rfl
  obtain ⟨hs, hn, hc, hAut, T, hTnc, hΓ⟩ := hRC.red.exists_sylow_of_not_mem hRC.four_le_pRank
    hRC.catalog hzZ hzp hRC.comp hRC.normal (hout KC hRC.comp) hβ
  obtain ⟨A, f, hf⟩ := hd.exists_surjective_of_reducedCentralizer hz hRC hSch
  obtain ⟨T₁, -, hs₁, hn₁, hc₁, hT₁nc, hΓ₁, -⟩ := hd.exists_sylow
  exact hnSPL (hK10 KC hs hn hc p hd.cfg.red.prime hd.cfg.red.ne_two T hTnc hΓ hAut K hs₁ hn₁ hc₁
    T₁ hT₁nc hΓ₁ hd.small A f hf)

end CFSG.AGLEmbedding
