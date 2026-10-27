module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeK
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeakCaseTwo
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeBlocksAux
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKillAux
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.LocalAnalysis.SectionRank.TwoGenerators
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

open scoped commutatorElement

private theorem pRank_le_one_of_isCyclic_subgroup {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {C : Subgroup X} (hC : IsCyclic C) : Open.pRank p C ≤ 1 :=
  CFSG.SectionRank.pRank_le_one_of_isCyclic hp hC

namespace ReducedNongeneration

variable {p : ℕ} {X : Type} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem false_of_caseTwo_of_mem (h : ReducedNongeneration p X R X₀)
    (hR4 : 4 ≤ Open.pRank p (R : Subgroup X)) (hX : CatalogSimpleSections X) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∈ K) (hAE : KFactCaseTwoAlphaElimW)
    (hp35 : p = 3 ∨ p = 5) {A : Subgroup K} {Λ : Type} [Group Λ] (hiso : IsCaseTwoGroup p Λ)
    (f : A →* Λ) (hf : Function.Surjective f) : False := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hnc := h.not_isCyclic_inf_of_mem hz hzp hK hzK
  obtain ⟨T, hT⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal R hKn.isSubnormal
  rcases hAE K hK.2.2 (hX.isCatalogGroup_center_quotient hK) p hp35
      (center_ne_bot_of_mem hp hz hzp hzK) (isPGroup_center_of_isComponentOf hp h.core_eq_bot hK)
      (h.isCyclic_center hK hKn) A Λ hiso f hf T with
    ⟨hgen, h3 | hout⟩ | ⟨hgen, hZ3, hout⟩ | hb | ⟨hc, h3⟩
  · exact h.false_of_three_le_pRank_of_le hKn (h.le_of_kGenThree hR4 hz hzp hK hKn hzK hgen) h3
  · exact h.false_of_kOutNormalSylow (h.le_of_kGenThree hR4 hz hzp hK hKn hzK hgen)
      (h.centralizer_le_of_not_isCyclic hKn hnc) hout
  · exact h.false_of_kOutNormalSylow (h.le_of_kGenTwoModAbFix hz hzp hK hKn hzK hZ3 hgen)
      (h.centralizer_le_of_not_isCyclic hKn hnc) hout
  · exact h.false_of_pRank_mulAut_le_two hR4 hz hzp hK hKn hzK hb
  · exact h.false_of_three_le_pRank_of_le hKn (le_of_weakCore_eq_top h T hT hc) h3

theorem caseTwoCM_of_not_mem (h : ReducedNongeneration p X R X₀)
    (hR4 : 4 ≤ Open.pRank p (R : Subgroup X)) (hX : CatalogSimpleSections X) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∉ K) (hβ : KFactBeta)
    (hCM : KFactCaseTwoCM) (hp35 : p = 3 ∨ p = 5) {A : Subgroup K} {Λ : Type} [Group Λ]
    (hiso : IsCaseTwoGroup p Λ) (f : A →* Λ) (hf : Function.Surjective f) :
    p = 3 ∧ ∀ (B : Subgroup K) (Y : Type) [Group Y] (g : B →* Y), Function.Surjective g →
      IsSimpleGroup Y → (∃ a b : Y, a * b ≠ b * a) →
      (IsClassicalTwoOrG2 Y ∨ IsOrthogonalTwo Y ∨
        ∃ n : ℕ, Nonempty (Y ≃* alternatingGroup (Fin n))) →
      IsCaseTwoGroup 3 Y ∧ ¬ IsOrthogonalTwo Y ∧
        ¬ ∃ n : ℕ, Nonempty (Y ≃* alternatingGroup (Fin n)) := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hZ, hcycC, hfacts⟩ := h.rankOneLieAutFacts_of_not_mem hR4 hX hz hzp hK hKn hzK hβ
  obtain ⟨hsimple, hnonab, hcat⟩ := hX.isSimpleGroup_of_center_eq_bot hK hZ
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
  exact hCM K hsimple hnonab hcat p hp35 T hTnc (h.glbCore_ne_top_of_rankOne hN hKX₀ hT) hAut A
    Λ hiso f hf

end ReducedNongeneration

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} {e : H}

theorem D1CaseTwoEscapeData.exists_surjective_block
    (he : D1CaseTwoEscapeData p P M H R Rbar L e)
    {Pbar : Sylow p (Subgroup.centralizer ({(e : G)} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({(e : G)} : Set G)) p)}
    {K : Subgroup (Subgroup.centralizer ({(e : G)} : Set G) ⧸
      primeComplementCore (G := Subgroup.centralizer ({(e : G)} : Set G)) p)}
    (hRC : D1ReducedCentralizer p P M (e : G) Pbar K) (hSch : KFactCatalogSchreier)
    (hp3 : p = 3) {LB : Subgroup G} (hLB : IsWeakSBlock M (pCoreOf 2 H) LB)
    (hB : BlockHasThree M (pCoreOf 2 H) LB) :
    ∃ (B : Subgroup K) (g : B →* (↥(barM M LB) ⧸ Subgroup.center ↥(barM M LB))),
      Function.Surjective g := by
  have hp := he.data.cfg.red.prime
  have hp2 := he.data.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal
  set πM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  obtain ⟨eM, heO, heM⟩ := he.mem_pCorePreimage
  replace heM : (eM : G) = (e : G) := heM
  have hcomm : ∀ x ∈ barM M LB, x * πM eM = πM eM * x := by
    intro x hx
    have h1 := Subgroup.commutator_mem_commutator (CFSG.pCore_le_fitting _ p heO)
      (CFSG.LocalCores.component_le_layer ((CFSG.isComponent_iff_open _).mpr hLB.component) hx)
    rw [CFSG.LocalCores.fitting_layer_commute, Subgroup.mem_bot] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  set W : Subgroup G :=
    Subgroup.centralizer ({(e : G)} : Set G) ⊓ ((barM M LB).comap πM).map M.subtype
  have hWM : W ≤ M := inf_le_right.trans (Subgroup.map_subtype_le _)
  have hWC : W ≤ Subgroup.centralizer ({(e : G)} : Set G) := inf_le_left
  have hφ₀ : ∀ w : W, πM (Subgroup.inclusion hWM w) ∈ barM M LB := by
    rintro ⟨w, -, m, hm, rfl⟩
    exact hm
  set φ₁ : W →* barM M LB := (πM.comp (Subgroup.inclusion hWM)).codRestrict _ hφ₀
  have heMp : orderOf eM = p := by rw [← Subgroup.orderOf_coe, heM, he.orderOf_eq]
  have hφ₁ : Function.Surjective φ₁ := by
    intro x
    have hcop : p.Coprime (Nat.card (CFSG.pCore 2 ↥M)) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
      rw [hk]
      exact ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right k
    obtain ⟨g, hg, hgx⟩ := exists_mem_centralizer_mk_eq hp _ hcop
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, heMp, pow_one]))
      (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x x.2))
    have hgC : (g : G) ∈ Subgroup.centralizer ({(e : G)} : Set G) := by
      rw [← heM]
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg))
    have hgL : g ∈ (barM M LB).comap πM := by
      rw [Subgroup.mem_comap, hgx]
      exact x.2
    exact ⟨⟨g, hgC, g, hgL, rfl⟩, Subtype.ext hgx⟩
  have hφ : Function.Surjective ((QuotientGroup.mk' (Subgroup.center ↥(barM M LB))).comp φ₁) :=
    (QuotientGroup.mk'_surjective _).comp hφ₁
  have : IsSimpleGroup (↥(barM M LB) ⧸ Subgroup.center ↥(barM M LB)) := hLB.component.2.2.2
  have : Group.IsPerfect ↥(barM M LB) := ⟨hLB.component.2.2.1⟩
  obtain ⟨y, ⟨-, hyL⟩, hy3, l, hl, hyl⟩ := hB
  set ybar : ↥(barM M LB) := ⟨πM ⟨y, hLB.le hyL⟩, ⟨y, hLB.le hyL⟩, hyL, rfl⟩
  have hx : QuotientGroup.mk' (Subgroup.center ↥(barM M LB)) ybar ≠ 1 := by
    intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.mp h1
      ⟨πM ⟨l, hLB.le hl⟩, ⟨l, hLB.le hl⟩, hl, rfl⟩)
    have h3 : πM ⁅(⟨y, hLB.le hyL⟩ : ↥M), ⟨l, hLB.le hl⟩⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr h2.symm
    exact hyl ((mk_eq_one_iff_coe_mem_pCoreOf _).mp h3)
  obtain ⟨k, hk⟩ := hy3 ⟨y, Subgroup.mem_zpowers y⟩
  have hyk : (⟨y, hLB.le hyL⟩ : ↥M) ^ 3 ^ k = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; simpa using congrArg Subtype.val hk)
  have hxk : QuotientGroup.mk' (Subgroup.center ↥(barM M LB)) ybar ^ p ^ k = 1 := by
    have h1 : ybar ^ 3 ^ k = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      change πM ⟨y, hLB.le hyL⟩ ^ 3 ^ k = 1
      rw [← map_pow, hyk, map_one])
    rw [hp3, ← map_pow, h1, map_one]
  exact hRC.exists_surjective_of_isSimpleGroup hSch hWC inferInstance _ hφ hx hxk

end Data

theorem d1CaseTwoEscaping_of (hβ : KFactBeta) (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal)
    (hCM : KFactCaseTwoCM) (hAE : KFactCaseTwoAlphaElimW) (hSch : KFactCatalogSchreier)
    (hL28 : KFactL28Parabolic) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
      (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData p P M H R Rbar →
      ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
        ¬ L ≤ d1X0 p M H →
        d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L) = ⊥ →
        pCorePreimage p M ⊓ R ≠ ⊥ → False := by
  intro G _ _ p P M H R Rbar hd L hL hLX₀ hVL hV
  obtain ⟨e, he⟩ := hd.exists_escapeData hβ hS hKL h84 hD2 hL hLX₀ hVL hV
  obtain ⟨Pbar, K, hRC⟩ := he.exists_reducedCentralizer
  obtain ⟨A, f, hf⟩ := he.exists_surjective hRC hSch
  have hiso := he.isCaseTwoGroup
  have hp35 : p = 3 ∨ p = 5 := by
    obtain ⟨d, hd' | hd', -⟩ := hiso
    · exact Or.inl hd'.1
    · exact Or.inr hd'.1
  obtain ⟨hzZ, hzp⟩ :=
    hRC.center ⟨(e : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ rfl
  by_cases hzK : QuotientGroup.mk' (primeComplementCore
      (G := Subgroup.centralizer ({(e : G)} : Set G)) p)
      ⟨(e : G), Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ∈ K
  · exact hRC.red.false_of_caseTwo_of_mem hRC.four_le_pRank hRC.catalog hzZ hzp hRC.comp
      hRC.normal hzK hAE hp35 hiso f hf
  · obtain ⟨hp3, hsec⟩ := hRC.red.caseTwoCM_of_not_mem hRC.four_le_pRank hRC.catalog hzZ hzp
      hRC.comp hRC.normal hzK hβ hCM hp35 hiso f hf
    have h3 := hd.toPhaseThree hβ hS hKL
    obtain ⟨LB, hLB⟩ := h3.exists_weakSBlock h84 hD2
    obtain ⟨B, g, hg⟩ := he.exists_surjective_block hRC hSch hp3 hLB (hB3 h3 hLB)
    exact h3.false_of_block_section h85 h93 hD2 hL28 hLB (hsec B _ g hg hLB.component.2.2.2
      (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _
        hLB.component.2.2))

end CFSG.AGLEmbedding
