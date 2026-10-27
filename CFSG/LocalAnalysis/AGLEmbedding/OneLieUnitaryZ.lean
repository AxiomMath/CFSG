module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUnitaryZData
import CFSG.LocalAnalysis.AGLEmbedding.ComponentCentralizer
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSide
import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideComp
import CFSG.LocalAnalysis.AGLEmbedding.OneLieUnitaryZBlocks
import CFSG.LocalAnalysis.AGLEmbedding.OneLieUnitaryZPCore
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Final

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {n : ℕ} {P : Sylow p G}
  {M H R X Z Np : Subgroup G}

theorem D1OneLieU3Data.false_of (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (hD2 : D1NoXBlock) (hB3 : StmtBlockThree) (hLB : StmtLemmaBRelCyc)
    (h : D1OneLieU3Data p n P M H R X Z Np) : False := by
  have hp : p.Prime := Fact.out
  set Y := pCorePreimage p M with hYdef
  set Q := pCoreOf 2 M with hQdef
  set N := GLBPrimeCore p H with hNdef
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hXH : X ≤ H := h.le_R.trans h.ph3.le_H
  have hXM : X ≤ M := h.le_R.trans h.ph3.le_M
  have hYK : Y ≤ H ⊓ M := h.ph3.pCorePreimage_le_inf h84 hD2
  have hYeq : (R ⊓ Y) ⊔ Q = Y := h.ph3.inf_sup_twoCore_eq h84 hD2
  set Sb := barM M (pCoreOf 2 H) with hSb
  set Nb := barM M N with hNb
  set Xb := barM M X with hXb
  have hSbp : IsPGroup 2 Sb :=
    ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H).comap_subtype
      (K := M)).map _
  have hNS : N ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    (glbPrimeCore_le p H).trans (localGroup_le_normalizer_pCoreOf 2 H)
  have hNbS : Nb ≤ Subgroup.normalizer (Sb : Set _) := by
    rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
    exact mem_normalizer_barM hxM (hNS (Subgroup.mem_subgroupOf.mp hx))
  have hcomm : ∀ a ∈ Xb, ∀ x ∈ Nb, a * x * a⁻¹ * x⁻¹ ∈ Sb := by
    rintro _ ⟨⟨u, huM⟩, hu, rfl⟩ _ ⟨⟨m, hmM⟩, hm, rfl⟩
    have hc : u * m * u⁻¹ * m⁻¹ ∈ pCoreOf 2 H := by
      have h1 : ⁅m, u⁆ ∈ ⁅N, X⁆ := Subgroup.commutator_mem_commutator
        (Subgroup.mem_subgroupOf.mp hm) (Subgroup.mem_subgroupOf.mp hu)
      have h2 := (pCoreOf 2 H).inv_mem (h.comm_core h1)
      rw [commutatorElement_def] at h2
      convert h2 using 1
      group
    refine ⟨⟨u, huM⟩ * ⟨m, hmM⟩ * (⟨u, huM⟩)⁻¹ * (⟨m, hmM⟩)⁻¹,
      Subgroup.mem_subgroupOf.mpr (by simpa using hc), ?_⟩
    simp only [map_mul, map_inv]
  have hXcomp : ∀ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ →
      Xb ≤ Subgroup.centralizer (Lb : Set _) := by
    intro Lb hLb
    obtain ⟨L, hL2, rfl, hL'⟩ := h.ph3.exists_weakSBlock_or_le_inf hLb
    rcases hL' with hw | hle
    · exact h.barM_le_centralizer_of_weakSBlock hB3 hLB h85 hD2 hw
    · by_cases hLN : L ≤ N
      · exact le_centralizer_of_forall_commutator_mem hLb
          (Subgroup.map_mono (Subgroup.subgroupOf_mono M hLN)) hSbp hNbS hcomm
      · exact barM_le_centralizer_of_commutator_mem h.ph3 hL2 (hle.trans inf_le_left) hLN
          hXM hXH (fun x hx l hl => h.comm_plus x hx l (h.perfect_le L hle hL2.perfect hl))
  have hXcore : ∀ l : ℕ, l.Prime →
      Xb ≤ Subgroup.centralizer (CFSG.pCore l (↥M ⧸ CFSG.pCore 2 ↥M) : Set _) := by
    intro l hl
    by_cases hl2 : l = 2
    · rw [hl2, pCore_quotient_pCore_eq_bot']
      exact Subgroup.le_centralizer_iff.mp bot_le
    by_cases hlp : l = p
    · rw [hlp]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro o ho
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) o
      have hmY : (m : G) ∈ Y := ⟨m, ho, rfl⟩
      have hmY' : (m : G) ∈ (((R ⊓ Y) ⊔ Q : Subgroup G) : Set G) := by
        rw [SetLike.mem_coe, hYeq]
        exact hmY
      rw [Subgroup.coe_mul_of_left_le_normalizer_right (R ⊓ Y) Q
        ((inf_le_right.trans hYK).trans (inf_le_right.trans
          (localGroup_le_normalizer_pCoreOf 2 M)))] at hmY'
      obtain ⟨x, hx, q, hq, hxq⟩ := hmY'
      have hxq' : x * q = (m : G) := hxq
      have hxM : x ∈ M := h.ph3.le_M hx.1
      have hqM : q ∈ M := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M hq
      have hmeq : m = ⟨x, hxM⟩ * ⟨q, hqM⟩ := Subtype.ext hxq'.symm
      have hq1 : mk ⟨q, hqM⟩ = 1 := (mk_eq_one_iff_coe_mem_pCoreOf _).mpr hq
      rw [hmeq, map_mul, hq1, mul_one]
      obtain ⟨⟨u, huM⟩, hu, rfl⟩ := ha
      have hux : u * x = x * u := h.comm_pCore u (Subgroup.mem_subgroupOf.mp hu) x hx
      rw [← map_mul, ← map_mul, show (⟨x, hxM⟩ : M) * ⟨u, huM⟩ = ⟨u, huM⟩ * ⟨x, hxM⟩ from
        Subtype.ext hux.symm]
    ·
      have : Fact l.Prime := ⟨hl⟩
      set Ol := CFSG.pCore l (↥M ⧸ CFSG.pCore 2 ↥M) with hOl
      set Sh : Subgroup G := (Ol.comap mk).map M.subtype with hSh
      have hShK : Sh ≤ H ⊓ M := h.ph3.preimage_le_inf (h.ph3.le_barM_inf_of_le_centralizer
        ((pCore_le_pPrimeCore_two hl hl2).trans (h.ph3.oddCore_le_centralizer h84 hD2)))
      have hShn : H ⊓ M ≤ Subgroup.normalizer (Sh : Set G) :=
        inf_le_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
          (Subgroup.map_subtype_le _)).mp (normal_preimage_subgroupOf Ol))
      have hShN : Sh ≤ N := by
        rw [hNdef, ← h.core_eq]
        exact le_glbPrimeCore hShK hShn (coprime_card_preimage_pCore hl hp hlp h.ph3.ne_two)
      have hOlN : Ol ≤ Nb := by
        rw [← barM_preimage Ol]
        exact Subgroup.map_mono (Subgroup.subgroupOf_mono M hShN)
      exact le_centralizer_pCore_of_forall_commutator_mem hl hl2 hSbp hOlN hcomm
  have hXbp : IsPGroup p Xb := ((h.ph3.isPGroup_R.to_le h.le_R).comap_subtype (K := M)).map _
  have hXbO := le_pCore_of_le_centralizer_components hXbp hXcomp hXcore
  have hXY : X ≤ Y := fun x hx =>
    ⟨⟨x, hXM hx⟩, hXbO ⟨⟨x, hXM hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩, rfl⟩
  have hXZ : X ≤ Z := (le_inf le_rfl hXY).trans h.inf_pCore
  have hle := Subgroup.card_le_of_le hXZ
  rw [h.card_eq, h.card_center] at hle
  have := h.two_le
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  omega

end Final

theorem d1OneLieU3Z_of (hK : KFactOneLie) (hKU2 : KFactUnitarySylowStructure)
    (hKU3 : KFactUnitarySylowCenterTorus) (hKU4 : KFactUnitaryTorusPPD)
    (hKU6 : KFactUnitaryBorelMaximal) (hKU8 : KFactUnitarySylowNormalizerSolvable)
    (hKU9 : KFactUnitaryAutElemRank) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (hD2 : D1NoXBlock) (hB3 : StmtBlockThree) (hLB : StmtLemmaBRelCyc) : D1OneLieU3Z := by
  intro G _ _ p P M H R Rbar K hd _huniq hY hU hZ
  have : Fact p.Prime := ⟨hd.cfg.red.prime⟩
  obtain ⟨n, h⟩ := hd.unitary_u3Data hK hKU2 hKU3 hKU4 hKU6 hKU8 hKU9 h84 hD2 hY hU hZ
  exact h.false_of h84 h85 hD2 hB3 hLB

end CFSG.AGLEmbedding
