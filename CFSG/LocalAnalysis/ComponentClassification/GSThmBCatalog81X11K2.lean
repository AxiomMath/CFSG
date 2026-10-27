module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X11K1
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3a
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrLayerStandardCore
public import CFSG.LocalAnalysis.ComponentInitial.RankOneCentralizerStandardOrQuaternion
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bOrders
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Core
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S4d
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Sec
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S3
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S7d
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S9c
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Statement
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5L34
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X11B
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPropC

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁}

theorem _root_.CFSG.ComponentClassification.GSThmB.X11.pPrimeCore_eq_bot_of_normal
    (hO : pPrimeCore 2 H = ⊥) (N : Subgroup H) [N.Normal] : pPrimeCore 2 ↥N = ⊥ := by
  have h1 := UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal
    (Normal.isSubnormal (inferInstance : N.Normal))
  rw [hO, inf_bot_eq] at h1
  exact (map_eq_bot_iff_of_injective _ N.subtype_injective).mp h1

theorem isQuasisimple_J_of_localB (hLB : Assembly.ComponentType.LocalBProperty H) :
    IsQuasisimple ↥h.J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN := UnbalancedCorr.normalizer_zpowers_eq_centralizer h.orderOf_a
  have key : ∀ M : Subgroup H, M = centralizer ({h.a} : Set H) → h.J ≤ M ∧
      IsPComponent 2 (h.J.subgroupOf M) := by
    rintro M rfl
    exact ⟨h.J_le, h.isPComponent_J⟩
  obtain ⟨hJM, hJpc⟩ := key _ hN
  have ha2 : IsPGroup 2 (zpowers h.a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.orderOf_a, pow_one])
  have hne : zpowers h.a ≠ ⊥ := fun h1 => a_ne_one' (h := h)
    (by have := mem_zpowers h.a; rwa [h1, mem_bot] at this)
  obtain ⟨-, -, hq⟩ := hLB (zpowers h.a) hne ha2 _ (Seven.isTwoPComponent_of_isPComponent' hJpc)
  have hq' := (AssemblyBPredicates.isQuasisimple_iff_native _).mp hq
  exact (LocalAnalysis.ComponentInitial.isQuasisimple_congr (subgroupOfEquivOfLe hJM)).mp hq'

variable {v : H} (I : In81) (hst : d.Stage7 v)
  {N : Subgroup H} [N.Normal] (hNc : IsCyclic (H ⧸ N)) (hNa : h.a * d.sigma ∉ N)

include I hst hNc in
theorem orderOf_a_N : orderOf (⟨h.a, a_mem_N I hst hNc⟩ : ↥N) = 2 := by
  rw [Subgroup.orderOf_mk, h.orderOf_a]

include I hst hNc in
theorem isComponentOf_J_N (hLB : Assembly.ComponentType.LocalBProperty H) :
    CFSG.Assembly.IsComponentOf (h.J.subgroupOf N)
      (centralizer ({⟨h.a, a_mem_N I hst hNc⟩} : Set ↥N)) := by
  have hJN := J_le_N (h := h) hNc
  have hle : h.J.subgroupOf N ≤ centralizer ({⟨h.a, a_mem_N I hst hNc⟩} : Set ↥N) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (h.J_le (mem_subgroupOf.mp hx)))
  rw [LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hle]
  refine ⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr
    ((subgroupOfEquivOfLe hle).trans (subgroupOfEquivOfLe hJN))).mpr
      (isQuasisimple_J_of_localB hLB), ?_⟩
  refine Normal.isSubnormal ⟨fun x hx g => ?_⟩
  rw [mem_subgroupOf, mem_subgroupOf] at hx ⊢
  have hn := H₁.J_normal
  rw [normal_subgroupOf_iff h.J_le] at hn
  have hg : ((g : ↥N) : H) ∈ centralizer ({h.a} : Set H) := by
    have := mem_centralizer_singleton_iff.mp g.2
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val this)
  exact hn _ _ hx hg

include I hst hNc hNa in
theorem pRank_centralizer_J_N :
    CFSG.Assembly.pRank 2 (centralizer ((h.J.subgroupOf N : Subgroup ↥N) : Set ↥N)) = 1 := by
  set a' : ↥N := ⟨h.a, a_mem_N I hst hNc⟩ with ha'
  have ha'2 : a' * a' = 1 := Subtype.ext (Six.a_mul_a_self h.toHyp52)
  have ha'C : a' ∈ centralizer ((h.J.subgroupOf N : Subgroup ↥N) : Set ↥N) :=
    mem_centralizer_iff.mpr fun j hj =>
      Subtype.ext (mem_centralizer_singleton_iff.mp (h.J_le (mem_subgroupOf.mp hj)))
  unfold CFSG.Assembly.pRank
  set S : Set ℕ := {k | ∃ E : Subgroup ↥N,
    E ≤ centralizer ((h.J.subgroupOf N : Subgroup ↥N) : Set ↥N) ∧
      CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} with hS
  have h1 : 1 ∈ S := by
    refine ⟨zpowers a', zpowers_le.mpr ha'C, ⟨?_, fun x hx => ?_⟩, ?_⟩
    · exact ⟨⟨fun x y => Subtype.ext (by
        obtain ⟨i, hi⟩ := mem_zpowers_iff.mp x.2
        obtain ⟨j, hj⟩ := mem_zpowers_iff.mp y.2
        rw [coe_mul, coe_mul, ← hi, ← hj, ← zpow_add, ← zpow_add, add_comm])⟩⟩
    · rcases mem_zpowers_two (orderOf_a_N I hst hNc) hx with rfl | rfl
      · exact one_pow 2
      · rw [pow_two]
        exact ha'2
    · rw [Nat.card_zpowers, orderOf_a_N I hst hNc, pow_one]
  have hle : ∀ k ∈ S, k ≤ 1 := by
    rintro k ⟨E, hEC, ⟨-, hE2⟩, hEk⟩
    have hmap : E.map N.subtype ≤ centralizer (h.J : Set H) ⊓ N := by
      rintro _ ⟨x, hx, rfl⟩
      refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun j hj => ?_, x.2⟩
      have := mem_centralizer_iff.mp (hEC hx) ⟨j, J_le_N (h := h) hNc hj⟩ (mem_subgroupOf.mpr hj)
      exact congrArg Subtype.val this
    have hmap2 : ∀ y ∈ E.map N.subtype, y * y = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      have := hE2 x hx
      rw [pow_two] at this
      exact congrArg Subtype.val this
    have h2 := card_le_two_of_le_centralizer_J I hst hNc hNa hmap hmap2
    rw [card_map_of_injective N.subtype_injective, hEk] at h2
    by_contra hk
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact le_antisymm (csSup_le ⟨1, h1⟩ hle) (le_csSup ⟨1, hle⟩ h1)

include I hst hNc hNa in
theorem isStandardSubgroup_J_N (hLB : Assembly.ComponentType.LocalBProperty H) :
    IsStandardSubgroup (h.J.subgroupOf N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases LocalAnalysis.ComponentInitial.rank_one_centralizer_standard_or_quaternion
      (orderOf_a_N I hst hNc) (isComponentOf_J_N I hst hNc hLB)
      (pRank_centralizer_J_N I hst hNc hNa) with hstd | ⟨z, hz2, hzJ, hzC, -⟩
  · exact UnbalancedCorr.isStandardSubgroup_of_assembly_isStandardSubgroup hstd
  · exfalso
    set zJ : ↥h.J := ⟨z, mem_subgroupOf.mp hzJ⟩ with hzJ'
    have hcen : (zJ : ↥h.J ⧸ pPrimeCore 2 ↥h.J) ∈ center (↥h.J ⧸ pPrimeCore 2 ↥h.J) := by
      rw [mem_center_iff]
      intro y
      induction y using QuotientGroup.induction_on with
      | H j =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      have h2 := mem_centralizer_iff.mp hzC ⟨j, J_le_N (h := h) hNc j.2⟩ (mem_subgroupOf.mpr j.2)
      have h3 : (j : H) * (z : H) = (z : H) * (j : H) := congrArg Subtype.val h2
      exact Subtype.ext h3
    rw [H₁.center_J, mem_bot, QuotientGroup.eq_one_iff] at hcen
    have hodd := (Nat.prime_two.coprime_iff_not_dvd).mp
      (pPrimeCore_coprime_card (p := 2) (G := ↥h.J))
    have hdvd : orderOf (⟨zJ, hcen⟩ : ↥(pPrimeCore 2 ↥h.J)) ∣ _ := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hzJ', Subgroup.orderOf_mk] at hdvd
    have : orderOf ((z : ↥N) : H) = 2 := (Subgroup.orderOf_coe z).trans hz2
    rw [this] at hdvd
    exact hodd hdvd

include hNc in
theorem not_normal_J_N (hLB : Assembly.ComponentType.LocalBProperty H) :
    ¬ (h.J.subgroupOf N).Normal := by
  intro hn
  obtain ⟨-, -, hC, -, huniq⟩ := h.generalizedFitting_simple
  have hJsub : h.J.IsSubnormal :=
    IsSubnormal.trans (J_le_N (h := h) hNc) hn.isSubnormal (Normal.isSubnormal inferInstance)
  have hJeq := huniq h.J ⟨isQuasisimple_J_of_localB hLB, hJsub⟩
  have haC : h.a ∈ centralizer (h.J : Set H) :=
    mem_centralizer_iff.mpr fun j hj => mem_centralizer_singleton_iff.mp (h.J_le hj)
  rw [hJeq, hC, mem_bot] at haC
  exact a_ne_one' (h := h) haC

include I hst hNc hNa in
theorem gsRestricted_components (hRS : RestrictedStandardInput)
    (hKG : SectionRank.IsKGroupCat H) (hLB : Assembly.ComponentType.LocalBProperty H)
    (hJ : Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 3 2) :
    ∀ M : Subgroup H, IsComponent M → GSRestricted (↥M ⧸ center ↥M) := by
  have hJN := J_le_N (h := h) hNc
  have e : ↥(h.J.subgroupOf N) ≃* ↥h.J := subgroupOfEquivOfLe hJN
  have hJ' : Blueprint.LieModel (↥(h.J.subgroupOf N) ⧸ pPrimeCore 2 ↥(h.J.subgroupOf N))
      .PSL 2 3 2 :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e).symm hJ
  have hres := hRS ↥N (hKG.subgroup N) (X11.pPrimeCore_eq_bot_of_normal h.oddCore_eq_bot N)
    (h.J.subgroupOf N) (isStandardSubgroup_J_N I hst hNc hNa hLB) (not_normal_J_N hNc hLB)
    (Or.inl ⟨3, 2, Nat.prime_three, by norm_num, by norm_num, by norm_num, hJ'⟩)
  intro M hM
  have hMN : M ≤ N := by
    have hperf : ⁅M, M⁆ = M := Subgroup.isPerfect_iff.mp hM.1.1
    rw [← hperf]
    exact (commutator_mono le_top le_top).trans (X11.commutator_le_of_isCyclic hNc)
  have eM : ↥(M.subgroupOf N) ≃* ↥M := subgroupOfEquivOfLe hMN
  have hM' : IsComponent (M.subgroupOf N) :=
    ⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr eM).mpr hM.1, hM.2.subgroupOf⟩
  exact OddQuot.gsRestricted_of_mulEquiv
    (QuotientGroup.congr _ _ eM (Subgroup.map_center_eq eM)) (hres _ hM')

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
