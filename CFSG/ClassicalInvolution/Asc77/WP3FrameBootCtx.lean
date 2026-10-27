module

import CFSG.ClassicalInvolution.Asc77.AscE187Img
public import CFSG.ClassicalInvolution.Asc77.WP3FrameData

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD (le_centralizer_of_isClassicalMember)
open scoped commutatorElement

section Ctx

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

structure XCtx (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (Ω : Set (Subgroup G)) (z : G) where
  K : Subgroup G
  hK : K ∈ Ω
  hKz : IsUniqueInvolution K z
  hΩ : HypOmegaMod p f Ω
  hp : p ≠ 2
  hq : 5 ≤ p ^ f
  D : LocalLieSystemAt p f (exactFamily Ω z) z

namespace XCtx

omit [Finite G] in
theorem hzC (z : G) : z ∈ Subgroup.centralizer ({z} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

variable (C : XCtx p f Ω z)

include C

theorem hz2 : z * z = 1 := C.hKz.sq

theorem hc2 : IsPGroup 2 (Subgroup.zpowers z) := isPGroup_zpowers_of_sq_eq_one C.hz2

theorem hKtq : z ∈ trivialOnQuot C.K :=
  trivialOnQuot_of_isUniqueInvolution C.hp C.hq C.hΩ C.hK C.hKz

theorem hne : (tqMembers Ω z).Nonempty := ⟨C.K, C.hK, C.hKtq⟩

theorem hs : SecData p f z (exactFamily Ω z) :=
  secData_exactFamily C.hΩ.conjInvariant C.hΩ.classical C.hc2 C.hne

noncomputable abbrev psi (j : Fin C.D.card) : (compModel C.D j).K →* OddQuot z :=
  secComponentHom C.hs.normalizes C.D j

theorem psi_ker (j : Fin C.D.card) : (C.psi j).ker ≤ Subgroup.center (compModel C.D j).K :=
  secComponentHom_ker_le_center C.hs.normalizes C.D j

theorem exists_fund_of_mem {N : Subgroup G} (hN : N ∈ tqMembers Ω z) :
    ∃ j : Fin C.D.card, ∃ R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D,
      R.map (C.psi j) = modOdd z (exactCore z N) := by
  have hM : exactCore z N ∈ centMembers (exactFamily Ω z) z :=
    ⟨exactCore_mem_exactFamily hN, exactCore_le_centralizer z N⟩
  have hMY : exactCore z N ≤ centralizingLayer (exactFamily Ω z) {z} := le_centralizingLayer hM
  have hMfam : modOddIn (centralizingLayer (exactFamily Ω z) {z}) (exactCore z N) ∈
      localFamily (exactFamily Ω z) z := ⟨(exactCore z N).subgroupOf _, ⟨_, hM, hMY, rfl⟩, rfl⟩
  obtain ⟨i, R, hR, hMR⟩ := C.D.fundamental _ hMfam
  refine ⟨i, R, hR, ?_⟩
  have h1 : (R.map (C.D.hom i)).map (sectionQuotientHom C.hs.normalizes) =
      R.map (C.psi i) := Subgroup.map_map _ _ _
  rw [← h1, ← hMR]
  exact map_sectionQuotientHom_modOddIn C.hs.normalizes hM

theorem exists_member_of_fund (j : Fin C.D.card)
    (hsingle : FundamentalSingleClass (C.D.tag j) (compModel C.D j).D)
    {R : Subgroup (compModel C.D j).K}
    (hR : R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D) :
    ∃ N ∈ tqMembers Ω z, modOdd z (exactCore z N) = R.map (C.psi j) := by
  obtain ⟨M, hM, hMR⟩ := map_secComponentHom_mem_memberImages C.hs C.D j hsingle hR
  obtain ⟨N, hN, rfl⟩ := hM.1
  exact ⟨N, hN, hMR⟩


theorem involution_mem_exactCore {N : Subgroup G} {w : G} (hN : N ∈ tqMembers Ω z)
    (hw : IsClassicalMember p f N w) : w ∈ exactCore z N :=
  mem_exactCore hw C.hc2 hN.2

theorem involution_mem_centralizer {N : Subgroup G} {w : G} (hN : N ∈ tqMembers Ω z)
    (hw : IsClassicalMember p f N w) : w ∈ Subgroup.centralizer ({z} : Set G) :=
  exactCore_le_centralizer z N (C.involution_mem_exactCore hN hw)

theorem isUniqueInvolution_modOdd {N : Subgroup G} {w : G} (hN : N ∈ tqMembers Ω z)
    (hw : IsClassicalMember p f N w) :
    IsUniqueInvolution (modOdd z (exactCore z N))
      (oddQuotMk z ⟨w, C.involution_mem_centralizer hN hw⟩) := by
  have hwE := C.involution_mem_exactCore hN hw
  have hwC := C.involution_mem_centralizer hN hw
  have hcw := isCentralInvolution_of_isClassicalMember hw
  set Cz : Subgroup G := Subgroup.centralizer ({z} : Set G) with hCz
  set E' : Subgroup ↥Cz := (exactCore z N).subgroupOf Cz with hE'
  have hU : IsUniqueInvolution E' ⟨w, hwC⟩ := by
    refine ⟨hwE, fun h => hcw.ne_one (congrArg Subtype.val h), Subtype.ext hcw.sq, ?_⟩
    intro y hy hy2
    rcases eq_one_or_eq_of_mem_exactCore hw C.hp C.hq hy (congrArg Subtype.val hy2) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hodd : Odd (Nat.card ↥(componentClassificationOddCore ↥Cz ⊓ E')) :=
    (OddCore.odd_card ↥Cz).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  exact isUniqueInvolution_map_mk_of_odd hodd hU

theorem exists_conj_of_oddQuotMk_eq {w₁ w₂ : G} (h₁ : w₁ ∈ exactLayer Ω z)
    (h₂ : w₂ ∈ exactLayer Ω z) (hs₁ : w₁ * w₁ = 1) (hs₂ : w₂ * w₂ = 1)
    (heq : oddQuotMk z ⟨w₁, exactLayer_le_centralizer Ω z h₁⟩ =
      oddQuotMk z ⟨w₂, exactLayer_le_centralizer Ω z h₂⟩) :
    ∃ o ∈ oddCoreIn (exactLayer Ω z), w₁ = o * w₂ * o⁻¹ := by
  have hker : (⟨w₁, h₁⟩ : ↥(exactLayer Ω z)) * ⟨w₂, h₂⟩⁻¹ ∈
      (layerToOddQuot (exactFamily Ω z) z).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, layerToOddQuot_apply, layerToOddQuot_apply]
    exact mul_inv_eq_one.mpr heq
  rw [ker_layerToOddQuot_of_normalizes C.hs.normalizes] at hker
  have hmem := mem_oddCoreIn_of_mem_classicalInvolutionOddCore hker
  have hinv : w₂⁻¹ = w₂ := inv_eq_of_mul_eq_one_right hs₂
  have hmem' : w₁ * w₂ ∈ oddCoreIn (exactLayer Ω z) := by
    have : ((⟨w₁, h₁⟩ * ⟨w₂, h₂⟩⁻¹ : ↥(exactLayer Ω z)) : G) = w₁ * w₂ := by
      simp [hinv]
    rwa [this] at hmem
  exact exists_conj_of_mul_mem hs₂ hs₁ (odd_card_oddCoreIn _) hmem'

theorem exists_lift_psi (j : Fin C.D.card) (k : (compModel C.D j).K) :
    ∃ (y : G) (hy : y ∈ exactLayer Ω z),
      oddQuotMk z ⟨y, exactLayer_le_centralizer Ω z hy⟩ = C.psi j k := by
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective _ (C.D.hom j k)
  refine ⟨y, y.2, ?_⟩
  have h : C.psi j k = sectionQuotientHom C.hs.normalizes (C.D.hom j k) := rfl
  rw [h, ← hy]
  rfl

theorem z_mem_exactLayer : z ∈ exactLayer Ω z := by
  have hKcl : IsClassicalMember p f C.K z := isClassicalMember_of_twin C.hΩ C.hK C.hKz
  have hKN : C.K ∈ tqMembers Ω z := ⟨C.hK, C.hKtq⟩
  exact exactCore_le_exactLayer hKN (C.involution_mem_exactCore hKN hKcl)

theorem psi_mem_memberJoin (j : Fin C.D.card) (k : (compModel C.D j).K) :
    C.psi j k ∈ memberJoin (exactFamily Ω z) z := by
  rw [← range_sectionQuotientHom C.hs.normalizes]
  exact ⟨C.D.hom j k, rfl⟩

theorem psi_commute {i j : Fin C.D.card} (hij : i ≠ j) (x : (compModel C.D i).K)
    (y : (compModel C.D j).K) : C.psi i x * C.psi j y = C.psi j y * C.psi i x := by
  have h1 := map_mul (sectionQuotientHom C.hs.normalizes) (C.D.hom i x) (C.D.hom j y)
  have h2 := map_mul (sectionQuotientHom C.hs.normalizes) (C.D.hom j y) (C.D.hom i x)
  have h3 := congrArg (sectionQuotientHom C.hs.normalizes) (C.D.commute i j hij x y)
  exact h1.symm.trans (h3.trans h2)

theorem conj_psi_range (j : Fin C.D.card) {y : OddQuot z}
    (hy : y ∈ memberJoin (exactFamily Ω z) z) :
    ∀ n ∈ (C.psi j).range, y * n * y⁻¹ ∈ (C.psi j).range := by
  rw [← range_sectionQuotientHom C.hs.normalizes] at hy
  obtain ⟨x, rfl⟩ := hy
  have hx : x ∈ ⨆ i, (C.D.hom i).range := by
    rw [C.D.generate]
    exact Subgroup.mem_top x
  induction hx using Subgroup.iSup_induction' with
  | hp k y hy =>
    intro n hn
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hn
    have h2 : sectionQuotientHom C.hs.normalizes (C.D.hom k a) = C.psi k a := rfl
    rw [h2]
    by_cases hkj : k = j
    · subst hkj
      refine ⟨a * b * a⁻¹, ?_⟩
      simp
    · rw [C.psi_commute hkj a b, mul_assoc, mul_inv_cancel, mul_one]
      exact ⟨b, rfl⟩
  | h1 =>
    intro n hn
    rw [map_one, one_mul, inv_one, mul_one]
    exact hn
  | hmul a b _ _ ha hb =>
    intro n hn
    rw [map_mul]
    have e : ∀ u v : OddQuot z, u * v * n * (u * v)⁻¹ = u * (v * n * v⁻¹) * u⁻¹ :=
      fun u v => by group
    rw [e]
    exact ha _ (hb n hn)

theorem isComponentOf_range (j : Fin C.D.card) : IsComponentOf (C.psi j).range ⊤ := by
  have hJ : (memberJoin (exactFamily Ω z) z).Normal :=
    memberJoin_normal_of_normalizes C.hs.normalizes
  have hle : (C.psi j).range ≤ memberJoin (exactFamily Ω z) z := by
    rintro _ ⟨k, rfl⟩
    exact C.psi_mem_memberJoin j k
  refine ⟨le_top, ?_, ?_⟩
  · refine IsSubnormal.step hle ?_ ?_
    · refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using C.conj_psi_range j g.2 _ hn
    · exact isSubnormal_of_normal_subgroupOf le_top Subgroup.normal_subgroupOf
  · have hK : CFSG.Open.IsQuasisimple
        (modelUniv (C.D.tag j) (C.D.rank j) p (C.D.exp j) Fact.out).K :=
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero _ _ _ _ _ (C.D.isFundTag j)
        (C.D.admissible j)).1
    have hq : CFSG.Open.IsQuasisimple ↥((⊤ : Subgroup (compModel C.D j).K).map (C.psi j)) :=
      isQuasisimple_map_of_ker_le_center _ (C.psi_ker j)
        (Components.quasisimple_of_equiv Subgroup.topEquiv hK)
    rwa [Subgroup.map_top] at hq

theorem isComponent_range (j : Fin C.D.card) : CFSG.IsComponent (C.psi j).range :=
  (CFSG.isComponent_iff_open _).mpr (C.isComponentOf_range j)

theorem K_cl : IsClassicalMember p f C.K z := isClassicalMember_of_twin C.hΩ C.hK C.hKz

theorem K_tq : C.K ∈ tqMembers Ω z := ⟨C.hK, C.hKtq⟩

theorem exactCore_K : exactCore z C.K = C.K :=
  exactCore_eq_self C.K_cl.perfect (le_centralizer_of_isClassicalMember C.K_cl)

theorem fund_eq_top (j : Fin C.D.card) (hj : C.D.tag j = .PSL ∧ C.D.rank j = 2)
    {R : Subgroup (compModel C.D j).K}
    (hR : R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D) : R = ⊤ := by
  have key : ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n e : ℕ), t = .PSL → n = 2 →
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n p e →
      ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, R = ⊤ := by
    intro t n e ht hn hadm R hR
    subst ht hn
    exact CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups_eq_top_PSL_two p e Fact.out
      hadm R hR
  exact key (C.D.tag j) (C.D.rank j) (C.D.exp j) hj.1 hj.2 (C.D.admissible j) R hR

theorem exp_eq (j : Fin C.D.card) (hj : C.D.tag j ≠ .trialityD4) : C.D.exp j = f := by
  rcases C.D.exp_eq j with h | ⟨h, -⟩
  · exact h
  · exact absurd h hj

theorem four_le (j : Fin C.D.card) (hj : C.D.tag j ≠ .trialityD4) : 4 ≤ p ^ C.D.exp j := by
  rw [C.exp_eq j hj]
  have := C.hq
  omega

theorem single (j : Fin C.D.card) (hG2 : C.D.tag j ≠ .G2) (hD4 : C.D.tag j ≠ .trialityD4) :
    FundamentalSingleClass (C.D.tag j) (compModel C.D j).D :=
  ModelFacts.fundamentalSingleClass (C.D.tag j) (C.D.rank j) p (C.D.exp j) Fact.out
    (C.D.isFundTag j) (C.D.admissible j) hG2 hD4

theorem perfect_A1 (j : Fin C.D.card) (hj : C.D.tag j = .PSL ∧ C.D.rank j = 2)
    {R : Subgroup (compModel C.D j).K}
    (hR : R ∈ fundamentalSubgroups (C.D.tag j) (compModel C.D j).D) : ⁅R, R⁆ = R :=
  commutator_self_eq_of_le (ModelFacts.fundPerfect_core (C.D.tag j) (C.D.rank j) p (C.D.exp j)
    C.hp (C.D.isFundTag j) (C.D.admissible j) (C.four_le j (by rw [hj.1]; decide)) R hR)

theorem exists_A1_of_member {N : Subgroup G} (hN : N ∈ Ω) (hNz : IsClassicalMember p f N z) :
    ∃ j : Fin C.D.card, (C.D.tag j = .PSL ∧ C.D.rank j = 2) ∧ modOdd z N = (C.psi j).range := by
  have hNc : N ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_isClassicalMember hNz
  have hNtq : N ∈ tqMembers Ω z := ⟨hN, mem_trivialOnQuot_of_le_centralizer hNc⟩
  have hNeq : exactCore z N = N := exactCore_eq_self hNz.perfect hNc
  obtain ⟨j, R, hR, hmod⟩ := C.exists_fund_of_mem hNtq
  rw [hNeq] at hmod
  by_cases hj : C.D.tag j = .PSL ∧ C.D.rank j = 2
  · refine ⟨j, hj, ?_⟩
    rw [← hmod, C.fund_eq_top j hj hR, Subgroup.map_top]
  · exfalso
    have hzC := XCtx.hzC z
    have hzmem : oddQuotMk z ⟨z, hzC⟩ ∈ R.map (C.psi j) :=
      hmod ▸ oddQuotMk_mem_modOdd hNz.mem hzC
    obtain ⟨r, hrR, hr⟩ := hzmem
    have hr1 : r = 1 := by
      refine CFSG.ClassicalInvolution.RouteD.Gaps.fundNoncentral p (C.D.tag j) (C.D.rank j)
        (C.D.exp j) (C.D.isFundTag j) (C.D.admissible j) hj R hR r hrR fun y => C.psi_ker j ?_
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hr]
      have := oddQuotMk_central hzC (C.psi j y)
      calc oddQuotMk z ⟨z, hzC⟩ * C.psi j y * (oddQuotMk z ⟨z, hzC⟩)⁻¹ * (C.psi j y)⁻¹
          = (C.psi j y * oddQuotMk z ⟨z, hzC⟩) * (oddQuotMk z ⟨z, hzC⟩)⁻¹ * (C.psi j y)⁻¹ := by
            rw [this]
        _ = 1 := by group
    rw [hr1, map_one] at hr
    exact C.hKz.ne_one (congrArg Subtype.val
      (eq_one_of_oddQuotMk_eq_one (Subtype.ext C.hKz.sq) hr.symm))

theorem exists_A1_of_K : ∃ j : Fin C.D.card, (C.D.tag j = .PSL ∧ C.D.rank j = 2) ∧
    modOdd z (exactCore z C.K) = (C.psi j).range := by
  obtain ⟨j, hj, h⟩ := C.exists_A1_of_member C.hK C.K_cl
  exact ⟨j, hj, by rw [C.exactCore_K]; exact h⟩

theorem range_not_comm_of_A1 (j : Fin C.D.card) (hj : C.D.tag j = .PSL ∧ C.D.rank j = 2)
    (hz : oddQuotMk z ⟨z, XCtx.hzC z⟩ ∈ (C.psi j).range)
    (hab : ∀ a ∈ (C.psi j).range, ∀ b ∈ (C.psi j).range, a * b = b * a) : False := by
  obtain ⟨R, hR, -⟩ := C.D.meets j
  have hR1 : R = ⊤ := C.fund_eq_top j hj hR
  have hperf : ⁅(⊤ : Subgroup (compModel C.D j).K), (⊤ : Subgroup (compModel C.D j).K)⁆ = ⊤ := by
    have := C.perfect_A1 j hj hR
    rwa [hR1] at this
  have hker : (⊤ : Subgroup (compModel C.D j).K) ≤ (C.psi j).ker := by
    rw [← hperf, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
    calc C.psi j a * C.psi j b * (C.psi j a)⁻¹ * (C.psi j b)⁻¹
        = (C.psi j b * C.psi j a) * (C.psi j a)⁻¹ * (C.psi j b)⁻¹ := by
          rw [hab _ ⟨a, rfl⟩ _ ⟨b, rfl⟩]
      _ = 1 := by group
  obtain ⟨k, hk⟩ := hz
  have hk1 : C.psi j k = 1 := MonoidHom.mem_ker.mp (hker (Subgroup.mem_top k))
  rw [hk1] at hk
  exact C.hKz.ne_one (congrArg Subtype.val
    (eq_one_of_oddQuotMk_eq_one (Subtype.ext C.hKz.sq) hk.symm))

end XCtx

end Ctx

end CFSG.ClassicalInvolution.Asc77
