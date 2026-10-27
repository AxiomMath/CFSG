module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQuotBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphGlobal

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (involutionCentralizersComponentFree_of_evenLieType)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Cover

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {N : ℕ}

@[expose] def NsCoverType (e : L ≃* StatedSp N K) (κ : Sp2mKind) : Prop :=
  CFSG.IsQuasisimple (nsGlobal e) ∧ Odd (Nat.card (center (nsGlobal e))) ∧
    Sp2mKindType (nsGlobal e ⧸ center (nsGlobal e)) N 1 κ

theorem odd_card_center_statedSU_two {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ 1) ^ 2) {r : ℕ} (hr : 4 ≤ r) :
    Odd (Nat.card (center (StatedSU r (2 ^ 1) F))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := LinearPilot.charP_two_of_card_eq_two_pow (f := 2) (by rw [hF]; norm_num)
  have hnq : (r, 2 ^ 1) ≠ (3, 2) := fun h => by
    obtain ⟨h1, -⟩ := Prod.mk.inj h
    omega
  have h := odd_card_center_SU (F := F) (f := 1) hF le_rfl (by omega : 3 ≤ r) hnq
  rwa [Nat.card_congr (Subgroup.centerCongr
    (CFSG.LieType.Universal.Unitary.equivStatedSU (p := 2) (f := 1) hF r)).toEquiv] at h

theorem coverType_of_nsUnitaryCover {e : L ≃* StatedSp N K} {r : ℕ} (hr : 4 ≤ r)
    (hcov : NsUnitaryCover e r) :
    CFSG.IsQuasisimple (nsGlobal e) ∧ Odd (Nat.card (center (nsGlobal e))) ∧
      LieModel (nsGlobal e ⧸ center (nsGlobal e)) .PSU r 2 1 := by
  obtain ⟨F, _, _, hF, ψ, hs, hk⟩ := exists_surjective_of_nsUnitaryCover hcov
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnq : (r, 2 ^ 1) ≠ (3, 2) := fun h3 => by
    obtain ⟨h1, -⟩ := Prod.mk.inj h3
    omega
  obtain ⟨hq, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2)
    (f := 1) hF (by omega) hnq
  have hnt : ∃ k, ψ k ≠ 1 := by
    by_contra hc
    push Not at hc
    obtain ⟨-, -, a, b, hab⟩ := hq
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have ha : a' ∈ center (StatedSU r (2 ^ 1) F) := hk (hc a')
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (mem_center_iff.1 ha b').symm]
  have hGq : CFSG.IsQuasisimple (nsGlobal e) :=
    CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq hs hnt
  have hZG := CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hq hs hk
  refine ⟨hGq, ?_, ?_⟩
  · rw [hZG]
    exact Odd.of_dvd_nat (odd_card_center_statedSU_two hF hr) (Subgroup.card_map_dvd _ _)
  · have e3 := (CFSG.LieType.CurtisTits.centerQuotientEquivOfSurjective ψ hs hk hZG).symm
    have e4 : StatedSU r (2 ^ 1) F ⧸ center (StatedSU r (2 ^ 1) F) ≃*
        StatedProj (StatedSU r (2 ^ 1) F) := QuotientGroup.quotientMulEquivOfEq hZ
    exact Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
      ⟨Nat.prime_two, le_rfl, by omega, hnq⟩, F, inferInstance, inferInstance, hF,
        ⟨e3.trans e4⟩⟩

theorem nsCoverType_of_nsUnitaryCover {e : L ≃* StatedSp N K} {κ : Sp2mKind} {ε : ℕ}
    (hκ : (κ = .unitaryEven ∧ ε = 0) ∨ (κ = .unitaryOdd ∧ ε = 1)) (hN : 2 ≤ N)
    (hcov : NsUnitaryCover e (2 * N + ε)) : NsCoverType e κ := by
  obtain ⟨hq, hZ, hty⟩ := coverType_of_nsUnitaryCover (by omega) hcov
  refine ⟨hq, hZ, ?_⟩
  rcases hκ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hty
  · exact hty

end Cover

@[expose] def NsRowGlobalQuot {G : Type} [Group G] {L : Subgroup G} {N : ℕ} {K : Type}
    [Field K] (e : L ≃* StatedSp N K) (t : G) (κ : Sp2mKind) : Prop :=
  NsCoverType e κ ∧
    ∀ hN : t ∈ normalizer (nsGlobal e : Set G),
      centerQuotAction (nsGlobal e) ⟨t, hN⟩ ∉
          (MulAut.conj : nsGlobal e ⧸ center (nsGlobal e) →* MulAut _).range ∧
        LieModel (fixedSubgroup (centerQuotAction (nsGlobal e) ⟨t, hN⟩)) .PSp N 2 1

section Global


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem nsRowGlobalQuot_of_coverType (hset : SeitzSetting G L) {m : ℕ} (hK : Nat.card K = 2)
    (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {κ : Sp2mKind}
    (hκ : IsLinearUnitaryKind κ) (hcov : NsCoverType e κ) : NsRowGlobalQuot e t κ := by
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hLS : L ≤ nsGlobal e := le_nsGlobal hK hm e
  obtain ⟨hqs, hZ, hty⟩ := hcov
  have hperf : Group.IsPerfect (nsGlobal e) := hqs.1
  have hSperf : ⁅nsGlobal e, nsGlobal e⁆ = nsGlobal e := isPerfect_iff.mp hperf
  obtain ⟨τ, r, hτ, hr, hτm⟩ := exists_lieModel_of_isLinearUnitaryKind hκ hty
  have hadm : StatedLieAdmissible τ r 2 1 := F4Pilot.statedLieAdmissible_of_lieModel hτm
  have hS : IsSimpleGroup (nsGlobal e ⧸ center (nsGlobal e)) := by
    rcases hτ with rfl | rfl
    · exact LinearPilot.isSimpleGroup_of_lieModel_PSL hτm
    · exact LinearPilot.isSimpleGroup_of_lieModel_PSU hτm
  have hna : ∃ a b : nsGlobal e ⧸ center (nsGlobal e), a * b ≠ b * a := hqs.2.2
  have hLm : LieModel L .PSp (m + 1) 2 1 := lieModel_of_mulEquiv_statedSp e hKc (by omega) (by
    intro h
    obtain ⟨h1, -⟩ := Prod.mk.inj h
    omega)
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by omega) e)
  refine ⟨⟨hqs, hZ, hty⟩, fun hN => ?_⟩
  set θ := (nsGlobal e).normalizerMonoidHom ⟨t, hN⟩ with hθdef
  set θq := centerQuotAction (nsGlobal e) ⟨t, hN⟩ with hθqdef
  set π : nsGlobal e →* nsGlobal e ⧸ center (nsGlobal e) := QuotientGroup.mk' (center (nsGlobal e))
    with hπ
  have hfix : (fixedSubgroup θ).map π = fixedSubgroup θq :=
    map_mk_fixedSubgroup_eq_centerQuot hZ ht hN
  have hfixC : ∀ x : nsGlobal e, x ∈ fixedSubgroup θ → (x : G) * t = t * x := by
    intro x hx
    have h1 := (Subgroup.ext_iff.1 (fixedSubgroup_normalizerMonoidHom_eq hN) x).1 hx
    rw [mem_subgroupOf, mem_centralizer_singleton_iff] at h1
    exact h1
  set L₀ : Subgroup (nsGlobal e) := L.subgroupOf (nsGlobal e) with hL₀
  have hL₀C : L₀ ≤ fixedSubgroup θ := by
    intro x hx
    change θ x = x
    apply Subtype.ext
    rw [hθdef, Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hxL : (x : G) ∈ L := hx
    rw [← mem_centralizer_iff.1 htC (x : G) hxL, mul_inv_cancel_right]
  have hθ1 : θq ≠ 1 := by
    intro h1
    have hθ1' : θ = 1 := normalizerMonoidHom_eq_one_of_centerQuotAction_eq_one hN h1
    have hSt : nsGlobal e ≤ centralizer ({t} : Set G) := fun g hg => by
      rw [mem_centralizer_singleton_iff]
      exact hfixC ⟨g, hg⟩ (by change θ ⟨g, hg⟩ = ⟨g, hg⟩; rw [hθ1', MulAut.one_apply])
    have heq : nsGlobal e = L :=
      le_antisymm (std_perfect_le hset.standardSetting hOut htC ht hSperf hSt) hLS
    have hZ1 : center (nsGlobal e) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      exact (mem_bot).2 (eq_one_of_mem_center_of_commute hLS ht hKt hZ hz
        (mem_centralizer_singleton_iff.1 (hSt z.2)))
    have hXL : nsGlobal e ⧸ center (nsGlobal e) ≃* L :=
      (QuotientGroup.quotientMulEquivOfEq hZ1).trans
        (QuotientGroup.quotientBot.trans (MulEquiv.subgroupCongr heq))
    have hLτ : LieModel L τ r 2 1 := LieType.CurtisTits.lieModel_of_mulEquiv hXL hτm
    exact false_of_lieModel_ne_PSp (sp2mEvenTypeDetClassical (m + 1)) hLm
      (Or.inl (by rcases hτ with rfl | rfl <;> decide)) (by rcases hτ with rfl | rfl <;> decide)
      hadm hLτ
  have hθ2 : orderOf θq = 2 :=
    orderOf_eq_prime (by rw [_root_.sq]; exact centerQuotAction_mul_self ht hN) hθ1
  have hinjL : Function.Injective (π.comp L₀.subtype) :=
    injective_mk_comp_subtype_of_commute hLS ht hKt hZ fun x hx =>
      hfixC x (hL₀C hx)
  have hrangeL : (π.comp L₀.subtype).range = L₀.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hL₀q : L₀.map π ≤ fixedSubgroup θq := hfix ▸ Subgroup.map_mono hL₀C
  let eL : L₀.map π ≃* L :=
    (MulEquiv.subgroupCongr hrangeL.symm).trans
      ((MonoidHom.ofInjective hinjL).symm.trans (Subgroup.subgroupOfEquivOfLe hLS))
  let D : Subgroup (fixedSubgroup θq) := (L₀.map π).subgroupOf (fixedSubgroup θq)
  have eD : D ≃* L := (Subgroup.subgroupOfEquivOfLe hL₀q).trans eL
  have hDm : LieModel D .PSp (m + 1) 2 1 := LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hLm
  have hDq : IsQuasisimple D :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv
      (isComponent_top_of_lieModel_PSp hDm).1.1
  have hDn : D.Normal := by
    refine ⟨fun d hd c => ?_⟩
    have hd' : ((d : fixedSubgroup θq) : nsGlobal e ⧸ center (nsGlobal e)) ∈ L₀.map π := hd
    obtain ⟨l, hl, hld⟩ := hd'
    have hc' : ((c : fixedSubgroup θq) : nsGlobal e ⧸ center (nsGlobal e)) ∈
        (fixedSubgroup θ).map π := by
      rw [hfix]
      exact c.2
    obtain ⟨y, hy, hyc⟩ := hc'
    have hyN := hCN (mem_centralizer_singleton_iff.2 (hfixC y hy))
    have hlL : (l : G) ∈ L := hl
    have hmem : (y : G) * l * (y : G)⁻¹ ∈ L := (mem_normalizer_iff.1 hyN _).1 hlL
    change (((c * d * c⁻¹ : fixedSubgroup θq) : nsGlobal e ⧸ center (nsGlobal e))) ∈ L₀.map π
    refine ⟨y * l * y⁻¹, hmem, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hld, hyc]
  have hD : IsComponent D := ⟨hDq, hDn.isSubnormal⟩
  by_cases hin : θq ∈ (MulAut.conj : nsGlobal e ⧸ center (nsGlobal e) →* MulAut _).range
  · exact (F4Pilot.false_of_isComponent_fixedSubgroup_inner hna
      (involutionCentralizersComponentFree_of_evenLieType ⟨τ, r, 1, hadm, hτm⟩) hθ2 hin
      hD).elim
  · refine ⟨hin, ?_⟩
    rcases hτ with rfl | rfl
    · exact (catSp2mEvenOuterFamily_PSL (sp2mEvenTypeDetClassical (m + 1)) _ hS hna r 1
        hadm hτm θq hθ2 hin 1 D hD hDm).2
    · exact (catSp2mEvenOuterFamily_PSU (sp2mEvenTypeDetClassical (m + 1)) _ hS hna r 1
        hadm hτm θq hθ2 hin 1 D hD hDm).2

end Global

end CFSG.SeitzReduction.SymplecticPilot
