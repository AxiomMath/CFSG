module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LULinear

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.ComponentClassification.CatLeaf (involutionCentralizersComponentFree_of_evenLieType)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def NsRowGlobal {G : Type} [Group G] {L : Subgroup G} {N : ℕ} {K : Type} [Field K]
    (e : L ≃* StatedSp N K) (t : G) (κ : Sp2mKind) : Prop :=
  Sp2mKindType (nsGlobal e) N 1 κ ∧
    ∀ hN : t ∈ normalizer (nsGlobal e : Set G),
      (nsGlobal e).normalizerMonoidHom ⟨t, hN⟩ ∉
          (MulAut.conj : nsGlobal e →* MulAut (nsGlobal e)).range ∧
        LieModel (fixedSubgroup ((nsGlobal e).normalizerMonoidHom ⟨t, hN⟩)) .PSp N 2 1

section Global

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem nsRowGlobal_of_sp2mKindType_linearUnitary (hset : SeitzSetting G L) {m : ℕ}
    (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {κ : Sp2mKind}
    (hκ : IsLinearUnitaryKind κ) (hty : Sp2mKindType (nsGlobal e) (m + 1) 1 κ) :
    NsRowGlobal e t κ := by
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hLS : L ≤ nsGlobal e := le_nsGlobal hK hm e
  obtain ⟨τ, r, hτ, hr, hτm⟩ := exists_lieModel_of_isLinearUnitaryKind hκ hty
  have hadm : StatedLieAdmissible τ r 2 1 := F4Pilot.statedLieAdmissible_of_lieModel hτm
  have hS : IsSimpleGroup (nsGlobal e) := by
    rcases hτ with rfl | rfl
    · exact LinearPilot.isSimpleGroup_of_lieModel_PSL hτm
    · exact LinearPilot.isSimpleGroup_of_lieModel_PSU hτm
  have hLm : LieModel L .PSp (m + 1) 2 1 := lieModel_of_mulEquiv_statedSp e hKc (by omega) (by
    intro h
    obtain ⟨h1, -⟩ := Prod.mk.inj h
    omega)
  have hna : ∃ a b : nsGlobal e, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    let _ : CommGroup (nsGlobal e) := { (inferInstance : Group (nsGlobal e)) with mul_comm := hc }
    have hp : (Nat.card (nsGlobal e)).Prime := IsSimpleGroup.prime_card
    have h8 : 2 ^ 8 ∣ Nat.card (nsGlobal e) :=
      (two_pow_eight_dvd_card_of_lieModel_PSp hLm).trans (Subgroup.card_dvd_of_le hLS)
    rcases (Nat.dvd_prime hp).1 h8 with h1 | h1
    · norm_num at h1
    · rw [← h1] at hp
      norm_num at hp
  have hSperf : ⁅nsGlobal e, nsGlobal e⁆ = nsGlobal e :=
    isPerfect_iff.mp (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna).1.1
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  refine ⟨hty, fun hN => ?_⟩
  set θ := (nsGlobal e).normalizerMonoidHom ⟨t, hN⟩ with hθdef
  have hθθ : θ * θ = 1 := by
    rw [hθdef, ← map_mul, show (⟨t, hN⟩ : normalizer (nsGlobal e : Set G)) * ⟨t, hN⟩ = 1 from
      Subtype.ext htt, map_one]
  have hfixC : ∀ x : nsGlobal e, x ∈ fixedSubgroup θ → (x : G) ∈ centralizer ({t} : Set G) := by
    intro x hx
    have h1 : t * (x : G) * t⁻¹ = x := by
      have := congrArg Subtype.val (show θ x = x from hx)
      rwa [hθdef, Subgroup.normalizerMonoidHom_apply_apply_coe] at this
    rw [mem_centralizer_singleton_iff]
    calc (x : G) * t = t * (x : G) * t⁻¹ * t := by rw [h1]
      _ = t * (x : G) := by group
  have hLS' : L.subgroupOf (nsGlobal e) ≤ fixedSubgroup θ := by
    intro x hx
    change θ x = x
    apply Subtype.ext
    rw [hθdef, Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hxL : (x : G) ∈ L := hx
    rw [← mem_centralizer_iff.1 htC (x : G) hxL, mul_inv_cancel_right]
  have hθ1 : θ ≠ 1 := by
    intro h1
    have hSt : nsGlobal e ≤ centralizer ({t} : Set G) := fun g hg =>
      hfixC ⟨g, hg⟩ (by change θ ⟨g, hg⟩ = ⟨g, hg⟩; rw [h1, MulAut.one_apply])
    have hOut : Group.IsSolvable (Outer L) :=
      isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by omega) e)
    have heq : nsGlobal e = L :=
      le_antisymm (std_perfect_le hset.standardSetting hOut htC ht hSperf hSt) hLS
    have hLτ : LieModel L τ r 2 1 :=
      LieType.CurtisTits.lieModel_of_mulEquiv (MulEquiv.subgroupCongr heq) hτm
    exact false_of_lieModel_ne_PSp (sp2mEvenTypeDetClassical (m + 1)) hLm
      (Or.inl (by rcases hτ with rfl | rfl <;> decide)) (by rcases hτ with rfl | rfl <;> decide)
      hadm hLτ
  have hθ2 : orderOf θ = 2 := orderOf_eq_prime (by rw [_root_.sq]; exact hθθ) hθ1
  let D : Subgroup (fixedSubgroup θ) := (L.subgroupOf (nsGlobal e)).subgroupOf (fixedSubgroup θ)
  have eD : D ≃* L :=
    (Subgroup.subgroupOfEquivOfLe hLS').trans (Subgroup.subgroupOfEquivOfLe hLS)
  have hDm : LieModel D .PSp (m + 1) 2 1 := LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hLm
  have hDq : IsQuasisimple D :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv
      (isComponent_top_of_lieModel_PSp hDm).1.1
  have hDn : D.Normal := by
    refine ⟨fun d hd g => ?_⟩
    have hdL : (((d : fixedSubgroup θ) : nsGlobal e) : G) ∈ L := hd
    have hgN := hCN (hfixC _ g.2)
    change ((((g * d * g⁻¹ : fixedSubgroup θ) : nsGlobal e) : G)) ∈ L
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (mem_normalizer_iff.1 hgN _).1 hdL
  have hD : IsComponent D := ⟨hDq, hDn.isSubnormal⟩
  by_cases hin : θ ∈ (MulAut.conj : nsGlobal e →* MulAut (nsGlobal e)).range
  · exact (F4Pilot.false_of_isComponent_fixedSubgroup_inner hna
      (involutionCentralizersComponentFree_of_evenLieType ⟨τ, r, 1, hadm, hτm⟩) hθ2 hin
      hD).elim
  · refine ⟨hin, ?_⟩
    rcases hτ with rfl | rfl
    · exact (catSp2mEvenOuterFamily_PSL (sp2mEvenTypeDetClassical (m + 1)) (nsGlobal e) hS hna r
        1 hadm hτm θ hθ2 hin 1 D hD hDm).2
    · exact (catSp2mEvenOuterFamily_PSU (sp2mEvenTypeDetClassical (m + 1)) (nsGlobal e) hS hna r
        1 hadm hτm θ hθ2 hin 1 D hD hDm).2

end Global

section Endgame

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_linearRow_of_subgroup (hset : SeitzSetting G L) {M : Subgroup G} {t : G}
    (ht : orderOf t = 2) (htN : t ∈ normalizer (M : Set G)) {r f : ℕ} (hr : 3 ≤ r)
    (hty : LieModel M .PSL r 2 f)
    (hout : M.normalizerMonoidHom ⟨t, htN⟩ ∉ (MulAut.conj : M →* MulAut M).range) {n' f' : ℕ}
    (hfix : LieModel (fixedSubgroup (M.normalizerMonoidHom ⟨t, htN⟩)) .PSp n' 2 f')
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (M : Set G) → g ∈ normalizer (M : Set G)) :
    False := by
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hadm : StatedLieAdmissible .PSL r 2 f := F4Pilot.statedLieAdmissible_of_lieModel hty
  obtain ⟨F, _, _, hF, ⟨eJ⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hty
  set ε : M ≃* LinearFlag.projectiveSL r F :=
    eJ.trans (CatalogueBLinearHigherB.nativeEquiv r F).symm with hεdef
  set θ := M.normalizerMonoidHom ⟨t, htN⟩ with hθdef
  have hθθ : θ * θ = 1 := by
    rw [hθdef, ← map_mul, show (⟨t, htN⟩ : normalizer (M : Set G)) * ⟨t, htN⟩ = 1 from
      Subtype.ext htt, map_one]
  have hα2 : MulAut.congr ε θ ^ 2 = 1 := by rw [_root_.sq, ← map_mul, hθθ, map_one]
  have hαo : MulAut.congr ε θ ∉
      (MulAut.conj : LinearFlag.projectiveSL r F →* MulAut _).range := fun h =>
    hout ((FixedFourGroup.congr_mem_inner_iff ε θ).1 h)
  have hαfix : LieModel (fixedSubgroup (MulAut.congr ε θ)) .PSp n' 2 f' :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv ε θ) hfix
  have hαE := not_mem_semilinearAutGroup_of_lieModel_PSp hr hadm.2.1 hF hα2 hαo hαfix
  obtain ⟨χ, hχInn, hχE⟩ := exists_linearGraphCoordinate (F := F) hr
  have : IsSimpleGroup G := hset.1
  refine EPilot.false_of_simple_of_mulAut_hom ε htN ht huniq χ (by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]; decide) hχInn ?_
  change χ (MulAut.congr ε θ) ≠ 1
  exact hχE _ hαE

end Endgame

section Unique

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_mulAut_conj_of_nsRowGlobal_linearOdd (hset : SeitzSetting G L) {m : ℕ}
    (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : NsRowGlobal e t .linearOdd) (htN : t ∈ normalizer (nsGlobal e : Set G)) (g : G)
    (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)) :
    ∃ β : MulAut (nsGlobal e), β * (nsGlobal e).normalizerMonoidHom ⟨t, htN⟩ =
      (nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ * β := by
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨hty, -⟩ := hglob
  have hty' : LieModel (nsGlobal e) .PSL (2 * (m + 1) + 1) 2 1 := hty
  have hadm : StatedLieAdmissible .PSL (2 * (m + 1) + 1) 2 1 :=
    F4Pilot.statedLieAdmissible_of_lieModel hty'
  obtain ⟨F, _, _, hF, ⟨eJ⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hty'
  have : CharP F 2 := LinearPilot.charP_two_of_card_eq_two_pow hF
  set ε : nsGlobal e ≃* LinearFlag.projectiveSL (2 * (m + 1) + 1) F :=
    eJ.trans (CatalogueBLinearHigherB.nativeEquiv (2 * (m + 1) + 1) F).symm with hεdef
  set θt := (nsGlobal e).normalizerMonoidHom ⟨t, htN⟩ with hθt
  set θw := (nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ with hθw
  have hαt : MulAut.congr ε θt * MulAut.congr ε θt = 1 := by
    rw [← map_mul, hθt, normalizerMonoidHom_mul_self htt htN, map_one]
  have hαw : MulAut.congr ε θw * MulAut.congr ε θw = 1 := by
    rw [← map_mul, hθw, normalizerMonoidHom_mul_self (mul_self_inv_conj_eq_one htt g) hg, map_one]
  have hdt : Nat.card (fixedSubgroup (MulAut.congr ε θt)) ∣
      2 * (Nat.card (StatedSp (m + 1) K) * 1) := by
    rw [LinearPilot.card_fixedSubgroup_congr]
    exact card_fixedSubgroup_dvd_of_mem hset (by omega) hKc e ht hKt htN
  have hdw : Nat.card (fixedSubgroup (MulAut.congr ε θw)) ∣
      2 * (Nat.card (StatedSp (m + 1) K) * 1) := by
    rw [LinearPilot.card_fixedSubgroup_congr]
    exact card_fixedSubgroup_conj_dvd hset (by omega) hKc e ht hKt hg
  obtain ⟨H₁, C₁, hc₁, he₁⟩ := exists_graph_normal_form_of_card_dvd (K := K) (by omega)
    le_rfl hF hKc (Or.inr rfl) hαt hdt
  obtain ⟨H₂, C₂, hc₂, he₂⟩ := exists_graph_normal_form_of_card_dvd (K := K) (by omega)
    le_rfl hF hKc (Or.inr rfl) hαw hdw
  have h1 : C₁ = 1 := by
    rcases hc₁ with h1 | ⟨h1, -⟩
    · exact Units.ext h1
    · omega
  have h2 : C₂ = 1 := by
    rcases hc₂ with h2 | ⟨h2, -⟩
    · exact Units.ext h2
    · omega
  subst h1 h2
  refine exists_mulAut_mul_eq_of_congr ε
    (γ := LinearFlag.conjAut (2 * (m + 1) + 1) F H₂ *
      (LinearFlag.conjAut (2 * (m + 1) + 1) F H₁)⁻¹) ?_
  rw [he₁, he₂]
  group

theorem unique_of_nsRowGlobal_linearOdd (hset : SeitzSetting G L) {m : ℕ} (hK : Nat.card K = 2)
    (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : NsRowGlobal e t .linearOdd) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G) →
      g ∈ normalizer (nsGlobal e : Set G) := by
  intro g hg
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_nsGlobal e htC
  obtain ⟨β, hβ⟩ := exists_mulAut_conj_of_nsRowGlobal_linearOdd hset hK hm e ht hKt hglob htN g hg
  exact mem_normalizer_nsGlobal_of_conj_mulAut hset hK hm e ht hKt htN hg β hβ

@[expose] def SpTwoLinearEvenSecondClassInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n →
    ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (n + 1), NsKindSp e t k .linearEven) → NsRowGlobal e t .linearEven →
      ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)),
        ¬ IsCharacteristicP 2
          (fixedSubgroup ((nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩))

theorem exists_mulAut_conj_of_nsRowGlobal_linearEven (hset : SeitzSetting G L) {m : ℕ}
    (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : NsRowGlobal e t .linearEven) (htN : t ∈ normalizer (nsGlobal e : Set G))
    (h2 : ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)),
      ¬ IsCharacteristicP 2
        (fixedSubgroup ((nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩)))
    (g : G) (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)) :
    ∃ β : MulAut (nsGlobal e), β * (nsGlobal e).normalizerMonoidHom ⟨t, htN⟩ =
      (nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ * β := by
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hty' : LieModel (nsGlobal e) .PSL (2 * (m + 1)) 2 1 := hglob.1
  have hadm : StatedLieAdmissible .PSL (2 * (m + 1)) 2 1 :=
    F4Pilot.statedLieAdmissible_of_lieModel hty'
  obtain ⟨F, _, _, hF, ⟨eJ⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hty'
  have : CharP F 2 := LinearPilot.charP_two_of_card_eq_two_pow hF
  set ε : nsGlobal e ≃* LinearFlag.projectiveSL (2 * (m + 1)) F :=
    eJ.trans (CatalogueBLinearHigherB.nativeEquiv (2 * (m + 1)) F).symm with hεdef
  have hJ : ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)),
      ∃ H C : GL (Fin (2 * (m + 1))) F,
        (C : Matrix (Fin (2 * (m + 1))) (Fin (2 * (m + 1))) F) =
          UnitaryHigher.blockSwapJ (2 * (m + 1)) (m + 1) ∧
        MulAut.congr ε ((nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) =
          LinearFlag.conjAut (2 * (m + 1)) F H *
            (LinearFlag.conjAut (2 * (m + 1)) F C * LinearFlag.dualAut (2 * (m + 1)) F) *
              (LinearFlag.conjAut (2 * (m + 1)) F H)⁻¹ := by
    intro g hg
    have hαw : MulAut.congr ε ((nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) *
        MulAut.congr ε ((nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩) = 1 := by
      rw [← map_mul, normalizerMonoidHom_mul_self (mul_self_inv_conj_eq_one htt g) hg, map_one]
    have hdw : Nat.card (fixedSubgroup (MulAut.congr ε
        ((nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩))) ∣
          2 * (Nat.card (StatedSp (m + 1) K) * 1) := by
      rw [LinearPilot.card_fixedSubgroup_congr]
      exact card_fixedSubgroup_conj_dvd hset (by omega) hKc e ht hKt hg
    obtain ⟨H, C, hc, he⟩ := exists_graph_normal_form_of_card_dvd (K := K) (by omega)
      le_rfl hF hKc (Or.inl rfl) hαw hdw
    rcases hc with h1 | ⟨-, hJ⟩
    · exfalso
      apply h2 g hg
      have hC1 : C = 1 := Units.ext h1
      rw [hC1, map_one, one_mul] at he
      have hδ : LinearFlag.dualAut (2 * (m + 1)) F =
          LinearFlag.conjAut (2 * (m + 1)) F 1 * LinearFlag.dualAut (2 * (m + 1)) F := by
        rw [map_one, one_mul]
      rw [hδ, ← LinearPilot.mulAut_congr_eq_mul] at he
      obtain ⟨E⟩ := CatLeafProof.nonempty_fixed_canonical_equiv le_rfl hF (by omega)
        (1 : GL (Fin (2 * (m + 1))) F) (Or.inl rfl)
      have hch := CatLeafProof.isCharacteristicP_matrixIsometryGroup_one (k := F)
        (even_two_mul (m + 1)) (by omega)
      have Φ := ((fixedSubgroupCongrEquiv ε _).trans (MulEquiv.subgroupCongr
        (congrArg fixedSubgroup he))).trans ((fixedSubgroupCongrEquiv
          (LinearFlag.conjAut (2 * (m + 1)) F H) _).symm.trans E)
      rw [Units.val_one] at Φ
      exact isCharacteristicP_of_mulEquiv Φ.symm hch
    · exact ⟨H, C, hJ, he⟩
  obtain ⟨hg1, he1⟩ := normalizerMonoidHom_one_conj htN
  obtain ⟨H₁, C₁, hJ₁, h₁⟩ := hJ 1 hg1
  rw [he1] at h₁
  obtain ⟨H₂, C₂, hJ₂, h₂⟩ := hJ g hg
  obtain rfl : C₂ = C₁ := Units.ext (hJ₂.trans hJ₁.symm)
  refine exists_mulAut_mul_eq_of_congr ε
    (γ := LinearFlag.conjAut (2 * (m + 1)) F H₂ * (LinearFlag.conjAut (2 * (m + 1)) F H₁)⁻¹) ?_
  rw [h₁, h₂]
  group

theorem unique_of_nsRowGlobal_linearEven (hset : SeitzSetting G L) {m : ℕ} (hK : Nat.card K = 2)
    (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : NsRowGlobal e t .linearEven)
    (h2 : ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)),
      ¬ IsCharacteristicP 2
        (fixedSubgroup ((nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩))) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G) →
      g ∈ normalizer (nsGlobal e : Set G) := by
  intro g hg
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_nsGlobal e htC
  obtain ⟨β, hβ⟩ :=
    exists_mulAut_conj_of_nsRowGlobal_linearEven hset hK hm e ht hKt hglob htN h2 g hg
  exact mem_normalizer_nsGlobal_of_conj_mulAut hset hK hm e ht hKt htN hg β hβ

end Unique

@[expose] def SpTwoGraphKindInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n →
    ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (n + 1), NsKindSp e t k κ) → Sp2mKindType (nsGlobal e) (n + 1) 1 κ

section Row

theorem false_of_sp2mKindType_nsGlobal_linearOdd {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] (hset : SeitzSetting G L)
    {m : ℕ} (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hty : Sp2mKindType (nsGlobal e) (m + 1) 1 .linearOdd) : False := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_nsGlobal e htC
  have hglob := nsRowGlobal_of_sp2mKindType_linearUnitary hset hK hm e ht hKt
    (Or.inr (Or.inr (Or.inl rfl))) hty
  obtain ⟨hout, hfix⟩ := hglob.2 htN
  exact false_of_linearRow_of_subgroup hset ht htN (by omega : 3 ≤ 2 * (m + 1) + 1) hty hout hfix
    (unique_of_nsRowGlobal_linearOdd hset hK hm e ht hKt hglob)

theorem false_of_sp2mKindType_nsGlobal_linearEven {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] (hset : SeitzSetting G L)
    {m : ℕ} (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hty : Sp2mKindType (nsGlobal e) (m + 1) 1 .linearEven)
    (h2 : NsRowGlobal e t .linearEven →
      ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)),
      ¬ IsCharacteristicP 2
        (fixedSubgroup ((nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩))) : False := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_nsGlobal e htC
  have hglob := nsRowGlobal_of_sp2mKindType_linearUnitary hset hK hm e ht hKt (Or.inl rfl) hty
  obtain ⟨hout, hfix⟩ := hglob.2 htN
  exact false_of_linearRow_of_subgroup hset ht htN (by omega : 3 ≤ 2 * (m + 1)) hty hout hfix
    (unique_of_nsRowGlobal_linearEven hset hK hm e ht hKt hglob (h2 hglob))

theorem spTwoRowInput_linearOdd_of_four_le (hkind : SpTwoGraphKindInput .linearOdd) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n →
      ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
        centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∀ k : Fin (n + 1), NsKindSp e t k .linearOdd) → False :=
  fun G _ _ L hset n K _ _ _ hK hn e t ht hKt hroot =>
    false_of_sp2mKindType_nsGlobal_linearOdd hset hK (by omega) e ht hKt
      (hkind G L hset n K hK hn e t ht hKt hroot)

theorem spTwoRowInput_linearEven_of_four_le (hkind : SpTwoGraphKindInput .linearEven)
    (h2 : SpTwoLinearEvenSecondClassInput) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n →
      ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
        centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∀ k : Fin (n + 1), NsKindSp e t k .linearEven) → False :=
  fun G _ _ L hset n K _ _ _ hK hn e t ht hKt hroot =>
    false_of_sp2mKindType_nsGlobal_linearEven hset hK (by omega) e ht hKt
      (hkind G L hset n K hK hn e t ht hKt hroot)
      (fun hglob => h2 G L hset n K hK hn e t ht hKt hroot hglob)

end Row

end CFSG.SeitzReduction.SymplecticPilot
