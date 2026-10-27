module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaDickson

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (involutionCentralizersComponentFree_of_evenLieType)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Global

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem spOmegaRowGlobal_of_sp2mKindType (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {κ : Sp2mKind}
    (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (hty : Sp2mKindType (spGlobal e) n f κ) :
    SpOmegaRowGlobal e t f κ := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hLS : L ≤ spGlobal e := le_spGlobal hK4 (by omega) e
  obtain ⟨τ, hτ, hτm⟩ : ∃ τ : StatedLieTag, (τ = .POmegaPlus ∨ τ = .POmegaMinus) ∧
      LieModel (spGlobal e) τ (n + 1) 2 f := by
    rcases hκ with rfl | rfl
    · exact ⟨_, Or.inl rfl, hty⟩
    · exact ⟨_, Or.inr rfl, hty⟩
  have hadm : StatedLieAdmissible τ (n + 1) 2 f := F4Pilot.statedLieAdmissible_of_lieModel hτm
  have hS : IsSimpleGroup (spGlobal e) := LinearPilot.isSimpleGroup_of_lieModel_POmega hτ hτm
  have hLm : LieModel L .PSp n 2 f := lieModel_of_mulEquiv_statedSp e hKc (by omega) (by
    intro h
    obtain ⟨h1, -⟩ := Prod.mk.inj h
    omega)
  have hna : ∃ a b : spGlobal e, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    let _ : CommGroup (spGlobal e) := { (inferInstance : Group (spGlobal e)) with mul_comm := hc }
    have hp : (Nat.card (spGlobal e)).Prime := IsSimpleGroup.prime_card
    have h8 : 2 ^ 8 ∣ Nat.card (spGlobal e) :=
      (two_pow_eight_dvd_card_of_lieModel_PSp hLm).trans (Subgroup.card_dvd_of_le hLS)
    rcases (Nat.dvd_prime hp).1 h8 with h1 | h1
    · norm_num at h1
    · rw [← h1] at hp
      norm_num at hp
  have hSperf : ⁅spGlobal e, spGlobal e⁆ = spGlobal e :=
    isPerfect_iff.mp (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna).1.1
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  refine ⟨hty, fun hN => ?_⟩
  set θ := (spGlobal e).normalizerMonoidHom ⟨t, hN⟩ with hθdef
  have hθθ : θ * θ = 1 := by
    rw [hθdef, ← map_mul, show (⟨t, hN⟩ : normalizer (spGlobal e : Set G)) * ⟨t, hN⟩ = 1 from
      Subtype.ext htt, map_one]
  have hfixC : ∀ x : spGlobal e, x ∈ fixedSubgroup θ → (x : G) ∈ centralizer ({t} : Set G) := by
    intro x hx
    have h1 : t * (x : G) * t⁻¹ = x := by
      have := congrArg Subtype.val (show θ x = x from hx)
      rwa [hθdef, Subgroup.normalizerMonoidHom_apply_apply_coe] at this
    rw [mem_centralizer_singleton_iff]
    calc (x : G) * t = t * (x : G) * t⁻¹ * t := by rw [h1]
      _ = t * (x : G) := by group
  have hLS' : L.subgroupOf (spGlobal e) ≤ fixedSubgroup θ := by
    intro x hx
    change θ x = x
    apply Subtype.ext
    rw [hθdef, Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hxL : (x : G) ∈ L := hx
    rw [← mem_centralizer_iff.1 htC (x : G) hxL, mul_inv_cancel_right]
  have hθ1 : θ ≠ 1 := by
    intro h1
    have hSt : spGlobal e ≤ centralizer ({t} : Set G) := fun g hg =>
      hfixC ⟨g, hg⟩ (by change θ ⟨g, hg⟩ = ⟨g, hg⟩; rw [h1, MulAut.one_apply])
    have hOut : Group.IsSolvable (Outer L) :=
      isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp hn e)
    have heq : spGlobal e = L :=
      le_antisymm (std_perfect_le hset.standardSetting hOut htC ht hSperf hSt) hLS
    have hLτ : LieModel L τ (n + 1) 2 f :=
      LieType.CurtisTits.lieModel_of_mulEquiv (MulEquiv.subgroupCongr heq) hτm
    exact false_of_lieModel_ne_PSp (sp2mEvenTypeDetClassical n) hLm
      (Or.inl (by rcases hτ with rfl | rfl <;> decide)) (by rcases hτ with rfl | rfl <;> decide)
      hadm hLτ
  have hθ2 : orderOf θ = 2 := orderOf_eq_prime (by rw [_root_.sq]; exact hθθ) hθ1
  let D : Subgroup (fixedSubgroup θ) := (L.subgroupOf (spGlobal e)).subgroupOf (fixedSubgroup θ)
  have eD : D ≃* L :=
    (Subgroup.subgroupOfEquivOfLe hLS').trans (Subgroup.subgroupOfEquivOfLe hLS)
  have hDm : LieModel D .PSp n 2 f := LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hLm
  have hDq : IsQuasisimple D :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv
      (isComponent_top_of_lieModel_PSp hDm).1.1
  have hDn : D.Normal := by
    refine ⟨fun d hd g => ?_⟩
    have hdL : (((d : fixedSubgroup θ) : spGlobal e) : G) ∈ L := hd
    have hgN := hCN (hfixC _ g.2)
    change ((((g * d * g⁻¹ : fixedSubgroup θ) : spGlobal e) : G)) ∈ L
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (mem_normalizer_iff.1 hgN _).1 hdL
  have hD : IsComponent D := ⟨hDq, hDn.isSubnormal⟩
  by_cases hin : θ ∈ (MulAut.conj : spGlobal e →* MulAut (spGlobal e)).range
  · exact (F4Pilot.false_of_isComponent_fixedSubgroup_inner hna
      (involutionCentralizersComponentFree_of_evenLieType ⟨τ, n + 1, f, hadm, hτm⟩) hθ2 hin
      hD).elim
  · exact ⟨hin, (catSp2mEvenOuterFamily_POmega hτ (sp2mEvenTypeDetClassical n) (spGlobal e) hS
      hna (n + 1) f hadm hτm θ hθ2 hin f D hD hDm).2⟩

end Global

@[expose] def SpOmegaKindInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k κ) → Sp2mKindType (spGlobal e) n f κ

section Rows

theorem spOmegaRecognitionInput_of_kind {κ : Sp2mKind} (hκ : κ = .omegaPlus ∨ κ = .omegaMinus)
    (h : SpOmegaKindInput κ) : SpOmegaRecognitionInput κ := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot
  exact spOmegaRowGlobal_of_sp2mKindType hset (by omega) hKc hf e ht hKt hκ
    (h G L hset n f K hn hKc hf e t ht hKt hroot)

theorem false_of_spOmegaPlusRow_of_kind (hk : SpOmegaKindInput .omegaPlus)
    (hu : SpOmegaRowUniqueInput .omegaPlus) : SpOmegaPlusRowInput :=
  false_of_spOmegaPlusRow_of_recognition (spOmegaRecognitionInput_of_kind (Or.inl rfl) hk) hu

theorem false_of_spOmegaMinusRow_of_kind (hk : SpOmegaKindInput .omegaMinus)
    (hu : SpOmegaRowUniqueInput .omegaMinus) (hO : OmegaMinusOutInput) : SpOmegaMinusRowInput :=
  false_of_spOmegaMinusRow (spOmegaRecognitionInput_of_kind (Or.inr rfl) hk) hu hO

end Rows

end CFSG.SeitzReduction.SymplecticPilot
