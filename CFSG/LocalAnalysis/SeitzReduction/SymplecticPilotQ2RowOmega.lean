module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLinear
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowMinusOut

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.ComponentClassification.CatLeaf (involutionCentralizersComponentFree_of_evenLieType)
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.SeitzReduction.F4Pilot (normalizerMulAut)

@[expose] def q2GlobalKind : Sp2mKind → Sp2mKind
  | .omegaPlus => .omegaMinus
  | .omegaMinus => .omegaPlus
  | κ => κ

@[simp] theorem q2GlobalKind_omegaPlus : q2GlobalKind .omegaPlus = .omegaMinus := rfl

@[simp] theorem q2GlobalKind_omegaMinus : q2GlobalKind .omegaMinus = .omegaPlus := rfl

section Global


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem nsRowGlobal_of_sp2mKindType_omega (hset : SeitzSetting G L) {m : ℕ}
    (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {κ : Sp2mKind}
    (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (hty : Sp2mKindType (nsGlobal e) (m + 1) 1 κ) :
    NsRowGlobal e t κ := by
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hLS : L ≤ nsGlobal e := le_nsGlobal hK hm e
  obtain ⟨τ, hτ, hτm⟩ : ∃ τ : StatedLieTag, (τ = .POmegaPlus ∨ τ = .POmegaMinus) ∧
      LieModel (nsGlobal e) τ (m + 1 + 1) 2 1 := by
    rcases hκ with rfl | rfl
    · exact ⟨_, Or.inl rfl, hty⟩
    · exact ⟨_, Or.inr rfl, hty⟩
  have hadm : StatedLieAdmissible τ (m + 1 + 1) 2 1 := F4Pilot.statedLieAdmissible_of_lieModel hτm
  have hS : IsSimpleGroup (nsGlobal e) := LinearPilot.isSimpleGroup_of_lieModel_POmega hτ hτm
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
    have hLτ : LieModel L τ (m + 1 + 1) 2 1 :=
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
      (involutionCentralizersComponentFree_of_evenLieType ⟨τ, m + 1 + 1, 1, hadm, hτm⟩) hθ2 hin
      hD).elim
  · exact ⟨hin, (catSp2mEvenOuterFamily_POmega hτ (sp2mEvenTypeDetClassical (m + 1)) (nsGlobal e)
      hS hna (m + 1 + 1) 1 hadm hτm θ hθ2 hin 1 D hD hDm).2⟩

end Global

section Endgame


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_omegaPlusRow_of_subgroup (hset : SeitzSetting G L) {M : Subgroup G} {t : G}
    (ht : orderOf t = 2) (htN : t ∈ normalizer (M : Set G)) {N f : ℕ} (hN : 5 ≤ N)
    (hty : LieModel M .POmegaPlus N 2 f)
    (hout : M.normalizerMonoidHom ⟨t, htN⟩ ∉ (MulAut.conj : M →* MulAut M).range) {m' f' : ℕ}
    (hfix : LieModel (fixedSubgroup (M.normalizerMonoidHom ⟨t, htN⟩)) .PSp m' 2 f')
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (M : Set G) → g ∈ normalizer (M : Set G)) :
    False := by
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hC := CFSG.ComponentClassification.EvenOrthSelector.statedModel_of_lieModel
    (by decide) hty
  have hI := (even_orthogonal_involutions_conjugate_into_semilinear_image M
    .POmegaPlus (Or.inl rfl) N f hC).1
  obtain ⟨⟨-, hf1, hn4'⟩, K', _, _, hK', ⟨eE⟩⟩ := hC
  have hn4 : 4 ≤ N := hn4'
  have : CharP K' 2 := LinearPilot.charP_two_of_card_eq_two_pow hK'
  have hconj := (hI K' hK' eE).1
  have hreg := regular_coordinateQuadPlus (K := K') (n := N) (by omega)
  have hE := commutator_coordinateQuadPlus (K := K') (n := N) (by omega)
  obtain ⟨v, hv, χ, hχInn, hχv⟩ := omegaPlusDicksonInput_holds K' N hN
  set ε := coordinatePlusWitnessEquiv K' eE with hεdef
  set θ := M.normalizerMonoidHom ⟨t, htN⟩ with hθdef
  have hθθ : θ * θ = 1 := by
    rw [hθdef, ← map_mul, show (⟨t, htN⟩ : normalizer (M : Set G)) * ⟨t, htN⟩ = 1 from
      Subtype.ext htt, map_one]
  have hαα : MulAut.congr ε θ * MulAut.congr ε θ = 1 := by rw [← map_mul, hθθ, map_one]
  have hαo : MulAut.congr ε θ ∉ inner (matrixProjectiveDerived (coordinateQuadPlus N K')) := by
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hout
  have hαfix : LieModel (fixedSubgroup (MulAut.congr ε θ)) .PSp m' 2 f' :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv ε θ) hfix
  obtain ⟨Ψ, hΨ⟩ := exists_conj_eq_symmetryAut_of_lieModel_PSp hf1 hK' hn4 hreg.1 hreg.2 hE hconj
    hv _ hαα hαo hαfix
  have : IsSimpleGroup G := hset.1
  refine EPilot.false_of_simple_of_mulAut_hom ε htN ht huniq χ (by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]; decide) hχInn ?_
  have h1 : χ (MulAut.congr ε θ) = χ (symmetryAut (coordinateQuadPlus N K') v) := by
    rw [hΨ, map_mul, map_mul, map_inv]
    exact mul_inv_cancel_comm _ _
  change χ (MulAut.congr ε θ) ≠ 1
  rw [h1]
  exact hχv

theorem false_of_omegaMinusRow_of_subgroup (hset : SeitzSetting G L) {M : Subgroup G}
    (hLM : L ≤ M) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (htN : t ∈ normalizer (M : Set G)) {N f : ℕ} (hty : LieModel M .POmegaMinus N 2 f)
    (hout : M.normalizerMonoidHom ⟨t, htN⟩ ∉ (MulAut.conj : M →* MulAut M).range) {m' f' : ℕ}
    (hfix : LieModel (fixedSubgroup (M.normalizerMonoidHom ⟨t, htN⟩)) .PSp m' 2 f')
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (M : Set G) → g ∈ normalizer (M : Set G)) :
    False := by
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hC := CFSG.ComponentClassification.EvenOrthSelector.statedModel_of_lieModel
    (by decide) hty
  have hI := (even_orthogonal_involutions_conjugate_into_semilinear_image M
    .POmegaMinus (Or.inr rfl) N f hC).1
  obtain ⟨⟨-, hf1, hn4'⟩, K', _, _, hK', b, c, hirr, ⟨eE⟩⟩ := hC
  have hn4 : 4 ≤ N := hn4'
  have h1n : 1 ≤ N := by omega
  have : CharP K' 2 := LinearPilot.charP_two_of_card_eq_two_pow hK'
  have hconj := hI h1n K' hK' b c hirr eE
  have hreg := regular_coordinateQuadMinus N K' b c hn4 hirr
  have hE := commutator_coordinateQuadMinus N K' b c hn4 hirr
  obtain ⟨v, hv, C, hCcyc, hCInn, hNF, hvC⟩ := omegaMinusOutInput_holds K' N hn4 b c hirr
  set ε := coordinateMinusWitnessEquiv K' h1n b c eE with hεdef
  set θ := M.normalizerMonoidHom ⟨t, htN⟩ with hθdef
  have hθθ : θ * θ = 1 := by
    rw [hθdef, ← map_mul, show (⟨t, htN⟩ : normalizer (M : Set G)) * ⟨t, htN⟩ = 1 from
      Subtype.ext htt, map_one]
  have hαα : MulAut.congr ε θ * MulAut.congr ε θ = 1 := by rw [← map_mul, hθθ, map_one]
  have hαo : MulAut.congr ε θ ∉
      inner (matrixProjectiveDerived (coordinateQuadMinus N K' h1n b c)) := by
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hout
  have hαfix : LieModel (fixedSubgroup (MulAut.congr ε θ)) .PSp m' 2 f' :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv ε θ) hfix
  obtain ⟨Ψ, hΨ⟩ := exists_conj_eq_symmetryAut_of_lieModel_PSp hf1 hK' hn4 hreg.1 hreg.2 hE hconj
    hv _ hαα hαo hαfix
  have htZ : t ∉ centralizer (M : Set G) := by
    intro htZ
    apply hout
    refine ⟨1, MulEquiv.ext fun y => Subtype.ext ?_⟩
    rw [map_one, MulAut.one_apply, hθdef, Subgroup.normalizerMonoidHom_apply_apply_coe,
      ← mem_centralizer_iff.1 htZ y y.2, mul_inv_cancel_right]
  have hZ := EPilot.odd_card_centralizer_of_inf_eq_zpowers hKt hLM ht htN htZ
  have hker : Odd (Nat.card (normalizerMulAut ε).ker) := by
    rw [EPilot.card_ker_normalizerMulAut]
    exact hZ
  have : IsCyclic C := hCcyc
  have hout' : normalizerMulAut ε ⟨t, htN⟩ ∉
      (MulAut.conj : matrixProjectiveDerived (coordinateQuadMinus N K' h1n b c) →*
        MulAut _).range := hαo
  have hidx := EPilot.exists_normal_index_two_of_action_complement_of_isConj (normalizerMulAut ε)
    hker hCInn hNF (EPilot.exists_normalizerMulAut_eq_conj ε) htN ht hout' huniq ⟨Ψ⁻¹, by
      change Ψ⁻¹ * MulAut.congr ε θ * Ψ⁻¹⁻¹ ∈ C
      have h1 : Ψ⁻¹ * MulAut.congr ε θ * Ψ⁻¹⁻¹ =
          symmetryAut (coordinateQuadMinus N K' h1n b c) v := by
        rw [hΨ]
        group
      rw [h1]
      exact hvC⟩
  have : IsSimpleGroup G := hset.1
  have htG : t ∉ M := EPilot.not_mem_of_normalizerMulAut_not_mem_range ε htN hout'
  exact CFSG.SeitzReduction.not_exists_normal_index_two_of_simple
    (EPilot.two_lt_card_of_odd_centralizer hZ ht htG) hidx

end Endgame

@[expose] def SpTwoOmegaKindInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n →
    ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (n + 1), NsKindSp e t k κ) →
        Sp2mKindType (nsGlobal e) (n + 1) 1 (q2GlobalKind κ)

@[expose] def SpTwoOmegaClassInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n →
    ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin (n + 1), NsKindSp e t k κ) → NsRowGlobal e t (q2GlobalKind κ) →
      ∀ (htN : t ∈ normalizer (nsGlobal e : Set G)) (g : G)
        (hg : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G)),
        ∃ β : MulAut (nsGlobal e), β * (nsGlobal e).normalizerMonoidHom ⟨t, htN⟩ =
          (nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ * β

theorem unique_of_spTwoOmegaClassInput {κ : Sp2mKind} (hcls : SpTwoOmegaClassInput κ)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hset : SeitzSetting G L) {n : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) (hn : 4 ≤ n)
    (e : L ≃* StatedSp (n + 1) K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hroot : ∀ k : Fin (n + 1), NsKindSp e t k κ) (hglob : NsRowGlobal e t (q2GlobalKind κ)) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G) →
      g ∈ normalizer (nsGlobal e : Set G) := by
  intro g hg
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_nsGlobal e htC
  obtain ⟨β, hβ⟩ := hcls G L hset n K hK hn e t ht hKt hroot hglob htN g hg
  exact mem_normalizer_nsGlobal_of_conj_mulAut hset hK (by omega) e ht hKt htN hg β hβ

section Row


theorem spTwoRowInput_omegaPlus_of_four_le (hkind : SpTwoOmegaKindInput .omegaPlus)
    (hcls : SpTwoOmegaClassInput .omegaPlus) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n →
      ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
        centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∀ k : Fin (n + 1), NsKindSp e t k .omegaPlus) → False := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt hroot
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_nsGlobal e htC
  have hty : Sp2mKindType (nsGlobal e) (n + 1) 1 .omegaMinus :=
    hkind G L hset n K hK hn e t ht hKt hroot
  have hglob := nsRowGlobal_of_sp2mKindType_omega hset hK (by omega) e ht hKt (Or.inr rfl) hty
  obtain ⟨hout, hfix⟩ := hglob.2 htN
  exact false_of_omegaMinusRow_of_subgroup hset (le_nsGlobal hK (by omega) e) ht hKt htN hty
    hout hfix (unique_of_spTwoOmegaClassInput hcls hset hK hn e ht hKt hroot hglob)

theorem spTwoRowInput_omegaMinus_of_four_le (hkind : SpTwoOmegaKindInput .omegaMinus)
    (hcls : SpTwoOmegaClassInput .omegaMinus) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
      ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → 4 ≤ n →
      ∀ (e : L ≃* StatedSp (n + 1) K) (t : G), orderOf t = 2 →
        centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        (∀ k : Fin (n + 1), NsKindSp e t k .omegaMinus) → False := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht hKt hroot
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_nsGlobal e htC
  have hty : Sp2mKindType (nsGlobal e) (n + 1) 1 .omegaPlus :=
    hkind G L hset n K hK hn e t ht hKt hroot
  have hglob := nsRowGlobal_of_sp2mKindType_omega hset hK (by omega) e ht hKt (Or.inl rfl) hty
  obtain ⟨hout, hfix⟩ := hglob.2 htN
  exact false_of_omegaPlusRow_of_subgroup hset ht htN (by omega : 5 ≤ n + 1 + 1) hty hout hfix
    (unique_of_spTwoOmegaClassInput hcls hset hK hn e ht hKt hroot hglob)

end Row

end CFSG.SeitzReduction.SymplecticPilot
