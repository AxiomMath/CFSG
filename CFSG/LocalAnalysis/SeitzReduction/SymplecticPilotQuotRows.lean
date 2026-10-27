module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQuotTransfer
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUEven
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryBar
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryPower
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LULinear
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut)

section Basic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]

theorem exists_orderOf_eq_two_of_mulEquiv_quot {n f : ℕ} (hn : 1 ≤ n) (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hZ : Odd (Nat.card (center (spGlobal e)))) {P : Type*} [Group P]
    (ψ : spGlobal e ⧸ center (spGlobal e) ≃* P) : ∃ y : P, orderOf y = 2 := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hLS : L ≤ spGlobal e := le_spGlobal hK4 hn e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2L : 2 ∣ Nat.card L := by
    rw [Nat.card_congr e.toEquiv]
    have h := factorization_card_statedSp hn hKc (by omega)
    refine Nat.dvd_of_factorization_pos ?_
    rw [h]
    positivity
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2L
  refine ⟨ψ (QuotientGroup.mk' (center (spGlobal e)) (Subgroup.inclusion hLS x)), ?_⟩
  rw [MulEquiv.orderOf_eq]
  change orderOf (((QuotientGroup.mk' (center (spGlobal e))).comp (Subgroup.inclusion hLS)) x) = 2
  rw [orderOf_injective _ (injective_mk_comp_inclusion hLS ht hKt hZ) x, hx]

end Basic

theorem spGraphStandardClassQuotInput_linearOdd : SpGraphStandardClassQuotInput .linearOdd := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt _ hglob htN g hg
  obtain ⟨⟨-, hZ, hty⟩, -⟩ := hglob
  have hty' : LieModel (spGlobal e ⧸ center (spGlobal e)) .PSL (2 * n + 1) 2 f := hty
  have hadm : StatedLieAdmissible .PSL (2 * n + 1) 2 f :=
    F4Pilot.statedLieAdmissible_of_lieModel hty'
  obtain ⟨F, _, _, hF, ⟨eJ⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hty'
  have : CharP F 2 := LinearPilot.charP_two_of_card_eq_two_pow hF
  have hw2 : orderOf (g⁻¹ * t * g) = 2 := by
    rw [show g⁻¹ * t * g = MulAut.conj g⁻¹ t by simp, MulEquiv.orderOf_eq, ht]
  set ε : spGlobal e ⧸ center (spGlobal e) ≃* LinearFlag.projectiveSL (2 * n + 1) F :=
    eJ.trans (CatalogueBLinearHigherB.nativeEquiv (2 * n + 1) F).symm with hεdef
  set θt := centerQuotAction (spGlobal e) ⟨t, htN⟩ with hθt
  set θw := centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩ with hθw
  have hαt : MulAut.congr ε θt * MulAut.congr ε θt = 1 := by
    rw [← map_mul, hθt, centerQuotAction_mul_self ht htN, map_one]
  have hαw : MulAut.congr ε θw * MulAut.congr ε θw = 1 := by
    rw [← map_mul, hθw, centerQuotAction_mul_self hw2 hg, map_one]
  have hdt : Nat.card (fixedSubgroup (MulAut.congr ε θt)) ∣
      2 * (Nat.card (StatedSp n K) * f) := by
    rw [LinearPilot.card_fixedSubgroup_congr]
    exact (card_fixedSubgroup_quot_dvd hZ (MulEquiv.refl _) ht htN).trans
      (card_fixedSubgroup_dvd_of_mem hset (by omega) hKc e ht hKt htN)
  have hdw : Nat.card (fixedSubgroup (MulAut.congr ε θw)) ∣
      2 * (Nat.card (StatedSp n K) * f) := by
    rw [LinearPilot.card_fixedSubgroup_congr]
    exact (card_fixedSubgroup_quot_dvd hZ (MulEquiv.refl _) hw2 hg).trans
      (card_fixedSubgroup_conj_dvd hset (by omega) hKc e ht hKt hg)
  obtain ⟨H₁, C₁, hc₁, he₁⟩ := exists_graph_normal_form_of_card_dvd (K := K) (by omega)
    (by omega) hF hKc (Or.inr rfl) hαt hdt
  obtain ⟨H₂, C₂, hc₂, he₂⟩ := exists_graph_normal_form_of_card_dvd (K := K) (by omega)
    (by omega) hF hKc (Or.inr rfl) hαw hdw
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
    (γ := LinearFlag.conjAut (2 * n + 1) F H₂ * (LinearFlag.conjAut (2 * n + 1) F H₁)⁻¹) ?_
  rw [he₁, he₂]
  group

theorem spOmegaRowUniqueQuotInput_linearOdd : SpOmegaRowUniqueQuotInput .linearOdd :=
  spOmegaRowUniqueQuotInput_of_standardClass spGraphStandardClassQuotInput_linearOdd

theorem spGraphStandardClassQuotInput_unitaryOdd : SpGraphStandardClassQuotInput .unitaryOdd := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt _ hglob htN g hg
  obtain ⟨⟨-, hZ, hty⟩, -⟩ := hglob
  have hty' : LieModel (spGlobal e ⧸ center (spGlobal e)) .PSU (2 * n + 1) 2 f := hty
  have hadm : StatedLieAdmissible .PSU (2 * n + 1) 2 f :=
    F4Pilot.statedLieAdmissible_of_lieModel hty'
  obtain ⟨K', _, h, ⟨ψ⟩⟩ := CatLeafProof.nonempty_mulEquiv_primeFormP_of_lieModel hadm hty'
  have : Finite K' := h.finite
  have hq : ¬(2 * n + 1 = 3 ∧ 2 ^ f = 2) := by omega
  have hv : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  have hinner : ∀ y : primeFormP h ((1 : GL (Fin (2 * n + 1)) K') :
      Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) K'), orderOf y = 2 →
      f * n ^ 2 + 1 + f.factorization 2 <
        (Nat.card (centralizer ({y} : Set (primeFormP h ((1 : GL (Fin (2 * n + 1)) K') :
          Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) K'))))).factorization 2 := by
    intro y hy
    have h1 := le_factorization_card_centralizer_primeFormP_one h y hy
    rw [show (2 * n + 1) / 2 = n by omega, show (2 * n + 1) % 2 = 1 by omega] at h1
    have h3 : f * (n * (n + 2 * 1)) = f * n ^ 2 + 2 * (f * n) := by ring
    have h4 : f ≤ f * n := Nat.le_mul_of_pos_right f (by omega)
    omega
  have hy0 := exists_orderOf_eq_two_of_mulEquiv_quot (by omega) hKc hf e ht hKt hZ ψ
  have hw2 : orderOf (g⁻¹ * t * g) = 2 := by
    rw [show g⁻¹ * t * g = MulAut.conj g⁻¹ t by simp, MulEquiv.orderOf_eq, ht]
  set θt := centerQuotAction (spGlobal e) ⟨t, htN⟩ with hθt
  set θw := centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩ with hθw
  have hαt : MulAut.congr ψ θt * MulAut.congr ψ θt = 1 := by
    rw [← map_mul, hθt, centerQuotAction_mul_self ht htN, map_one]
  have hαw : MulAut.congr ψ θw * MulAut.congr ψ θw = 1 := by
    rw [← map_mul, hθw, centerQuotAction_mul_self hw2 hg, map_one]
  have hlet : (Nat.card (fixedSubgroup (MulAut.congr ψ θt))).factorization 2 ≤
      f * n ^ 2 + 1 + f.factorization 2 := by
    rw [LinearPilot.card_fixedSubgroup_congr]
    exact (factorization_card_fixedSubgroup_quot_le hZ (MulEquiv.refl _) ht htN).trans
      (factorization_card_fixedSubgroup_le_of_mem hset (by omega) hKc e ht hKt htN)
  have hlew : (Nat.card (fixedSubgroup (MulAut.congr ψ θw))).factorization 2 ≤
      f * n ^ 2 + 1 + f.factorization 2 := by
    rw [LinearPilot.card_fixedSubgroup_congr]
    exact (factorization_card_fixedSubgroup_quot_le hZ (MulEquiv.refl _) hw2 hg).trans
      (factorization_card_fixedSubgroup_conj_le hset (by omega) hKc e ht hKt hg)
  obtain ⟨C₁, hC₁, hc₁, θ₁, he₁⟩ :=
    exists_fieldBar_normal_form_of_factorization_le h (by omega) hq hinner hy0 hαt hlet
  obtain ⟨C₂, hC₂, hc₂, θ₂, he₂⟩ :=
    exists_fieldBar_normal_form_of_factorization_le h (by omega) hq hinner hy0 hαw hlew
  have h1 : C₁ = 1 := by
    rcases hc₁ with h1 | ⟨r, hr, -⟩
    · exact Units.ext h1
    · omega
  have h2 : C₂ = 1 := by
    rcases hc₂ with h2 | ⟨r, hr, -⟩
    · exact Units.ext h2
    · omega
  subst h1 h2
  refine exists_mulAut_mul_eq_of_congr ψ (γ := θ₁.symm.trans θ₂) ?_
  rw [he₁, he₂]
  exact symm_trans_mul_congr θ₁ θ₂ _

theorem spOmegaRowUniqueQuotInput_unitaryOdd : SpOmegaRowUniqueQuotInput .unitaryOdd :=
  spOmegaRowUniqueQuotInput_of_standardClass spGraphStandardClassQuotInput_unitaryOdd

section Endgame

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem false_of_spLinearRow_of_globalQuot
    (hset : SeitzSetting G L) {n f : ℕ}
    (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {κ : Sp2mKind}
    (hκ : κ = .linearEven ∨ κ = .linearOdd) (hglob : SpOmegaRowGlobalQuot e t f κ)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G) →
      g ∈ normalizer (spGlobal e : Set G)) : False := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_spGlobal e htC
  obtain ⟨⟨-, -, hty⟩, hact⟩ := hglob
  obtain ⟨hout, hfix⟩ := hact htN
  have hn2 : 2 ≤ n := (admissible_of_lieModel_PSp hfix).2.1
  obtain ⟨r, hτm, hr⟩ : ∃ r, LieModel (spGlobal e ⧸ center (spGlobal e)) .PSL r 2 f ∧ 3 ≤ r := by
    rcases hκ with rfl | rfl
    · exact ⟨_, hty, by omega⟩
    · exact ⟨_, hty, by omega⟩
  have hadm : StatedLieAdmissible .PSL r 2 f := F4Pilot.statedLieAdmissible_of_lieModel hτm
  obtain ⟨F, _, _, hF, ⟨eJ⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hτm
  set ε : spGlobal e ⧸ center (spGlobal e) ≃* LinearFlag.projectiveSL r F :=
    eJ.trans (CatalogueBLinearHigherB.nativeEquiv r F).symm with hεdef
  set θ := centerQuotAction (spGlobal e) ⟨t, htN⟩ with hθdef
  have hα2 : MulAut.congr ε θ ^ 2 = 1 := by
    rw [_root_.sq, ← map_mul, hθdef, centerQuotAction_mul_self ht htN, map_one]
  have hαo : MulAut.congr ε θ ∉
      (MulAut.conj : LinearFlag.projectiveSL r F →* MulAut _).range := fun h =>
    hout ((FixedFourGroup.congr_mem_inner_iff ε θ).1 h)
  have hαfix : LieModel (fixedSubgroup (MulAut.congr ε θ)) .PSp n 2 f :=
    LieType.CurtisTits.lieModel_of_mulEquiv (fixedSubgroupCongrEquiv ε θ) hfix
  have hαE := not_mem_semilinearAutGroup_of_lieModel_PSp hr hadm.2.1 hF hα2 hαo hαfix
  obtain ⟨χ, hχInn, hχE⟩ := exists_linearGraphCoordinate (F := F) hr
  have : IsSimpleGroup G := hset.1
  refine EPilot.false_of_simple_of_quotMulAut_hom ε htN ht huniq χ (by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]; decide) hχInn ?_
  rw [normalizerQuotMulAut_eq_congr]
  exact hχE _ hαE

theorem false_of_spUnitaryRow_of_globalQuot (hset : SeitzSetting G L) {n f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {κ : Sp2mKind}
    (hκ : κ = .unitaryEven ∨ κ = .unitaryOdd) (hglob : SpOmegaRowGlobalQuot e t f κ)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G) →
      g ∈ normalizer (spGlobal e : Set G)) : False := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have htN := mem_normalizer_spGlobal e htC
  obtain ⟨⟨hqs, -, hty⟩, hact⟩ := hglob
  obtain ⟨hout, hfix⟩ := hact htN
  have hn : 2 ≤ n := (admissible_of_lieModel_PSp hfix).2.1
  obtain ⟨m, hτm⟩ : ∃ m, LieModel (spGlobal e ⧸ center (spGlobal e)) .PSU m 2 f := by
    rcases hκ with rfl | rfl
    · exact ⟨_, hty⟩
    · exact ⟨_, hty⟩
  set θ := centerQuotAction (spGlobal e) ⟨t, htN⟩ with hθdef
  have hθθ : θ * θ = 1 := centerQuotAction_mul_self ht htN
  obtain ⟨K', _, h, C₀, hC₀, hm, hq, φ, ε, -, hφ, hε⟩ :=
    exists_primeFormFieldHom_eq_of_lieModel_PSU hτm hθθ hout
  have : Finite K' := h.finite
  obtain ⟨hcard, hcyc⟩ := card_ringAut_and_isCyclic Nat.prime_two K' h.card
  have : Finite (K' ≃+* K') :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; have := h.one_le; omega)
  have : IsCyclic (K' ≃+* K') := hcyc
  have htZ : t ∉ centralizer (spGlobal e : Set G) := by
    intro htZ
    apply hout
    refine ⟨1, ?_⟩
    rw [map_one]
    exact (EPilot.normalizerQuotMulAut_eq_one_of_mem_centralizer (MulEquiv.refl _) htN htZ).symm
  have hZc := EPilot.odd_card_centralizer_of_inf_eq_zpowers hKt (le_spGlobal hK4 (by omega) e)
    ht htN htZ
  have : Group.IsPerfect (spGlobal e) := hqs.1
  have hker : Odd (Nat.card (normalizerQuotMulAut ε).ker) := by
    rw [EPilot.card_ker_normalizerQuotMulAut]
    exact hZc
  have hρt : normalizerQuotMulAut ε ⟨t, htN⟩ = primeFormFieldHom h hC₀ φ := by
    rw [normalizerQuotMulAut_eq_congr]
    exact hε
  have hout' : normalizerQuotMulAut ε ⟨t, htN⟩ ∉
      (MulAut.conj : primeFormP h (C₀ : Matrix (Fin m) (Fin m) K') →* MulAut _).range := by
    rw [normalizerQuotMulAut_eq_congr]
    exact fun h' => hout ((FixedFourGroup.congr_mem_inner_iff ε θ).1 h')
  have hidx := exists_normal_index_two_of_fieldFactor (normalizerQuotMulAut ε) hker
    (EPilot.exists_normalizerQuotMulAut_eq_conj ε) (primeFormFieldFactor h hC₀ hm hq)
    (primeFormFieldHom h hC₀) (primeFormFieldFactor_fieldHom h hC₀ hm hq)
    (fun d hd k hk => UnitaryPilot.mem_inner_of_mem_primeFormD_of_pow h C₀
      (by rwa [← ker_primeFormFieldFactor h hC₀ hm hq]) hk)
    htN ht ⟨φ, hρt.symm⟩ hout' (fun d hd hcomm => by
      rw [hρt] at hcomm
      exact primeFormBarInvertsInput_holds f K' h m C₀ hC₀ hm φ hφ d
        (by rwa [← ker_primeFormFieldFactor h hC₀ hm hq]) hcomm)
    huniq
  have : IsSimpleGroup G := hset.1
  exact CFSG.SeitzReduction.not_exists_normal_index_two_of_simple
    (EPilot.two_lt_card_of_normalizerQuotMulAut_not_mem_range ε htN hout') hidx

end Endgame

section Even

theorem centerQuotAction_one_conj {G : Type} [Group G] {M : Subgroup G} {t : G}
    (htM : t ∈ normalizer (M : Set G)) :
    ∃ hg : (1 : G)⁻¹ * t * 1 ∈ normalizer (M : Set G),
      centerQuotAction M ⟨(1 : G)⁻¹ * t * 1, hg⟩ = centerQuotAction M ⟨t, htM⟩ := by
  have he : (1 : G)⁻¹ * t * 1 = t := by group
  have hg : (1 : G)⁻¹ * t * 1 ∈ normalizer (M : Set G) := by rw [he]; exact htM
  refine ⟨hg, ?_⟩
  have hs : (⟨(1 : G)⁻¹ * t * 1, hg⟩ : normalizer (M : Set G)) = ⟨t, htM⟩ := Subtype.ext he
  rw [hs]

@[expose] def SpLinearEvenSecondClassQuotInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k .linearEven) → SpOmegaRowGlobalQuot e t f .linearEven →
      ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G))
        (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ f →
        ∀ (ε : spGlobal e ⧸ center (spGlobal e) ≃* LinearFlag.projectiveSL (2 * n) F)
          (H : GL (Fin (2 * n)) F),
          MulAut.congr ε (centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩) ≠
            LinearFlag.conjAut (2 * n) F H * LinearFlag.dualAut (2 * n) F *
              (LinearFlag.conjAut (2 * n) F H)⁻¹

@[expose] def SpUnitaryEvenSecondClassQuotInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k .unitaryEven) → SpOmegaRowGlobalQuot e t f .unitaryEven →
      ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G))
        (K' : Type) [Field K'] (h : UnitaryFieldData 2 f K')
        (ψ : spGlobal e ⧸ center (spGlobal e) ≃* primeFormP h ((1 : GL (Fin (2 * n)) K') :
          Matrix (Fin (2 * n)) (Fin (2 * n)) K'))
        (θ : MulAut (primeFormP h ((1 : GL (Fin (2 * n)) K') :
          Matrix (Fin (2 * n)) (Fin (2 * n)) K'))),
          MulAut.congr ψ (centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩) ≠
            θ * primeFormFieldHom h isPrimeFormGram_one (UnitaryPilot.barRingEquiv h) * θ⁻¹

theorem spGraphStandardClassQuotInput_linearEven_of_secondClass
    (h2 : SpLinearEvenSecondClassQuotInput) : SpGraphStandardClassQuotInput .linearEven := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot hglob htN g hg
  have hZ : Odd (Nat.card (center (spGlobal e))) := hglob.1.2.1
  have hty' : LieModel (spGlobal e ⧸ center (spGlobal e)) .PSL (2 * n) 2 f := hglob.1.2.2
  have hadm : StatedLieAdmissible .PSL (2 * n) 2 f :=
    F4Pilot.statedLieAdmissible_of_lieModel hty'
  obtain ⟨F, _, _, hF, ⟨eJ⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hty'
  have : CharP F 2 := LinearPilot.charP_two_of_card_eq_two_pow hF
  set ε : spGlobal e ⧸ center (spGlobal e) ≃* LinearFlag.projectiveSL (2 * n) F :=
    eJ.trans (CatalogueBLinearHigherB.nativeEquiv (2 * n) F).symm with hεdef
  have hJ : ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)),
      ∃ H C : GL (Fin (2 * n)) F,
        (C : Matrix (Fin (2 * n)) (Fin (2 * n)) F) = blockSwapJ (2 * n) n ∧
        MulAut.congr ε (centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩) =
          LinearFlag.conjAut (2 * n) F H *
            (LinearFlag.conjAut (2 * n) F C * LinearFlag.dualAut (2 * n) F) *
              (LinearFlag.conjAut (2 * n) F H)⁻¹ := by
    intro g hg
    have hw2 : orderOf (g⁻¹ * t * g) = 2 := by
      rw [show g⁻¹ * t * g = MulAut.conj g⁻¹ t by simp, MulEquiv.orderOf_eq, ht]
    have hαw : MulAut.congr ε (centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩) *
        MulAut.congr ε (centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩) = 1 := by
      rw [← map_mul, centerQuotAction_mul_self hw2 hg, map_one]
    have hdw : Nat.card (fixedSubgroup (MulAut.congr ε
        (centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩))) ∣
          2 * (Nat.card (StatedSp n K) * f) := by
      rw [LinearPilot.card_fixedSubgroup_congr]
      exact (card_fixedSubgroup_quot_dvd hZ (MulEquiv.refl _) hw2 hg).trans
        (card_fixedSubgroup_conj_dvd hset (by omega) hKc e ht hKt hg)
    obtain ⟨H, C, hc, he⟩ := exists_graph_normal_form_of_card_dvd (K := K) (by omega)
      (by omega) hF hKc (Or.inl rfl) hαw hdw
    rcases hc with h1 | ⟨-, hJ⟩
    · exfalso
      have hC1 : C = 1 := Units.ext h1
      rw [hC1, map_one, one_mul] at he
      exact h2 G L hset n f K hn hKc hf e t ht hKt hroot hglob g hg F hF ε H he
    · exact ⟨H, C, hJ, he⟩
  obtain ⟨hg1, he1⟩ := centerQuotAction_one_conj htN
  obtain ⟨H₁, C₁, hJ₁, h₁⟩ := hJ 1 hg1
  rw [he1] at h₁
  obtain ⟨H₂, C₂, hJ₂, h₂⟩ := hJ g hg
  obtain rfl : C₂ = C₁ := Units.ext (hJ₂.trans hJ₁.symm)
  refine exists_mulAut_mul_eq_of_congr ε
    (γ := LinearFlag.conjAut (2 * n) F H₂ * (LinearFlag.conjAut (2 * n) F H₁)⁻¹) ?_
  rw [h₁, h₂]
  group

theorem spOmegaRowUniqueQuotInput_linearEven_of_secondClass
    (h2 : SpLinearEvenSecondClassQuotInput) : SpOmegaRowUniqueQuotInput .linearEven :=
  spOmegaRowUniqueQuotInput_of_standardClass
    (spGraphStandardClassQuotInput_linearEven_of_secondClass h2)

theorem spGraphStandardClassQuotInput_unitaryEven_of_inputs (hI : UnitaryEvenInnerTwoPart)
    (h2 : SpUnitaryEvenSecondClassQuotInput) : SpGraphStandardClassQuotInput .unitaryEven := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot hglob htN g hg
  have hZ : Odd (Nat.card (center (spGlobal e))) := hglob.1.2.1
  have hty' : LieModel (spGlobal e ⧸ center (spGlobal e)) .PSU (2 * n) 2 f := hglob.1.2.2
  have hadm : StatedLieAdmissible .PSU (2 * n) 2 f :=
    F4Pilot.statedLieAdmissible_of_lieModel hty'
  obtain ⟨K', _, h, ⟨ψ⟩⟩ := CatLeafProof.nonempty_mulEquiv_primeFormP_of_lieModel hadm hty'
  have : Finite K' := h.finite
  have hq : ¬(2 * n = 3 ∧ 2 ^ f = 2) := by omega
  have hv : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  have hinner : ∀ y : primeFormP h ((1 : GL (Fin (2 * n)) K') :
      Matrix (Fin (2 * n)) (Fin (2 * n)) K'), orderOf y = 2 →
      f * n ^ 2 + 1 + f.factorization 2 <
        (Nat.card (centralizer ({y} : Set (primeFormP h ((1 : GL (Fin (2 * n)) K') :
          Matrix (Fin (2 * n)) (Fin (2 * n)) K'))))).factorization 2 := by
    intro y hy
    set φ := OutcomeLocal.primeFormOneEquiv h (2 * n)
    have h1 := hI f K' h n (by omega) (φ y) (by rw [MulEquiv.orderOf_eq, hy])
    rw [card_centralizer_map_mulEquiv] at h1
    have h3 : f * (n ^ 2 + 2) = f * n ^ 2 + 2 * f := by ring
    omega
  have hy0 := exists_orderOf_eq_two_of_mulEquiv_quot (by omega) hKc hf e ht hKt hZ ψ
  have hJ : ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)),
      ∃ (C₀ : GL (Fin (2 * n)) K') (hC₀ : IsPrimeFormGram C₀),
        (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') = blockSwapJ (2 * n) n ∧
        ∃ θ : primeFormP h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') ≃*
            primeFormP h ((1 : GL (Fin (2 * n)) K') : Matrix (Fin (2 * n)) (Fin (2 * n)) K'),
          MulAut.congr ψ (centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩) =
            MulAut.congr θ (primeFormFieldHom h hC₀ (UnitaryPilot.barRingEquiv h)) := by
    intro g hg
    have hw2 : orderOf (g⁻¹ * t * g) = 2 := by
      rw [show g⁻¹ * t * g = MulAut.conj g⁻¹ t by simp, MulEquiv.orderOf_eq, ht]
    have hαw : MulAut.congr ψ (centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩) *
        MulAut.congr ψ (centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩) = 1 := by
      rw [← map_mul, centerQuotAction_mul_self hw2 hg, map_one]
    have hlew : (Nat.card (fixedSubgroup (MulAut.congr ψ
        (centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩)))).factorization 2 ≤
          f * n ^ 2 + 1 + f.factorization 2 := by
      rw [LinearPilot.card_fixedSubgroup_congr]
      exact (factorization_card_fixedSubgroup_quot_le hZ (MulEquiv.refl _) hw2 hg).trans
        (factorization_card_fixedSubgroup_conj_le hset (by omega) hKc e ht hKt hg)
    obtain ⟨C₀, hC₀, hc, θ, he⟩ :=
      exists_fieldBar_normal_form_of_factorization_le h (by omega) hq hinner hy0 hαw hlew
    rcases hc with h1 | ⟨r, hr, hJ⟩
    · exfalso
      have hC1 : C₀ = 1 := Units.ext h1
      subst hC1
      refine h2 G L hset n f K hn hKc hf e t ht hKt hroot hglob g hg K' h ψ θ ?_
      rw [he, LinearPilot.mulAut_congr_eq_mul]
    · obtain rfl : r = n := by omega
      exact ⟨C₀, hC₀, hJ, θ, he⟩
  obtain ⟨hg1, he1⟩ := centerQuotAction_one_conj htN
  obtain ⟨C₁, hC₁, hJ₁, θ₁, h₁⟩ := hJ 1 hg1
  rw [he1] at h₁
  obtain ⟨C₂, hC₂, hJ₂, θ₂, h₂⟩ := hJ g hg
  obtain rfl : C₂ = C₁ := Units.ext (hJ₂.trans hJ₁.symm)
  refine exists_mulAut_mul_eq_of_congr ψ (γ := θ₁.symm.trans θ₂) ?_
  rw [h₁, h₂]
  exact symm_trans_mul_congr θ₁ θ₂ _

theorem spOmegaRowUniqueQuotInput_unitaryEven_of_inputs (hI : UnitaryEvenInnerTwoPart)
    (h2 : SpUnitaryEvenSecondClassQuotInput) : SpOmegaRowUniqueQuotInput .unitaryEven :=
  spOmegaRowUniqueQuotInput_of_standardClass
    (spGraphStandardClassQuotInput_unitaryEven_of_inputs hI h2)

end Even

section Rows

theorem false_of_spLinearOddRow_of_cover (hc : SpKindCoverInput .linearOdd) :
    SpLinearOddRowInput := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot
  have hglob := spOmegaRowGlobalQuot_of_coverType hset (by omega) hKc hf e ht hKt
    (Or.inr (Or.inr (Or.inl rfl))) (hc G L hset n f K hn hKc hf e t ht hKt hroot)
  exact false_of_spLinearRow_of_globalQuot hset e ht hKt (Or.inr rfl) hglob
    (spOmegaRowUniqueQuotInput_linearOdd G L hset n f K hn hKc hf e t ht hKt hroot hglob)

theorem false_of_spUnitaryOddRow_of_cover (hc : SpKindCoverInput .unitaryOdd) :
    SpUnitaryOddRowInput := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot
  have hglob := spOmegaRowGlobalQuot_of_coverType hset (by omega) hKc hf e ht hKt
    (Or.inr (Or.inr (Or.inr rfl))) (hc G L hset n f K hn hKc hf e t ht hKt hroot)
  exact false_of_spUnitaryRow_of_globalQuot hset hKc hf e ht hKt (Or.inr rfl) hglob
    (spOmegaRowUniqueQuotInput_unitaryOdd G L hset n f K hn hKc hf e t ht hKt hroot hglob)

theorem false_of_spLinearEvenRow_of_cover (hc : SpKindCoverInput .linearEven)
    (h2 : SpLinearEvenSecondClassQuotInput) : SpLinearEvenRowInput := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot
  have hglob := spOmegaRowGlobalQuot_of_coverType hset (by omega) hKc hf e ht hKt
    (Or.inl rfl) (hc G L hset n f K hn hKc hf e t ht hKt hroot)
  exact false_of_spLinearRow_of_globalQuot hset e ht hKt (Or.inl rfl) hglob
    (spOmegaRowUniqueQuotInput_linearEven_of_secondClass h2 G L hset n f K hn hKc hf e t ht hKt
      hroot hglob)

theorem false_of_spUnitaryEvenRow_of_cover (hc : SpKindCoverInput .unitaryEven)
    (hI : UnitaryEvenInnerTwoPart) (h2 : SpUnitaryEvenSecondClassQuotInput) :
    SpUnitaryEvenRowInput := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot
  have hglob := spOmegaRowGlobalQuot_of_coverType hset (by omega) hKc hf e ht hKt
    (Or.inr (Or.inl rfl)) (hc G L hset n f K hn hKc hf e t ht hKt hroot)
  exact false_of_spUnitaryRow_of_globalQuot hset hKc hf e ht hKt (Or.inl rfl) hglob
    (spOmegaRowUniqueQuotInput_unitaryEven_of_inputs hI h2 G L hset n f K hn hKc hf e t ht hKt
      hroot hglob)

end Rows

end CFSG.SeitzReduction.SymplecticPilot
