module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQuotRows

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)

section Classes

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_conj_centerQuotAction_linearOdd (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobalQuot e t f .linearOdd) (htN : t ∈ normalizer (spGlobal e : Set G))
    {g : G} (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)) :
    ∃ γ : MulAut (spGlobal e ⧸ center (spGlobal e)),
      γ * centerQuotAction (spGlobal e) ⟨t, htN⟩ =
        centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩ * γ := by
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
      (card_fixedSubgroup_dvd_of_mem hset hn hKc e ht hKt htN)
  have hdw : Nat.card (fixedSubgroup (MulAut.congr ε θw)) ∣
      2 * (Nat.card (StatedSp n K) * f) := by
    rw [LinearPilot.card_fixedSubgroup_congr]
    exact (card_fixedSubgroup_quot_dvd hZ (MulEquiv.refl _) hw2 hg).trans
      (card_fixedSubgroup_conj_dvd hset hn hKc e ht hKt hg)
  obtain ⟨H₁, C₁, hc₁, he₁⟩ := exists_graph_normal_form_of_card_dvd (K := K) hn
    (by omega) hF hKc (Or.inr rfl) hαt hdt
  obtain ⟨H₂, C₂, hc₂, he₂⟩ := exists_graph_normal_form_of_card_dvd (K := K) hn
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

theorem exists_conj_centerQuotAction_unitaryOdd (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobalQuot e t f .unitaryOdd) (htN : t ∈ normalizer (spGlobal e : Set G))
    {g : G} (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)) :
    ∃ γ : MulAut (spGlobal e ⧸ center (spGlobal e)),
      γ * centerQuotAction (spGlobal e) ⟨t, htN⟩ =
        centerQuotAction (spGlobal e) ⟨g⁻¹ * t * g, hg⟩ * γ := by
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
      (factorization_card_fixedSubgroup_le_of_mem hset hn hKc e ht hKt htN)
  have hlew : (Nat.card (fixedSubgroup (MulAut.congr ψ θw))).factorization 2 ≤
      f * n ^ 2 + 1 + f.factorization 2 := by
    rw [LinearPilot.card_fixedSubgroup_congr]
    exact (factorization_card_fixedSubgroup_quot_le hZ (MulEquiv.refl _) hw2 hg).trans
      (factorization_card_fixedSubgroup_conj_le hset hn hKc e ht hKt hg)
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

theorem mem_normalizer_of_conj_linearOdd (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobalQuot e t f .linearOdd) (g : G)
    (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)) :
    g ∈ normalizer (spGlobal e : Set G) := by
  have htN := mem_normalizer_spGlobal e (LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt)
  obtain ⟨γ, hγ⟩ := exists_conj_centerQuotAction_linearOdd hset hn hKc hf e ht hKt hglob htN hg
  exact mem_normalizer_of_conj_centerQuotAction hset hn hKc hf e ht hKt hglob.1.1.1
    hglob.1.2.1 htN hg γ hγ

theorem mem_normalizer_of_conj_unitaryOdd (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hglob : SpOmegaRowGlobalQuot e t f .unitaryOdd) (g : G)
    (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)) :
    g ∈ normalizer (spGlobal e : Set G) := by
  have htN := mem_normalizer_spGlobal e (LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt)
  obtain ⟨γ, hγ⟩ := exists_conj_centerQuotAction_unitaryOdd hset hn hKc hf e ht hKt hglob htN hg
  exact mem_normalizer_of_conj_centerQuotAction hset hn hKc hf e ht hKt hglob.1.1.1
    hglob.1.2.1 htN hg γ hγ

end Classes

section Rows


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem false_of_coverType_linearOdd (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hcov : SpGlobalCoverType e f .linearOdd) : False := by
  have hglob := spOmegaRowGlobalQuot_of_coverType hset hn hKc hf e ht hKt
    (Or.inr (Or.inr (Or.inl rfl))) hcov
  exact false_of_spLinearRow_of_globalQuot hset e ht hKt (Or.inr rfl) hglob
    (mem_normalizer_of_conj_linearOdd hset hn hKc hf e ht hKt hglob)

theorem false_of_coverType_unitaryOdd (hset : SeitzSetting G L) {n f : ℕ} (hn : 3 ≤ n)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hcov : SpGlobalCoverType e f .unitaryOdd) : False := by
  have hglob := spOmegaRowGlobalQuot_of_coverType hset hn hKc hf e ht hKt
    (Or.inr (Or.inr (Or.inr rfl))) hcov
  exact false_of_spUnitaryRow_of_globalQuot hset hKc hf e ht hKt (Or.inr rfl) hglob
    (mem_normalizer_of_conj_unitaryOdd hset hn hKc hf e ht hKt hglob)

end Rows

end CFSG.SeitzReduction.SymplecticPilot
