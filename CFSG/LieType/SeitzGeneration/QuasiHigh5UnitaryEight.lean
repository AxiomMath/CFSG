module

public import CFSG.LieType.SeitzGeneration.QuasiHigh5Rest
import CFSG.LieType.SeitzGeneration.QuasiHigh5FieldAutThree
import CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.Holds

public section

namespace CFSG.LieType.SeitzGeneration.QuasiHigh5

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel

theorem seitzHyperGamma_eq_top_unitary_field_three
    {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K) {ℓ f : ℕ}
    {Kf : Type} [Field Kf] (h : UnitaryFieldData ℓ f Kf) (hne : ¬(3 = 3 ∧ ℓ ^ f = 2))
    (hℓ : 3 ≠ ℓ) (θ : K ⧸ Subgroup.center K ≃* primeFormP h (idGram Kf 3))
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 2)
    (hout : ¬ E.map (QuasiHigh2.modelAut θ) ≤ primeFormD h (idGram Kf 3)) :
    seitzHyperGamma 3 E = ⊤ := by
  classical
  obtain ⟨a, haE, haD⟩ : ∃ a ∈ E.map (QuasiHigh2.modelAut θ), a ∉ primeFormD h (idGram Kf 3) := by
    by_contra hcon
    push Not at hcon
    exact hout fun a ha => hcon a ha
  obtain ⟨α, hαE, rfl⟩ := Subgroup.mem_map.1 haE
  have hα3 : α ^ 3 = 1 := hE.2 α hαE
  have hα1 : α ≠ 1 := by
    rintro rfl
    exact haD (by rw [map_one]; exact one_mem _)
  have hfield : ∀ k : ℕ, IsFieldAutThree (α ^ k) := fun k =>
    isFieldAutThree_pow_of_not_mem_primeFormD h hne hℓ θ hα3 haD k
  have hT : IsThreeType K := IsThreeType.of_isFieldAutThree (by simpa using hfield 1) hα1
  haveI : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let αE : ↥E := ⟨α, hαE⟩
  have hαEord : orderOf αE = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hα3 hα1
  have hHcard : Nat.card ↥E = 3 * Nat.card (Subgroup.zpowers αE) := by
    rw [Nat.card_zpowers, hαEord, hcard]
    norm_num
  have hHfield : ∀ g ∈ Subgroup.zpowers αE, IsFieldAutThree (E.subtype g) := by
    intro g hg
    rw [mem_zpowers_iff_mem_range_orderOf] at hg
    obtain ⟨k, -, hkg⟩ := Finset.mem_image.mp hg
    rw [← hkg]
    have hpow : E.subtype (αE ^ k) = α ^ k := by rw [map_pow]; rfl
    rw [hpow]
    exact hfield k
  have hB : IsElemAbelian 3 (⊤ : Subgroup ↥E) := isElemAbelian_top_subgroup hE
  have hgen := CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.input23_16Three_holds
    K hK hT ↥E E.subtype hB ⟨Subgroup.zpowers αE, hHcard, hHfield⟩
  have hrk : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥E) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hB (by rw [Subgroup.card_top]; exact hcard)
  have hplane : planeClosure E = ⊤ := by
    rw [eq_top_iff]
    refine hgen.trans (iSup₂_le fun F hF => ?_)
    intro k hk
    have hF1 : 1 ≤ CFSG.Open.pRank 3 F := by omega
    obtain ⟨e₀, he₀F, he₀1⟩ : ∃ e₀ ∈ F, e₀ ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hFbot : F = ⊥ := (Subgroup.eq_bot_iff_forall F).2 hcon
      have h0 : CFSG.Open.pRank 3 F ≤ 0 :=
        CFSG.SectionRank.pRank_le (by norm_num) fun F' hF' _ => by
          rw [hFbot] at hF'
          rw [pow_zero]
          exact (Subgroup.card_le_one_iff_eq_bot F').2 (le_bot_iff.1 hF')
      omega
    refine mem_planeClosure_of_fixed (e := E.subtype e₀) ?_ ?_ (hk e₀ he₀F)
    · exact e₀.2
    · intro h1
      apply he₀1
      exact Subtype.ext (by simpa using h1)
  exact (planeGen_iff_seitzHyperGamma Nat.prime_three hcard).mp hplane

theorem seitzHyperGamma_eq_top_unitary_eight
    {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K) {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group)
    (h8 : q.card = 8) {E : Subgroup (MulAut K)} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) :
    seitzHyperGamma 3 E = ⊤ := by
  classical
  obtain ⟨hℓ, hf, hn3, hne, Kf, _, hU, ⟨θ'⟩⟩ :=
    CFSG.RankThree.PartOne.exists_primeFormP_of_statedClassicalModel_PSU
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e)
  have hperf : commutator K = ⊤ := hq.1
  haveI := hU.finite
  haveI : Fact q.p.Prime := ⟨hℓ⟩
  haveI : CharP Kf q.p := hU.charP
  have h8' : q.p ^ q.exponent = 8 := by
    rw [← TauCeti.PrimePower.card_def]
    exact h8
  have hpq1 : 3 ∣ q.p ^ q.exponent + 1 := by rw [h8']; norm_num
  have hq2 : q.p ^ q.exponent ≠ 2 := by rw [h8']; norm_num
  have hq4 : Even (2 + 1) → 4 ≤ q.p ^ q.exponent := by
    intro _
    rw [h8']
    norm_num
  have hℓ3 : 3 ≠ q.p := by
    intro h3
    have hdvd : 3 ∣ q.p ^ q.exponent := by
      rw [← h3]
      exact dvd_pow_self 3 q.exponent_pos.ne'
    rw [h8'] at hdvd
    norm_num at hdvd
  by_cases hD : E.map (QuasiHigh2.modelAut θ') ≤ primeFormD hU (idGram Kf (2 + 1))
  · exact seitzHyperGamma_eq_top_unitary_diag hperf hU hn3 hq2 Nat.prime_three (by norm_num)
      hpq1 hq4 θ' hE hcard hD
  · exact seitzHyperGamma_eq_top_unitary_field_three hq hU hne hℓ3 θ' hE hcard hD

end CFSG.LieType.SeitzGeneration.QuasiHigh5
