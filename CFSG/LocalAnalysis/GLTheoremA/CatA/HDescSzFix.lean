module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescRankOne
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQBasic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.LocalAnalysis.UniqueFourCatalog.ClosureTop
public import CFSG.LocalAnalysis.GL83PartI.I713.Chain
public import CFSG.RankThree.PartOne.K159.AutSzModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (fixSubgroupCongrEquiv)
open CFSG.RankThree.PartOne.K159.SzAbs (SzSylow)
open scoped commutatorElement

theorem exists_noncomm_of_commutator_eq_top {G : Type*} [Group G] [Nontrivial G]
    (h : commutator G = ⊤) : ∃ x y : G, x * y ≠ y * x := by
  by_contra hcomm
  push Not at hcomm
  have hbot : commutator G = ⊥ := by
    rw [commutator, eq_bot_iff, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm x y
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have hg' : g ∈ commutator G := h ▸ Subgroup.mem_top g
  rw [hbot, Subgroup.mem_bot] at hg'
  exact hg hg'

section Fix


variable {S : Type} [Group S] [Finite S] {f : ℕ}

theorem suzuki_outer_cyclic (hS : SuzukiModel S 2 f) : IsCyclic (Outer S) :=
  (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} S 2 f hS).1.1

theorem suzuki_rank_one (hS : SuzukiModel S 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ E : Subgroup S, IsElemAbelian p E → Nat.card E ≤ p := by
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := hS
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
  have e' : S ≃* GLASzGroup a F :=
    e.trans (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F))
  have hSyl := CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzuki_model_oddSylow_cyclic
    a ha hF' e'
  intro E hE
  have hcyc : IsCyclic E :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.odd_commutative_subgroup_cyclic E
      (CFSG.LocalAnalysis.UniqueFourCatalog.odd_card_of_isElemAbelian hp hp2 hE) hE.1 hSyl
  exact GL83.I713.card_le_of_isElemAbelian_of_isCyclic hp hE hcyc

noncomputable def fixSubgroupConjEquiv' {Y : Type*} [Group Y] (β α : MulAut Y) :
    ↥(fixSubgroup α) ≃* ↥(fixSubgroup (β * α * β⁻¹)) := by
  have hc : MulAut.congr (β : Y ≃* Y) α = β * α * β⁻¹ := by
    ext x
    rfl
  exact (fixSubgroupCongrEquiv (β : Y ≃* Y) α).trans (MulEquiv.subgroupCongr (by rw [hc]))

theorem suzuki_outer_fix (hS : SuzukiModel S 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {α : MulAut S}
    (hα : orderOf α = p) (hout : α ∉ inner S) :
    (f = p ∧ Nat.card ↥(fixSubgroup α) = 20) ∨
      (IsSimpleGroup ↥(fixSubgroup α) ∧ ∃ x y : ↥(fixSubgroup α), x * y ≠ y * x) := by
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := hS
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
  have hαord : orderOf (MulAut.congr e α) = p := by
    rw [MulEquiv.orderOf_eq (MulAut.congr e) α, hα]
  have hαinn : MulAut.congr e α ∉ inner (suzukiGroup a F) :=
    fun h => hout ((FQ.congr_mem_range_conj e α).1 h)
  obtain ⟨σ, h, b, k, hkF, hkfin, hσp, hbp, hkcard, hconj, ⟨eH⟩⟩ :=
    CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha F hF' p hp hp2 (MulAut.congr e α)
      hαord hαinn
  have e₁ : ↥(fixSubgroup α) ≃* suzukiGroup b k :=
    (fixSubgroupCongrEquiv e α).trans ((fixSubgroupConjEquiv' (MulAut.conj h) _).trans
      ((MulEquiv.subgroupCongr (by rw [hconj]; rfl)).trans eH))
  rcases Nat.eq_zero_or_pos b with hb0 | hb1
  · subst hb0
    left
    refine ⟨by omega, ?_⟩
    rw [Nat.card_congr e₁.toEquiv, CFSG.LieType.Ree.suzuki_order hkcard]
    norm_num
  · right
    obtain ⟨hfin, hnt, hsimple⟩ := CFSG.LieType.Ree.suzuki_simple hb1 hkcard
    haveI := hsimple
    haveI := hnt
    refine ⟨e₁.isSimpleGroup, ?_⟩
    obtain ⟨x, y, hxy⟩ := exists_noncomm_of_commutator_eq_top
      (CFSG.LieType.Ree.suzuki_perfect hb1 hkcard).1
    refine ⟨e₁.symm x, e₁.symm y, fun hc => hxy ?_⟩
    have := congrArg e₁ hc
    simpa using this

theorem isQuasisimple_of_simple_nonab' {L : Type*} [Group L] [IsSimpleGroup L]
    (hL : ∃ a b : L, a * b ≠ b * a) : CFSG.Open.IsQuasisimple L := by
  have hZ : Subgroup.center L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hL
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator L) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hL
      have : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.mp this)
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup

theorem glaPLayer_ne_bot_of_simple {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    {X : Subgroup Y} (hs : IsSimpleGroup ↥X) (hnc : ∃ x y : ↥X, x * y ≠ y * x)
    (hdvd : p ∣ Nat.card X) : GLAPLayer p X ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hs
  have hq : CFSG.Open.IsQuasisimple ↥X := isQuasisimple_of_simple_nonab' hnc
  have hcore : GLAPPrimeCore p ↥X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p ↥X) with h | h
    · exact h
    · exfalso
      have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥X)) :=
        CFSG.pPrimeCore_coprime_card (p := p) (G := ↥X)
      rw [h, Subgroup.card_top] at hcop
      exact hp.one_lt.ne' (hcop.eq_one_of_dvd hdvd)
  have hcomp := glaPComponent_self_p hq hcore
  intro hbot
  have hle : X ≤ GLAPLayer p X := le_sSup hcomp
  rw [hbot] at hle
  obtain ⟨x, y, hxy⟩ := hnc
  apply hxy
  have hx : (x : Y) ∈ (⊥ : Subgroup Y) := hle x.2
  rw [Subgroup.mem_bot] at hx
  have hx1 : x = 1 := Subtype.ext hx
  rw [hx1, one_mul, mul_one]

theorem szSylow_of_model_five (hS : SuzukiModel S 2 5) : SzSylow S := by
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := hS
  have ha2 : a = 2 := by omega
  subst ha2
  have hF' : Nat.card F = 2 ^ (2 * 2 + 1) := by rw [hF, hfa]
  exact CFSG.RankThree.PartOne.K159.SzAbs.SzSylow.of_mulEquiv e
    (CFSG.RankThree.PartOne.K159.SzAbs.szSylow_model hF')

end Fix

section Normalizer

variable {S : Type} [Group S] [Finite S]

theorem not_five_normalizes_two (h : SzSylow S) {T : Subgroup S} (hT2 : IsPGroup 2 T) (hT : T ≠ ⊥)
    {s : S} (hs : orderOf s = 5) (hn : T.map (MulAut.conj s).toMonoidHom = T) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite S := Finite.of_equiv _ (Equiv.refl S)
  obtain ⟨V, hTV⟩ := hT2.exists_le_sylow
  have hTsV : T ≤ ((s • V : Sylow 2 S) : Subgroup S) := by
    intro t ht
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have h1 : t ∈ T.map (MulAut.conj s).toMonoidHom := by rw [hn]; exact ht
    obtain ⟨t', ht', rfl⟩ := h1
    have h2 : (MulAut.conj s)⁻¹ • ((MulAut.conj s).toMonoidHom t') = t' := by
      simp [MulAut.smul_def]
      group
    rw [h2]
    exact hTV ht'
  by_cases hVV : V = s • V
  · have hsN : s ∈ Subgroup.normalizer (V : Set S) :=
      Sylow.smul_eq_iff_mem_normalizer.1 hVV.symm
    have hcardN : Nat.card (Subgroup.normalizer (V : Set S)) = 31744 := by
      have h1 := Sylow.card_eq_index_normalizer V
      rw [h.card_sylow] at h1
      have h2 := Subgroup.card_mul_index (Subgroup.normalizer (V : Set S))
      rw [← h1, h.card] at h2
      omega
    have h5 : 5 ∣ Nat.card (Subgroup.normalizer (V : Set S)) := by
      have h6 : orderOf (⟨s, hsN⟩ : Subgroup.normalizer (V : Set S)) = 5 := by
        rw [← Subgroup.orderOf_coe]
        exact hs
      rw [← h6]
      exact orderOf_dvd_natCard _
    rw [hcardN] at h5
    omega
  · apply hT
    have h7 : T ≤ (V : Subgroup S) ⊓ ((s • V : Sylow 2 S) : Subgroup S) := le_inf hTV hTsV
    rw [h.ti V (s • V) hVV] at h7
    exact le_bot_iff.1 h7

end Normalizer

section RankOne


variable {S : Type} [Group S] [Finite S] {f : ℕ}

theorem map_conj_eq_of_mem_normalizer {T : Subgroup S} {s : S}
    (hs : s ∈ Subgroup.normalizer (T : Set S)) : T.map (MulAut.conj s).toMonoidHom = T := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.1 hs t).1 ht
  · intro hx
    refine ⟨s⁻¹ * x * s, ?_, by simp [MulAut.conj_apply]; group⟩
    refine (Subgroup.mem_normalizer_iff.1 hs (s⁻¹ * x * s)).2 ?_
    simpa [mul_assoc] using hx

theorem suzuki_twoLocalRankLE1 (hS : SuzukiModel S 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    TwoLocalRankLE1 p S :=
  fun E _ hE _ _ _ => suzuki_rank_one hS hp hp2 E hE

theorem suzuki_outerFixLayer (hS : SuzukiModel S 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    OuterFixLayer p S := by
  intro α hα hout s hs hsα hT
  obtain ⟨T, hT2, hT1, hsT⟩ := hT
  have hsF : s ∈ fixSubgroup α := hsα
  have hdvd : p ∣ Nat.card ↥(fixSubgroup α) := by
    have h6 : orderOf (⟨s, hsF⟩ : ↥(fixSubgroup α)) = p := by
      rw [← Subgroup.orderOf_coe]
      exact hs
    rw [← h6]
    exact orderOf_dvd_natCard _
  rcases suzuki_outer_fix hS hp hp2 hα hout with ⟨hfp, hcard20⟩ | ⟨hsimple, hnc⟩
  · exfalso
    have h20 : p ∣ 2 ^ 2 * 5 := by
      have : p ∣ 20 := hcard20 ▸ hdvd
      simpa using this
    have hp5 : p = 5 := by
      rcases (Nat.Prime.dvd_mul hp).1 h20 with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)) hp2
      · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
    have hf5 : f = 5 := hfp.trans hp5
    rw [hf5] at hS
    have hSyl := szSylow_of_model_five hS
    rw [hp5] at hs
    exact not_five_normalizes_two hSyl hT2 hT1 hs (map_conj_eq_of_mem_normalizer hsT)
  · exact glaPLayer_ne_bot_of_simple hp hsimple hnc hdvd

end RankOne

end CFSG.LocalAnalysis.GLTheoremA.HDesc
