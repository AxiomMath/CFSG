module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Families
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115EvenL2
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinear
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalSymplecticAut
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatG2
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatRee
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatTits
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatTriality

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.QuasithinUnique CFSG.QuasithinUnique.K1 CFSG.Assembly.LowTwoRank

theorem isInnerAut_of_odd_outer {X : Type} [Group X]
    (hodd : Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)))
    (β : X ≃* X) (hβ : ∀ x, β (β x) = x) : IsInnerAut β := by
  let q : MulAut X →* CFSG.ComponentClassification.OuterAutomorphisms.Outer X :=
    QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X)
  have hsq : (q β) ^ 2 = 1 := by
    rw [← map_pow]
    have : β ^ 2 = 1 := by
      ext x
      simp [pow_two, MulAut.mul_apply, hβ]
    rw [this, map_one]
  have h1 : orderOf (q β) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have h2 : orderOf (q β) ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) :=
    orderOf_dvd_natCard _
  have h3 : orderOf (q β) = 1 := by
    have h4 : orderOf (q β) ∣ Nat.gcd 2 (Nat.card
        (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) := Nat.dvd_gcd h1 h2
    have h5 : Nat.gcd 2 (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) = 1 :=
      (Nat.coprime_two_left.mpr hodd)
    rw [h5] at h4
    exact Nat.dvd_one.mp h4
  have h6 : q β = 1 := orderOf_eq_one_iff.mp h3
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff β).mp h6
  refine ⟨g⁻¹, fun x => ?_⟩
  have := congrArg (fun φ : MulAut X => φ x) hg
  simpa [MulAut.conj_apply] using this.symm

theorem isInnerAut_of_suzukiModel {X : Type} [Group X] {p f : ℕ}
    (h : CFSG.Blueprint.SuzukiModel X p f) (β : X ≃* X) (hβ : ∀ x, β (β x) = x) :
    IsInnerAut β :=
  isInnerAut_of_odd_outer
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} X p f h).1.2.2 β hβ

theorem sylowCentralizingAutInner_of_stated_psl {X : Type} [Group X] {n f : ℕ} (hn : 3 ≤ n)
    (hf : 1 ≤ f) (h : StatedClassicalModel X .PSL n 2 f) : SylowCentralizingAutInner X := by
  obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf
      hcard
  exact SylowCentralizingAutInner.of_mulEquiv (e.trans (statedProjEquivProjectiveSL n K))
    (sylowCentralizingAutInner_projectiveSL hn)

theorem sylowCentralizingAutInner_of_stated_psp {X : Type} [Group X] {f : ℕ} (hf : 2 ≤ f)
    (h : StatedClassicalModel X .PSp 2 2 f) : SylowCentralizingAutInner X := by
  obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hcard
  exact SylowCentralizingAutInner.of_mulEquiv e sylowCentralizingAutInner_statedProj

section G2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem sylowCentralizingAutInner_of_g2_model
    {X : Type} [Group X] {f : ℕ} (hf : 2 ≤ f)
    (hmodel : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 2 f) : SylowCentralizingAutInner X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact SylowCentralizingAutInner.of_mulEquiv
    (e.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)) (sylowCentralizingAutInner_g2 hK4)

end G2

section Triality

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem sylowCentralizingAutInner_of_triality_model
    {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    (hmodel : CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f) :
    SylowCentralizingAutInner X := by
  obtain ⟨-, K, _, _, hK, σ₀, hσ₀, ⟨e⟩⟩ := hmodel
  have hK3 : Nat.card K = (2 ^ f) ^ 3 := hK
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) (show Nat.card K = 2 ^ (f * 3) by rw [hK3, ← pow_mul])
  obtain ⟨σ, rfl⟩ : ∃ σ : K ≃+* K, σ.toRingHom = σ₀ :=
    ⟨RingEquiv.ofBijective σ₀ ⟨σ₀.injective, Finite.surjective_of_injective σ₀.injective⟩, rfl⟩
  have hσ : ∀ c, σ c = c ^ (2 ^ f) := hσ₀
  obtain ⟨-, -, -, -, -, -, -, ⟨E⟩⟩ := even_triality_exact_automorphism_normal_form hf K hK3 σ hσ
  exact SylowCentralizingAutInner.of_mulEquiv (e.trans E)
    (sylowCentralizingAutInner_triality σ hf hK3 hσ)

end Triality

section Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.LargeReeCatalog

theorem sylowCentralizingAutInner_of_ree_model
    {X : Type} [Group X] {f : ℕ}
    (hmodel : CFSG.Blueprint.ReeTitsModel X .twistedF4 2 f) : SylowCentralizingAutInner X := by
  obtain ⟨-, -, -, -, ⟨a₀, ha₀, hfa₀⟩, hiso⟩ := large_Ree_model_Schreier X 2 f hmodel
  obtain ⟨-, a, hfa, hmodel'⟩ := hmodel
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel'
  have : Fintype K := Fintype.ofFinite K
  have : CharP K F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hiso a K hfa hK ⟨e⟩
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := hfa ▸ hK
  have ha : 1 ≤ a := by omega
  exact SylowCentralizingAutInner.of_mulEquiv E (sylowCentralizingAutInner_ree ha hK')

end Ree

@[expose] def EvenUnitaryAutInner : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (f : ℕ), 2 ≤ f → StatedClassicalModel K .PSU 3 2 f →
    SylowCentralizingAutInner K

theorem evenLieAutInner_of_inputs
    (hT : TitsSylowCentralizingAutInner)
    (hU : EvenUnitaryAutInner) : EvenLieAutInner := by
  intro K _ _ hK β hβ hex
  obtain ⟨P, hPfix⟩ := hex
  have hPs : IsSylowTwoOf (P : Subgroup K) ⊤ :=
    isSylowTwoOf_top_iff.mpr ⟨P.isPGroup', P.not_dvd_index⟩
  have key : SylowCentralizingAutInner K → IsInnerAut β := fun hS => hS _ hPs β hPfix
  rcases hK with ((⟨f, h | h | h | h | h | h | h | h⟩ | h) | ⟨n, hn, h⟩)
  · exact key (sylowCentralizingAutInner_of_stated_psl_two (by have := h.1; omega) h.2)
  · exact key (sylowCentralizingAutInner_of_stated_psl (by norm_num) h.1 h.2)
  · exact key (hU K f h.1 h.2)
  · exact key (sylowCentralizingAutInner_of_stated_psp h.1 h.2)
  · exact key (sylowCentralizingAutInner_of_g2_model h.1 h.2)
  · exact key (sylowCentralizingAutInner_of_triality_model h.1 h.2)
  · exact key (sylowCentralizingAutInner_of_ree_model h.2.2)
  · exact isInnerAut_of_suzukiModel h.2.2 β hβ
  · exact key (hT K h)
  · rcases hn with rfl | rfl
    · exact key (sylowCentralizingAutInner_of_stated_psl (by norm_num) le_rfl h)
    · exact key (sylowCentralizingAutInner_of_stated_psl (by norm_num) le_rfl h)

end CFSG.QuasithinUnique.Ch1
