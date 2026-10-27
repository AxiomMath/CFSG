module

public import CFSG.LocalAnalysis.GLTheoremB.Lemma23Proof
public import CFSG.Assembly.Defs

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped Pointwise commutatorElement

@[expose] def InputFeitThompson : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Odd (Nat.card X) → Group.IsSolvable X

variable {G : Type*} [Group G]

theorem isSolvable_of_odd_card (hFT : InputFeitThompson) {K : Type*} [Group K] [Finite K]
    (h : Odd (Nat.card K)) : Group.IsSolvable K := by
  have : Small.{0} K := inferInstance
  have : Finite (Shrink.{0} K) := Finite.of_equiv K (equivShrink K : K ≃ Shrink.{0} K)
  have hc : Odd (Nat.card (Shrink.{0} K)) := by
    rw [Nat.card_congr (Shrink.mulEquiv (α := K)).toEquiv]
    exact h
  have := hFT (Shrink.{0} K) hc
  exact Group.isSolvable_of_surjective (f := (Shrink.mulEquiv (α := K)).toMonoidHom)
    (Shrink.mulEquiv (α := K)).surjective

theorem two_dvd_card_of_glaPComponent [Finite G] (hFT : InputFeitThompson) {p : ℕ}
    {X L : Subgroup G} (hL : GLAPComponent p X L) : 2 ∣ Nat.card L := by
  set Lbar := (L.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p X)) with hLbar
  have hq : CFSG.Open.IsQuasisimple Lbar := hL.2.2.1.2.2
  by_contra h2
  have hdvd : Nat.card Lbar ∣ Nat.card L :=
    (Subgroup.card_map_dvd _ _).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL.1).toEquiv).dvd
  have hodd : Odd (Nat.card Lbar) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact fun h => h2 (h.trans hdvd)
  have := isSolvable_of_odd_card hFT hodd
  have : IsSimpleGroup (↥Lbar ⧸ Subgroup.center ↥Lbar) := hq.2
  have : Nontrivial ↥Lbar :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥Lbar)).nontrivial
  have := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥Lbar
  exact this.ne hq.1

theorem card_sup_dvd_of_le_normalizer [Finite G] {P O : Subgroup G}
    (h : P ≤ Subgroup.normalizer (O : Set G)) :
    Nat.card ↥(P ⊔ O) ∣ Nat.card O * Nat.card P := by
  have hS := Subgroup.coe_mul_of_left_le_normalizer_right P O h
  have hc : Nat.card ↥(P ⊔ O) =
      Nat.card O * Nat.card (((P : Set G).image (↑) : Set (G ⧸ O))) := by
    rw [← Subgroup.card_mul_eq_card_subgroup_mul_card_quotient O (P : Set G), ← hS]
    rfl
  have himg : ((P : Set G).image (↑) : Set (G ⧸ O)) =
      (MulAction.orbit P ((1 : G) : G ⧸ O) : Set (G ⧸ O)) := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, by simp [Subgroup.smul_def]⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, by simp [Subgroup.smul_def]⟩
  rw [hc, himg]
  refine mul_dvd_mul_left _ ?_
  rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
  exact Subgroup.index_dvd_card _

theorem exists_twoGroup_normalized_of_centralizes [Finite G] (hFT : InputFeitThompson) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {X L A : Subgroup G} (hL : GLAPComponent p X L) (hAX : A ≤ X)
    (hA : IsPGroup p A) (hLA : ⁅L, A⁆ ≤ GLAPPrimeCoreOf p X) :
    ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ A ≤ Subgroup.normalizer (T : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLX : L ≤ X := hL.1
  have h2L := two_dvd_card_of_glaPComponent hFT hL
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥L) := inferInstance
  set Pg : Subgroup G := (P : Subgroup ↥L).map L.subtype with hPg
  set O : Subgroup G := GLAPPrimeCoreOf p X with hO
  have hPgL : Pg ≤ L := Subgroup.map_subtype_le _
  have hPgX : Pg ≤ X := hPgL.trans hLX
  have hPg2 : IsPGroup 2 Pg := P.isPGroup'.map L.subtype
  have hPgcard : 2 ∣ Nat.card Pg := by
    rw [hPg, Subgroup.card_map_of_injective L.subtype_injective]
    exact P.dvd_card_of_dvd_card h2L
  have hOnorm : ∀ g ∈ X, ∀ n ∈ O, g * n * g⁻¹ ∈ O := fun g hg n hn =>
    mem_gLAPPrimeCoreOf_conj hn hg
  have hPO : Pg ≤ Subgroup.normalizer (O : Set G) := fun g hg =>
    Subgroup.mem_normalizer_fintype fun n hn => hOnorm g (hPgX hg) n hn
  have hS : (↑(Pg ⊔ O) : Set G) = (Pg : Set G) * (O : Set G) := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hPO
  set S : Subgroup G := Pg ⊔ O with hSdef
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have hn' : n ∈ ((Pg : Set G) * (O : Set G)) := hS ▸ hn
    obtain ⟨x, hx, o, ho, rfl⟩ := hn'
    have hc : ⁅a, x⁆ ∈ O := by
      refine hLA ?_
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator ha (hPgL hx)
    have hao : a * o * a⁻¹ ∈ O := hOnorm a (hAX ha) o ho
    have : a * (x * o) * a⁻¹ = ⁅a, x⁆ * x * (a * o * a⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact S.mul_mem (S.mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hx))
      (Subgroup.mem_sup_right hao)
  have hScard : ¬ p ∣ Nat.card S := by
    intro hpS
    have h1 := hpS.trans (card_sup_dvd_of_le_normalizer hPO)
    have hOcard : Nat.card O = Nat.card (GLAPPrimeCore p ↥X) :=
      Subgroup.card_map_of_injective X.subtype_injective
    have hOc : ¬ p ∣ Nat.card O := by
      rw [hOcard, ← hp.coprime_iff_not_dvd]
      exact CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore hp _
    obtain ⟨k, hk⟩ := hPg2.exists_card_eq
    have hPc : ¬ p ∣ Nat.card Pg := by
      rw [hk]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    rcases (Nat.Prime.dvd_mul hp).1 h1 with h | h
    · exact hOc h
    · exact hPc h
  obtain ⟨Q, -, hQ2, hQc, hAQ⟩ := exists_sylow_normalized_of_not_dvd (p := p) (q := 2) S A hA hAS
    hScard
  refine ⟨Q, ?_, hQ2, hAQ⟩
  intro h
  have h1 := hQc 1 (by simpa using hPgcard.trans (Subgroup.card_dvd_of_le le_sup_left))
  rw [h, Subgroup.card_bot] at h1
  simp at h1

end CFSG.HardMathSupport.Solomon.LocalBalance
