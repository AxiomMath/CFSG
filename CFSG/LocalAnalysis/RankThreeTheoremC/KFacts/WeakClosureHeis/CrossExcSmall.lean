module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.LieDispatch
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.RankThree.PartOne.Q1327C.BNoCube
import CFSG.LieType.Ree.SmallReeModelSchreier
import CFSG.LieType.SeitzGeneration.ExcReeG2Rank
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic
import CFSG.LieType.BorelTits.Suzuki
import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.LieType.Ree.Duality
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.FamilyTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley

private theorem card_lt_of_no_elemAbelian {G : Type} [Group G] {p k : ℕ} (hp : p.Prime)
    (hno : ∀ E : Subgroup G, CFSG.Open.IsElemAbelian p E → Nat.card E = p ^ k → False)
    (F : Subgroup G) (hF : CFSG.Open.IsElemAbelian p F) : Nat.card F < p ^ k := by
  by_contra h
  push Not at h
  obtain ⟨F', hF'⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card hp hF.isPGroup h
  refine hno (F'.map F.subtype) (hF.mono (Subgroup.map_subtype_le F')) ?_
  rw [Subgroup.card_map_of_injective F.subtype_injective, hF']

private theorem card_le_sq_of_no_cube {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hno : ∀ E : Subgroup G, (∀ x ∈ E, x ^ p = 1) → Nat.card E = p ^ 3 → False)
    (F : Subgroup G) (hF : CFSG.Open.IsElemAbelian p F) : Nat.card F ≤ p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hlt := card_lt_of_no_elemAbelian hp (k := 3) (fun E hE hc => hno E hE.2 hc) F hF
  obtain ⟨j, hj⟩ := hF.isPGroup.exists_card_eq
  rw [hj] at hlt ⊢
  have : j < 3 := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt
  exact Nat.pow_le_pow_right hp.pos (by omega)

private theorem card_le_sq_of_no_plane {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    (hno : ∀ E : Subgroup G, CFSG.Open.IsElemAbelian p E → Nat.card E = p ^ 2 → False)
    (F : Subgroup G) (hF : CFSG.Open.IsElemAbelian p F) : Nat.card F ≤ p ^ 2 :=
  (card_lt_of_no_elemAbelian hp hno F hF).le

section Ree


theorem sdLieCross_G2 : SDLieCrossAt .G2 := by
  intro K _ _ _ _ _ _ _ _ hmodel p hp h5 hpℓ _
  obtain ⟨⟨hℓ, -, -⟩, hm⟩ :=
    hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have hpq : ¬ p ∣ Nat.card F := by
    rw [hF]
    intro hd
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow hd))
  let e' : K ≃* adjointGroup .G2 F := e.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := F))).trans
      QuotientGroup.quotientBot)
  haveI : Finite (adjointGroup .G2 F) := Finite.of_equiv K e'.toEquiv
  refine SylowDichotomyAt.of_mulEquiv hp e' (SylowDichotomyAt.of_card_elemAbelian_le hp ?_)
  intro E hE
  exact card_le_sq_of_no_cube hp (fun E' hE' hc =>
    CFSG.RankThree.PartOne.Q1327C.false_of_pow_three_G2_five F hp h5 hpq hE' hc) E hE

theorem sdLieCross_twistedG2 : SDLieCrossAt .twistedG2 := by
  intro K _ _ _ _ _ ℓ f _ hmodel p hp h5 _ _
  obtain ⟨-, hrt⟩ := hmodel.reeTitsModel (by simp [reeTitsTags])
  obtain ⟨-, -, hℓ, ⟨a', ha', hfa'⟩, hiso⟩ := CFSG.LieType.Ree.small_Ree_model_Schreier K ℓ f hrt
  subst hℓ
  obtain ⟨-, a, hfa, X, _, _, hXcard, ⟨e2⟩⟩ := hrt
  have ha : 1 ≤ a := by omega
  haveI : Fintype X := Fintype.ofFinite X
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CharP X CFSG.LieType.Ree.ReeTag.G2.prime :=
    charP_of_card_eq_prime_pow (p := 3) (f := f) (by rw [← Nat.card_eq_fintype_card, hXcard])
  obtain ⟨E⟩ := hiso a X hfa hXcard ⟨e2⟩
  have hX : Nat.card X = 3 ^ (2 * a + 1) := by rw [← hfa]; exact hXcard
  have hp3 : 3 < p := by omega
  refine SylowDichotomyAt.of_card_elemAbelian_le hp fun F hF => card_le_sq_of_no_plane hp ?_ F hF
  intro F' hF' hFc
  have hF₁ : CFSG.Open.IsElemAbelian p (F'.map E.toMonoidHom) := hF'.map E.toMonoidHom
  have hF₂ : CFSG.Open.IsElemAbelian p ((F'.map E.toMonoidHom).map
      (CFSG.LieType.Ree.ReeTag.G2.reeGamma X a).subtype) := hF₁.map _
  refine CFSG.LieType.SeitzGeneration.no_plane_reeGamma_G2 ha hX hp hp3
    (Subgroup.map_subtype_le _) hF₂.isElementaryAbelian ?_
  rw [Subgroup.card_map_of_injective (CFSG.LieType.Ree.ReeTag.G2.reeGamma X a).subtype_injective,
    Subgroup.card_map_of_injective E.injective, hFc]

theorem sdLieCross_twistedF4 : SDLieCrossAt .twistedF4 := by
  intro K _ _ _ _ _ _ _ hadm hmodel p hp h5 _ _
  obtain ⟨-, hrt⟩ := hmodel.reeTitsModel (by simp [reeTitsTags])
  obtain ⟨-, -, -, hℓ, -, -⟩ := hadm
  subst hℓ
  exact SylowDichotomyAt.of_card_elemAbelian_le hp fun F hF =>
    card_le_sq_of_no_cube hp (fun E hE hc =>
      CFSG.RankThree.PartOne.Q1327C.false_of_pow_three_ree_five hrt hp h5 hE hc) F hF

end Ree

section Suzuki

private local instance : DecidableEq (Equiv.Perm (Fin 3)) :=
  Fintype.decidableEqEquivFintype

private theorem certificate43_of_decide :
      ∀ s t : Equiv.Perm (Fin 3),
        (s ≠ 1 ∧ s ^ 2 = 1) → (t ≠ 1 ∧ t ^ 2 = 1) → s ≠ t →
          (s * t) ^ 3 = 1 ∧ s * t ≠ 1 := by
  decide +kernel

theorem sdLieCross_twistedB2 : SDLieCrossAt .twistedB2 := by
  intro K _ _ _ _ _ ℓ f _ hmodel p hp _ hpℓ _
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := certificate43_of_decide
  have hS : SuzukiModel K ℓ f := by
    rcases hmodel with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact hS
  obtain ⟨hℓ, a, ha, F, _, _, hfa, hcard, ⟨e⟩⟩ := hS
  subst hℓ
  have hF : Nat.card F = 2 ^ (2 * a + 1) := by rw [hcard, hfa]
  let e' : K ≃* CFSG.Open.GLASzGroup a F :=
    e.trans (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F))
  have hsyl := CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzuki_model_oddSylow_cyclic
    a ha hF e' p hpℓ
  refine SylowDichotomyAt.of_sylow_comm fun S => ?_
  haveI := hsyl S
  infer_instance

end Suzuki

private theorem factorization_titsOrder_le (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    (17971200 : ℕ).factorization p ≤ 3 := by
  by_contra h
  push Not at h
  have h4 : p ^ 4 ∣ 17971200 := (hp.pow_dvd_iff_le_factorization (by norm_num)).2 h
  have hle : p ^ 4 ≤ 17971200 := Nat.le_of_dvd (by norm_num) h4
  have hp65 : p ≤ 65 := by
    by_contra hc
    push Not at hc
    have : 66 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left hc 4
    omega
  interval_cases p <;> norm_num at h4

section Tits


theorem sdLieCross_Tits : SDLieCrossAt .Tits := by
  intro K _ _ _ _ _ _ f hadm hmodel p hp h5 _ _
  obtain ⟨-, hrt⟩ := hmodel.reeTitsModel (by simp [reeTitsTags])
  obtain ⟨-, -, -, hℓ, -⟩ := hadm
  subst hℓ
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv K 2 f hrt
  have hcard : Nat.card K = 17971200 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Schreier.Tits.card_titsD
  exact SylowDichotomyAt.of_factorization_le (by rw [hcard]; exact factorization_titsOrder_le p hp h5)

end Tits

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
