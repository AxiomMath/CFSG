module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenProj
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenZsig
public import CFSG.RankThree.PartOne.KF.ParabolicNormalizesFixed
public import CFSG.Timmesfeld.Orders.ExceptionalTwistedOrder
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

namespace OLTwisted

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits
open CFSG.Timmesfeld.ExceptionalOrders

section Zsigmondy

theorem exists_zsig_prime_twelve_eighteen {f₀ p e : ℕ} (hf₀ : 1 ≤ f₀) (he : e = 12 ∨ e = 18)
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∃ r : ℕ, r.Prime ∧ ∀ k : ℕ,
      (r ∣ (2 ^ f₀) ^ k - 1 ↔ e ∣ k) ∧ (r ∣ (2 ^ (p * f₀)) ^ k - 1 ↔ e ∣ k) := by
  have hpe : ¬ p ∣ e := by
    intro h
    have hle := Nat.le_of_dvd (by omega) h
    rcases he with rfl | rfl
    · interval_cases p <;> first | omega | (norm_num at hp)
    · interval_cases p <;> first | omega | (norm_num at hp)
  obtain ⟨r, m, hrm, hm, hcorr⟩ := exists_ppd_data hf₀ (by omega : 2 ≤ e) (fun h => by omega)
  exact ⟨r, hrm.1, fun k => ppd_dvd_iff hrm hm hcorr hp hpe k⟩

theorem not_dvd_of_dvd_pow_sub_one {r q k : ℕ} (hq : 1 ≤ q) (hk : k ≠ 0) (hr : r.Prime)
    (h : r ∣ q ^ k - 1) : ¬ r ∣ q := by
  intro hrq
  have h1 : r ∣ q ^ k := dvd_pow hrq hk
  have h2 : 1 ≤ q ^ k := Nat.one_le_pow _ _ hq
  have h3 : r ∣ q ^ k - (q ^ k - 1) := Nat.dvd_sub h1 h
  have h4 : q ^ k - (q ^ k - 1) = 1 := by omega
  rw [h4] at h3
  exact hr.one_lt.ne' (Nat.dvd_one.1 h3)

theorem dvd_sq_sub_one_of_dvd_one_add {r x : ℕ} (hx : 1 ≤ x) (h : r ∣ 1 + x) :
    r ∣ x ^ 2 - 1 := by
  have e : x ^ 2 - 1 = (x - 1) * (1 + x) := by
    have h2 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ hx
    zify [hx, h2]
    ring
  rw [e]
  exact Dvd.dvd.mul_left h _

end Zsigmondy

section Transport

theorem not_dvd_card_normalizer_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite B]
    (e : A ≃* B) {r : ℕ}
    (h : ∀ U : Subgroup B, IsPGroup 2 U → U ≠ ⊥ →
      ¬ r ∣ Nat.card (Subgroup.normalizer (U : Set B)))
    (R : Subgroup A) (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    ¬ r ∣ Nat.card (Subgroup.normalizer (R : Set A)) := fun hrN =>
  h (R.map e.toMonoidHom) (hR2.map e.toMonoidHom)
    (fun hb => hR1 ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 hb))
    (hrN.trans (card_normalizer_dvd_of_mulEquiv e R))

end Transport

section Twisted


theorem not_dvd_card_graphFixedRootBorel {t : TwistTag} {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) {q r : ℕ} (hr : r.Prime)
    (hq : ∀ a, Nat.card (orbitField t K σ.toRingHom a) = q ^ (t.orbit a).card)
    (hrq : ¬ r ∣ q) (hrT : ∀ a, ¬ r ∣ q ^ (t.orbit a).card - 1) :
    ¬ r ∣ Nat.card (graphFixedRootBorel t K σ.toRingHom) := by
  have hσ : Function.Surjective σ.toRingHom := σ.surjective
  rw [card_graphFixedRootBorel hσ, graphFixedRootTorus_eq_compatTorus hσ,
    card_graphFixedPosUnipotent hσ hq]
  intro h
  rcases (Nat.Prime.dvd_mul hr).1 h with h1 | h1
  · have h2 : Nat.card (compatTorus (t := t) σ.toRingHom) ∣
        Nat.card (compatSubgroup (t := t) σ.toRingHom) :=
      Dvd.intro _ (card_compatTorus_mul (t := t) σ.toRingHom)
    rw [card_compatSubgroup] at h2
    have h3 := h1.trans h2
    obtain ⟨a, -, ha⟩ := (Prime.dvd_finset_prod_iff hr.prime _).1 h3
    rw [hq a] at ha
    exact hrT a ha
  · exact hrq (hr.dvd_of_dvd_pow h1)

theorem exists_card_normalizer_dvd_card_maximal_parabolic (t : TwistTag) {K : Type} [Field K]
    [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hH : Holds (graphFixedRootGroup t K σ.toRingHom) 2)
    {U : Subgroup (graphFixedRootGroup t K σ.toRingHom)} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) :
    ∃ a : Fin t.foldedTag.rank,
      Nat.card (Subgroup.normalizer (U : Set (graphFixedRootGroup t K σ.toRingHom))) ∣
        Nat.card (graphFixedParabolic t K σ.toRingHom {b | b ≠ a}) := by
  obtain ⟨J, φ, hJ, hφ, hmem⟩ :=
    CFSG.RankThree.PartOne.KFU.exists_hom_into_graphFixedParabolic_of_normalizes t σ hH hU hU2
      (le_refl _)
  obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem J).1 hJ
  refine ⟨a, ?_⟩
  have hfin : Finite (ModGL t.tag K) := finite_modGL
  have hsub : J ⊆ {b | b ≠ a} := fun b hb h => ha (h ▸ hb)
  have hle : graphFixedParabolic t K σ.toRingHom J ≤
      graphFixedParabolic t K σ.toRingHom {b | b ≠ a} :=
    ((fixed_standard_parabolic_cells t K σ).2.2.2.1 J _).2 hsub
  have hle' : φ.range ≤ graphFixedParabolic t K σ.toRingHom {b | b ≠ a} := by
    rintro _ ⟨e, rfl⟩
    exact hle (hmem e)
  have h1 := Subgroup.card_dvd_of_le hle'
  rwa [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv] at h1

end Twisted

end OLTwisted

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
