module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubAbstract
public import CFSG.RankThree.PartOne.KF.ClsExcD4
public import CFSG.RankThree.PartOne.KLC.TriTorus

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc

open CFSG.Blueprint CFSG.Open
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub Subgroup
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace Tri

theorem dvd_add_one_or_dvd_sq_sub {p q : ℕ} (hp : p.Prime) (h : p ∣ 1 + q ^ 3) :
    p ∣ q + 1 ∨ p ∣ q ^ 2 - q + 1 := by
  have hle : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have e : 1 + q ^ 3 = (q + 1) * (q ^ 2 - q + 1) := by
    zify [hle]
    ring
  rw [e] at h
  exact hp.dvd_mul.1 h

theorem not_dvd_two_pow {p m : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : ¬ p ∣ 2 ^ m := fun h =>
  absurd (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)) (by omega)

end Tri


namespace Tri

section Parabolic

variable {K : Type} [Field K]

theorem graphFixedRootBorel_subgroupOf_le_normalizer (t : TwistTag) (σ : K →+* K) :
    (graphFixedRootBorel t K σ).subgroupOf (graphFixedRootGroup t K σ) ≤
      normalizer (((graphFixedPosUnipotent t K σ).subgroupOf (graphFixedRootGroup t K σ) :
        Subgroup ↥(graphFixedRootGroup t K σ)) : Set ↥(graphFixedRootGroup t K σ)) := by
  rw [← Subgroup.subgroupOf_normalizer_eq (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ)]
  exact fun x hx => graphFixedRootBorel_le_normalizer_graphFixedPosUnipotent hx

theorem exists_le_graphFixedParabolic_singleton (σ : K ≃+* K)
    {A : Subgroup (ModGL TwistTag.D4.tag K)}
    (hBA : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤ A)
    (hAC : A ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hA : A ≠ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    ∃ b : Fin TwistTag.D4.foldedTag.rank,
      A ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {b} := by
  have hAJ := (fixed_Borel_overgroup_classification TwistTag.D4 K σ A hBA hAC).1
  obtain ⟨a, ha⟩ : ∃ a : Fin TwistTag.D4.foldedTag.rank,
      canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) ∉ A := by
    by_contra h
    have hJ : {a | canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection a) ∈ A} = Set.univ :=
      Set.eq_univ_of_forall fun a => by
        by_contra ha
        exact h ⟨a, ha⟩
    apply hA
    rw [hAJ, hJ]
    exact (fixed_standard_parabolic_cells TwistTag.D4 K σ).2.2.2.2.2
  have hex : ∀ i : Fin TwistTag.D4.foldedTag.rank, ∃ j : Fin TwistTag.D4.foldedTag.rank,
      ∀ k, k ≠ i → k = j := by decide
  obtain ⟨b, hb⟩ := hex a
  refine ⟨b, ?_⟩
  rw [hAJ]
  exact ((fixed_standard_parabolic_cells TwistTag.D4 K σ).2.2.2.1 _ {b}).2 fun k hk =>
    hb k fun h => ha (h ▸ hk)

theorem exists_le_parabolic_of_normalizer_le (σ : K ≃+* K)
    {K₀ : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hN : normalizer (((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
        Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≤ K₀)
    (hne : K₀ ≠ ⊤) :
    ∃ b : Fin TwistTag.D4.foldedTag.rank,
      K₀.map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype ≤
        graphFixedParabolic TwistTag.D4 K σ.toRingHom {b} := by
  have hBK₀ : (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≤ K₀ :=
    (graphFixedRootBorel_subgroupOf_le_normalizer TwistTag.D4 σ.toRingHom).trans hN
  have hBA : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤
      K₀.map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype := fun x hx =>
    ⟨⟨x, graphFixedRootBorel_le _ _ _ hx⟩, hBK₀ hx, rfl⟩
  have hAC : K₀.map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := Subgroup.map_subtype_le _
  have hA : K₀.map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype ≠
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    intro h
    apply hne
    rw [eq_top_iff]
    intro x _
    have hx : (x : ModGL TwistTag.D4.tag K) ∈
        K₀.map (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype := by
      rw [h]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [← Subtype.ext hyx]
  exact exists_le_graphFixedParabolic_singleton σ hBA hAC hA

end Parabolic

section Rank

variable {K : Type} [Field K]

open CFSG.RankThree.PartOne.KLC CFSG.RankThree.PartOne.KFU

theorem two_le_pRank_of_dvd_card_parabolic [Finite K] [CharP K 2] (σ : K ≃+* K) {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (b : Fin TwistTag.D4.foldedTag.rank) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hdvd : p ∣ Nat.card (graphFixedParabolic TwistTag.D4 K σ.toRingHom {b})) :
    2 ≤ CFSG.pRank p ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσs : Function.Surjective σ.toRingHom := σ.surjective
  have hcard : Nat.card (graphFixedParabolic TwistTag.D4 K σ.toRingHom {b}) =
      Nat.card (graphFixedRootTorus TwistTag.D4 K σ.toRingHom) *
        Nat.card (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) *
          (1 + (2 ^ n) ^ (TwistTag.D4.orbit b).card) := by
    rw [CFSG.Quasithin.F134.LieD4.card_graphFixedParabolic_singleton hσs b,
      CFSG.Quasithin.F134.LieD4.card_graphFixedInversionUnipotent_D4 σ hn hK hσ b,
      CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootBorel hσs]
  have hU2 : IsPGroup 2 (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) :=
    (isPGroup_posUnipotent 2 TwistTag.D4.tag).to_le inf_le_left
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hU2
  have hnU : ¬ p ∣ Nat.card (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) := by
    rw [hm]
    exact not_dvd_two_pow hp h5
  rw [hcard] at hdvd
  rcases hp.dvd_mul.1 hdvd with hHU | hk
  ·
    have hH : p ∣ Nat.card (graphFixedRootTorus TwistTag.D4 K σ.toRingHom) :=
      (hp.dvd_mul.1 hHU).resolve_right hnU
    by_cases h1 : p ∣ 2 ^ n - 1
    · exact two_le_pRank_triality_phi1 (σ := σ.toRingHom) ⟨hp, h5, hn, hK, fun c => hσ c, h1⟩
    · by_cases h3 : p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1
      · refine two_le_pRank_triality_phi36 (ℓ := 2) hn hK σ hσ (ε := 1) (Or.inl rfl) hp ?_
        have e : ((2 ^ n : ℕ) : ℤ) ^ 2 + 1 * ((2 ^ n : ℕ) : ℤ) + 1 =
            (((2 ^ n) ^ 2 + 2 ^ n + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [e]
        exact_mod_cast h3
      · exact absurd hH (not_dvd_card_graphFixedRootTorus_D4 σ hn hK hσ hp h1 h3)
  ·
    have hk13 : (TwistTag.D4.orbit b).card = 1 ∨ (TwistTag.D4.orbit b).card = 3 := by
      have : ∀ c : Fin TwistTag.D4.foldedTag.rank,
          (TwistTag.D4.orbit c).card = 1 ∨ (TwistTag.D4.orbit c).card = 3 := by decide
      exact this b
    have hphi2 : p ∣ 2 ^ n + 1 →
        2 ≤ CFSG.pRank p ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      fun h => two_le_pRank_triality_phi2 (ℓ := 2) hn hK σ hσ hp (by omega) (by exact_mod_cast h)
    rcases hk13 with h | h
    · rw [h, pow_one, add_comm] at hk
      exact hphi2 hk
    · rw [h] at hk
      rcases dvd_add_one_or_dvd_sq_sub hp hk with h2 | h6
      · exact hphi2 h2
      · have hle : 2 ^ n ≤ (2 ^ n) ^ 2 := Nat.le_self_pow (by norm_num) _
        refine two_le_pRank_triality_phi36 (ℓ := 2) hn hK σ hσ (ε := -1) (Or.inr rfl) hp ?_
        have e : ((2 ^ n : ℕ) : ℤ) ^ 2 + (-1) * ((2 ^ n : ℕ) : ℤ) + 1 =
            (((2 ^ n) ^ 2 - 2 ^ n + 1 : ℕ) : ℤ) := by push_cast [Nat.cast_sub hle]; ring
        rw [e]
        exact_mod_cast h6

theorem leviSubAt_graphFixedRootGroup [Finite K] (σ : K ≃+* K) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    LeviSubAt ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega : 1 ≤ 3 * n) (by rw [hK, ← pow_mul, mul_comm])
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element TwistTag.D4.tag
  obtain ⟨⟨T₀, hT₀⟩, -⟩ := exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀
  refine leviSubAt_of_standard_sylow T₀ fun K₀ p hN => ?_
  intro _ hp h5 hrank _ hne hsyl
  exfalso
  rw [hT₀] at hN
  obtain ⟨b, hb⟩ := exists_le_parabolic_of_normalizer_le σ hN hne
  have hdvd : p ∣ Nat.card (graphFixedParabolic TwistTag.D4 K σ.toRingHom {b}) := by
    refine (dvd_card_of_sylow_hyp hp hsyl).trans ?_
    rw [← Subgroup.card_map_of_injective
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective]
    exact Subgroup.card_dvd_of_le hb
  have h2 := two_le_pRank_of_dvd_card_parabolic σ hn hK hσ b hp h5 hdvd
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
  omega

end Rank

end Tri


theorem leviSubAt_trialityD4 {S : Type} [Group S] [Finite S] {f : ℕ}
    (hm : ChevalleyExceptionalModel S .trialityD4 2 f) : LeviSubAt S := by
  obtain ⟨⟨-, hf, -⟩, hmod⟩ := hm
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf hmod
  exact LeviSubAt.of_mulEquiv e (Tri.leviSubAt_graphFixedRootGroup σ hf hK hσ)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc
