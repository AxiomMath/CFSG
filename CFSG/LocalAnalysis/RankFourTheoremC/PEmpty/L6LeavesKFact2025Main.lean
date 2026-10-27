module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2025Form
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2401ThreeLie

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup
open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)

@[expose] def IsG2OddIndex : TauCeti.LieTypeIndex → Prop
  | .G2 q => q.p ≠ 2
  | _ => False

@[expose] def KFact2025G2 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L S : Subgroup A) (z : A) (p : ℕ),
    catalogIs ↥L (onLie IsG2OddIndex) → p.Prime → p ≠ 2 → orderOf z = p → z ∈ L →
    CFSG.Open.pRank p L ≤ 1 → S ≤ L → IsPGroup 2 S → S ≠ ⊥ → z ∈ normalizer (S : Set A) →
    ⁅S, zpowers z⁆ = S → KxSection z (normalizer (S : Set A) ⊓ L) 3

namespace KF2025

theorem five_le_of_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : 5 ≤ p := by
  by_contra h
  have h4 : p ≤ 4 := by omega
  interval_cases p
  · exact Nat.not_prime_zero hp
  · exact Nat.not_prime_one hp
  · exact hp2 rfl
  · exact hp3 rfl
  · exact absurd hp (by norm_num)

theorem two_ne_zero_of_card {K : Type} [Field K] [Finite K] {p f : ℕ} (hpp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) : (2 : K) ≠ 0 := by
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hK)
  intro h
  have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h')

theorem two_le_pRank_three_twistedA3' {G : Type} [Group G] [Finite G] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq2 : q.p ≠ 2)
    (e : G ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  by_cases hq3 : q.p = 3
  · have hc : TauCeti.ValidLieTypeIndex.characteristic
        ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩ = q.p :=
      TauCeti.LieTypeIndex.characteristic_twistedA 3 q
    rcases (CFSG.Models.lieModel_twistedA 3 q hv e).2 with hC | ⟨h0, -⟩
    · obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank (by rw [hc]; exact hq2) hC
      rw [hc, hq3] at hr
      rcases hr with ⟨h1, -⟩ | ⟨-, ⟨hn3, -⟩ | h4⟩ | ⟨h1, -⟩ | h4 <;>
        first | omega | exact absurd h1 (by decide)
    · omega
  · exact Lie2401.two_le_pRank_three_of_twistedA3 hv e hq3

end KF2025

open KF2025

theorem kFact2025_of_g2 (hG2 : KFact2025G2) : KFact2025 := by
  intro A _ _ L S z p hcat hp hp2 hzp hzL hrank hSL hS2 hS1 hzS hcomm
  have hrank' : ∀ r : ℕ, r = p → 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup ↥L) → False := by
    rintro r rfl h
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup L] at hrank
    omega
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic _ _ => exact (hi : False).elim
  | alternating _ _ => exact (hi : False).elim
  | sporadic _ => exact (hi : False).elim
  | lie v =>
    obtain ⟨dd, hv⟩ := v
    have hd : IsRankTwoOddIndex dd := hi
    rcases Lie2401.rankTwoOdd_cases dd hd with ⟨q, rfl, hq2⟩ | ⟨q, rfl, hq2⟩ | ⟨q, rfl, hq2⟩ |
        ⟨q, rfl, hq2⟩
    ·
      have hp3 : p ≠ 3 := fun h => hrank' 3 h.symm (Lie2401.two_le_pRank_three_of_A3 hv e)
      have hp5 := five_le_of_prime hp hp2 hp3
      rcases (CFSG.Models.lieModel_A 3 q hv e).2 with hC | ⟨h0, -⟩
      · obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := id hC
        exact kxSection_sl (two_ne_zero_of_card q.prime_p hq2 hK) e' hp hp5 hzp hzL hSL hS2 hS1
          hzS hcomm
      · omega
    ·
      have hp3 : p ≠ 3 := fun h => hrank' 3 h.symm (two_le_pRank_three_twistedA3' hv hq2 e)
      have hp5 := five_le_of_prime hp hp2 hp3
      have hc : TauCeti.ValidLieTypeIndex.characteristic
          ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩ = q.p :=
        TauCeti.LieTypeIndex.characteristic_twistedA 3 q
      rcases (CFSG.Models.lieModel_twistedA 3 q hv e).2 with hC | ⟨h0, -⟩
      · obtain ⟨⟨hpp, hf, -⟩, K, _, _, hK, ⟨e'⟩⟩ := id hC
        exact kxSection_su hpp (by rw [hc]; exact hq2) (by omega) hK e' hp hp5 hzp hzL hSL hS2
          hS1 hzS hcomm
      · omega
    ·
      have hp3 : p ≠ 3 := fun h => hrank' 3 h.symm (Lie2401.two_le_pRank_three_of_B2 hv e)
      have hp5 := five_le_of_prime hp hp2 hp3
      rcases CFSG.Models.lieModel_B 2 q hv e with hL | hL
      · rcases hL.2 with hC | ⟨h0, -⟩
        · obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := id hC
          exact kxSection_sp (two_ne_zero_of_card q.prime_p hq2 hK) e' hp hp5 hzp hzL hSL hS2 hS1
            hzS hcomm
        · omega
      · exact absurd hL.1.2.2.1 (by norm_num)
    ·
      exact hG2 A L S z p ⟨.lie ⟨.G2 q, hv⟩, hq2, ⟨e⟩⟩ hp hp2 hzp hzL hrank hSL hS2 hS1 hzS hcomm

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
