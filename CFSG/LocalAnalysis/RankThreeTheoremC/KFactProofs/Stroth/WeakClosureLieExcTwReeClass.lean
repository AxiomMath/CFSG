module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwReeData
public import CFSG.RankThree.PartOne.K128.ReeShape
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwReeEngine

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC
  CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.K1214 CFSG.RankThree.LargeReeOrder
open scoped commutatorElement Matrix

section Gen

variable {a : ℕ} {K : Type} [Field K] [Finite K]
  [CharP K ReeTag.F4.prime] {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2]

theorem ree_sylow_of_torus (D : ReeFrameData K L a) (w : WeylGroup ReeTag.F4.tag) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {e : ℕ}
    (hle : (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ≤ 2 * e)
    (Φ : (rootsOfUnity (p ^ e) L) × (rootsOfUnity (p ^ e) L) →* ModGL ReeTag.F4.tag L)
    (hΦ : Function.Injective Φ) (hΦT : Φ.range ≤ torusGroup ReeTag.F4.tag L)
    (hΦF : Φ.range ≤ twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w))
    (hdet : (1 - (2 ^ a : ℤ) • (reeB * weylMat w⁻¹)).det ≠ 0)
    {u₁ u₂ : WeylGroup ReeTag.F4.tag} (h₁ : w * ReeTag.F4.weylPerm u₁ = u₁ * w)
    (h₂ : w * ReeTag.F4.weylPerm u₂ = u₂ * w)
    (hu : ∀ x : Fin ReeTag.F4.tag.rank → ℤ, ⁅u₁, u₂⁆⁻¹ • x = -x) :
    ∃ P : Sylow p (ReeTag.F4.reeGamma K a),
      NormalizerMovesLines p (P : Subgroup (ReeTag.F4.reeGamma K a)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hpL : (p : L) ≠ 0 := fun h0 =>
    hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      ((CharP.cast_eq_zero_iff L 2 p).1 h0)).symm
  have hcard : Nat.card Φ.range = p ^ (2 * e) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hΦ).toEquiv, Nat.card_prod,
      card_rootsOfUnity_pow hpL, ← pow_add, two_mul]
  exact exists_sylow_moves_lines_ree D w hdet hp2 Φ.range hΦT hΦF hcard hle h₁ h₂ hu

end Gen

section Classes

variable {a : ℕ} {K : Type} [Field K] [Finite K]
  [CharP K ReeTag.F4.prime]

theorem ree_sylow_phi1 (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ (2 * a + 1) - 1) :
    ∃ P : Sylow p (ReeTag.F4.reeGamma K a),
      NormalizerMovesLines p (P : Subgroup (ReeTag.F4.reeGamma K a)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hodd : Odd (p ^ (2 ^ (2 * a + 1) - 1).factorization p) :=
    (hp.odd_of_ne_two (by omega)).pow
  have hmM : ((p ^ (2 ^ (2 * a + 1) - 1).factorization p : ℕ) : ℤ) ∣ 2 ^ (2 * a + 1) - 1 := by
    have := int_dvd_sub_one' hq1 (Nat.ordProj_dvd (2 ^ (2 * a + 1) - 1) p)
    exact_mod_cast this
  obtain ⟨Φ, hΦ, hΦT, hΦF⟩ := torus_hom_m_phi1 (L := AlgebraicClosure K) D.isFrob hodd hmM
  obtain ⟨u₁, u₂, h₁, h₂, hu, hdet⟩ := reeOne_data a
  exact ree_sylow_of_torus D wPhi1 hp (by omega)
    (le_two_mul_of_pow_dvd_sq hp (by omega)
      (pow_factorization_card_reeGamma_dvd_phi1 hK hp (by omega) hpq)) Φ hΦ hΦT hΦF hdet
    h₁ h₂ hu

theorem ree_sylow_phi2 (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ (2 * a + 1) + 1) :
    ∃ P : Sylow p (ReeTag.F4.reeGamma K a),
      NormalizerMovesLines p (P : Subgroup (ReeTag.F4.reeGamma K a)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hodd : Odd (p ^ (2 ^ (2 * a + 1) + 1).factorization p) :=
    (hp.odd_of_ne_two (by omega)).pow
  have hmM : ((p ^ (2 ^ (2 * a + 1) + 1).factorization p : ℕ) : ℤ) ∣ 2 ^ (2 * a + 1) + 1 := by
    have := Int.natCast_dvd_natCast.2 (Nat.ordProj_dvd (2 ^ (2 * a + 1) + 1) p)
    exact_mod_cast this
  obtain ⟨Φ, hΦ, hΦT, hΦF⟩ := torus_hom_m_phi2 (L := AlgebraicClosure K) D.isFrob hodd hmM
  obtain ⟨u₁, u₂, h₁, h₂, hu, hdet⟩ := reeTwo_data a
  exact ree_sylow_of_torus D wPhi2 hp (by omega)
    (le_two_mul_of_pow_dvd_sq hp (by omega)
      (pow_factorization_card_reeGamma_dvd_phi2 hK hp (by omega) hpq)) Φ hΦ hΦT hΦF hdet
    h₁ h₂ hu

theorem ree_sylow_phi4 (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ (2 ^ (2 * a + 1)) ^ 2 + 1) :
    ∃ P : Sylow p (ReeTag.F4.reeGamma K a),
      NormalizerMovesLines p (P : Subgroup (ReeTag.F4.reeGamma K a)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have hle : 2 ^ (a + 1) ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  set e := ((2 ^ (2 * a + 1)) ^ 2 + 1).factorization p with he
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two (by omega)).pow
  have hpe : p ^ e ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := Nat.ordProj_dvd _ p
  have hLE : (Nat.card (ReeTag.F4.reeGamma K a)).factorization p ≤ 2 * e :=
    le_two_mul_of_pow_dvd_sq hp (by omega)
      (pow_factorization_card_reeGamma_dvd_four hK hp (by omega) hpq)
  rcases dvd_phi4_cases hp (by omega) hpq with ⟨hp1, hnd⟩ | ⟨hp1, hnd⟩
  · have hdiv : p ^ e ∣ 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1 := by
      have h1 : p ^ e ∣ (2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1) *
          (2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1) := by rw [phi4_factor a]; exact hpe
      exact (Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)).dvd_of_dvd_mul_right
        h1
    have hmM : ((p ^ e : ℕ) : ℤ) ∣ 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1 := by
      have := Int.natCast_dvd_natCast.2 hdiv
      exact_mod_cast this
    obtain ⟨Φ, hΦ, hΦT, hΦF⟩ := torus_hom_m_phi4p (L := AlgebraicClosure K) D.isFrob hodd hmM
    obtain ⟨u₁, u₂, h₁, h₂, hu, hdet⟩ := reeFourP_data a
    exact ree_sylow_of_torus D wPhi4p hp (by omega) hLE Φ hΦ hΦT hΦF hdet h₁ h₂ hu
  · have hdiv : p ^ e ∣ 2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1 := by
      have h1 : p ^ e ∣ (2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1) *
          (2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1) := by rw [phi4_factor a]; exact hpe
      exact (Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)).dvd_of_dvd_mul_left
        h1
    have hmM : ((p ^ e : ℕ) : ℤ) ∣ 2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1 := by
      exact int_dvd_sub_add_one' hle hdiv |> fun h => by exact_mod_cast h
    obtain ⟨Φ, hΦ, hΦT, hΦF⟩ := torus_hom_m_phi4m (L := AlgebraicClosure K) D.isFrob hodd hmM
    obtain ⟨u₁, u₂, h₁, h₂, hu, hdet⟩ := reeFourM_data a
    exact ree_sylow_of_torus D wPhi4m hp (by omega) hLE Φ hΦ hΦT hΦF hdet h₁ h₂ hu

end Classes

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
