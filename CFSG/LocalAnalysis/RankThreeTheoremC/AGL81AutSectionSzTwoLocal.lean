module

public import CFSG.LieType.Ree.SuzukiUnipotentStructure
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionLinear
import CFSG.LinearAlgebra.TwoGroupNormalizerLargePrime
import CFSG.RankThree.PartTwo.Sec16.Item166StepsProofSz

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSection

open CFSG.Blueprint CFSG.LieType.Ree CFSG.RankThree.PartTwo.Sec16.Steps166 Subgroup

theorem sz32_frobenius {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * 2 + 1)) :
    ∃ t : suzukiGroup 2 K, t ^ 31 = 1 ∧ t ∈ normalizer (suzukiZ0 2 K : Set (suzukiGroup 2 K)) ∧
      ∃ x ∈ suzukiZ0 2 K, t * x ≠ x * t := by
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have hcardU : Nat.card Kˣ = 31 := by rw [Nat.card_units, hK]; norm_num
  obtain ⟨l, hl⟩ := exists_prime_orderOf_dvd_card' 31 (by rw [hcardU])
  have hD31 : suzukiDElt 2 K l ^ 31 = 1 := by
    change suzukiDHom166 (a := 2) l ^ 31 = 1
    rw [← map_pow, ← hl, pow_orderOf_eq_one, map_one]
  refine ⟨(suzukiDElt 2 K l)⁻¹, by rw [inv_pow, hD31, inv_one], ?_,
    suzukiSElt 2 K 0 1, (mem_suzukiZ0_iff hK).mpr ⟨1, rfl⟩, ?_⟩
  · refine mem_normalizer_iff.mpr fun x => ?_
    constructor
    · intro hx
      obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).mp hx
      rw [inv_inv, suzukiDElt_conj hK, mul_zero]
      exact (mem_suzukiZ0_iff hK).mpr ⟨_, rfl⟩
    · intro hx
      rw [inv_inv] at hx
      obtain ⟨v, hv⟩ := (mem_suzukiZ0_iff hK).mp hx
      have hx' : x = suzukiDElt 2 K l * suzukiSElt 2 K 0 v * (suzukiDElt 2 K l)⁻¹ := by
        rw [hv]
        group
      rw [hx', suzukiDElt_conj' hK, mul_zero]
      exact (mem_suzukiZ0_iff hK).mpr ⟨_, rfl⟩
  · intro hcomm
    have hfix : (suzukiDElt 2 K l)⁻¹ * suzukiSElt 2 K 0 1 * (suzukiDElt 2 K l)⁻¹⁻¹ =
        suzukiSElt 2 K 0 1 := by rw [hcomm, mul_inv_cancel_right]
    rw [inv_inv, suzukiDElt_conj hK, mul_zero, mul_one, suzukiSElt_inj] at hfix
    have h9 : l ^ 9 = 1 := Units.ext (by simpa using hfix.2)
    have := orderOf_dvd_of_pow_eq_one h9
    rw [hl] at this
    norm_num at this

open CFSG.LinearAlgebra.TwoGroupNormalizer in
theorem autSectionSz :
    ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 5 → ∀ d : TauCeti.ValidLieTypeIndex,
      d.1 = .suzuki 2 → ∀ (V : Type) [Group V] [Finite V], IsPGroup q V →
      Open.pRank q (⊤ : Subgroup V) ≤ 3 →
      ∀ (A : Subgroup (MulAut V)) (φ : ↥A →* (TauCeti.CFSGIndex.lie d).Group),
        ¬ Function.Surjective φ := by
  intro q hq hq2 _ d hd V _ _ hV hrank A φ hφ
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨W, _, _, _, hW, ρ, hρ⟩ := hasSmallLinearModel hq2 hV hrank
  obtain ⟨d, hv⟩ := d
  change d = _ at hd
  subst hd
  have hiso : CFSG.RankThree.PartOne.Census3.IsoLie
      (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group (.suzuki 2) := ⟨hv, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨-, a, -, F, _, _, hfa, hF, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie 2 hiso
  have ha2 : a = 2 := by omega
  subst ha2
  have hF' : Nat.card F = 2 ^ (2 * 2 + 1) := by rw [hF, hfa]
  obtain ⟨t, ht31, htN, x, hx, hxt⟩ := sz32_frobenius hF'
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp this)
  have hker : ∀ y : A, (ρ.comp A.subtype) y = 1 → ∀ m : ℕ, y ^ 2 ^ m = 1 → y = 1 := by
    intro y hy m hm
    obtain ⟨k, hk⟩ := hρ y hy
    have hk' : y ^ q ^ k = 1 := Subtype.ext (by simpa using hk)
    have hcop : Nat.Coprime (q ^ k) (2 ^ m) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hm))
  set Q : Subgroup (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group :=
    (suzukiZ0 2 F).map e.symm.toMonoidHom with hQdef
  have hQ : IsPGroup 2 Q := by
    rintro ⟨_, z, hz, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change e.symm z ^ 2 ^ 1 = 1
    rw [pow_one, ← map_pow, suzukiZ0_sq hF' hz, map_one]
  have hQab : ∀ b ∈ Q, ∀ c ∈ Q, b * c = c * b := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    change e.symm z * e.symm w = e.symm w * e.symm z
    rw [← map_mul, ← map_mul, suzukiZ0_comm hF' hz hw]
  have hh : e.symm t ∈ normalizer (Q : Set _) := by
    rw [hQdef, ← map_equiv_normalizer_eq]
    exact ⟨t, htN, rfl⟩
  have hne : e.symm t * e.symm x ≠ e.symm x * e.symm t := by
    rw [← map_mul, ← map_mul]
    exact fun h => hxt (e.symm.injective h)
  exact false_of_surjective (K := ZMod q) (W := W) h2 hW (ρ.comp A.subtype) hker φ hφ Q hQ hQab
    hh (r := 31) (by norm_num) (by norm_num) (by rw [← map_pow, ht31, map_one]) ⟨x, hx, rfl⟩ hne

end CFSG.LocalAnalysis.RankThreeTheoremC.AutSection
