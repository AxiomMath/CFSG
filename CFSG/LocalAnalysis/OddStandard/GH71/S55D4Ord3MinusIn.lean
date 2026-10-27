module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3FrMv
public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3Tri
public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3Plus
public import CFSG.RankThree.PartOne.KGD.D4QFrame

public section

namespace CFSG.OddStandard.GH71.S55

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.Stage2.Bender.Thm1


variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

local notation "𝒞" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

omit [Finite K] in
theorem d4_frame_normalizesPSub_toral {p f : ℕ} [Fact p.Prime] {L : Type} [Field L] [Algebra K L]
    [IsAlgClosure K L] [CharP L p] {g₀ : ModGL TwistTag.D4.tag L} (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 2)
    (hg₀ : D4MinusFrame p f L g₀) (n : 𝒞)
    (hnT : d4MinusPsi σ L g₀ n ∈ twistedTorusOf (trialityOpposition L)
      (twistHom TwistTag.D4 L (iterateFrobenius L p f)))
    (hn3 : n ^ 3 = 1) (hn1 : n ≠ 1) : NormalizesPSub p (MulAut.conj n) := by
  have hp : p.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨hg₀C, -, hg₀F⟩ := hg₀
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have hinj := d4MinusPsi_injective (σ := σ) g₀
  rw [d4Q_twistedTorus Fr] at hnT
  obtain ⟨a, ha, han⟩ := hnT
  change rootDiagUnit TwistTag.D4.tag a = d4MinusPsi σ L g₀ n at han
  have ha3 : ∀ i, a i ^ 3 = 1 := by
    have h : a ^ 3 = 1 := by
      apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)
      rw [rootDiagUnit_one]
      change rootDiagUnitHom TwistTag.D4.tag L (a ^ 3) = 1
      rw [map_pow]
      change rootDiagUnit TwistTag.D4.tag a ^ 3 = 1
      rw [han, ← map_pow, hn3, map_one]
    exact fun i => congrFun h i
  obtain ⟨h10, h30⟩ := d4Q_eq_of_pow_eq_one hFr (by omega : 3 ∣ p ^ f + 1) ha ha3
  have hshape : a = ![a 0, a 0, a 2, a 0] := by
    funext i
    fin_cases i
    · rfl
    · exact h10
    · rfl
    · exact h30
  have hne : ¬ (a 0 = 1 ∧ a 2 = 1) := by
    rintro ⟨h0, h2⟩
    apply hn1
    apply hinj
    have h1 : (![1, 1, 1, 1] : Fin TwistTag.D4.tag.rank → Lˣ) = 1 := by
      funext i
      fin_cases i <;> rfl
    rw [← han, map_one, hshape, h0, h2, h1]
    exact rootDiagUnit_one
  obtain ⟨u, hu, hu1, hup, huF, huc⟩ := d4_toral3_pElt (L := L) (p := p) hf (ha3 0) (ha3 2) hne
  obtain ⟨y, hy⟩ := (d4MinusPsi_mem_range_iff hp hf hK hσ Fr hFr hg₀C hg₀F u).2 ⟨hu, huF⟩
  have hyp : y ^ p = 1 := hinj (by rw [map_pow, hy, hup, map_one])
  have hfix : MulAut.conj n y = y := by
    apply hinj
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hy, ← han, hshape, huc, mul_inv_cancel_right]
  refine ⟨Subgroup.zpowers y, fun h => hu1 ?_, fun x => ?_, ?_⟩
  · rw [← hy, Subgroup.zpowers_eq_bot.1 h, map_one]
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 x.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hyp, one_zpow]
    rfl
  · rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hfix]

theorem d4_ord3Alt_inner_minus {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 2)
    (g : 𝒞) (hg : MulAut.conj g ^ 3 = 1) : Ord3Alt p (MulAut.conj g) := by
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK3
  have : Fact p.Prime := ⟨hp⟩
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  obtain ⟨g₀, hg₀C, hg₀P, hg₀F⟩ := d4Minus_exists_frame (L := AlgebraicClosure K) p hp2 hf
  have hg₀ : D4MinusFrame p f (AlgebraicClosure K) g₀ := ⟨hg₀C, hg₀P, hg₀F⟩
  obtain ⟨N, hidx, -, hprop⟩ := d4Minus_exists_N hf hq hK hσ hg₀
  have hinj := mulAut_conj_injective_of_center_eq_bot
    (exceptional_fixed_center_trivial TwistTag.D4 K σ)
  have hg3 : g * g * g = 1 := hinj (by rw [map_mul, map_mul, map_one, ← pow_three']; exact hg)
  obtain ⟨y, n, hnN, hconj⟩ := exists_conj_mem_of_index_not_dvd (1 : MulAut 𝒞) (fun _ => rfl)
    N (fun _ h => h) hidx g (by change g * g * g = 1; exact hg3)
  rw [mul_one, mul_one] at hconj
  refine ord3Alt_of_conj (MulAut.conj y) ?_
  rw [hconj]
  have hn3 : n ^ 3 = 1 := hinj (by
    rw [map_pow, ← hconj, conj_pow, hg, mul_one, mul_inv_cancel, map_one])
  obtain ⟨hnM, hnT⟩ := hprop n hnN
  by_cases htor : d4MinusPsi σ (AlgebraicClosure K) g₀ n ∈
      torusGroup TwistTag.D4.tag (AlgebraicClosure K)
  · by_cases hn1 : n = 1
    · subst hn1
      have h := d4_normalizesPSub_toral σ (ℓ := p) (h := 1) (one_mem _) 1
      rw [fieldActor_one, mul_one] at h
      exact Or.inl h
    · exact Or.inl (d4_frame_normalizesPSub_toral σ hf hK hσ hq hg₀ n (hnT htor) hn3 hn1)
  · exact Or.inr (d4_frame_movesAbelianTwo_inner σ hp2 hf hK hσ hg₀ n hnM htor hn3)

end CFSG.OddStandard.GH71.S55
