module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
import CFSG.Adapters.LieModelSmallOrders
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLift

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

theorem card_mul_two_of_psl2 {Z : Type} [Group Z] {p m : ℕ} (hp2 : p ≠ 2)
    (h : Blueprint.LieModel Z .PSL 2 p m) : Nat.card Z * 2 = p ^ m * ((p ^ m) ^ 2 - 1) := by
  obtain ⟨hp, -, h4, F', _, _, hF', ⟨e⟩⟩ := HarrisLit.exists_psl2_of_lieModel h
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F') :=
    AutL2Facts.isOddPrimePower_of hp hp2 (by
      by_contra h0
      push Not at h0
      rw [Nat.lt_one_iff.mp h0, pow_zero] at h4
      omega) hF'
  rw [Nat.card_congr e.toEquiv, GorensteinWalter.psl2_card_formula F' hodd, hF']
  set q := p ^ m
  have hqodd : Odd q := (hp.odd_of_ne_two hp2).pow
  have heven : 2 ∣ q * (q ^ 2 - 1) := by
    obtain ⟨j, hj⟩ := hqodd
    refine Dvd.dvd.mul_left ⟨2 * j ^ 2 + 2 * j, ?_⟩ q
    rw [hj]
    ring_nf
    omega
  exact Nat.div_mul_cancel heven

theorem cube_mono {a b : ℕ} (h : a ≤ b) : a * (a ^ 2 - 1) ≤ b * (b ^ 2 - 1) :=
  Nat.mul_le_mul h (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)

theorem cube_ne {N T : ℕ} (h1 : N * (N ^ 2 - 1) < T) (h2 : T < (N + 1) * ((N + 1) ^ 2 - 1))
    (q : ℕ) : q * (q ^ 2 - 1) ≠ T := by
  intro hq
  rcases Nat.lt_or_ge N q with hlt | hle
  · have := cube_mono (show N + 1 ≤ q by omega)
    omega
  · have := cube_mono hle
    omega

theorem not_psl2_of_card {Z : Type} [Group Z] {p m T : ℕ} (hp2 : p ≠ 2)
    (hT : ∀ q : ℕ, q * (q ^ 2 - 1) ≠ 2 * T) (hZ : Nat.card Z = T) :
    ¬ Blueprint.LieModel Z .PSL 2 p m := fun h => by
  have := card_mul_two_of_psl2 hp2 h
  exact hT (p ^ m) (by rw [← this, hZ, mul_comm])

theorem admissible_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h : Blueprint.LieModel X t n p f) : StatedLieAdmissible t n p f :=
  CFSG.Blueprint.LieModel.admissible h

theorem card_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h : Blueprint.LieModel X t n p f) :
    Nat.card X * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f) :=
  (CatLeafProof.lieOrderFormulasInput X t n p f (admissible_of_lieModel h) h).2.1

theorem card_F4_two {X : Type} [Group X] (h : Blueprint.LieModel X .F4 0 2 1) :
    Nat.card X = 3311126603366400 := by
  have := card_of_lieModel h
  simp only [lieOrderNumerator, lieOrderDivisor, mul_one] at this
  norm_num at this
  exact this

theorem card_tits {X : Type} [Group X] (h : Blueprint.LieModel X .Tits 0 2 1) :
    Nat.card X = 17971200 := by
  have := card_of_lieModel h
  simp only [lieOrderNumerator, lieOrderDivisor, mul_one] at this
  exact this

theorem card_U33 {X : Type} [Group X] (h : Blueprint.LieModel X .PSU 3 3 1) :
    Nat.card X = 6048 :=
  CFSG.Blueprint.LieModel.card_psu_three_three h

theorem cube_ne_orders (q : ℕ) :
    q * (q ^ 2 - 1) ≠ 2 * 3311126603366400 ∧ q * (q ^ 2 - 1) ≠ 2 * 17971200 ∧
      q * (q ^ 2 - 1) ≠ 2 * 6048 ∧ q * (q ^ 2 - 1) ≠ 2 * 1451520 :=
  ⟨cube_ne (N := 187788) (by norm_num) (by norm_num) q,
    cube_ne (N := 330) (by norm_num) (by norm_num) q,
    cube_ne (N := 22) (by norm_num) (by norm_num) q,
    cube_ne (N := 142) (by norm_num) (by norm_num) q⟩

end CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover
