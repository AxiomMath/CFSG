module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6One7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6One2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6One3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerTwE6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.TwistedE6 CFSG.SeitzReduction CFSG.StandardType
  CFSG.LieType.Steinberg.Exceptional CFSG.SectionRank CFSG.SeitzReduction.F4Pilot
  CFSG.LieType.SeitzGeneration
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6One
open CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6One.SplitCentralizer

theorem isElemAbelian_thetaTorusP_sup_R3Levi {f p : ℕ} {k : Type} [Field k] [Finite k]
    [Algebra k (GaloisField 2 (2 * f))] [NeZero p] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (h : UnitaryFieldData 2 f (GaloisField 2 (2 * f))) (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : GaloisField 2 (2 * f)) = ζ)
    {t : kˣ} (ht : orderOf t = p) (hσ : ∀ c, frobQ 2 f c = c ^ 2 ^ f) :
    IsElemAbelian p (thetaTorusP (f := f) t ⊔
      (R3Levi h p hp hp2 ζ hζ hζbar hσ).subgroupOf (C0 f)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hdisj : W0 f k ⊓ DLevi f = ⊥ := by
    rw [inf_comm]
    exact (TwistedE6Pilot.su6Levi_facts hf hk hK hσ).2.2.1
  refine IsElemAbelian.sup_of_commute (isElemAbelian_thetaTorusP hf hk hp ht)
    (IsElemAbelian.subgroupOf (isElemAbelian_R3Levi h p hp hp2 ζ hζ hζbar hσ) (C0 f)) ?_
  intro a ha b hb
  have haW := thetaTorusP_le_thetaTorus hf hk t ha
  have hbD : b ∈ (DLevi f).subgroupOf (C0 f) :=
    (R3Levi_le_su6Levi h p hp hp2 ζ hζ hζbar hσ) hb
  exact commute_thetaTorus_su6Levi hf hk haW hbD

theorem card_thetaTorusP_sup_R3Levi {f p : ℕ} {k : Type} [Field k] [Finite k]
    [Algebra k (GaloisField 2 (2 * f))] [NeZero p] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (h : UnitaryFieldData 2 f (GaloisField 2 (2 * f))) (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : GaloisField 2 (2 * f)) = ζ)
    {t : kˣ} (ht : orderOf t = p) (hσ : ∀ c, frobQ 2 f c = c ^ 2 ^ f) :
    Nat.card ↥(thetaTorusP (f := f) t ⊔
      (R3Levi h p hp hp2 ζ hζ hζbar hσ).subgroupOf (C0 f)) = p ^ 4 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hdisj : W0 f k ⊓ DLevi f = ⊥ := by
    rw [inf_comm]
    exact (TwistedE6Pilot.su6Levi_facts hf hk hK hσ).2.2.1
  have hinf : thetaTorusP (f := f) t ⊓
      (R3Levi h p hp hp2 ζ hζ hζbar hσ).subgroupOf (C0 f) = ⊥ := by
    refine le_bot_iff.mp ?_
    intro x hx
    obtain ⟨hxT, hxR⟩ := Subgroup.mem_inf.mp hx
    have hxW : (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈ W0 f k :=
      thetaTorusP_le_thetaTorus hf hk t hxT
    have hxD : (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈ DLevi f :=
      (R3Levi_le_su6Levi h p hp hp2 ζ hζ hζbar hσ) hxR
    have hmem : (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈ W0 f k ⊓ DLevi f :=
      Subgroup.mem_inf.mpr ⟨hxW, hxD⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hcomm : ∀ a ∈ thetaTorusP (f := f) t,
      ∀ b ∈ (R3Levi h p hp hp2 ζ hζ hζbar hσ).subgroupOf (C0 f), a * b = b * a := by
    intro a ha b hb
    exact commute_thetaTorus_su6Levi hf hk (thetaTorusP_le_thetaTorus hf hk t ha)
      ((R3Levi_le_su6Levi h p hp hp2 ζ hζ hζbar hσ) hb)
  rw [CFSG.CGT.Timmesfeld75.card_sup_eq_mul_of_commute hcomm hinf,
    card_thetaTorusP hf hk ht,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (R3Levi_le_C0 h p hp hp2 ζ hζ hζbar hσ)).toEquiv,
    card_R3Levi h p hp hp2 ζ hζ hζbar hσ]
  ring

theorem exists_orderOf_eq_prime_sl2 {n q : ℕ} (hn : 1 ≤ n) (hq : q.Prime)
    (hdvd : q ∣ 2 ^ n + 1) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n), orderOf g = q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    have := Fintype.ofFinite (GaloisField 2 n)
    have h := Matrix.card_SL_field (𝔽 := GaloisField 2 n) 2
    have hq2 : Fintype.card (GaloisField 2 n) = 2 ^ n := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 n (by omega)]
    rw [hq2, Fin.prod_univ_two] at h
    rw [h]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hm : (2 ^ n) ^ 2 - 2 ^ n = 2 ^ n * (2 ^ n - 1) := by
      rw [Nat.mul_sub, sq, mul_one]
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    rw [hm]
    apply Nat.div_eq_of_eq_mul_left (by omega)
    ring
  have hdvd' : q ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
    rw [hcard]
    have h2 : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
      have hsq := Nat.sq_sub_sq (2 ^ n) 1
      rw [one_pow, mul_comm] at hsq
      exact hsq
    rw [h2]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left hdvd _) _
  haveI : Fact q.Prime := ⟨hq⟩
  exact exists_prime_orderOf_dvd_card' q hdvd'

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
