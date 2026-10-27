module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.Adapters.LieModelOrders
import CFSG.Quasithin.Background.A3FactsClassical
import CFSG.HardMathSupport.Timmesfeld.FieldBonus.Classify
import CFSG.Quasithin.Vol2.KGFactInspSp4
import CFSG.ClassicalGroups.Symplectic.Sp4ElemAbelianPlus
import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87EngAb
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossRank

public section

namespace CFSG.Blueprint

open CFSG.Open CFSG.SectionRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SectionRank.ClassicalEven (torusDiag torusDiag_mem_SL torusDiag_mem_SU torusVec
  prod_torusVec torusVec_pow torusVec_one)

variable {X : Type} [Group X]

private theorem toNat_even_sub_one {q i : ℕ} (hq : 1 ≤ q) (hi : Even i) :
    (((q : ℤ) ^ i - (-1 : ℤ) ^ i)).toNat = q ^ i - 1 := by
  rw [hi.neg_one_pow]
  rw [show ((q : ℤ) ^ i - 1) = ((q ^ i - 1 : ℕ) : ℤ) by
    rw [Nat.cast_sub (Nat.one_le_pow i q hq)]
    push_cast
    ring]
  exact Int.toNat_natCast _

private theorem toNat_odd_add_one {q i : ℕ} (hi : Odd i) :
    (((q : ℤ) ^ i - (-1 : ℤ) ^ i)).toNat = q ^ i + 1 := by
  rw [hi.neg_one_pow, sub_neg_eq_add]
  rw [show ((q : ℤ) ^ i + 1) = ((q ^ i + 1 : ℕ) : ℤ) by
    push_cast
    ring]
  exact Int.toNat_natCast _

private theorem ordA_three_eq (q : ℕ) :
    ordA 3 q = q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) / Nat.gcd 4 (q - 1) := by
  simp [ordA, Finset.prod_Icc_succ_top, Nat.mul_assoc]

private theorem ordTwistedA_three_eq {q : ℕ} (hq : 1 ≤ q) :
    ordTwistedA 3 q =
      q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) / Nat.gcd 4 (q + 1) := by
  rw [ordTwistedA, show Finset.Icc 2 (3 + 1) = {2, 3, 4} from rfl, Finset.prod_insert (by decide),
    Finset.prod_pair (by norm_num), toNat_even_sub_one hq (by decide),
    toNat_odd_add_one (by decide), toNat_even_sub_one hq (by decide),
    show 3 * (3 + 1) / 2 = 6 from rfl, show (3 : ℕ) + 1 = 4 from rfl, Nat.mul_assoc]

private theorem ordBC_two_eq (q : ℕ) :
    ordBC 2 q = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) / Nat.gcd 2 (q - 1) := by
  rw [ordBC, show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) from rfl, Finset.prod_pair (by norm_num),
    show (2 : ℕ) * 1 = 2 from rfl, show (2 : ℕ) * 2 = 4 from rfl]

theorem LieModel.two_le_pRank_psl4_of_dvd [Finite X] {p f r : ℕ} (h : LieModel X .PSL 4 p f)
    (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ∣ p ^ f - 1) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup X) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hdvd : r ∣ Nat.card K - 1 := by rw [hK]; exact hrq
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r (by rwa [Nat.card_units])
  rw [pRank_top_eq_of_mulEquiv hr.one_lt e]
  exact CFSG.Quasithin.A3Facts.two_le_pRank_torus_disjoint (H := StatedSL 4 K) hr2 hζ
    (i₀ := (0 : Fin 4)) (i₁ := (1 : Fin 4)) (k₀ := (2 : Fin 4)) (k₁ := (3 : Fin 4))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (torusDiag_mem_SL (prod_torusVec ζ _ _)) (torusDiag_mem_SL (prod_torusVec ζ _ _))

theorem LieModel.two_le_pRank_psu4_of_dvd [Finite X] {p f r : ℕ} (h : LieModel X .PSU 4 p f)
    (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ∣ p ^ f + 1) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup X) := by
  haveI : Fact r.Prime := ⟨hr⟩
  by_cases hr3 : r = 3
  · subst hr3
    exact CFSG.HardMathSupport.Timmesfeld.FieldBonus.two_le_pRank_three_psu_four_of_dvd
      (n := 4) (by norm_num) (h.statedClassicalModel_of_ne_zero (by norm_num)) hrq
  · obtain ⟨⟨hp, hf, -⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
      h.statedClassicalModel_of_ne_zero (by norm_num)
    letI : Field K := hfield
    letI : Finite K := hfinite
    have hq : p ^ f ≠ 0 := (pow_pos hp.pos f).ne'
    have hcard : Nat.card Kˣ = (p ^ f + 1) * (p ^ f - 1) := by
      rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r
      (by rw [hcard]; exact hrq.mul_right _)
    have hζq : ζ ^ (p ^ f + 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (by rw [hζ]; exact hrq)
    rw [pRank_top_eq_of_mulEquiv hr.one_lt e]
    exact CFSG.Quasithin.A3Facts.two_le_pRank_torus_shared (H := StatedSU 4 (p ^ f) K) hr3 hζ
      (i₀ := (0 : Fin 4)) (i₁ := (1 : Fin 4)) (i₂ := (2 : Fin 4)) (by decide) (by decide)
      (by decide)
      (torusDiag_mem_SU hq (prod_torusVec ζ _ _) (by rw [torusVec_pow, hζq, torusVec_one]))
      (torusDiag_mem_SU hq (prod_torusVec ζ _ _) (by rw [torusVec_pow, hζq, torusVec_one]))

theorem LieModel.two_le_pRank_psp4_of_dvd [Finite X] {p f r : ℕ} (h : LieModel X .PSp 2 p f)
    (hr : r.Prime) (hr2 : r ≠ 2) (hrq : r ∣ p ^ f - 1 ∨ r ∣ p ^ f + 1) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup X) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  letI : Field K := hfield
  letI : Finite K := hfinite
  rw [pRank_top_eq_of_mulEquiv hr.one_lt e]
  rcases hrq with hq1 | hq1
  · exact CFSG.Quasithin.H13.KGInsp4316.two_le_pRank_psp4 (K := K) hr2 (by rw [hK]; exact hq1)
  ·
    obtain ⟨E, hE, hEcard⟩ :=
      CFSG.ClassicalGroups.Symplectic.Sp4.exists_isElemAbelian_card_sq_of_dvd_card_add_one
        (K := K) hr (by rw [hK]; exact hq1)
    let N := (StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)
    have hsqN : ∀ w : StatedSp 2 K, w ∈ N → w * w = 1 := by
      intro w hw
      rw [Subgroup.mem_subgroupOf] at hw
      rw [StatedScalars] at hw
      obtain ⟨c, hc⟩ := hw
      have hm : (Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c : GL (Fin 2 ⊕ Fin 2) K) ∈
          StatedSp 2 K := hc ▸ w.2
      have hc2 : c ^ 2 = 1 :=
        (CFSG.Open.StatedAPI.scalar_mem_statedSp_iff (by norm_num) c).1 hm
      apply Subtype.ext
      change ((w : GL (Fin 2 ⊕ Fin 2) K) * (w : GL (Fin 2 ⊕ Fin 2) K)) = 1
      rw [← hc, ← map_mul, ← pow_two, hc2, map_one]
    let φ : E →* StatedProj (StatedSp 2 K) := (QuotientGroup.mk' N).comp E.subtype
    have hφ : Function.Injective φ := by
      intro a b hab
      have hzN : ((a : StatedSp 2 K)⁻¹ * (b : StatedSp 2 K)) ∈ N := by
        change QuotientGroup.mk' N (a : StatedSp 2 K) = QuotientGroup.mk' N (b : StatedSp 2 K)
          at hab
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hab
        exact hab
      have hzE : ((a : StatedSp 2 K)⁻¹ * (b : StatedSp 2 K)) ∈ E :=
        E.mul_mem (E.inv_mem a.2) b.2
      have h2 : ((a : StatedSp 2 K)⁻¹ * (b : StatedSp 2 K)) ^ 2 = 1 := by
        rw [pow_two]
        exact hsqN _ hzN
      have hr2' : ((a : StatedSp 2 K)⁻¹ * (b : StatedSp 2 K)) ^ r = 1 := hE.2 _ hzE
      have h1 : ((a : StatedSp 2 K)⁻¹ * (b : StatedSp 2 K)) = 1 := by
        have hord : orderOf ((a : StatedSp 2 K)⁻¹ * (b : StatedSp 2 K)) ∣ Nat.gcd 2 r :=
          Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hr2')
        have hodd : Odd r := by
          rcases hr.eq_two_or_odd with h | h
          · exact absurd h hr2
          · exact Nat.odd_iff.mpr h
        have hg : Nat.gcd 2 r = 1 := Nat.coprime_two_left.mpr hodd
        rw [hg] at hord
        exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hord)
      have hba : (b : StatedSp 2 K) = (a : StatedSp 2 K) := by
        have hh := congrArg (fun w => (a : StatedSp 2 K) * w) h1
        simp only [mul_one] at hh
        rw [← mul_assoc, mul_inv_cancel, one_mul] at hh
        exact hh
      exact Subtype.ext hba.symm
    haveI hEcomm : IsMulCommutative E := hE.1
    have hcomm : ∀ a b : E, a * b = b * a :=
      fun a b => Subtype.ext (setLike_mul_comm (s := E) a.2 b.2)
    have hpow : ∀ a : E, a ^ r = 1 :=
      fun a => Subtype.ext (hE.2 (a : StatedSp 2 K) a.2)
    exact le_pRank_of_injective (G := StatedProj (StatedSp 2 K)) (A := E) hr.one_lt hcomm hpow
      (k := 2) hEcard φ hφ le_top

private theorem isMulCommutative_sylow_statedProj_of_gl {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] {r : ℕ} [Fact r.Prime]
    (hGL : ∀ Q : Subgroup (GL ι K), IsPGroup r Q → IsMulCommutative Q)
    (H : Subgroup (GL ι K)) (R : Sylow r (StatedProj H)) :
    IsMulCommutative (R : Subgroup (StatedProj H)) := by
  let N := (StatedScalars ι K).subgroupOf H
  let π : H →* StatedProj H := QuotientGroup.mk' N
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective (f := π)
    (QuotientGroup.mk'_surjective N) r R
  rw [Sylow.coe_mapSurjective]
  have h1 : IsMulCommutative ((S : Subgroup H).map H.subtype) := hGL _ (S.isPGroup'.map _)
  have h2 : IsMulCommutative (S : Subgroup H) :=
    .of_setLike_mul_comm fun a ha b hb => Subtype.ext
      (setLike_mul_comm (s := (S : Subgroup H).map H.subtype) ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩)
  haveI : IsMulCommutative (S : Subgroup H) := h2
  have hmap : IsMulCommutative ((S : Subgroup H).map π) := by
    refine IsMulCommutative.of_setLike_mul_comm ?_
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hb
    change π x * π y = π y * π x
    rw [← map_mul, ← map_mul]
    exact congrArg π (setLike_mul_comm hx hy)
  exact hmap

theorem LieModel.isMulCommutative_sylow_psl4 [Finite X] {p f r : ℕ} (h : LieModel X .PSL 4 p f)
    (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : r ≠ p) (P : Sylow r X) :
    IsMulCommutative (P : Subgroup X) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨⟨hp, hf, -⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
    h.statedClassicalModel_of_ne_zero (by norm_num)
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hchar : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hrK : ringChar K ≠ r := by
    rw [ringChar.eq K p]
    exact hrp.symm
  have h4 : Fintype.card (Fin 4) < r := by
    have : Fintype.card (Fin 4) = 4 := by simp
    omega
  exact CFSG.LocalAnalysis.RankFourTheoremC.isMulCommutative_sylow_of_mulEquiv e
    (fun R => isMulCommutative_sylow_statedProj_of_gl
      (fun Q hQ => IsMulCommutative.of_setLike_mul_comm
        (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.abelian_of_pGroup_of_card_lt hrK h4 Q hQ))
      (StatedSL 4 K) R) P

theorem LieModel.isMulCommutative_sylow_psu4 [Finite X] {p f r : ℕ} (h : LieModel X .PSU 4 p f)
    (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : r ≠ p) (P : Sylow r X) :
    IsMulCommutative (P : Subgroup X) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨⟨hp, hf, -⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
    h.statedClassicalModel_of_ne_zero (by norm_num)
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hchar : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic (k := 2 * f) hp
      (by omega) (by rw [hK, ← pow_mul, mul_comm])
  have hrK : ringChar K ≠ r := by
    rw [ringChar.eq K p]
    exact hrp.symm
  have h4 : Fintype.card (Fin 4) < r := by
    have : Fintype.card (Fin 4) = 4 := by simp
    omega
  exact CFSG.LocalAnalysis.RankFourTheoremC.isMulCommutative_sylow_of_mulEquiv e
    (fun R => isMulCommutative_sylow_statedProj_of_gl
      (fun Q hQ => IsMulCommutative.of_setLike_mul_comm
        (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.abelian_of_pGroup_of_card_lt hrK h4 Q hQ))
      (StatedSU 4 (p ^ f) K) R) P

theorem LieModel.isMulCommutative_sylow_psp4 [Finite X] {p f r : ℕ} (h : LieModel X .PSp 2 p f)
    (hr : r.Prime) (hr5 : 5 ≤ r) (hrp : r ≠ p) (P : Sylow r X) :
    IsMulCommutative (P : Subgroup X) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨⟨hp, hf, -⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
    h.statedClassicalModel_of_ne_zero (by norm_num)
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hchar : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hrK : ringChar K ≠ r := by
    rw [ringChar.eq K p]
    exact hrp.symm
  have h4 : Fintype.card (Fin 2 ⊕ Fin 2) < r := by
    have : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by simp
    omega
  exact CFSG.LocalAnalysis.RankFourTheoremC.isMulCommutative_sylow_of_mulEquiv e
    (fun R => isMulCommutative_sylow_statedProj_of_gl
      (fun Q hQ => IsMulCommutative.of_setLike_mul_comm
        (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.abelian_of_pGroup_of_card_lt hrK h4 Q hQ))
      (StatedSp 2 K) R) P

theorem LieModel.card_outer_psl4_dvd {p f : ℕ} (h : LieModel X .PSL 4 p f) :
    Nat.card (Outer X) ∣ 2 * f * Nat.gcd 4 (p ^ f - 1) := by
  obtain ⟨⟨hp, hf, -⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
    h.statedClassicalModel_of_ne_zero (by norm_num)
  letI : Field K := hfield
  letI : Finite K := hfinite
  have e' : X ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 4 K :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 K).symm).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 K)
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
  exact
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound
      (p := p) (f := f) (n := 4) hp hf (by norm_num) hK

theorem LieModel.card_outer_psu4 {p f : ℕ} (h : LieModel X .PSU 4 p f) :
    Nat.card (Outer X) = 2 * f * Nat.gcd 4 (p ^ f + 1) := by
  obtain ⟨⟨hp, hf, -⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
    h.statedClassicalModel_of_ne_zero (by norm_num)
  letI : Field K := hfield
  letI : Finite K := hfinite
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬ (4 = 3 ∧ p ^ f = 2) := by
    rintro ⟨h, -⟩
    omega
  have hout :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_full_diagonal_outer_order hU
      (n := 4) (by norm_num) hq
  have e' : X ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU 4 :=
    e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (n := 4) (by norm_num)).symm
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
  exact hout.2.2.2.2.1

theorem LieModel.card_outer_psp4_dvd {p f : ℕ} (h : LieModel X .PSp 2 p f) :
    Nat.card (Outer X) ∣ 2 * f * Nat.gcd 2 (p ^ f - 1) :=
  (CFSG.LocalAnalysis.ComponentInitial.symplectic_model_outer_two_part_bound X 2 p f
    (h.statedClassicalModel_of_ne_zero (by norm_num))).2.1

theorem LieModel.not_dvd_card_outer_psl4 {p f r : ℕ} (h : LieModel X .PSL 4 p f) (hr : r.Prime)
    (hr5 : 5 ≤ r) (hrf : ¬ r ∣ f) : ¬ r ∣ Nat.card (Outer X) := by
  intro hd
  have h' : r ∣ 2 * f * Nat.gcd 4 (p ^ f - 1) := hd.trans h.card_outer_psl4_dvd
  have hgle : Nat.gcd 4 (p ^ f - 1) ≤ 4 := Nat.gcd_le_left _ (by norm_num)
  rw [mul_assoc] at h'
  rcases (hr.dvd_mul).1 h' with h2 | hfg
  · exact Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega) h2
  · rcases (hr.dvd_mul).1 hfg with hf' | hg
    · exact hrf hf'
    · exact Nat.not_dvd_of_pos_of_lt (n := Nat.gcd 4 (p ^ f - 1))
        (Nat.gcd_pos_of_pos_left _ (by norm_num)) (by omega) hg

theorem LieModel.not_dvd_card_outer_psu4 {p f r : ℕ} (h : LieModel X .PSU 4 p f) (hr : r.Prime)
    (hr5 : 5 ≤ r) (hrf : ¬ r ∣ f) : ¬ r ∣ Nat.card (Outer X) := by
  intro hd
  have hgle : Nat.gcd 4 (p ^ f + 1) ≤ 4 := Nat.gcd_le_left _ (by norm_num)
  rw [h.card_outer_psu4, mul_assoc] at hd
  rcases (hr.dvd_mul).1 hd with h2 | hfg
  · exact Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega) h2
  · rcases (hr.dvd_mul).1 hfg with hf' | hg
    · exact hrf hf'
    · exact Nat.not_dvd_of_pos_of_lt (n := Nat.gcd 4 (p ^ f + 1))
        (Nat.gcd_pos_of_pos_left _ (by norm_num)) (by omega) hg

theorem LieModel.not_dvd_card_outer_psp4 {p f r : ℕ} (h : LieModel X .PSp 2 p f) (hr : r.Prime)
    (hr5 : 5 ≤ r) (hrf : ¬ r ∣ f) : ¬ r ∣ Nat.card (Outer X) := by
  intro hd
  have h' : r ∣ 2 * f * Nat.gcd 2 (p ^ f - 1) := hd.trans h.card_outer_psp4_dvd
  have hgle : Nat.gcd 2 (p ^ f - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
  rw [mul_assoc] at h'
  rcases (hr.dvd_mul).1 h' with h2 | hfg
  · exact Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega) h2
  · rcases (hr.dvd_mul).1 hfg with hf' | hg
    · exact hrf hf'
    · exact Nat.not_dvd_of_pos_of_lt (n := Nat.gcd 2 (p ^ f - 1))
        (Nat.gcd_pos_of_pos_left _ (by norm_num)) (by omega) hg

theorem LieModel.three_thousand_six_hundred_lt_card_psl4 {p f : ℕ}
    (h : LieModel X .PSL 4 p f) : 3600 < Nat.card X := by
  have hq2 : 2 ≤ p ^ f := by
    obtain ⟨hp, hf, -⟩ := h.admissible
    have h1 : 2 ≤ p := hp.two_le
    have h2 : 2 ^ 1 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ p ^ f := le_trans h2 (Nat.pow_le_pow_left h1 f)
  rw [h.card_eq_lieOrd (by norm_num : (4 : ℕ) ≠ 0)]
  change 3600 < ordA 3 (p ^ f)
  rw [ordA_three_eq]
  rcases eq_or_lt_of_le hq2 with hq | hq
  · rw [← hq]
    norm_num
  ·
    have h6 : 729 ≤ (p ^ f) ^ 6 := by
      calc 729 = 3 ^ 6 := by norm_num
        _ ≤ (p ^ f) ^ 6 := Nat.pow_le_pow_left hq 6
    have h2 : 8 ≤ (p ^ f) ^ 2 - 1 := by
      have h' : 9 ≤ (p ^ f) ^ 2 := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hq 2
      omega
    have h3 : 26 ≤ (p ^ f) ^ 3 - 1 := by
      have h' : 27 ≤ (p ^ f) ^ 3 := by
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_left hq 3
      omega
    have h4 : 80 ≤ (p ^ f) ^ 4 - 1 := by
      have h' : 81 ≤ (p ^ f) ^ 4 := by
        calc 81 = 3 ^ 4 := by norm_num
          _ ≤ (p ^ f) ^ 4 := Nat.pow_le_pow_left hq 4
      omega
    have hB : 14404 ≤
        (p ^ f) ^ 6 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1) * ((p ^ f) ^ 4 - 1)) := by
      have h : 729 * ((8 * 26) * 80) ≤
          (p ^ f) ^ 6 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1) * ((p ^ f) ^ 4 - 1)) :=
        Nat.mul_le_mul h6 (Nat.mul_le_mul (Nat.mul_le_mul h2 h3) h4)
      norm_num at h ⊢
      omega
    have hg : Nat.gcd 4 (p ^ f - 1) ≤ 4 := Nat.gcd_le_left _ (by norm_num)
    have hposg : 0 < Nat.gcd 4 (p ^ f - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have h1 : 3600 <
        (p ^ f) ^ 6 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1) * ((p ^ f) ^ 4 - 1)) / 4 := by
      rw [Nat.lt_div_iff_mul_lt (by norm_num)]
      omega
    exact h1.trans_le (Nat.div_le_div_left hg hposg)

theorem LieModel.three_thousand_six_hundred_lt_card_psu4 {p f : ℕ}
    (h : LieModel X .PSU 4 p f) : 3600 < Nat.card X := by
  have hq1 : 1 ≤ p ^ f := by
    obtain ⟨hp, hf, -⟩ := h.admissible
    exact Nat.one_le_pow _ _ hp.pos
  have hq2 : 2 ≤ p ^ f := by
    obtain ⟨hp, hf, -⟩ := h.admissible
    have h1 : 2 ≤ p := hp.two_le
    have h2 : 2 ^ 1 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ p ^ f := le_trans h2 (Nat.pow_le_pow_left h1 f)
  rw [h.card_eq_lieOrd (by norm_num : (4 : ℕ) ≠ 0)]
  change 3600 < ordTwistedA 3 (p ^ f)
  rw [ordTwistedA_three_eq hq1]
  rcases eq_or_lt_of_le hq2 with hq | hq
  · rw [← hq]
    decide
  · have h6 : 729 ≤ (p ^ f) ^ 6 := by
      calc 729 = 3 ^ 6 := by norm_num
        _ ≤ (p ^ f) ^ 6 := Nat.pow_le_pow_left hq 6
    have h2 : 8 ≤ (p ^ f) ^ 2 - 1 := by
      have h' : 9 ≤ (p ^ f) ^ 2 := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hq 2
      omega
    have h3 : 28 ≤ (p ^ f) ^ 3 + 1 := by
      have h' : 27 ≤ (p ^ f) ^ 3 := by
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_left hq 3
      omega
    have h4 : 80 ≤ (p ^ f) ^ 4 - 1 := by
      have h' : 81 ≤ (p ^ f) ^ 4 := by
        calc 81 = 3 ^ 4 := by norm_num
          _ ≤ (p ^ f) ^ 4 := Nat.pow_le_pow_left hq 4
      omega
    have hB : 14404 ≤
        (p ^ f) ^ 6 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1)) := by
      have h : 729 * ((8 * 28) * 80) ≤
          (p ^ f) ^ 6 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1)) :=
        Nat.mul_le_mul h6 (Nat.mul_le_mul (Nat.mul_le_mul h2 h3) h4)
      norm_num at h ⊢
      omega
    have hg : Nat.gcd 4 (p ^ f + 1) ≤ 4 := Nat.gcd_le_left _ (by norm_num)
    have hposg : 0 < Nat.gcd 4 (p ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have h1 : 3600 <
        (p ^ f) ^ 6 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1)) / 4 := by
      rw [Nat.lt_div_iff_mul_lt (by norm_num)]
      omega
    exact h1.trans_le (Nat.div_le_div_left hg hposg)

theorem LieModel.three_thousand_six_hundred_lt_card_psp4 {p f : ℕ}
    (h : LieModel X .PSp 2 p f) : 3600 < Nat.card X := by
  have hq2 : 2 ≤ p ^ f := by
    obtain ⟨hp, hf, -⟩ := h.admissible
    have h1 : 2 ≤ p := hp.two_le
    have h2 : 2 ^ 1 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ p ^ f := le_trans h2 (Nat.pow_le_pow_left h1 f)
  have hne2 : p ^ f ≠ 2 := by
    obtain ⟨-, -, -, hne⟩ := h.admissible
    intro hpq
    exact hne (by rw [hpq])
  rw [h.card_eq_lieOrd (by norm_num : (2 : ℕ) ≠ 0)]
  change 3600 < ordBC 2 (p ^ f)
  rw [ordBC_two_eq]
  have hq3 : 3 ≤ p ^ f := by
    rcases eq_or_lt_of_le hq2 with hq | hq
    · exact absurd hq.symm hne2
    · omega
  rcases eq_or_lt_of_le hq3 with hq | hq
  · rw [← hq]
    decide
  · have h4 : 256 ≤ (p ^ f) ^ 4 := by
      calc 256 = 4 ^ 4 := by norm_num
        _ ≤ (p ^ f) ^ 4 := Nat.pow_le_pow_left hq 4
    have h2 : 15 ≤ (p ^ f) ^ 2 - 1 := by
      have h' : 16 ≤ (p ^ f) ^ 2 := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hq 2
      omega
    have h5 : 255 ≤ (p ^ f) ^ 4 - 1 := by omega
    have hB : 14404 ≤ (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) := by
      have h : 256 * (15 * 255) ≤
          (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) :=
        Nat.mul_le_mul h4 (Nat.mul_le_mul h2 h5)
      norm_num at h ⊢
      omega
    have hg : Nat.gcd 2 (p ^ f - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
    have hposg : 0 < Nat.gcd 2 (p ^ f - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have h1 : 3600 < (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) / 2 := by
      rw [Nat.lt_div_iff_mul_lt (by norm_num)]
      omega
    exact h1.trans_le (Nat.div_le_div_left hg hposg)

end CFSG.Blueprint
