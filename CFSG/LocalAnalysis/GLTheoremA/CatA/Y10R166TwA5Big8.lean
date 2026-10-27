module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Big7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Build
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Cases
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Big5

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
open CFSG.LocalAnalysis.ComponentInitial
open TwA5Big
open Matrix


section Certs


variable {n : ℕ} {F : Type} [Field F] [Finite F] (h : UnitaryFieldData 2 n F)

theorem exists_concl166S_unitaryPSU_six_of_four_le (hn : 4 ≤ n) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpdvd : p ∣ 2 ^ n - 1) :
    ∃ (q : ℕ) (B' : Subgroup (unitaryPSU h 6)) (x' : unitaryPSU h 6)
      (J : Subgroup (unitaryPSU h 6)), Concl166S (unitaryPSU h 6) p q B' x' J := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨q, hq, hqfac, hq30⟩ := exists_twA5_prime hn
  obtain ⟨ζu, hζ, hζo⟩ := exists_twA5_zeta h hq hqfac
  have hq2 : q ≠ 2 := by
    intro hqeq
    subst hqeq
    exact hq30 (by norm_num : (2 : ℕ) ∣ 30)
  have hq3 : ¬ q ∣ 3 := fun hd => hq30 (hd.trans (by norm_num : (3 : ℕ) ∣ 30))
  have hq5 : ¬ q ∣ 5 := fun hd => hq30 (hd.trans (by norm_num : (5 : ℕ) ∣ 30))
  have hq6 : ¬ q ∣ 6 := fun hd => hq30 (hd.trans (by norm_num : (6 : ℕ) ∣ 30))
  have hfac : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    have hsq : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by
      rw [show 2 * n = n * 2 by omega, pow_mul]
    rw [hsq]
    simpa using Nat.sq_sub_sq (2 ^ n) 1
  have hqd : q ∣ 2 ^ (2 * n) - 1 := hfac ▸ dvd_mul_of_dvd_left hqfac (2 ^ n - 1)
  have hpd : p ∣ 2 ^ (2 * n) - 1 := hfac ▸ dvd_mul_of_dvd_right hpdvd (2 ^ n + 1)
  have hq_not : ¬ q ∣ 2 ^ n - 1 := by
    intro hq1
    have hsub : q ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hqfac hq1
    have h2 : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
      have := Nat.one_le_two_pow (n := n)
      omega
    rw [h2] at hsub
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 hsub)
  have hpq : p ≠ q := by
    intro hpq
    subst hpq
    exact hq_not hpdvd
  have he : evenRank (unitaryPSU h 6) = 4 :=
    evenRank_unitaryPSU_six h hn hq hqfac hq6 hq2
  have hclauses := blockSU_suFiveIndex_clauses h hn2
  have hm2 : evenRank (unitaryPSU h 6) + 2 ≤ twoRank ↥(blockSU h suFiveIndex) := by
    have h4n : 4 * n ≤ twoRank ↥(blockSU h suFiveIndex) := hclauses.2.2.1
    omega
  have hodd : Odd (Nat.card (Subgroup.center ↥(blockSU h suFiveIndex))) := hclauses.2.1
  have hdvd : p * q ∣ Nat.card (↥(blockSU h suFiveIndex) ⧸
      Subgroup.center ↥(blockSU h suFiveIndex)) := by
    have hpJ : p ∣ Nat.card (↥(blockSU h suFiveIndex) ⧸
        Subgroup.center ↥(blockSU h suFiveIndex)) := hclauses.2.2.2 p hp hp2 hpd
    have hqJ : q ∣ Nat.card (↥(blockSU h suFiveIndex) ⧸
        Subgroup.center ↥(blockSU h suFiveIndex)) := hclauses.2.2.2 q hq hq2 hqd
    exact ((Nat.coprime_primes hp hq).2 hpq).mul_dvd_of_dvd_of_dvd hpJ hqJ
  have hB : IsElemAbelian q (twA5B h hζ) := twA5B_isElemAbelian h hζ hζo
  have hx : unitaryProj h 6 (diagFiveLast h (ζu : F) hζ) ∈ twA5B h hζ :=
    diagFiveLast_mem_twA5B h hζ
  have hx1 : unitaryProj h 6 (diagFiveLast h (ζu : F) hζ) ≠ 1 := by
    intro h1
    refine diagFiveLast_not_scalar h hq hq6 hζ hζo ?_
    rw [← ker_unitaryProj h 6]
    exact MonoidHom.mem_ker.mpr h1
  have hrankB : Nat.card (twA5B h hζ) = q ^ evenRank (unitaryPSU h 6) := by
    rw [card_twA5B h hζ hζo hq hq6, he]
  have hJx : blockSU h suFiveIndex ≤ Subgroup.centralizer
      ({unitaryProj h 6 (diagFiveLast h (ζu : F) hζ)} : Set (unitaryPSU h 6)) := by
    rw [centralizer_unitaryProj_diagFiveLast h hζ (pow_six_ne_one hζo hq6)]
    exact Subgroup.map_mono (unitaryBlock_le_unitaryBlockDiag h suFiveIndex)
  have hJq : CFSG.IsQuasisimple ↥(blockSU h suFiveIndex) :=
    isQuasisimple_blockSU_of_three_le h (by rw [card_suFiveIndex]; norm_num)
      (five_two_pow_ne_three_two hn2) (by rw [card_suFiveIndex]; norm_num)
  have hcomm := twA5_commutator_mem h hζ hζo hq6
  have hJlab : HasLabel ↥(blockSU h suFiveIndex)
      (fun l : GLALabel => l = (⟨.twA, 4, n⟩ : GLALabel)) :=
    hasLabel_blockSU_suFiveIndex h hn2
  have hshape := twA5_shape h hn he
  have hsix := twA5_six h hn hζ hζo hq hqfac hq6 hq2
  have hE : IsElemAbelian q (twA5E h hζ) := twA5E_isElemAbelian h hζ hζo
  have hEcard : Nat.card (twA5E h hζ) = q ^ 3 := card_twA5E h hζ hζo hq hq3 hq6
  have hxE : unitaryProj h 6 (diagFiveLast h (ζu : F) hζ) ∈ twA5E h hζ :=
    diagFiveLast_mem_twA5E h hζ
  have he3 := twA5E_layer_ne_bot h hζ hζo hq hn2 hq3 hqd
  have hBJ := twA5B_le_sup h hζ hζo hq hq5
  have hrankinf := twA5B_inf_blockSU_pRank h hζ hζo hq hq6 he
  have hSJ : (unitaryLineRadical h).map (unitaryProj h 6) ≤ blockSU h suFiveIndex :=
    Subgroup.map_mono (unitaryLineRadical_le_unitaryBlock h)
  have hS2 : IsPGroup 2 ((unitaryLineRadical h).map (unitaryProj h 6)) :=
    IsPGroup.map (unitaryLineRadical_isPGroup h) (unitaryProj h 6)
  have hBS := twA5B_le_normalizer_lineRadical h hζ
  have hBJS := twA5_eight h hζ hζo
  have hsu := twA5_su_case (q := q) h hn2 hζ
  have hsix' : (Subgroup.center ↥(blockSU h suFiveIndex) = ⊥ ∧
        TrivialMultiplierT ↥(blockSU h suFiveIndex)) ∨
      (evenRank (unitaryPSU h 6) = 4 ∧ ∃ labJ : GLALabel,
        HasLabel ↥(blockSU h suFiveIndex) (fun l => l = labJ) ∧
        labJ.tag = .twA ∧ labJ.rank = 4 ∧ Even labJ.n) ∨
      (blockSU h suFiveIndex = ⊤ ∧ 3 ∣ Nat.card (Subgroup.center (unitaryPSU h 6)) ∧
        ∃ lab : GLALabel, HasLabel (unitaryPSU h 6) (fun l => l = lab) ∧ Odd lab.n ∧
        ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)) :=
    hsix.elim Or.inl (fun h => Or.inr (Or.inl h))
  exact ⟨q, twA5B h hζ, unitaryProj h 6 (diagFiveLast h (ζu : F) hζ),
    blockSU h suFiveIndex, concl166S_of_witness hq hq2 hB hx hx1 hrankB (le_of_eq he.symm)
      hJx hJq hcomm ⟨.twA, 4, n⟩ hJlab hshape hm2 hodd hdvd hsix'
      (twA5E h hζ) (twA5E_le h hζ) hE hEcard hxE he3 hBJ hrankinf
      ((unitaryLineRadical h).map (unitaryProj h 6)) hSJ hS2 hBS hBJS hsu⟩

theorem concl166S_twA5Big_of_transport
    (htr : ∀ {K R : Type} [Group K] [Finite K] [Group R] [Finite R], (K ≃* R) → ∀ {p : ℕ},
      (∃ (q : ℕ) (B' : Subgroup R) (x' : R) (J : Subgroup R), Concl166S R p q B' x' J) →
      ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J)
    {X : Type} [Group X] [Finite X] {lab : GLALabel} {p : ℕ}
    (hK : HasLabel X (fun l : GLALabel => l = lab))
    (hfam : i166FamTwA5 lab p (Subgroup.center X = ⊥))
    (hp : p.Prime) (hp2 : p ≠ 2) (hz : Subgroup.center X = ⊥) (hn : 4 ≤ lab.n) :
    ∃ (q : ℕ) (B' : Subgroup X) (x' : X) (J : Subgroup X), Concl166S X p q B' x' J := by
  obtain ⟨ht, hr, hn2, hpdvd⟩ := hfam
  obtain ⟨F, hFld, hFin, h', ⟨e⟩⟩ :=
    exists_mulEquiv_unitaryPSU_of_hasLabel_twA hK hz ht hn2
  letI : Field F := hFld
  letI : Finite F := hFin
  refine htr (hr ▸ e) ?_
  exact exists_concl166S_unitaryPSU_six_of_four_le (p := p) h' hn hp hp2 hpdvd

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
