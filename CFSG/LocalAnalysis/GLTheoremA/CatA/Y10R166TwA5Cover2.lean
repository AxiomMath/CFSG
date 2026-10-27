module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Cover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Build
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def TwA5CoverWitness (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] : Prop :=
  ∃ (B : Subgroup (StatedSU 6 (2 ^ n) F)) (x : StatedSU 6 (2 ^ n) F)
    (E S : Subgroup (StatedSU 6 (2 ^ n) F)),
    x ∈ Subgroup.center (StatedSU 6 (2 ^ n) F) ∧ x ∈ B ∧ x ≠ 1 ∧
    IsElemAbelian 3 B ∧ Nat.card B = 3 ^ 4 ∧
    E ≤ B ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧ x ∈ E ∧
    GLAPLayer 3 ((⊤ : Subgroup (StatedSU 6 (2 ^ n) F)) ⊓
      Subgroup.centralizer (E : Set (StatedSU 6 (2 ^ n) F))) ≠ ⊥ ∧
    IsPGroup 2 S ∧ B ≤ Subgroup.normalizer (S : Set (StatedSU 6 (2 ^ n) F)) ∧
    B ⊓ Subgroup.centralizer (S : Set (StatedSU 6 (2 ^ n) F)) = Subgroup.zpowers x

theorem hasLabel_statedSU_six {n : ℕ} (hn : 2 ≤ n) (F : Type) [Field F] [Finite F]
    [CharP F 2] (hF : Nat.card F = (2 ^ n) ^ 2) :
    HasLabel (StatedSU 6 (2 ^ n) F) (fun l : GLALabel => l = ⟨.twA, 5, n⟩) := by
  have hZeq := center_statedSU_six_eq_scalars F hF
  refine hasLabel_of_statedClassicalModel_PSU (r := 5) (n := n)
    (isQuasisimple_statedSU_six F hF) ?_
  refine ⟨⟨Nat.prime_two, by omega, by norm_num, by simp⟩, F, inferInstance, inferInstance,
    hF, ⟨?_⟩⟩
  exact QuotientGroup.quotientMulEquivOfEq hZeq

section Certs


private theorem exceptionalOrders_PSU_six_eq_one {f : ℕ} (hf : 2 ≤ f) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 6 2 f = (1, 1) := by
  have hf1 : f ≠ 1 := by omega
  simp [CFSG.Blueprint.Multiplier.exceptionalOrders, hf1]

private theorem pRank_statedSU_six_le_three {n p : ℕ} (F : Type) [Field F] [Finite F]
    [CharP F 2] (hn : 2 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpdvd : p ∣ 2 ^ n - 1) :
    CFSG.Open.pRank p (⊤ : Subgroup (StatedSU 6 (2 ^ n) F)) ≤ 3 := by
  have hpnot : ¬ p ∣ 2 ^ n + 1 := by
    intro hdiv
    have h2 : p ∣ 2 := by
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have hsub : p ∣ 2 ^ n + 1 - (2 ^ n - 1) := Nat.dvd_sub hdiv hpdvd
      rwa [show 2 ^ n + 1 - (2 ^ n - 1) = 2 by omega] at hsub
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have h := rk2_twA_pRank_le (X := StatedSU 6 (2 ^ n) F) (ℓ := 5) (n := n) (q := p)
    (hasLabel_statedSU_six hn F hF) (exceptionalOrders_PSU_six_eq_one hn) hp hp2 hpnot
  simpa using h

private theorem evenRank_statedSU_six_eq_four {n p : ℕ} (F : Type) [Field F] [Finite F]
    [CharP F 2] (hn : 2 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpdvd : p ∣ 2 ^ n - 1) (he : 4 ≤ evenRank (StatedSU 6 (2 ^ n) F))
    (hr : GLATwoLocalRank p (StatedSU 6 (2 ^ n) F) + 1 =
      evenRank (StatedSU 6 (2 ^ n) F)) :
    evenRank (StatedSU 6 (2 ^ n) F) = 4 := by
  have hle : GLATwoLocalRank p (StatedSU 6 (2 ^ n) F) ≤ 3 :=
    (CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_pRank p hp
      (StatedSU 6 (2 ^ n) F)).trans (pRank_statedSU_six_le_three F hn hF hp hp2 hpdvd)
  omega

private theorem dvd_card_quot_center_statedSU_six {n p : ℕ} (F : Type) [Field F] [Finite F]
    [CharP F 2] (hn : 2 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2) (hodd : Odd n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpdvd : p ∣ 2 ^ n - 1)
    (hZ3 : 3 ∣ Nat.card (Subgroup.center (StatedSU 6 (2 ^ n) F))) :
    p * 3 ∣ Nat.card ((StatedSU 6 (2 ^ n) F) ⧸
      Subgroup.center (StatedSU 6 (2 ^ n) F)) := by
  have hRlab : HasLabel (StatedSU 6 (2 ^ n) F)
      (fun l : GLALabel => l = ⟨.twA, 5, n⟩) := hasLabel_statedSU_six hn F hF
  have hG : CFSG.Open.GriessAllModelsStatement :=
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have hmult := unitarySix_mult (n := n) hn hRlab hG hZ3
  have hpdvd2 : p ∣ 2 ^ (2 * n) - 1 := by
    have hfac : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      rw [show 2 ^ (2 * n) = (2 ^ n) ^ 2 by rw [pow_two, ← pow_add]; congr 1; ring]
      simpa using (Nat.sq_sub_sq (2 ^ n) 1)
    rw [hfac]
    exact dvd_mul_of_dvd_right hpdvd _
  have h3dvd2 : 3 ∣ 2 ^ (2 * n) - 1 := by
    have hfac : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      rw [show 2 ^ (2 * n) = (2 ^ n) ^ 2 by rw [pow_two, ← pow_add]; congr 1; ring]
      simpa using (Nat.sq_sub_sq (2 ^ n) 1)
    obtain ⟨k, hk⟩ := CFSG.SignalizerFunctorTheorem.McBride.PSL2Even.three_dvd_pow_add_one hodd
    rw [hfac, hk]
    exact ⟨k * (2 ^ n - 1), by ring⟩
  have hpd : p ∣ Nat.card ((StatedSU 6 (2 ^ n) F) ⧸
      Subgroup.center (StatedSU 6 (2 ^ n) F)) := hmult.2.2.2 p hp hp2 hpdvd2
  have h3d : 3 ∣ Nat.card ((StatedSU 6 (2 ^ n) F) ⧸
      Subgroup.center (StatedSU 6 (2 ^ n) F)) :=
    hmult.2.2.2 3 Nat.prime_three (by norm_num) h3dvd2
  have hp3 : p ≠ 3 := by
    intro h
    subst h
    exact CFSG.SignalizerFunctorTheorem.McBride.PSL2Even.not_three_dvd_pow_sub_one hodd hpdvd
  have hcop : Nat.Coprime p 3 := (Nat.Prime.coprime_iff_not_dvd hp).2 (by
    intro hd
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd))
  exact hcop.mul_dvd_of_dvd_of_dvd hpd h3d

private theorem shape_statedSU_six {n : ℕ} (F : Type) [Field F] [Finite F] [CharP F 2]
    (hn : 2 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2)
    (he : 4 ≤ evenRank (StatedSU 6 (2 ^ n) F))
    (hZ3 : 3 ∣ Nat.card (Subgroup.center (StatedSU 6 (2 ^ n) F))) :
    ∀ lab : GLALabel, HasLabel (StatedSU 6 (2 ^ n) F) (fun l : GLALabel => l = lab) →
      JShape lab (3 ∣ Nat.card (Subgroup.center (StatedSU 6 (2 ^ n) F))) ⟨.twA, 5, n⟩ := by
  intro lab hlab
  have hRlab : HasLabel (StatedSU 6 (2 ^ n) F)
      (fun l : GLALabel => l = ⟨.twA, 5, n⟩) := hasLabel_statedSU_six hn F hF
  have hEq : lab = ⟨.twA, 5, n⟩ := by
    rcases label_eq_or_BC (K := StatedSU 6 (2 ^ n) F) he hlab hRlab with h | ⟨-, h2, -⟩
    · exact h
    · exact absurd h2 (by simp)
  subst hEq
  exact ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨rfl, rfl, hZ3, rfl, rfl⟩))))))⟩

private theorem center_odd_and_twoRank_statedSU_six {n : ℕ} (F : Type) [Field F] [Finite F]
    [CharP F 2] (hn : 2 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2) (hodd : Odd n)
    (hZ3 : 3 ∣ Nat.card (Subgroup.center (StatedSU 6 (2 ^ n) F)))
    (hR4 : evenRank (StatedSU 6 (2 ^ n) F) = 4) :
    Odd (Nat.card (Subgroup.center ↥(⊤ : Subgroup (StatedSU 6 (2 ^ n) F)))) ∧
      evenRank (StatedSU 6 (2 ^ n) F) + 2 ≤
        twoRank ↥(⊤ : Subgroup (StatedSU 6 (2 ^ n) F)) := by
  have hRlab : HasLabel (StatedSU 6 (2 ^ n) F)
      (fun l : GLALabel => l = ⟨.twA, 5, n⟩) := hasLabel_statedSU_six hn F hF
  have hG : CFSG.Open.GriessAllModelsStatement :=
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have hmult := unitarySix_mult (n := n) hn hRlab hG hZ3
  have hoddZ : Odd (Nat.card (Subgroup.center (StatedSU 6 (2 ^ n) F))) := hmult.2.1
  have h9 : 9 * n ≤ twoRank (StatedSU 6 (2 ^ n) F) := hmult.2.2.1
  have hcenterodd : Odd (Nat.card (Subgroup.center ↥(⊤ : Subgroup
      (StatedSU 6 (2 ^ n) F)))) := by
    have hc : Nat.card (Subgroup.center ↥(⊤ : Subgroup (StatedSU 6 (2 ^ n) F))) =
        Nat.card (Subgroup.center (StatedSU 6 (2 ^ n) F)) :=
      (card_center_congr (Subgroup.topEquiv : ↥(⊤ : Subgroup
        (StatedSU 6 (2 ^ n) F)) ≃* StatedSU 6 (2 ^ n) F)).symm
    rwa [hc]
  have hm2 : evenRank (StatedSU 6 (2 ^ n) F) + 2 ≤
      twoRank ↥(⊤ : Subgroup (StatedSU 6 (2 ^ n) F)) := by
    have htop : twoRank ↥(⊤ : Subgroup (StatedSU 6 (2 ^ n) F)) =
        twoRank (StatedSU 6 (2 ^ n) F) :=
      (twoRank_congr (Subgroup.topEquiv : ↥(⊤ : Subgroup
        (StatedSU 6 (2 ^ n) F)) ≃* StatedSU 6 (2 ^ n) F)).symm
    rw [htop, hR4]
    omega
  exact ⟨hcenterodd, hm2⟩

theorem twA5CoverModel_of_witness
    (hwit : ∀ (n p : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2],
      Odd n → 2 ≤ n → Nat.card F = (2 ^ n) ^ 2 → TwA5CoverWitness n p F) :
    TwA5CoverModel := by
  unfold TwA5CoverModel
  intro n p F _ _ _ hF hodd hn hp hp2 hpdvd he hr
  classical
  have hG : CFSG.Open.GriessAllModelsStatement :=
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  obtain ⟨B, x, E, S, hxZ, hxB, hx1, hBelem, hBcard, hEB, hEelem, hEcard, hxE, he3,
    hS2, hBS, hBC⟩ := hwit n p F hodd hn hF
  have hRlab : HasLabel (StatedSU 6 (2 ^ n) F)
      (fun l : GLALabel => l = ⟨.twA, 5, n⟩) := hasLabel_statedSU_six hn F hF
  have hZcard : Nat.card (Subgroup.center (StatedSU 6 (2 ^ n) F)) = 3 :=
    card_center_statedSU_six F hF hodd
  have hZ3 : 3 ∣ Nat.card (Subgroup.center (StatedSU 6 (2 ^ n) F)) := by
    rw [hZcard]
  have hR4 := evenRank_statedSU_six_eq_four (F := F) hn hF hp hp2 hpdvd he hr
  have hmult := unitarySix_mult (n := n) hn hRlab hG hZ3
  have hoddn : Odd n := hmult.1
  have hoddZ : Odd (Nat.card (Subgroup.center (StatedSU 6 (2 ^ n) F))) := hmult.2.1
  have h9 : 9 * n ≤ twoRank (StatedSU 6 (2 ^ n) F) := hmult.2.2.1
  have hdvdR := dvd_card_quot_center_statedSU_six (F := F) hn hF hodd hp hp2 hpdvd hZ3
  have hrankB : Nat.card B = 3 ^ evenRank (StatedSU 6 (2 ^ n) F) := by
    rw [hBcard, hR4]
  obtain ⟨hcenterodd, hm2⟩ := center_odd_and_twoRank_statedSU_six F hn hF hodd hZ3 hR4
  have hdvd : p * 3 ∣ Nat.card (↥(⊤ : Subgroup (StatedSU 6 (2 ^ n) F)) ⧸
      Subgroup.center ↥(⊤ : Subgroup (StatedSU 6 (2 ^ n) F))) := by
    rw [← card_quot_center_congr (Subgroup.topEquiv : ↥(⊤ : Subgroup
      (StatedSU 6 (2 ^ n) F)) ≃* StatedSU 6 (2 ^ n) F)]
    exact hdvdR
  have htoplab : HasLabel ↥(⊤ : Subgroup (StatedSU 6 (2 ^ n) F))
      (fun l : GLALabel => l = ⟨.twA, 5, n⟩) :=
    (hasLabel_congr (Subgroup.topEquiv : ↥(⊤ : Subgroup
      (StatedSU 6 (2 ^ n) F)) ≃* StatedSU 6 (2 ^ n) F)
      (fun l : GLALabel => l = ⟨.twA, 5, n⟩)).2 hRlab
  have hshape := shape_statedSU_six (F := F) hn hF he hZ3
  have hxcent : x ∈ Subgroup.center (StatedSU 6 (2 ^ n) F) := hxZ
  have hJx : (⊤ : Subgroup (StatedSU 6 (2 ^ n) F)) ≤
      Subgroup.centralizer ({x} : Set (StatedSU 6 (2 ^ n) F)) := by
    intro g _
    exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_center_iff.1 hxZ g)
  have htopq : CFSG.IsQuasisimple ↥(⊤ : Subgroup (StatedSU 6 (2 ^ n) F)) :=
    CFSG.IsQuasisimple.of_mulEquiv (Subgroup.topEquiv : ↥(⊤ : Subgroup
      (StatedSU 6 (2 ^ n) F)) ≃* StatedSU 6 (2 ^ n) F) (isQuasisimple_statedSU_six F hF)
  have hcomm : ∀ g ∈ Subgroup.centralizer ({x} : Set (StatedSU 6 (2 ^ n) F)),
      ∀ h ∈ Subgroup.centralizer ({x} : Set (StatedSU 6 (2 ^ n) F)),
      g * h * g⁻¹ * h⁻¹ ∈ (⊤ : Subgroup (StatedSU 6 (2 ^ n) F)) :=
    fun _ _ _ _ => Subgroup.mem_top _
  have hrankinf : evenRank (StatedSU 6 (2 ^ n) F) ≤
      CFSG.Open.pRank 3 (B ⊓ ⊤) + 2 := by
    have hBtop : B ⊓ (⊤ : Subgroup (StatedSU 6 (2 ^ n) F)) = B := inf_top_eq B
    have hBelem' : IsElemAbelian 3 (⊤ ⊓ B : Subgroup (StatedSU 6 (2 ^ n) F)) := by
      rw [top_inf_eq]; exact hBelem
    have hle : 4 ≤ CFSG.Open.pRank 3 (⊤ ⊓ B : Subgroup (StatedSU 6 (2 ^ n) F)) := by
      refine CFSG.SectionRank.le_pRank (by norm_num) le_rfl hBelem' ?_
      rw [top_inf_eq, hBcard]
    rw [hR4, inf_comm]
    omega
  have hsix : (Subgroup.center ↥(⊤ : Subgroup (StatedSU 6 (2 ^ n) F)) = ⊥ ∧
      TrivialMultiplierT ↥(⊤ : Subgroup (StatedSU 6 (2 ^ n) F))) ∨
      (evenRank (StatedSU 6 (2 ^ n) F) = 4 ∧
        ∃ labJ : GLALabel, HasLabel ↥(⊤ : Subgroup (StatedSU 6 (2 ^ n) F))
          (fun l : GLALabel => l = labJ) ∧ labJ.tag = .twA ∧ labJ.rank = 4 ∧ Even labJ.n) ∨
      ((⊤ : Subgroup (StatedSU 6 (2 ^ n) F)) = ⊤ ∧
        3 ∣ Nat.card (Subgroup.center (StatedSU 6 (2 ^ n) F)) ∧ ∃ lab : GLALabel,
        HasLabel (StatedSU 6 (2 ^ n) F) (fun l : GLALabel => l = lab) ∧ Odd lab.n ∧
        ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)) :=
    Or.inr (Or.inr ⟨rfl, hZ3, ⟨.twA, 5, n⟩, hRlab, hoddn, Or.inl ⟨rfl, rfl⟩⟩)
  have hsu : 3 ∣ Nat.card (Subgroup.center (StatedSU 6 (2 ^ n) F)) →
      (∃ lab : GLALabel, HasLabel (StatedSU 6 (2 ^ n) F)
        (fun l : GLALabel => l = lab) ∧
        ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)) →
      (⊤ : Subgroup (StatedSU 6 (2 ^ n) F)) = ⊤ ∧ 3 = 3 ∧
        ∀ k : StatedSU 6 (2 ^ n) F, k * x = x * k :=
    fun _ _ => ⟨rfl, rfl, fun k => Subgroup.mem_center_iff.1 hxZ k⟩
  refine ⟨3, B, x, ⊤, concl166S_of_witness (K := StatedSU 6 (2 ^ n) F) (p := p) (q := 3)
    (B := B) (x := x) (J := ⊤) Nat.prime_three (by norm_num) hBelem hxB hx1 hrankB he
    hJx htopq hcomm ⟨.twA, 5, n⟩ htoplab hshape hm2 hcenterodd hdvd hsix E hEB hEelem
    hEcard hxE he3 (fun b _ => Subgroup.mem_sup_left (Subgroup.mem_top b)) hrankinf S le_top
    hS2 hBS (by simpa only [inf_top_eq] using hBC.le) hsu⟩

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
