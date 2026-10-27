module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Build
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6B10
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Arithmetic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open


theorem exists_concl166S_twE6_of_caseB_data
    {X : Type} [Group X] [Finite X] {lab : GLALabel} {p : ℕ}
    (hX : HasLabel X (fun l => l = lab)) (ht : lab.tag = .twE6) (hn : 2 ≤ lab.n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpdvd : p ∣ 2 ^ lab.n - 1)
    (hr : GLATwoLocalRank p X + 1 = evenRank X) (hZ : Subgroup.center X ≠ ⊥)
    {z : X} (hzZ : Subgroup.center X = Subgroup.zpowers z) (hz3 : orderOf z = 3)
    {B E S : Subgroup X} (hzB : z ∈ B) (hBelem : IsElemAbelian 3 B)
    (hBcard : Nat.card B = 3 ^ 5) (hEB : E ≤ B) (hEelem : IsElemAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ 3) (hzE : z ∈ E)
    (he3 : GLAPLayer 3 ((⊤ : Subgroup X) ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥)
    (hS2 : IsPGroup 2 S) (hBS : B ≤ Subgroup.normalizer (S : Set X))
    (hBC : B ⊓ Subgroup.centralizer (S : Set X) = Subgroup.zpowers z) :
    ∃ (q : ℕ) (B' : Subgroup X) (x' : X) (J : Subgroup X), Concl166S X p q B' x' J := by
  classical
  obtain ⟨hZcard, -, hoddn, -⟩ := twE6_caseB_arith hX ht hn hZ
  have h5 : evenRank X = 5 := evenRank_eq_five_of_center_ne_bot hX ht hn hp hp2 hpdvd hr hZ
  have he4 : 4 ≤ evenRank X := by omega
  have hZ3 : 3 ∣ Nat.card (Subgroup.center X) := by rw [hZcard]
  have hzZmem : z ∈ Subgroup.center X := by
    rw [hzZ]
    exact Subgroup.mem_zpowers z
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz3
    omega
  have hJq : CFSG.IsQuasisimple ↥(⊤ : Subgroup X) :=
    CFSG.IsQuasisimple.of_mulEquiv (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X)
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr (rk2_model_of_isLabel hX).1)
  have hJx : (⊤ : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X) := by
    intro g _
    exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_center_iff.1 hzZmem g)
  have hcomm : ∀ g ∈ Subgroup.centralizer ({z} : Set X),
      ∀ h ∈ Subgroup.centralizer ({z} : Set X),
      g * h * g⁻¹ * h⁻¹ ∈ (⊤ : Subgroup X) :=
    fun _ _ _ _ => Subgroup.mem_top _
  have htoplab : HasLabel ↥(⊤ : Subgroup X) (fun l : GLALabel => l = lab) :=
    (hasLabel_congr (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X)
      (fun l : GLALabel => l = lab)).2 hX
  have hshape : ∀ lab' : GLALabel, HasLabel X (fun l : GLALabel => l = lab') →
      JShape lab' (3 ∣ Nat.card (Subgroup.center X)) lab := by
    intro lab' hlab'
    rcases label_eq_or_BC (K := X) he4 hlab' hX with h | ⟨-, h2, -⟩
    · subst h
      exact ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨ht, hZ3, ht⟩))))))))⟩
    · exact absurd h2 (by simp [ht])
  have htwo : twoRank ↥(⊤ : Subgroup X) = twoRank X :=
    (twoRank_congr (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X)).symm
  have h11 : 11 * lab.n ≤ twoRank X :=
    eleven_mul_le_twoRank_of_isLabel_twE6 hX ht hn (by rw [hZcard]; norm_num)
  have hm2 : evenRank X + 2 ≤ twoRank ↥(⊤ : Subgroup X) := by
    rw [htwo, h5]
    omega
  have hcenterodd : Odd (Nat.card (Subgroup.center ↥(⊤ : Subgroup X))) := by
    have hc : Nat.card (Subgroup.center ↥(⊤ : Subgroup X)) =
        Nat.card (Subgroup.center X) :=
      (card_center_congr (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X)).symm
    rw [hc, hZcard]
    norm_num
  have hsix : (Subgroup.center ↥(⊤ : Subgroup X) = ⊥ ∧
      TrivialMultiplierT ↥(⊤ : Subgroup X)) ∨
      (evenRank X = 4 ∧ ∃ labJ : GLALabel,
        HasLabel ↥(⊤ : Subgroup X) (fun l : GLALabel => l = labJ) ∧
        labJ.tag = .twA ∧ labJ.rank = 4 ∧ Even labJ.n) ∨
      ((⊤ : Subgroup X) = ⊤ ∧ 3 ∣ Nat.card (Subgroup.center X) ∧ ∃ lab : GLALabel,
        HasLabel X (fun l : GLALabel => l = lab) ∧ Odd lab.n ∧
        ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)) :=
    Or.inr (Or.inr ⟨rfl, hZ3, lab, hX, hoddn, Or.inr ht⟩)
  have hrankinf : evenRank X ≤ CFSG.Open.pRank 3 (B ⊓ (⊤ : Subgroup X)) + 2 := by
    have hBelem' : IsElemAbelian 3 ((⊤ : Subgroup X) ⊓ B) := by
      rw [top_inf_eq]
      exact hBelem
    have hle : 5 ≤ CFSG.Open.pRank 3 ((⊤ : Subgroup X) ⊓ B) := by
      refine CFSG.SectionRank.le_pRank (p := 3) (H := (⊤ : Subgroup X) ⊓ B)
        (E := (⊤ : Subgroup X) ⊓ B) (by norm_num) le_rfl hBelem' ?_
      rw [top_inf_eq, hBcard]
    rw [h5, inf_comm]
    omega
  have hBJS : B ⊓ (⊤ : Subgroup X) ⊓ Subgroup.centralizer (S : Set X) ≤
      Subgroup.zpowers z := by
    simpa only [inf_top_eq] using hBC.le
  have hsu : 3 ∣ Nat.card (Subgroup.center X) →
      (∃ lab : GLALabel, HasLabel X (fun l : GLALabel => l = lab) ∧
        ((lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)) →
      (⊤ : Subgroup X) = ⊤ ∧ 3 = 3 ∧ ∀ k : X, k * z = z * k :=
    fun _ _ => ⟨rfl, rfl, fun k => Subgroup.mem_center_iff.1 hzZmem k⟩
  have hdvd : p * 3 ∣ Nat.card
      (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X)) := by
    rw [← card_quot_center_congr (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X)]
    have hpos : 0 < CFSG.RankThreeEvenClassification.Helpers.twoLocalRank p X := by
      change 0 < GLATwoLocalRank p X
      omega
    have hpX : p ∣ Nat.card X :=
      CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_positive_prime_dvd p hp X hpos
    have hcardX : Nat.card X = 3 * Nat.card (X ⧸ Subgroup.center X) := by
      calc Nat.card X = Nat.card (X ⧸ Subgroup.center X) *
            Nat.card ↥(Subgroup.center X) :=
            Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
        _ = Nat.card (X ⧸ Subgroup.center X) * 3 := by rw [hZcard]
        _ = 3 * Nat.card (X ⧸ Subgroup.center X) := by rw [mul_comm]
    have hp3 : p ≠ 3 := by
      intro h
      subst h
      exact CFSG.SignalizerFunctorTheorem.McBride.PSL2Even.not_three_dvd_pow_sub_one
        hoddn hpdvd
    have hcop : Nat.Coprime p 3 :=
      (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd =>
        hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd)
    have hpQ : p ∣ Nat.card (X ⧸ Subgroup.center X) := by
      have h := hpX
      rw [hcardX] at h
      exact hcop.dvd_of_dvd_mul_left h
    have h3Q : 3 ∣ Nat.card (X ⧸ Subgroup.center X) := by
      have hBdvd : 3 ^ 5 ∣ Nat.card X := by
        rw [← hBcard]
        exact Subgroup.card_subgroup_dvd_card B
      have h34 : 3 ^ 4 ∣ Nat.card (X ⧸ Subgroup.center X) := by
        have h : 3 * 3 ^ 4 ∣ 3 * Nat.card (X ⧸ Subgroup.center X) := by
          rw [(pow_succ' 3 4).symm, ← hcardX]
          exact hBdvd
        exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 3)).mp h
      exact (show 3 ∣ 3 ^ 4 from ⟨3 ^ 3, by norm_num⟩).trans h34
    exact hcop.mul_dvd_of_dvd_of_dvd hpQ h3Q
  exact ⟨3, B, z, ⊤, concl166S_of_witness (K := X) (p := p) (q := 3) (B := B) (x := z)
    (J := ⊤) Nat.prime_three (by norm_num) hBelem hzB hz1 (by rw [hBcard, h5]) he4 hJx hJq
    hcomm lab htoplab hshape hm2 hcenterodd hdvd hsix E hEB hEelem hEcard hzE he3
    (fun b _ => Subgroup.mem_sup_left (Subgroup.mem_top b)) hrankinf S le_top hS2 hBS hBJS hsu⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F

end
