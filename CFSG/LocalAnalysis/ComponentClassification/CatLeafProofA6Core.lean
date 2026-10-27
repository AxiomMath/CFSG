module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.Fischer.Classification.Recognition.PSU6

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open scoped MatrixGroups

@[expose] def A6CentreForm (G : Type) [Group G] : Prop :=
  ∀ L : Subgroup G, IsComponent L → Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 6)) →
    IsPGroup 2 (center L)

theorem a6CentreForm_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : A6CentreForm H) : A6CentreForm G := by
  rintro L hL ⟨eA⟩
  let eL : L ≃* L.map e.toMonoidHom := L.equivMapOfInjective _ e.injective
  have h1 := h _ (LocalCores.isComponent_map_mulEquiv e hL)
    ⟨(QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)).symm.trans eA⟩
  exact h1.of_equiv (Subgroup.centerCongr eL).symm

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem isPGroup_center_SL (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    IsPGroup 2 (center SL(2, F)) := by
  intro z
  refine ⟨1, ?_⟩
  obtain ⟨r, hr, hz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp z.2
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hz2 : (z : SL(2, F)) ^ 2 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hz, Matrix.SpecialLinearGroup.coe_one,
      ← map_pow (Matrix.scalar (Fin 2)), hr2, map_one]
  exact Subtype.ext (by rw [pow_one, SubgroupClass.coe_pow, hz2]; rfl)

theorem isPGroup_center_of_mulEquiv_SL {L : Type*} [Group L] {F : Type*} [Field F] [Finite F]
    (e : L ≃* SL(2, F)) : IsPGroup 2 (center L) := by
  classical
  have := Fintype.ofFinite F
  exact (isPGroup_center_SL F).of_equiv (Subgroup.centerCongr e).symm

theorem isPGroup_center_of_center_eq_bot {L : Type*} [Group L] (h : center L = ⊥) :
    IsPGroup 2 (center L) := by
  rw [h]
  exact IsPGroup.of_bot

theorem lieSylowExponent_ge_three {τ : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible τ n p f) (hp2 : p ≠ 2) :
    (τ = .PSL ∧ n = 2) ∨ 3 ≤ lieSylowExponent τ n := by
  obtain ⟨-, -, h⟩ := hadm
  cases τ with
  | PSL =>
    obtain ⟨h2, -⟩ := h
    rcases Nat.lt_or_ge n 3 with hn | hn
    · exact Or.inl ⟨rfl, by omega⟩
    · right
      change 3 ≤ n * (n - 1) / 2
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      exact Nat.mul_le_mul hn (by omega)
  | PSU =>
    obtain ⟨hn, -⟩ := h
    right
    change 3 ≤ n * (n - 1) / 2
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    exact Nat.mul_le_mul hn (by omega)
  | PSp =>
    obtain ⟨hn, -⟩ := h
    right
    change 3 ≤ n ^ 2
    nlinarith
  | POmegaOdd =>
    obtain ⟨hn, -⟩ := h
    right
    change 3 ≤ n ^ 2
    nlinarith
  | POmegaPlus =>
    right
    change 3 ≤ n * (n - 1)
    exact le_trans (by norm_num) (Nat.mul_le_mul (h : 4 ≤ n) (by omega : 3 ≤ n - 1))
  | POmegaMinus =>
    right
    change 3 ≤ n * (n - 1)
    exact le_trans (by norm_num) (Nat.mul_le_mul (h : 4 ≤ n) (by omega : 3 ≤ n - 1))
  | twistedB2 => exact absurd h.2.1 hp2
  | G2 => exact Or.inr (by simp only [lieSylowExponent]; norm_num)
  | F4 => exact Or.inr (by simp only [lieSylowExponent]; norm_num)
  | E6 => exact Or.inr (by simp only [lieSylowExponent]; norm_num)
  | E7 => exact Or.inr (by simp only [lieSylowExponent]; norm_num)
  | E8 => exact Or.inr (by simp only [lieSylowExponent]; norm_num)
  | twistedE6 => exact Or.inr (by simp only [lieSylowExponent]; norm_num)
  | trialityD4 => exact Or.inr (by simp only [lieSylowExponent]; norm_num)
  | twistedG2 => exact Or.inr (by simp only [lieSylowExponent]; norm_num)
  | twistedF4 => exact Or.inr (by simp only [lieSylowExponent]; norm_num)
  | Tits => exact Or.inr (by simp only [lieSylowExponent]; norm_num)

theorem lieModel_of_card_360
    {X : Type} [Group X] {τ : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible τ n p f)
    (hp2 : p ≠ 2) (hm : Blueprint.LieModel X τ n p f) (hX : Nat.card X = 360) :
    τ = .PSL ∧ n = 2 ∧ p = 3 ∧ f = 2 := by
  obtain ⟨-, hmul, hfac⟩ := lieOrderFormulasInput X τ n p f hadm hm
  have hp := hadm.1
  have hf := hadm.2.1
  rw [hX] at hmul hfac
  have hdvd : p ^ (lieSylowExponent τ n * f) ∣ 360 := by
    rw [← hfac]
    exact Nat.ordProj_dvd 360 p
  rcases lieSylowExponent_ge_three hadm hp2 with ⟨rfl, rfl⟩ | h3
  ·
    refine ⟨rfl, rfl, ?_⟩
    obtain ⟨q, hq⟩ : ∃ q, p ^ f = q := ⟨_, rfl⟩
    simp only [lieOrderDivisor, lieOrderNumerator, Finset.Icc_self, Finset.prod_singleton,
      hq] at hmul
    have hqodd : Odd q := hq ▸ (hp.odd_of_ne_two hp2).pow
    have hg : Nat.gcd 2 (q - 1) = 2 :=
      Nat.gcd_eq_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hqodd odd_one))
    rw [hg, show 2 * (2 - 1) / 2 = 1 from rfl, pow_one] at hmul
    obtain ⟨s, hs⟩ : ∃ s, q ^ 2 = s := ⟨_, rfl⟩
    rw [hs] at hmul
    have hsq : s = q * q := by rw [← hs, sq]
    have hq9 : q ≤ 9 := by
      by_contra hlt
      push Not at hlt
      have h1 : 100 ≤ s := by rw [hsq]; nlinarith
      have h2 : 10 * 99 ≤ q * (s - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    have hq9' : q = 9 := by
      interval_cases q <;> simp_all
    have hp3 : p = 3 := by
      have hpd : p ∣ 3 ^ 2 := by
        rw [show (3 : ℕ) ^ 2 = 9 from rfl, ← hq9', ← hq]
        exact dvd_pow_self p (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hpd)
    subst hp3
    refine ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3) ?_⟩
    change 3 ^ f = 3 ^ 2
    rw [hq, hq9']
  · exfalso
    have h3f : 3 ≤ lieSylowExponent τ n * f := le_trans h3 (Nat.le_mul_of_pos_right _ hf)
    have h27 : p ^ 3 ∣ 360 := (pow_dvd_pow p h3f).trans hdvd
    have hp7 : p ≤ 7 := by
      by_contra hlt
      push Not at hlt
      have h1 : 8 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hlt 3
      have h2 := Nat.le_of_dvd (by norm_num) h27
      omega
    interval_cases p <;> revert hp hp2 h27 <;> decide

theorem lieModel_of_a6
    {L : Type} [Group L] (hA : Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 6)))
    {τ : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible τ n p f) (hp2 : p ≠ 2)
    (hm : Blueprint.LieModel (L ⧸ center L) τ n p f) : τ = .PSL ∧ n = 2 ∧ p = 3 ∧ f = 2 := by
  obtain ⟨eA⟩ := hA
  exact lieModel_of_card_360 hadm hp2 hm
    (by rw [Nat.card_congr eA.toEquiv, card_alternatingGroup_six])

end CFSG.ComponentClassification.CatLeafProof
