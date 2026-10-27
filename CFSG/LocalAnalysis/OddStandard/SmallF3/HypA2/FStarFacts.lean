module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LeavesV
public import CFSG.Blueprint.LieModelAPI
public import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification CFSG.Open

private theorem exists_noncomm_of_simple_of_four_dvd {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (h : 2 ^ 2 ∣ Nat.card G) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  haveI : IsMulCommutative G := ⟨⟨fun a b => hcon a b⟩⟩
  have hprime : (Nat.card G).Prime := Group.is_simple_iff_prime_card.mp inferInstance
  have hpd : 2 ∣ Nat.card G := (dvd_pow_self 2 (by norm_num)).trans h
  rcases (Nat.dvd_prime hprime).1 hpd with h1 | h1
  · exact one_lt_two.ne' h1
  · rw [← h1] at h
    have h2 := Nat.le_of_dvd (by norm_num : 0 < 2) h
    omega

private theorem center_eq_bot_of_simple' {G : Type} [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (mem_center_iff.mp (h ▸ mem_top b) a)

private theorem center_eq_bot_of_lieModel {Q : Type} [Group Q] {t : StatedLieTag} {n p f : ℕ}
    (hn : n ≠ 0) (h : LieModel Q t n p f) (h4 : 4 ∣ Nat.card Q) : center Q = ⊥ := by
  obtain ⟨hfin, -, hsimp⟩ :=
    CFSG.LieType.Simplicity.fam_classical_converse Q
      ⟨t, n, p, f, GH74.statedClassicalModel_of_lieModel hn h⟩
  haveI : Finite Q := hfin
  haveI : IsSimpleGroup Q := hsimp
  exact center_eq_bot_of_simple' (exists_noncomm_of_simple_of_four_dvd (by simpa using h4))

private theorem lieModel_fusionZStar_of_lieModel {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ} (hn : n ≠ 0) (h : LieModel (X ⧸ pPrimeCore 2 X) t n p f)
    (h4 : 4 ∣ Nat.card (X ⧸ pPrimeCore 2 X)) :
    LieModel (X ⧸ Open.fusionZStar X) t n p f :=
  LieModel.of_mulEquiv (Sol78.coreQuotientCenterEquiv X)
    (LieModel.quotient_center (center_eq_bot_of_lieModel hn h h4) h)

private theorem smallF3OmegaQuotient_of_mulEquiv {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (h : SmallF3OmegaQuotient A) : SmallF3OmegaQuotient B := by
  unfold SmallF3OmegaQuotient at h ⊢
  rcases h with h1 | h2 | h3 | h4 | h5 | h6
  · exact Or.inl (LieModel.of_mulEquiv e h1)
  · exact Or.inr (Or.inl (LieModel.of_mulEquiv e h2))
  · exact Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e h3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e h4))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e h5)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (LieModel.of_mulEquiv e h6)))))

private theorem center_eq_bot_of_smallF3OmegaQuotient {Q : Type} [Group Q]
    (h : SmallF3OmegaQuotient Q) : center Q = ⊥ := by
  unfold SmallF3OmegaQuotient at h
  rcases h with h | h | h | h | h | h
  · exact center_eq_bot_of_lieModel (by norm_num) h
      (by rw [GH74.card_of_lieModel_PSp (G := Q) (n := 2) (p := 3) (f := 1) (by norm_num)
        (by norm_num) h]; decide)
  · exact center_eq_bot_of_lieModel (by norm_num) h
      (by rw [GH74.card_of_lieModel_PSL (G := Q) (n := 4) (p := 3) (f := 1) (by norm_num) h]
          decide)
  · exact center_eq_bot_of_lieModel (by norm_num) h
      (by rw [GH74.card_of_lieModel_PSU (G := Q) (n := 4) (p := 3) (f := 1) (by norm_num)
        (by norm_num) h]; decide)
  · have hcard : Nat.card Q = ordBC 3 (3 ^ 1) :=
      (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q) (t := .POmegaOdd)
        (n := 3) (p := 3) (f := 1) (by norm_num)
        (GH74.statedClassicalModel_of_lieModel (G := Q) (t := .POmegaOdd) (n := 3) (p := 3)
          (f := 1) (by norm_num) h)).2.2.2.1 rfl
    exact center_eq_bot_of_lieModel (by norm_num) h (by rw [hcard]; decide)
  · have hcard : Nat.card Q = ordD 4 (3 ^ 1) :=
      (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q) (t := .POmegaPlus)
        (n := 4) (p := 3) (f := 1) (by norm_num)
        (GH74.statedClassicalModel_of_lieModel (G := Q) (t := .POmegaPlus) (n := 4) (p := 3)
          (f := 1) (by norm_num) h)).2.2.2.2.1 rfl
    exact center_eq_bot_of_lieModel (by norm_num) h (by rw [hcard]; decide)
  · have hcard : Nat.card Q = ordTwistedD 4 (3 ^ 1) :=
      (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q) (t := .POmegaMinus)
        (n := 4) (p := 3) (f := 1) (by norm_num)
        (GH74.statedClassicalModel_of_lieModel (G := Q) (t := .POmegaMinus) (n := 4) (p := 3)
          (f := 1) (by norm_num) h)).2.2.2.2.2 rfl
    exact center_eq_bot_of_lieModel (by norm_num) h (by rw [hcard]; decide)

private theorem smallF3OmegaQuotient_center_quotient {Q : Type} [Group Q]
    (h : SmallF3OmegaQuotient Q) : SmallF3OmegaQuotient (Q ⧸ center Q) := by
  have hc := center_eq_bot_of_smallF3OmegaQuotient h
  unfold SmallF3OmegaQuotient at h ⊢
  rcases h with h1 | h2 | h3 | h4 | h5 | h6
  · exact Or.inl (LieModel.quotient_center hc h1)
  · exact Or.inr (Or.inl (LieModel.quotient_center hc h2))
  · exact Or.inr (Or.inr (Or.inl (LieModel.quotient_center hc h3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (LieModel.quotient_center hc h4))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (LieModel.quotient_center hc h5)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (LieModel.quotient_center hc h6)))))

private theorem fStarSimple_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : FStarSimple A) : FStarSimple B := by
  unfold FStarSimple at h ⊢
  rcases h with h1 | h2 | h3 | h4 | h5
  · exact Or.inl (LieModel.of_mulEquiv e h1)
  · exact Or.inr (Or.inl (LieModel.of_mulEquiv e h2))
  · exact Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e h3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e h4))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (smallF3OmegaQuotient_of_mulEquiv e h5))))

theorem fStarSimple_of_isFStar {X : Type} [Group X] [Finite X] (h : IsFStar X) :
    FStarSimple (X ⧸ Open.fusionZStar X) := by
  unfold IsFStar at h
  rcases h with h1 | h2 | h3 | h4 | h5 | ⟨_, h6⟩
  · exact Or.inl (lieModel_fusionZStar_of_lieModel (by norm_num) h1
      (by rw [GH74.card_of_lieModel_PSL (G := X ⧸ pPrimeCore 2 X) (n := 2) (p := 3) (f := 2)
        (by norm_num) h1]; decide))
  · exact Or.inr (Or.inl (lieModel_fusionZStar_of_lieModel (by norm_num) h2
      (by rw [GH74.card_of_lieModel_PSL (G := X ⧸ pPrimeCore 2 X) (n := 2) (p := 3) (f := 4)
        (by norm_num) h2]; decide)))
  · exact Or.inr (Or.inr (Or.inl (lieModel_fusionZStar_of_lieModel (by norm_num) h3
      (by rw [GH74.card_of_lieModel_PSL (G := X ⧸ pPrimeCore 2 X) (n := 3) (p := 3) (f := 1)
        (by norm_num) h3]; decide))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (lieModel_fusionZStar_of_lieModel (by norm_num) h4
      (by rw [GH74.card_of_lieModel_PSU (G := X ⧸ pPrimeCore 2 X) (n := 3) (p := 3) (f := 1)
        (by norm_num) (by norm_num) h4]; decide)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (smallF3OmegaQuotient_of_mulEquiv (Sol78.coreQuotientCenterEquiv X)
        (smallF3OmegaQuotient_center_quotient h5)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (LieModel.of_mulEquiv (Sol78.coreQuotientCenterEquiv X) h6)))))))

theorem fusionZStar_eq_center_of_pPrimeCore_eq_bot {K : Type} [Group K]
    (h : pPrimeCore 2 K = ⊥) : Open.fusionZStar K = center K := by
  rw [Sol78.fusionZStar_eq_comap K]
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_comap] at hx
    rw [mem_center_iff]
    intro y
    have h1 : QuotientGroup.mk' (pPrimeCore 2 K) (y * x) =
        QuotientGroup.mk' (pPrimeCore 2 K) (x * y) := by
      simpa only [map_mul] using mem_center_iff.mp hx (QuotientGroup.mk' (pPrimeCore 2 K) y)
    have h1' : ((y * x : K) : K ⧸ pPrimeCore 2 K) = (x * y : K) := by
      simpa only [QuotientGroup.mk'_apply] using h1
    have h2 : (y * x) / (x * y) ∈ pPrimeCore 2 K := QuotientGroup.eq_iff_div_mem.mp h1'
    rw [h, mem_bot, div_eq_mul_inv, mul_inv_eq_one] at h2
    exact h2
  · intro hx
    rw [Subgroup.mem_comap]
    rw [mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 K) q
    rw [← map_mul, ← map_mul, mem_center_iff.mp hx y]

theorem isFStar_of_fStarSimple {K : Type} [Group K] (hO : pPrimeCore 2 K = ⊥)
    (h : FStarSimple K) : IsFStar K := by
  unfold IsFStar
  let e : K ⧸ pPrimeCore 2 K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  rcases h with h1 | h2 | h3 | h4 | h5
  · exact Or.inl (LieModel.of_mulEquiv e.symm h1)
  · exact Or.inr (Or.inl (LieModel.of_mulEquiv e.symm h2))
  · exact Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e.symm h3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv e.symm h4))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (smallF3OmegaQuotient_of_mulEquiv e.symm h5)))))

theorem isSimpleChevalleyOver_three_of_fStarSimple {S : Type} [Group S] (h : FStarSimple S) :
    HarrisLit.IsSimpleChevalleyOver 3 S := by
  unfold HarrisLit.IsSimpleChevalleyOver
  unfold FStarSimple at h
  rcases h with h1 | h2 | h3 | h4 | h5
  · exact ⟨.PSL, 2, 2, h1⟩
  · exact ⟨.PSL, 2, 4, h2⟩
  · exact ⟨.PSL, 3, 1, h3⟩
  · exact ⟨.PSU, 3, 1, h4⟩
  · unfold SmallF3OmegaQuotient at h5
    rcases h5 with h | h | h | h | h | h
    · exact ⟨.PSp, 2, 1, h⟩
    · exact ⟨.PSL, 4, 1, h⟩
    · exact ⟨.PSU, 4, 1, h⟩
    · exact ⟨.POmegaOdd, 3, 1, h⟩
    · exact ⟨.POmegaPlus, 4, 1, h⟩
    · exact ⟨.POmegaMinus, 4, 1, h⟩

theorem false_of_fStarSimple_psl_two_seventeen {S : Type} [Group S] (h : FStarSimple S)
    (h17 : LieModel S .PSL 2 17 1) : False := by
  have h17dvd : 17 ∣ Nat.card S := by
    rw [GH74.card_of_lieModel_PSL (G := S) (n := 2) (p := 17) (f := 1) (by norm_num) h17]
    decide
  unfold FStarSimple at h
  rcases h with h1 | h2 | h3 | h4 | h5
  · have hc : ¬ 17 ∣ Nat.card S := by
      rw [GH74.card_of_lieModel_PSL (G := S) (n := 2) (p := 3) (f := 2) (by norm_num) h1]
      decide
    exact hc h17dvd
  · have hc : ¬ 17 ∣ Nat.card S := by
      rw [GH74.card_of_lieModel_PSL (G := S) (n := 2) (p := 3) (f := 4) (by norm_num) h2]
      decide
    exact hc h17dvd
  · have hc : ¬ 17 ∣ Nat.card S := by
      rw [GH74.card_of_lieModel_PSL (G := S) (n := 3) (p := 3) (f := 1) (by norm_num) h3]
      decide
    exact hc h17dvd
  · have hc : ¬ 17 ∣ Nat.card S := by
      rw [GH74.card_of_lieModel_PSU (G := S) (n := 3) (p := 3) (f := 1) (by norm_num)
        (by norm_num) h4]
      decide
    exact hc h17dvd
  · unfold SmallF3OmegaQuotient at h5
    rcases h5 with h | h | h | h | h | h
    · have hc : ¬ 17 ∣ Nat.card S := by
        rw [GH74.card_of_lieModel_PSp (G := S) (n := 2) (p := 3) (f := 1) (by norm_num)
          (by norm_num) h]
        decide
      exact hc h17dvd
    · have hc : ¬ 17 ∣ Nat.card S := by
        rw [GH74.card_of_lieModel_PSL (G := S) (n := 4) (p := 3) (f := 1) (by norm_num) h]
        decide
      exact hc h17dvd
    · have hc : ¬ 17 ∣ Nat.card S := by
        rw [GH74.card_of_lieModel_PSU (G := S) (n := 4) (p := 3) (f := 1) (by norm_num)
          (by norm_num) h]
        decide
      exact hc h17dvd
    · have hcard : Nat.card S = ordBC 3 (3 ^ 1) :=
        (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := S) (t := .POmegaOdd)
          (n := 3) (p := 3) (f := 1) (by norm_num)
          (GH74.statedClassicalModel_of_lieModel (G := S) (t := .POmegaOdd) (n := 3) (p := 3)
            (f := 1) (by norm_num) h)).2.2.2.1 rfl
      have hc : ¬ 17 ∣ Nat.card S := by rw [hcard]; decide
      exact hc h17dvd
    · have hcard : Nat.card S = ordD 4 (3 ^ 1) :=
        (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := S) (t := .POmegaPlus)
          (n := 4) (p := 3) (f := 1) (by norm_num)
          (GH74.statedClassicalModel_of_lieModel (G := S) (t := .POmegaPlus) (n := 4) (p := 3)
            (f := 1) (by norm_num) h)).2.2.2.2.1 rfl
      have hc : ¬ 17 ∣ Nat.card S := by rw [hcard]; decide
      exact hc h17dvd
    · have hcard : Nat.card S = ordTwistedD 4 (3 ^ 1) :=
        (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := S) (t := .POmegaMinus)
          (n := 4) (p := 3) (f := 1) (by norm_num)
          (GH74.statedClassicalModel_of_lieModel (G := S) (t := .POmegaMinus) (n := 4) (p := 3)
            (f := 1) (by norm_num) h)).2.2.2.2.2 rfl
      have hc : ¬ 17 ∣ Nat.card S := by rw [hcard]; decide
      exact hc h17dvd

theorem inChev2_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    GH74.GLS.InChev2 A ↔ GH74.GLS.InChev2 B :=
  ⟨GH74.E2.inChev2_of_mulEquiv e, GH74.E2.inChev2_of_mulEquiv e.symm⟩

theorem isSimpleChevalleyOver_congr {A B : Type} [Group A] [Group B] (r : ℕ) (e : A ≃* B) :
    HarrisLit.IsSimpleChevalleyOver r A ↔ HarrisLit.IsSimpleChevalleyOver r B := by
  unfold HarrisLit.IsSimpleChevalleyOver
  exact ⟨fun ⟨t, n, f, h⟩ => ⟨t, n, f, LieModel.of_mulEquiv e h⟩,
    fun ⟨t, n, f, h⟩ => ⟨t, n, f, LieModel.of_mulEquiv e.symm h⟩⟩

theorem fStarSimple_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    FStarSimple A ↔ FStarSimple B :=
  ⟨fStarSimple_of_mulEquiv e, fStarSimple_of_mulEquiv e.symm⟩

end CFSG.OddStandard.SmallF3.HypA2
