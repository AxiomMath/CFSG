module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Inv
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.RankThree.PartTwo.KFacts.KS21U34Unique
public import CFSG.LieType.Steinberg.CentralExt.Model

public section

namespace CFSG.ComponentClassification.HarrisLit.L33

open CFSG Subgroup

theorem not_harrisF_of_cyclic {Y : Type} [Group Y]
    (h : ∀ P : Subgroup Y, IsPGroup 3 P → IsCyclic P) : ¬ HarrisF 3 Y := by
  intro hY
  obtain ⟨-, -, P, hP, hc⟩ := harrisF_invariant hY
  exact hc (h P hP)

theorem cyclic_of_sylow {G : Type*} [Group G] [Finite G] [Fact (Nat.Prime 3)]
    (h : ∀ R : Sylow 3 G, IsCyclic R) (P : Subgroup G) (hP : IsPGroup 3 P) : IsCyclic P := by
  obtain ⟨R, hR⟩ := hP.exists_le_sylow
  have := h R
  exact Subgroup.isCyclic_of_le hR

theorem cyclic_of_not_nine_dvd {G : Type*} [Group G] [Finite G] (h9 : ¬ 9 ∣ Nat.card G)
    (P : Subgroup G) (hP : IsPGroup 3 P) : IsCyclic P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : 3 ^ k ∣ Nat.card G := hk ▸ Subgroup.card_subgroup_dvd_card P
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have h2 : 3 ^ 2 ∣ Nat.card G := (pow_dvd_pow 3 (by omega)).trans hdvd
    exact h9 (by simpa using h2)
  interval_cases k
  · have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
    infer_instance
  · exact isCyclic_of_prime_card (p := 3) (by simpa using hk)

theorem cyclic_of_mulEquiv {Y Z : Type} [Group Y] [Group Z] (e : Y ≃* Z)
    (h : ∀ Q : Subgroup Z, IsPGroup 3 Q → IsCyclic Q) (P : Subgroup Y) (hP : IsPGroup 3 P) :
    IsCyclic P := by
  have := h (P.map e.toMonoidHom) (hP.map _)
  exact isCyclic_of_surjective (P.equivMapOfInjective e.toMonoidHom e.injective).symm.toMonoidHom
    (MulEquiv.surjective _)

theorem cyclic_of_lieModel_psl2 {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp3 : p ≠ 3)
    (h : Blueprint.LieModel Y .PSL 2 p f) (P : Subgroup Y) (hP : IsPGroup 3 P) : IsCyclic P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hp, hf, h4, F, _, _, hF, ⟨e⟩⟩ := exists_psl2_of_lieModel h
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := Finite.of_equiv Y e.toEquiv
  refine cyclic_of_mulEquiv e (fun Q hQ => ?_) P hP
  by_cases hp2 : p = 2
  · subst hp2
    by_cases hf2 : f = 2
    · subst hf2
      refine cyclic_of_not_nine_dvd ?_ Q hQ
      rw [ClassicalModels.projectiveSpecialLinear_two_card_of_card_four F (by rw [hF]; norm_num)]
      norm_num
    · have hf3 : 3 ≤ f := by
        by_contra hlt
        interval_cases f
        · norm_num at h4
        · exact hf2 rfl
      have h7 : 7 ≤ Nat.card F := by
        rw [hF]
        calc 7 ≤ 2 ^ 3 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
      exact cyclic_of_sylow (GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card F hF h7 3
        (by norm_num) (by rw [hF]; exact Nat.Coprime.pow_right _ (by norm_num))) Q hQ
  · exact cyclic_of_sylow (fun R => SectionRank.OddCover.psl_two_sylow_isCyclic hp hp2 hF
      (by norm_num) (Ne.symm hp3) R) Q hQ

theorem not_three_dvd_suzuki_order (a : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  have hq2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  have h3 : Nat.Prime 3 := Nat.prime_three
  intro h
  rcases (Nat.Prime.dvd_mul h3).1 h with h | h
  · rcases (Nat.Prime.dvd_mul h3).1 h with h | h
    · have := h3.dvd_of_dvd_pow h
      omega
    · omega
  · omega

theorem cyclic_of_suzukiModel {Y : Type} [Group Y] [Finite Y]
    {p f : ℕ} (h : Blueprint.SuzukiModel Y p f) (P : Subgroup Y) (hP : IsPGroup 3 P) :
    IsCyclic P := by
  obtain ⟨-, a, -, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  refine cyclic_of_not_nine_dvd (fun h9 => not_three_dvd_suzuki_order a ?_) P hP
  rw [← CFSG.LieType.Ree.suzuki_order hK, ← Nat.card_congr e.toEquiv]
  exact (Dvd.intro 3 rfl).trans h9

theorem cyclic_of_lieModel_psu34 {Y : Type} [Group Y] (h : Blueprint.LieModel Y .PSU 3 2 2)
    (P : Subgroup Y) (hP : IsPGroup 3 P) : IsCyclic P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  by_cases hP1 : P = ⊥
  · subst hP1
    infer_instance
  · exact isCyclic_of_prime_card
      (RankThree.PartTwo.KFacts.KS21.U34.card_eq_three_of_isPGroup hX hP hP1)

end CFSG.ComponentClassification.HarrisLit.L33
