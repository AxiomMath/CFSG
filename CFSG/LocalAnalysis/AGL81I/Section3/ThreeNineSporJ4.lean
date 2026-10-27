module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporOrder
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefLocal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.J4Eleven

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporCent

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_normalizer_sylow_eq_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A]
    [Finite B] {p : ℕ} [Fact p.Prime] (e : A ≃* B) (S : Sylow p A) (T : Sylow p B) :
    Nat.card (normalizer ((S : Subgroup A) : Set A)) =
      Nat.card (normalizer ((T : Subgroup B) : Set B)) := by
  set S' : Sylow p B := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S
  have h1 : Nat.card (normalizer ((S' : Subgroup B) : Set B)) =
      Nat.card (normalizer ((S : Subgroup A) : Set A)) := by
    have hS' : (S' : Subgroup B) = (S : Subgroup A).map e.toMonoidHom := rfl
    rw [hS', ← map_equiv_normalizer_eq, card_map_of_injective e.injective]
  have h2 : Nat.card (normalizer ((S' : Subgroup B) : Set B)) * Nat.card (Sylow p B) =
      Nat.card B := by
    rw [S'.card_eq_index_normalizer]
    exact (normalizer _).card_mul_index
  have h3 : Nat.card (normalizer ((T : Subgroup B) : Set B)) * Nat.card (Sylow p B) =
      Nat.card B := by
    rw [T.card_eq_index_normalizer]
    exact (normalizer _).card_mul_index
  rw [← h1]
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h2.trans h3.symm)

theorem normalizer_sylow_eleven_j4
    {L : Type} [Group L] [Finite L] (e : L ≃* CFSG.Blueprint.NativeSporadic.Carrier .J4)
    (T : Sylow 11 L) :
    Nat.card (normalizer ((T : Subgroup L) : Set L)) = 11 ^ 3 * 240 ∧
      ∀ H : Subgroup L, normalizer ((T : Subgroup L) : Set L) ≤ H →
        H = normalizer ((T : Subgroup L) : Set L) ∨ H = ⊤ := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let φ : L ≃* ↥CFSG.Sporadic.J4.J :=
    e.trans (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat)
  have hfinJ : Finite ↥CFSG.Sporadic.J4.J := Finite.of_equiv L φ.toEquiv
  have hNJ : Nat.card (normalizer ((CFSG.Sporadic.J4Schreier.Q11Sylow :
      Subgroup ↥CFSG.Sporadic.J4.J) : Set ↥CFSG.Sporadic.J4.J)) = 11 ^ 3 * 240 := by
    rw [CFSG.Sporadic.J4Schreier.Q11Sylow_coe]
    exact CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.card_normalizer_Q11
  exact ⟨(@card_normalizer_sylow_eq_of_mulEquiv L ↥CFSG.Sporadic.J4.J _ (Subgroup.toGroup _) _
      hfinJ 11 _ φ T CFSG.Sporadic.J4Schreier.Q11Sylow).trans hNJ,
    @CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.NormMax.sylow_of_equiv L
      ↥CFSG.Sporadic.J4.J _ (Subgroup.toGroup _) 11 _ _ hfinJ φ
      CFSG.Sporadic.J4Schreier.Q11Sylow CFSG.AGLEmbeddingD2.Wilson.Coordinator.normMax_Q11 T⟩

end CFSG.LocalAnalysis.AGL81I.Section3.SporCent

namespace CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp

open CFSG.ComponentClassification.OuterAutomorphisms

theorem false_of_j4
    {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {d : ℕ}
    (h : ThreeNineHyp K E D X₁ 11 d)
    (hs : CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .J4) : False := by
  obtain ⟨e⟩ := hs
  have hsK : IsSimpleGroup ↥K :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J4.isSimpleGroup_J4 e
  have hcK : Nat.card ↥K = 86775571046077562880 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J4.card_J4
  have hZ : Subgroup.center ↥K = ⊥ :=
    SporCent.center_eq_bot_of_not_prime (by rw [hcK]; norm_num)
  have hO : Nat.card (Outer ↥K) = 1 := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.AGLEmbedding.card_outer_J4
  have hdp := h.d_prime
  have hout11 : ¬ 11 ∣ Nat.card (Outer ↥K) := by rw [hO]; norm_num
  have hDK : D ≤ K := h.D_le_K_of_not_dvd hZ (by rw [hO]; exact hdp.not_dvd_one)
  obtain ⟨S, hS⟩ := h.exists_sylow_subgroupOf_eq_normalizer hZ hout11
    (fun S => (SporCent.normalizer_sylow_eleven_j4 e S).2)
  have hc : Nat.card (X₁.subgroupOf K) = 11 ^ 3 * 240 := by
    rw [hS, (SporCent.normalizer_sylow_eleven_j4 e S).1]
  obtain ⟨hd1, hd2⟩ := h.dvd_card_of_subgroupOf_le hDK le_rfl
  rw [hc] at hd1 hd2
  have h' : d ∣ 2 ^ 4 * (3 * (5 * 11 ^ 3)) := by norm_num; exact hd1
  rcases hdp.dvd_mul.1 h' with h2 | h'
  · exact h.d_ne_two ((Nat.prime_dvd_prime_iff_eq hdp Nat.prime_two).1 (hdp.dvd_of_dvd_pow h2))
  rcases hdp.dvd_mul.1 h' with h3 | h'
  ·
    have h3' := (Nat.prime_dvd_prime_iff_eq hdp Nat.prime_three).1 h3
    subst h3'
    rw [hcK, SporCent.factorization_eq_of_pow_dvd (e := 3) Nat.prime_three (by norm_num)
      (by norm_num) (by norm_num)] at hd2
    norm_num at hd2
  rcases hdp.dvd_mul.1 h' with h5 | h11
  ·
    have h5' := (Nat.prime_dvd_prime_iff_eq hdp Nat.prime_five).1 h5
    subst h5'
    have hidx : (X₁.subgroupOf K).index = 271649045348352 := by
      have h1 := (X₁.subgroupOf K).card_mul_index
      rw [hc, hcK] at h1
      omega
    have hmod := (h.isBorelDLocal hZ hout11).index_modEq_one_of_dvd hdp
      (hd1.trans (hc ▸ Subgroup.card_subgroup_dvd_card (X₁.subgroupOf K)))
    rw [hidx] at hmod
    exact absurd hmod (by decide)
  · exact h.d_ne ((Nat.prime_dvd_prime_iff_eq hdp (by norm_num)).1 (hdp.dvd_of_dvd_pow h11))

end CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp
