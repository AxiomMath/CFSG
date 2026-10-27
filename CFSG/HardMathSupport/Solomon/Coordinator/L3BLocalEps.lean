module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BLocalMod27
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BLocalModel

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag Matrix CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns

theorem l3b_exists_piField_false' {K : Type} [Field K] [Finite K] {q : ℕ}
    (hcard : Nat.card K = q ^ 2) :
    ∃ p f : ℕ, q = p ^ f ∧ PiField false p f K := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpp, hn0⟩ := FiniteField.card K p
  have hn : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn0
  have hqd : q ∣ p ^ (n : ℕ) := by
    rw [← hn, hcard]
    exact Dvd.intro_left q (sq q).symm
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hpp).1 hqd
  have hq2 : 2 ≤ q := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hcard] at h1
    by_contra h
    interval_cases q <;> simp at h1
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hf
      omega
    · exact h0
  exact ⟨p, f, hf, hpp, hf1, by rw [piCard, Bool.cond_false, ← hf, hcard]⟩

theorem l3b_model_of_isSL3Eps {X : Type} [Group X] [Finite X] (h : IsSL3Eps X) :
    ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K) (φ : X →* GL (Fin 3) K),
      PiField π p f K ∧ ModThree π (p ^ f) ∧ L3Model π p f φ := by
  obtain ⟨hty, h3⟩ := h
  rcases hty with ⟨K, hF, hfin, ⟨e⟩⟩ | ⟨K, hF, hfin, q, hcard, ⟨e⟩⟩
  ·
    have hmod : Nat.card K % 3 = 1 := by
      let e' : SpecialLinearGroup (Fin 3) K ≃* X := (specialLinearGroupEquivStatedSL 3 K).trans e.symm
      have h1 : Nat.card (Subgroup.center X) =
          Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) K)) :=
        (Nat.card_congr (Subgroup.centerCongr e').toEquiv).symm
      have h2 : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) K)) =
          Nat.card (rootsOfUnity (max (Fintype.card (Fin 3)) 1) K) :=
        Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 3)
          (R := K)).toEquiv
      rw [h1, h2] at h3
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := rootsOfUnity (max (Fintype.card (Fin 3)) 1) K) 3 h3
      have hxo : orderOf ((x : Kˣ)) = 3 := (Subgroup.orderOf_coe x).trans hx
      have h4 : 3 ∣ Nat.card Kˣ := hxo ▸ orderOf_dvd_natCard (x : Kˣ)
      have h5 : Nat.card Kˣ = Nat.card K - 1 := by
        rw [Nat.card_units]
      rw [h5] at h4
      have h6 : 0 < Nat.card K := Nat.card_pos
      omega
    obtain ⟨p, f, hK, hq⟩ := l3b_exists_piField_true hmod
    refine ⟨true, p, f, K, hF, (StatedSL 3 K).subtype.comp e.toMonoidHom, hK, hq, ?_, ?_⟩
    · exact Subtype.val_injective.comp e.injective
    · intro g
      constructor
      · rintro ⟨x, rfl⟩
        exact (e x).2
      · intro hg
        obtain ⟨x, hx⟩ := e.surjective ⟨g, hg⟩
        exact ⟨x, congrArg Subtype.val hx⟩
  ·
    obtain ⟨p, f, rfl, hK⟩ := l3b_exists_piField_false' hcard
    have hU := hK.unitary
    have hpf : 2 ≤ p ^ f := (hK.prime.two_le).trans (Nat.le_self_pow (by have := hK.one_le; omega) p)
    have hmod : (p ^ f) % 3 = 2 := by
      by_cases hq2 : p ^ f = 2
      · rw [hq2]
      · have hq2' : 2 < p ^ f := by omega
        have heq : unitarySU p f K 3 = StatedSU 3 (p ^ f) K := by
          ext A
          exact (mem_unitarySU_iff hU).trans (mem_slPi_false hU).symm
        let e'' : X ≃* ↥(unitarySU p f K 3) := e.trans (MulEquiv.subgroupCongr heq.symm)
        have h1 : Nat.card (Subgroup.center X) =
            Nat.card (Subgroup.center ↥(unitarySU p f K 3)) :=
          Nat.card_congr (Subgroup.centerCongr e'').toEquiv
        rw [h1, CFSG.RankThree.PartTwo.KFacts.center_unitarySU_three (h := hU) hq2',
          card_unitaryScalars hU (by norm_num)] at h3
        have h4 : 3 ∣ p ^ f + 1 := (Nat.dvd_gcd_iff.1 h3).2
        omega
    refine ⟨false, p, f, K, hF, (StatedSU 3 (p ^ f) K).subtype.comp e.toMonoidHom, hK, hmod, ?_, ?_⟩
    · exact Subtype.val_injective.comp e.injective
    · intro g
      constructor
      · rintro ⟨x, rfl⟩
        exact (e x).2
      · intro hg
        obtain ⟨x, hx⟩ := e.surjective ⟨g, hg⟩
        exact ⟨x, congrArg Subtype.val hx⟩

end CFSG.HardMathSupport.Solomon.Coordinator
