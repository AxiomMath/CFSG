module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2

open CFSG.BenderSuzuki.MatrixGroups CFSG.Glauberman.Dickson

section Cyclic

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]

theorem dvd_three_of_dvd_pow {q k : ℕ} (hq : q.Prime) (h : q ∣ 3 ^ k) : q = 3 :=
  (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (hq.dvd_of_dvd_pow h)

theorem isCyclic_of_isPGroup_three (hF : Nat.card F = p ^ f)
    (hp3 : p ≠ 3) (X : Subgroup (PSL2MatrixGroup F)) (hX : IsPGroup 3 X) : IsCyclic X := by
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  have hp : p.Prime := Fact.out
  have h2 : ¬ 2 ∣ Nat.card X := by
    rw [hk]
    intro h
    exact absurd (dvd_three_of_dvd_pow Nat.prime_two h) (by norm_num)
  have hp' : ¬ p ∣ Nat.card X := fun h => hp3 (dvd_three_of_dvd_pow hp (hk ▸ h))
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield hF X with
    hE | ⟨z', -, -, hC⟩ | ⟨z', -, hcard, -⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
    ⟨m, t, -, -, N, C, hN, hNe, hNcard, hCc, -, hdisj, hsup⟩ | ⟨m, hm0, hmf, ⟨e⟩, -⟩ |
    ⟨m, hm0, hmf, ⟨e⟩, -⟩
  ·
    have : Subsingleton X := by
      refine ⟨fun a b => ?_⟩
      have key : ∀ x : X, x = 1 := by
        intro x
        have h1 : x ^ p = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p X) x
        have h2' : x ^ (3 ^ k) = 1 := by rw [← hk]; exact pow_card_eq_one'
        have hcop : Nat.Coprime p (3 ^ k) :=
          Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_three).2 hp3)
        have hd : orderOf x ∣ Nat.gcd p (3 ^ k) :=
          Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2')
        rw [hcop] at hd
        exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
      rw [key a, key b]
    exact isCyclic_of_subsingleton
  · exact hC
  · exact absurd (hcard ▸ (dvd_mul_right 2 z') : 2 ∣ Nat.card X) h2
  · exfalso
    apply h2
    rw [Nat.card_congr e.toEquiv, MaxUp.card_alternatingFour']
    norm_num
  · exfalso
    apply h2
    rw [Nat.card_congr e.toEquiv]
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  · exfalso
    apply h2
    rw [Nat.card_congr e.toEquiv, MaxUp.card_alternatingFive']
    norm_num
  ·
    have hNp : Nat.card N = 1 := by
      have hdvd : Nat.card N ∣ Nat.card X := Subgroup.card_subgroup_dvd_card N
      rw [hNcard] at hdvd ⊢
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · simp [h0]
      · exfalso
        exact hp' (dvd_trans (dvd_pow_self p hpos.ne') hdvd)
    have hNbot : N = ⊥ := Subgroup.card_eq_one.mp hNp
    rw [hNbot, bot_sup_eq] at hsup
    have : Function.Surjective C.subtype := by
      intro x
      have : x ∈ C := hsup ▸ Subgroup.mem_top x
      exact ⟨⟨x, this⟩, rfl⟩
    exact isCyclic_of_surjective C.subtype this
  · exfalso
    have hGF : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    obtain ⟨H, hHc, -⟩ := exists_elementaryAbelian_subgroup (F := GaloisField p m)
      (p := p) (f := m) hGF (m := 1) (Nat.one_le_iff_ne_zero.mpr hm0)
    have h1 : p ∣ Nat.card (PSL2MatrixGroup (GaloisField p m)) := by
      have := Subgroup.card_subgroup_dvd_card H
      rw [hHc, pow_one] at this
      exact this
    rw [← Nat.card_congr e.toEquiv] at h1
    exact hp' h1
  · exfalso
    have hGF : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    have h1 : p ∣ Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) := by
      rw [MaxUp.card_pgl2_galoisField hm0]
      exact dvd_mul_of_dvd_left (dvd_pow_self p hm0) _
    rw [← Nat.card_congr e.toEquiv] at h1
    exact hp' h1

end Cyclic

theorem psl2_overgroup_strong {F : Type} [Field F] [Finite F]
    (h3 : ¬ 3 ∣ Nat.card F) {A W : Subgroup (PSL2MatrixGroup F)} (hA : Nat.card A = 3)
    (hNW : Subgroup.normalizer (A : Set (PSL2MatrixGroup F)) ≤ W)
    (hW : ¬ CFSG.HallHigman.IsPSolvable 3 W) : W = ⊤ := by
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨p, f, hp, hf, hcard⟩ := (isPrimePow_nat_iff _).1 (FiniteField.isPrimePow_card F)
  haveI : Fact p.Prime := ⟨hp⟩
  have hF : Nat.card F = p ^ f := by
    rw [Nat.card_eq_fintype_card]
    exact hcard.symm
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact h3 (hF ▸ dvd_pow_self 3 hf.ne')
  exact eq_top_of_normalizer_le hF hp3
    (fun E _ _ y => CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.psl2_orderOf_le E y)
    (fun E _ _ y => CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.pgl2_orderOf_le E y)
    (isCyclic_of_isPGroup_three hF hp3) hA hNW hW

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2
