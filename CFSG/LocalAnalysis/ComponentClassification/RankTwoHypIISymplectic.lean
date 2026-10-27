module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIISymplecticFour

public section

namespace CFSG.ComponentClassification.RankTwoHypIISymplectic

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  SymplecticFlag SymplecticHigher CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.ComponentClassification.RankTwoHypIIY
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

variable {K : Type} [Field K] {r : ℕ}

theorem finite_mulAut_sp [Finite K] : Finite (MulAut (StatedProj (StatedSp r K))) :=
  Finite.of_injective (fun e : MulAut (StatedProj (StatedSp r K)) =>
    (e : StatedProj (StatedSp r K) → StatedProj (StatedSp r K))) fun _ _ hab =>
      MulEquiv.ext (congrFun hab)

theorem rigidInvolution_of_not_mem_sp [Finite K] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hr : 2 ≤ r) (hrf : ¬ (r = 2 ∧ f = 1))
    {t : MulAut (StatedProj (StatedSp r K))} (htX : t ∉ inner (StatedProj (StatedSp r K)))
    (ht2 : t ^ 2 = 1) : RigidInvolution (inner (StatedProj (StatedSp r K))) t := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : NeZero r := ⟨by omega⟩
  have hXn : (inner (StatedProj (StatedSp r K))).Normal := inner_normal _
  have ht1 : t ≠ 1 := fun h => htX (h ▸ one_mem _)
  have hconj : ∀ {w t₀ : MulAut (StatedProj (StatedSp r K))}, t = w * t₀ * w⁻¹ →
      t₀ ∉ inner (StatedProj (StatedSp r K)) ∧ t₀ ^ 2 = 1 := by
    intro w t₀ h
    subst h
    refine ⟨fun h0 => htX (hXn.conj_mem t₀ h0 w), ?_⟩
    rwa [conj_pow, conj_eq_one_iff] at ht2
  have hfield : t ∈ spSemilinearAutGroup r K → ∃ σ : K ≃+* K, Even f ∧
      (∀ x, σ x = x ^ 2 ^ (f / 2)) ∧ ∃ h : StatedSp r K,
        t = spInner r K h * fieldAut r K σ * (spInner r K h)⁻¹ := by
    intro htE
    obtain ⟨g, σ, hgσ⟩ := exists_eq_spInner_mul_fieldAut htE
    have hσ : σ ≠ 1 := by
      rintro rfl
      apply htX
      rw [hgσ, map_one, mul_one]
      exact spInner_mem_inner g
    obtain ⟨hfe, hσx, -, -, -, -, -, -, -, -, h, hh⟩ :=
      even_symplectic_quadratic_involution_descent (by omega) hf hK (a := t)
        (by rw [← sq, ht2]) g σ (by rw [hgσ, spInner_apply]) hσ
    exact ⟨σ, hfe, hσx, h, by rw [hh, spInner_apply]⟩
  rcases Nat.lt_or_ge r 3 with hr3 | hr3
  ·
    obtain rfl : r = 2 := by omega
    rcases Nat.even_or_odd f with hfe | hfo
    · have htE : t ∈ spSemilinearAutGroup 2 K := by
        obtain ⟨-, -, -, -, ⟨γ, hγ⟩, hrest⟩ :=
          even_symplectic_two_exterior_square_automorphism hf hK
        obtain ⟨-, -, -, -, -, -, -, -, -, -, heven, -⟩ := hrest γ hγ
        exact heven hfe t (orderOf_eq_prime ht2 ht1)
      obtain ⟨σ, -, hσx, h, hh⟩ := hfield htE
      obtain ⟨h0X, h02⟩ := hconj hh
      rw [hh]
      refine RigidInvolution.conj hXn ?_ _
      rcases Nat.lt_or_ge f 4 with hf4 | hf4
      · obtain rfl : f = 2 := by
          obtain ⟨i, hi⟩ := hfe
          omega
        exact rigidInvolution_fieldAut_four_two hK σ hσx h0X h02
      · exact rigidInvolution_fieldAut_four hf4 hfe hK σ hσx h0X h02
    · obtain ⟨m, rfl⟩ := hfo
      have hm : 1 ≤ m := by
        by_contra hm
        exact hrf ⟨rfl, by omega⟩
      obtain ⟨b, hb, hbt⟩ := exists_conj_eta hK (orderOf_eq_prime ht2 ht1) htX
      rw [hbt]
      exact (rigidInvolution_eta hm hK).conj hXn _
  ·
    have htE : t ∈ spSemilinearAutGroup r K := by
      rw [(automorphism_generation (K := K) hr3).1]
      exact mem_top t
    obtain ⟨σ, hfe, hσx, h, hh⟩ := hfield htE
    obtain ⟨h0X, h02⟩ := hconj hh
    have hf2 : 2 ≤ f := by
      obtain ⟨i, hi⟩ := hfe
      omega
    rw [hh]
    refine (rigidInvolution_fieldAut_sp hr hf2 hfe hK (Or.inl hr3) σ hσx (fun s hs => ?_) h0X
      h02).conj hXn _
    exact absurd (by rw [(automorphism_generation (K := K) hr3).1]; exact mem_top s) hs

theorem hypII_of_statedProj_statedSp [Finite K] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hr : 2 ≤ r) (hrf : ¬ (r = 2 ∧ f = 1)) {A : Type*}
    [Group A] (hA : commutator A = ⊤) (e : A ⧸ center A ≃* StatedProj (StatedSp r K)) :
    AS76b.HypII A := by
  have : Finite (MulAut (StatedProj (StatedSp r K))) := finite_mulAut_sp
  have hcond : 2 ≤ f ∨ 3 ≤ r := by
    rcases Nat.lt_or_ge f 2 with h | h
    · right
      by_contra h'
      exact hrf ⟨by omega, by omega⟩
    · left
      exact h
  have hZ := center_eq_bot hK (by omega) hcond hf
  exact hypII_of_rigidInvolution (autModel_mulAut hZ)
    (fun t htX ht2 => rigidInvolution_of_not_mem_sp hf hK hr hrf (t := t) htX ht2) hA e

theorem hypII_of_psp {A : Type} [Group A] (hA : commutator A = ⊤)
    {n m : ℕ} (h : StatedClassicalModel (A ⧸ center A) .PSp n 2 m) : AS76b.HypII A := by
  obtain ⟨⟨-, hm, hn, hnq⟩, K, _, _, hK, ⟨e⟩⟩ := h
  refine hypII_of_statedProj_statedSp hm hK hn (fun h => hnq ?_) hA e
  rw [h.1, h.2]
  rfl

end CFSG.ComponentClassification.RankTwoHypIISymplectic
