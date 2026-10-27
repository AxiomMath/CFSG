module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSU
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOmega

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace L34REvenOut

theorem not_isL34Type_of_statedSp {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2)
    {r : ℕ} (hr : 3 ≤ r) {X : Type} [Group X] [Finite X] (e : X ≃* StatedSp r k)
    (P : Subgroup X) (hP : IsPComponent 2 P) : ¬ IsL34Type (P ⧸ Open.fusionZStar P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk' : Nat.card k = 2 ^ 1 := by rw [hk, pow_one]
  have := ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp k r (by omega)
    (Or.inr (Or.inr ⟨hk, hr⟩))
  obtain ⟨-, -, -, -, ⟨eProj⟩⟩ :=
    SymmetricLocal.small_standard_source_even_simple_symplectic_parameters_stated
      (X := StatedSp r k) hk' (by omega) ⟨MulEquiv.refl _⟩
  have : IsSimpleGroup (StatedSp r k) := eProj.symm.isSimpleGroup
  have hXs : IsSimpleGroup X := e.isSimpleGroup
  have hsub := ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 P).mp hP).1
  have htop : P = ⊤ := by
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hXs hsub with h | h
    · exfalso
      have hnt := GrSLit.nontrivial_of_isPComponent hP
      rw [h] at hnt
      exact not_nontrivial_iff_subsingleton.mpr inferInstance hnt
    · exact h
  obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple hP
    (((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).trans e)
  intro hL
  obtain ⟨-, hst⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ := hL
  · exact (SymmetricLocal.small_standard_source_even_simple_symplectic_parameters_stated
      (X := P ⧸ Open.fusionZStar P) hk' (by omega) ⟨eZ⟩).2.2.1 hst
  all_goals exact absurd h0 (by norm_num)

theorem ringEquiv_eq_one_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (ρ : K ≃+* K) : ρ = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have huniv : ({0, 1} : Finset K) = Finset.univ := Finset.eq_univ_of_card _ (by
    rw [Finset.card_pair zero_ne_one, ← Nat.card_eq_fintype_card, hK])
  refine RingEquiv.ext fun x => ?_
  have hx : x ∈ ({0, 1} : Finset K) := huniv ▸ Finset.mem_univ x
  rw [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact map_zero ρ
  · exact map_one ρ

end L34REvenOut

theorem evenLieExcOuterL34Input_holds : EvenLieExcOuterL34Input := by
  intro S _ _ τ n f hτ hm σ hσ hσo P hP
  simp only [List.mem_cons, Prod.mk.injEq] at hτ
  rcases hτ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | hnil
  ·
    rcases CatLeafProof.even_unitary_outer_fixed_cases ⟨Nat.prime_two, le_rfl, by norm_num,
        by decide⟩ hm σ hσ hσo with hch | ⟨k, _, _, hk, r, -, hnr, ⟨Φ⟩⟩
    · exact absurd hP (CatLeafProof.not_isPComponent_of_isCharacteristicP hch P)
    · exact L34REvenOut.not_isL34Type_of_statedSp (by rw [hk, pow_one]) (by omega) Φ P hP
  ·
    obtain ⟨K, _, _, hK, hcases⟩ := CatLeafProof.evenOrthogonal_outer_fixed_cases (Or.inl rfl)
      ⟨Nat.prime_two, le_rfl, le_rfl⟩ hm σ hσ hσo
    rcases hcases with hch | ⟨⟨Φ⟩⟩ | ⟨⟨ρ, hρ⟩, -⟩
    · exact absurd hP (CatLeafProof.not_isPComponent_of_isCharacteristicP hch P)
    · exact L34REvenOut.not_isL34Type_of_statedSp (by rw [hK, pow_one]) (by norm_num) Φ P hP
    · exact absurd (L34REvenOut.ringEquiv_eq_one_of_card_two (by rw [hK, pow_one]) ρ) hρ
  · simp at hnil

end CFSG.ComponentClassification.GrSLit
