module

public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalDihedral
public import CFSG.LocalAnalysis.ComponentInitial.SLTwoInvolution
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LinearAlgebra.LinearGroups.SmallFieldModels
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Linear
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.ComponentClassification.OutcomeLocal

open Matrix CFSG.Assembly.LowTwoRank

section BlockEmbedding

variable {K : Type} [Field K]

@[expose] def slTwoBlock (m : ℕ) :
    SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 2 ⊕ Fin m) K where
  toFun B := ⟨fromBlocks (B : Matrix (Fin 2) (Fin 2) K) 0 0 1, by
    rw [det_fromBlocks_zero₂₁, B.2, det_one, mul_one]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' B C := by
    apply Subtype.ext
    change (fromBlocks ((B : Matrix (Fin 2) (Fin 2) K) * (C : Matrix (Fin 2) (Fin 2) K)) 0 0 1 :
        Matrix (Fin 2 ⊕ Fin m) (Fin 2 ⊕ Fin m) K) =
      fromBlocks (B : Matrix (Fin 2) (Fin 2) K) 0 0 1 *
        fromBlocks (C : Matrix (Fin 2) (Fin 2) K) 0 0 1
    rw [fromBlocks_multiply]
    simp

variable {d : ℕ}

@[expose] def blockIndexEquiv (hd : 2 ≤ d) : Fin 2 ⊕ Fin (d - 2) ≃ Fin d :=
  finSumFinEquiv.trans (finCongr (by omega))

@[expose] noncomputable def slTwoToGL (hd : 2 ≤ d) :
    SpecialLinearGroup (Fin 2) K →* GL (Fin d) K :=
  (Units.map ((reindexAlgEquiv K K (blockIndexEquiv hd)).toRingEquiv :
      Matrix (Fin 2 ⊕ Fin (d - 2)) (Fin 2 ⊕ Fin (d - 2)) K ≃+*
        Matrix (Fin d) (Fin d) K).toMonoidHom).comp
    (SpecialLinearGroup.toGL.comp (slTwoBlock (d - 2)))

theorem coe_slTwoToGL (hd : 2 ≤ d) (B : SpecialLinearGroup (Fin 2) K) :
    ((slTwoToGL hd B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      reindex (blockIndexEquiv hd) (blockIndexEquiv hd)
        (fromBlocks (B : Matrix (Fin 2) (Fin 2) K) 0 0 1) :=
  rfl

theorem det_slTwoToGL (hd : 2 ≤ d) (B : SpecialLinearGroup (Fin 2) K) :
    ((slTwoToGL hd B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).det = 1 := by
  rw [coe_slTwoToGL, det_reindex_self, det_fromBlocks_zero₂₁, B.2, det_one, mul_one]

@[expose] noncomputable def slTwoToStatedProj (hd : 2 ≤ d) :
    SpecialLinearGroup (Fin 2) K →* StatedProj (StatedSL d K) :=
  (QuotientGroup.mk' ((StatedScalars (Fin d) K).subgroupOf (StatedSL d K))).comp
    ((slTwoToGL hd).codRestrict (StatedSL d K) fun B =>
      Subgroup.subset_closure (det_slTwoToGL hd B))

theorem slTwoToStatedProj_injective (hd : 3 ≤ d) :
    Function.Injective (slTwoToStatedProj (K := K) (by omega : 2 ≤ d)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro B hB
  rw [MonoidHom.mem_ker, slTwoToStatedProj, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hB
  obtain ⟨c, hc⟩ := hB
  have hc' : ((slTwoToGL (by omega : 2 ≤ d) B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      scalar (Fin d) (c : K) := by
    rw [← GeneralLinearGroup.coe_scalar, hc]
    rfl
  rw [coe_slTwoToGL] at hc'
  have hentry : ∀ x y : Fin 2 ⊕ Fin (d - 2),
      fromBlocks (B : Matrix (Fin 2) (Fin 2) K) 0 0 1 x y = if x = y then (c : K) else 0 := by
    intro x y
    have h := congrFun₂ hc' (blockIndexEquiv (by omega) x) (blockIndexEquiv (by omega) y)
    simpa [reindex_apply, scalar_apply, diagonal_apply] using h
  have h1 : (c : K) = 1 := by
    have h := hentry (Sum.inr ⟨0, by omega⟩) (Sum.inr ⟨0, by omega⟩)
    simpa using h.symm
  rw [Subgroup.mem_bot]
  ext i j
  have h := hentry (Sum.inl i) (Sum.inl j)
  simp only [fromBlocks_apply₁₁, Sum.inl.injEq, h1] at h
  rw [h]
  simp [one_apply]

end BlockEmbedding

theorem dihedral_sylow_linear_model_odd_rank_one {T : Type} [Group T] {d p f : ℕ}
    (hT : StatedClassicalModel T .PSL d p f) {s : ℕ} (hs : 2 ≤ s) (P : Sylow 2 T)
    (hP : Nonempty ((P : Subgroup T) ≃* DihedralGroup (2 ^ (s - 1)))) :
    (d = 2 ∧ Odd p ∨ (d, p, f) = (2, 2, 2) ∨ (d, p, f) = (3, 2, 1)) ∧
      ∃ ℓ e : ℕ, ℓ.Prime ∧ Odd ℓ ∧ 1 ≤ e ∧ StatedClassicalModel T .PSL 2 ℓ e := by
  obtain ⟨⟨hp, hf, hd, hd22, hd23⟩, K, _, _, hK, ⟨eT⟩⟩ := hT
  have : Finite T := Finite.of_equiv _ eT.symm.toEquiv
  obtain ⟨hrank, hQ8⟩ :=
    SmallLocal.dihedral_sylow_rank_and_quaternion_obstructions hs ⟨P, hP⟩
  have hchar : CharP K p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hp hf hK
  rcases hp.eq_two_or_odd' with rfl | hpodd
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hle := SectionRank.ClassicalOdd.le_pRank_SL (n := d) (a := 1) (b := d - 1) le_rfl
      (by omega) hK
    rw [← SectionRank.pRank_top_eq_of_mulEquiv one_lt_two eT, ←
      SectionRank.pRank_eq_open_pRank_top] at hle
    have hfd : f * (d - 1) ≤ 2 := by
      rw [one_mul] at hle
      exact hle.trans hrank
    have hd3 : d ≤ 3 := by
      by_contra h
      have : 3 ≤ f * (d - 1) :=
        le_trans (by omega : 3 ≤ 1 * (d - 1)) (Nat.mul_le_mul_right _ hf)
      omega
    have hT' : StatedClassicalModel T .PSL d 2 f :=
      ⟨⟨hp, hf, hd, hd22, hd23⟩, K, inferInstance, inferInstance, hK, ⟨eT⟩⟩
    have hLie : CFSG.Blueprint.LieModel T .PSL d 2 f := Or.inl ⟨by decide, hT'⟩
    interval_cases d
    ·
      have hf2 : f = 2 := by
        rcases (by omega : f = 1 ∨ f = 2) with rfl | rfl
        · exact absurd (by norm_num) hd22
        · rfl
      subst hf2
      refine ⟨Or.inr (Or.inl rfl), 5, 1, Nat.prime_five, by decide, le_rfl, ?_⟩
      obtain ⟨eA⟩ := LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model T hLie
      have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      obtain ⟨e5⟩ := (LinearGroups.five_field_linear_two_alternating_five_model
        (GaloisField 5 1) (by rw [GaloisField.card 5 1 one_ne_zero, pow_one])).1
      exact statedClassicalModel_psl_two_of_mulEquiv T 5 1 (by norm_num) (eA.trans e5.symm)
    ·
      have hf1 : f = 1 := by omega
      subst hf1
      refine ⟨Or.inr (Or.inr rfl), 7, 1, by norm_num, by decide, le_rfl, ?_⟩
      have h7 := LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism T hLie
      rcases h7 with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
      · exact h
      · exact absurd ht (by decide)
      · exact absurd ht (by decide)
      · exact absurd ht (by decide)
  ·
    have hd2 : d = 2 := by
      by_contra hd'
      have hd3 : 3 ≤ d := by omega
      have hkchar : ringChar K ≠ 2 := by
        rw [ringChar.eq K p]
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr hpodd) even_two
      obtain ⟨-, ⟨H, ⟨eH⟩⟩, -⟩ :=
        LocalAnalysis.ComponentInitial.sl2_odd_field_involution_structure hkchar
      let φ := eT.symm.toMonoidHom.comp (slTwoToStatedProj (K := K) (by omega : 2 ≤ d))
      have hφ : Function.Injective φ := eT.symm.injective.comp (slTwoToStatedProj_injective hd3)
      exact hQ8 ⟨H.map φ, ⟨(H.equivMapOfInjective φ hφ).symm.trans eH.symm⟩⟩
    subst hd2
    exact ⟨Or.inl ⟨rfl, hpodd⟩, p, f, hp, hpodd, hf,
      ⟨⟨hp, hf, hd, hd22, hd23⟩, K, inferInstance, inferInstance, hK, ⟨eT⟩⟩⟩

end CFSG.ComponentClassification.OutcomeLocal
