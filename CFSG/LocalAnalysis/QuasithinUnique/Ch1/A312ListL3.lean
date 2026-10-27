module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3Block
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Setup.X6 CFSG.Assembly.LowTwoRank
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

section Residual

theorem linear_three_residual_of_cover {K : Type} [Field K] [Finite K]
    (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) {S : Type} [Group S] [Finite S]
    (π : Matrix.SpecialLinearGroup (Fin 3) K →* S) (hπ : Function.Surjective π)
    (hker : π.ker ≤ scalars 3 K) :
    ResidualOvergroupsAt S ((unitriangular 3 K).map π) (fun j : Fin 2 => (Q3 K j).map π) := by
  have hB := isSolvable_upperTriangular (n := 3) (K := K) hK
  exact residualOvergroupsAt_of_rank_two_data (π := π) hπ
    (V := unitriangular 3 K) (B := upperTriangular 3 K) (Q := Q3 K) (H := H3 K)
    (hker.trans (scalars_le_upperTriangular 3 K)) (unitriangular_le_upperTriangular 3 K)
    (fun j => by rw [Q3_eq]; exact upperTriangular_le_flagStabilizer _)
    Q3_ne covBy_Q3 (fun A hVA hAt => contained_in_Q3 hVA hAt) hB commutator_Q3_le
    (fun j A hVA hAQ hAns => H3_le_of_nonsolvable hB j hVA hAQ hAns)

theorem upperTriangular_le_Q3 {K : Type*} [Field K] (j : Fin 2) :
    upperTriangular 3 K ≤ Q3 K j := by
  rw [Q3_eq]
  exact upperTriangular_le_flagStabilizer _

end Residual

section PerfectCore

variable {G S : Type*} [Group G] [Finite G] [Group S] [Finite S]

noncomputable def perfectCoreMapEquiv (π : G →* S) (Q : Subgroup G)
    (hinj : ∀ x ∈ perfectCore Q, ∀ y ∈ perfectCore Q, π x = π y → x = y) :
    ↥(perfectCore Q) ≃* ↥(perfectCore (Q.map π)) :=
  (MulEquiv.ofBijective (π.subgroupMap (perfectCore Q))
    ⟨fun x y h => Subtype.ext (hinj x.1 x.2 y.1 y.2 (congrArg Subtype.val h)),
      π.subgroupMap_surjective _⟩).trans
    (MulEquiv.subgroupCongr (map_perfectCore π Q))

end PerfectCore

section Three

variable {K : Type} [Field K] [Finite K]

theorem isPGroup_unitriangular (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) :
    IsPGroup 2 ↥(unitriangular 3 K) := by
  obtain ⟨k, hk⟩ := hK
  exact IsPGroup.of_card (n := k * 3) (by rw [card_unitriangular, hk, pow_mul])

theorem blk3_ker_isPGroup (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) (j : Fin 2) :
    IsPGroup 2 (blk3 (K := K) j).ker := by
  intro x
  obtain ⟨k, hk⟩ := isPGroup_unitriangular hK ⟨(x.1 : SpecialLinearGroup (Fin 3) K),
    blk3_ker j x.1 x.2⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg Subtype.val hk
  exact this

theorem a312For_linear3 [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f) {S : Type} [Group S]
    [Finite S] (hq : CFSG.IsQuasisimple S) (π : SpecialLinearGroup (Fin 3) K →* S)
    (hπ : Function.Surjective π) (hker : π.ker ≤ scalars 3 K)
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf ((unitriangular 3 K).map π) ⊤)
    (hN : Subgroup.normalizer (((unitriangular 3 K).map π : Subgroup S) : Set S) ≤
      (upperTriangular 3 K).map π)
    (hR : IsRank2LieChar2 S) : A312For S := by
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hf⟩
  have hres := linear_three_residual_of_cover hK π hπ hker
  have hinj : ∀ j : Fin 2, ∀ x ∈ perfectCore (Q3 K j), ∀ y ∈ perfectCore (Q3 K j),
      π x = π y → x = y := by
    intro j x hx y hy hxy
    have hz : x⁻¹ * y ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    have hzN : x⁻¹ * y ∈ perfectCore (Q3 K j) := mul_mem (inv_mem hx) hy
    have h1 := blk3_scalars j ⟨x⁻¹ * y, hzN⟩ (hker hz)
    exact inv_mul_eq_one.mp (congrArg Subtype.val h1)
  have hpos : 1 < Nat.card K := Finite.one_lt_card
  by_cases h4 : 4 ≤ Nat.card K
  · have hK4 := exists_finset_card_four h4
    have hf2 : 2 ≤ f := by
      by_contra hlt
      rw [hf] at h4
      have : f ≤ 1 := by omega
      have h2 : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
      omega
    let eN : ∀ j : Fin 2, ↥(perfectCore (Q3 K j)) ≃* ↥(perfectCore ((Q3 K j).map π)) :=
      fun j => perfectCoreMapEquiv π (Q3 K j) (hinj j)
    refine a312For_of_rank2_levi hq hSyl hres
      (fun j => hN.trans (Subgroup.map_mono (upperTriangular_le_Q3 j))) hR hf hf2
      (fun j => (blk3 j).comp (eN j).symm.toMonoidHom)
      (fun j => (blk3_surjective hK4 j).comp (eN j).symm.surjective) fun j z => ?_
    obtain ⟨k, hk⟩ := blk3_ker_isPGroup hK j ⟨(eN j).symm z.1, z.2⟩
    have h1 : ((eN j).symm z.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    refine ⟨k, Subtype.ext ?_⟩
    show z.1 ^ 2 ^ k = 1
    have : (eN j).symm (z.1 ^ 2 ^ k) = 1 := by rw [map_pow]; exact h1
    exact (map_eq_one_iff _ (eN j).symm.injective).mp this
  · have hf1 : f = 1 := by
      by_contra hne
      rcases Nat.lt_or_ge f 2 with hlt | hge
      · have : f = 0 := by omega
        subst this
        simp at hf
        omega
      · apply h4
        rw [hf]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hge
    subst hf1
    have hK2 : Nat.card K = 2 := by rw [hf]; norm_num
    have hbot : ∀ j : Fin 2, perfectCore (Q3 K j) = ⊥ := by
      intro j
      have hSL : Group.IsSolvable (SpecialLinearGroup (Fin 2) K) := by
        refine isSolvable_of_card_two_three (a := 1) (b := 1) ?_
        rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK2]
        norm_num
      have hkerS : Group.IsSolvable (blk3 (K := K) j).ker := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have := (blk3_ker_isPGroup hK j).isNilpotent
        infer_instance
      have hN : Group.IsSolvable ↥(perfectCore (Q3 K j)) :=
        Group.isSolvable_of_ker_le_range (blk3 (K := K) j).ker.subtype (blk3 j)
          (by rw [Subgroup.range_subtype])
      have := (isSolvable_iff_perfectCore_eq_bot (perfectCore (Q3 K j))).mp hN
      rwa [perfectCore_eq_self_of_perfect (perfectCore_perfect _)] at this
    exact a312For_of_rank2_solvable hq hSyl hres
      (fun j => by rw [← map_perfectCore, hbot j, Subgroup.map_bot])

theorem a312For_projectiveSL3 [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (hq : CFSG.IsQuasisimple (projectiveSL 3 K)) (hR : IsRank2LieChar2 (projectiveSL 3 K)) :
    A312For (projectiveSL 3 K) := by
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  have hT₀ : CFSG.QuasithinUnique.IsSylowTwoOf (projUnitriangular 3 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact a312For_linear3 hf hq (proj 3 K) (proj_surjective 3 K) (ker_proj 3 K).le hT₀
    (normalizer_projUnitriangular 2).le hR

theorem a312For_specialLinear3 [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (hq : CFSG.IsQuasisimple (SpecialLinearGroup (Fin 3) K))
    (hR : IsRank2LieChar2 (SpecialLinearGroup (Fin 3) K)) :
    A312For (SpecialLinearGroup (Fin 3) K) := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  have hT₀ : CFSG.QuasithinUnique.IsSylowTwoOf (unitriangular 3 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  refine a312For_linear3 hf hq (MonoidHom.id _) Function.surjective_id
    (by rw [MonoidHom.ker_id]; exact bot_le) (by rw [Subgroup.map_id]; exact hT₀) ?_ hR
  rw [Subgroup.map_id, Subgroup.map_id]
  exact normalizer_unitriangular.le

end Three

@[expose] def FamSl3evenMinus : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (e : ℕ), CFSG.IsQuasisimple X → 1 ≤ e →
    Int.ModEq 3 ((2 ^ e : ℕ) : ℤ) (-1) → IsSU3 (2 ^ e) X → A312For X

theorem l3even : FamL3even := by
  intro X _ _ f hq hf hX
  have hX' := hX
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hX
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
  let e' : X ≃* projectiveSL 3 K := e.trans (statedSLEquivProjectiveSL 3 K)
  have hq' : CFSG.IsQuasisimple (projectiveSL 3 K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e' hq
  have hR : IsRank2LieChar2 (projectiveSL 3 K) :=
    Or.inl ⟨f, Or.inl ⟨hf, IsPSL.of_mulEquiv e' hX'⟩⟩
  exact A312For.of_mulEquiv e' (a312For_projectiveSL3 hcard hq' hR)

theorem sl3evenPlus :
    ∀ (X : Type) [Group X] [Finite X] (e : ℕ), CFSG.IsQuasisimple X → 1 ≤ e → IsSL3 (2 ^ e) X →
      A312For X := by
  intro X _ _ e hq he hX
  have hX' := hX
  obtain ⟨K, hF, hFin, hcard, ⟨φ⟩⟩ := hX
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two he hcard
  let e' : X ≃* SpecialLinearGroup (Fin 3) K := φ.trans (specialLinearGroupEquivStatedSL 3 K).symm
  have hq' : CFSG.IsQuasisimple (SpecialLinearGroup (Fin 3) K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e' hq
  have hR : IsRank2LieChar2 (SpecialLinearGroup (Fin 3) K) :=
    Or.inl ⟨e, Or.inr (Or.inl ⟨he, IsSL3.of_mulEquiv e' hX'⟩)⟩
  exact A312For.of_mulEquiv e' (a312For_specialLinear3 hcard hq' hR)

theorem famSl3even_of_minus (hM : FamSl3evenMinus) : FamSl3even := by
  intro X _ _ s e hq he hmod hX
  cases s
  · exact hM X e hq he (by simpa using hmod) hX
  · exact sl3evenPlus X e hq he hX

end CFSG.QuasithinUnique.Vol2Native.A312L
