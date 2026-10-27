module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4Block
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Setup.X6
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

section Sp4

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem spScalars_eq_bot [CharP K 2] : spScalars 2 K = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨c, hc⟩ := hg
  have hmat : spMat g = Matrix.scalar (Fin 2 ⊕ Fin 2) (c : K) := by
    change ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = _
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]
  have hs := congrFun₂ (mem_statedSp_iff.mp g.2) (Sum.inl 0) (Sum.inr 0)
  have hs' : (c : K) * (c : K) = 1 := by
    have h2 : (spMat g)ᵀ * fromBlocks 0 1 (-1) 0 * spMat g =
        fromBlocks 0 1 (-1) 0 := mem_statedSp_iff.mp g.2
    rw [hmat] at h2
    have := congrFun₂ h2 (Sum.inl 0) (Sum.inr 0)
    simpa [Matrix.scalar_apply, Matrix.diagonal_transpose, Matrix.diagonal_mul,
      Matrix.mul_diagonal] using this
  have hc1 : (c : K) = 1 := CharTwo.sq_injective (by
    show (c : K) ^ 2 = 1 ^ 2
    rw [one_pow, sq]
    exact hs')
  rw [Subgroup.mem_bot]
  apply statedSp_ext
  show spMat g = spMat 1
  rw [hmat, hc1, map_one]
  rfl

omit [Finite K] in
theorem proj_injective_charTwo [CharP K 2] : Function.Injective (proj 2 K) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_proj, spScalars_eq_bot]

theorem isPGroup_unipotent (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) : IsPGroup 2 ↥(unipotent 2 K) := by
  obtain ⟨k, hk⟩ := hK
  exact IsPGroup.of_card (n := k * 2 ^ 2) (by rw [card_unipotent, hk, pow_mul])

theorem blkN_ker_isPGroup (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) (j : Fin 2) :
    IsPGroup 2 (blkN (K := K) j).ker := by
  intro x
  obtain ⟨k, hk⟩ := isPGroup_unipotent hK ⟨(x.1 : StatedSp 2 K), blkN_ker j x.1 x.2⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg Subtype.val hk
  exact this

omit [Finite K] in
theorem borelSubgroup_le_Q2 (j : Fin 2) : borelSubgroup 2 K ≤ Q2 K j := by
  have hj := j.isLt
  rw [Q2_eq]
  exact borelSubgroup_le_flagStabilizer (fun x hx => by
    rw [Set.mem_singleton_iff] at hx
    omega)

theorem a312For_projSp4 [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f)
    (hq : CFSG.IsQuasisimple (StatedProj (StatedSp 2 K)))
    (hR : IsRank2LieChar2 (StatedProj (StatedSp 2 K))) :
    A312For (StatedProj (StatedSp 2 K)) := by
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hf⟩
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hf]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hres : ResidualOvergroupsAt (StatedProj (StatedSp 2 K)) (projUnipotent 2 K)
      (fun j : Fin 2 => (Q2 K j).map (proj 2 K)) := symplectic_two_residualOvergroupsAt hK
  obtain ⟨P, hP⟩ := exists_sylow_projUnipotent (K := K) 2 (r := 2) (by norm_num)
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf (projUnipotent 2 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : Subgroup.normalizer (projUnipotent 2 K : Set (StatedProj (StatedSp 2 K))) =
      projBorel 2 K := normalizer_projUnipotent 2 (by norm_num)
  have hinj : ∀ j : Fin 2, ∀ x ∈ perfectCore (Q2 K j), ∀ y ∈ perfectCore (Q2 K j),
      proj 2 K x = proj 2 K y → x = y := fun j x _ y _ h => proj_injective_charTwo h
  let eN : ∀ j : Fin 2, ↥(perfectCore (Q2 K j)) ≃* ↥(perfectCore ((Q2 K j).map (proj 2 K))) :=
    fun j => perfectCoreMapEquiv (proj 2 K) (Q2 K j) (hinj j)
  refine a312For_of_rank2_levi hq hU hres (fun j => ?_) hR hf hf2
    (fun j => (blkN j).comp (eN j).symm.toMonoidHom)
    (fun j => (blkN_surjective hK4 j).comp (eN j).symm.surjective) fun j z => ?_
  · rw [hN]
    exact Subgroup.map_mono (borelSubgroup_le_Q2 j)
  · obtain ⟨k, hk⟩ := blkN_ker_isPGroup hK j ⟨(eN j).symm z.1, z.2⟩
    have h1 : ((eN j).symm z.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    refine ⟨k, Subtype.ext ?_⟩
    show z.1 ^ 2 ^ k = 1
    have : (eN j).symm (z.1 ^ 2 ^ k) = 1 := by rw [map_pow]; exact h1
    exact (map_eq_one_iff _ (eN j).symm.injective).mp this

end Sp4

theorem sp4 : FamSp4 := by
  intro X _ _ f hq hf hX
  have hX' := hX
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hX
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  have hq' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq
  have hR : IsRank2LieChar2 (StatedProj (StatedSp 2 K)) :=
    Or.inl ⟨f, Or.inr (Or.inr (Or.inl ⟨hf, IsPSp4.of_mulEquiv e hX'⟩))⟩
  exact A312For.of_mulEquiv e (a312For_projSp4 hcard hf hq' hR)

end CFSG.QuasithinUnique.Vol2Native.A312L
