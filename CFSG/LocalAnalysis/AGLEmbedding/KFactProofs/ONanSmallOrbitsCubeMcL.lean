module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallMcL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOrbitsCubeCore
public import Certificates.Certificate9617

public section

namespace CFSG.AGLEmbedding.KFactProofs.OrbitsCube

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.RankThree.Native
  CFSG.AGLEmbedding.KFactProofs.SmallIdent
open scoped commutatorElement

theorem mclFive_norm_data :
    ∃ x y h : Equiv.Perm (Fin 275), Rep 275 (mcl275FiveArr 0) x ∧ Rep 275 (mcl275FiveArr 1) y ∧
      h ∈ mcl275P ∧ ⁅x, y⁆ ≠ 1 ∧ h * x * h⁻¹ = x ^ 1 * y ^ 2 * ⁅x, y⁆ ^ 0 ∧
      h * y * h⁻¹ = x ^ 1 * y ^ 4 * ⁅x, y⁆ ^ 0 := by
  have hc := Certificates.certificate9617
  simp only [mclFiveNormCheck, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨⟨⟨hvx, hvy⟩, hvh⟩, hsift⟩, hnc⟩, hcx⟩, hcy⟩ := hc
  have hX := rep_of_validA hvx
  have hY := rep_of_validA hvy
  have hH := rep_of_validA hvh
  have hz := rep_commutatorA hvx hvy
  have hword : ∀ i j k : ℕ, Rep 275 (mclFiveWord i j k)
      (permOfArr 275 (mcl275FiveArr 0) ^ i * permOfArr 275 (mcl275FiveArr 1) ^ j *
        ⁅permOfArr 275 (mcl275FiveArr 0), permOfArr 275 (mcl275FiveArr 1)⁆ ^ k) := fun i j k =>
    rep_compA (rep_compA (rep_powArr hX i) (rep_powArr hY j)) (rep_powArr hz k)
  refine ⟨_, _, _, hX, hY, mem_mcl275P_of_sift hH hsift, ?_, ?_, ?_⟩
  · intro h1
    have := (eqA_iff hz rep_idA).2 h1
    rw [this] at hnc
    exact Bool.false_ne_true hnc.symm
  · exact eq_of_eqA (rep_conjA hvh hX) (hword 1 2 0) hcx
  · exact eq_of_eqA (rep_conjA hvh hY) (hword 1 4 0) hcy

private theorem mcl275FiveQGens_zero : mcl275FiveQGens[0]! = mcl275FiveArr 0 := by
  simp [mcl275FiveQGens]

private theorem mcl275FiveQGens_one : mcl275FiveQGens[1]! = mcl275FiveArr 1 := by
  simp [mcl275FiveQGens]

private theorem size_mcl275FiveQGens : mcl275FiveQGens.size = 2 := by
  simp [mcl275FiveQGens]

theorem permsA_mcl275FiveQGens :
    permsA 275 mcl275FiveQGens =
      {permOfArr 275 (mcl275FiveArr 0), permOfArr 275 (mcl275FiveArr 1)} := by
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk2 : k < 2 := by simpa [size_mcl275FiveQGens] using hk
    interval_cases k
    · exact Or.inl (by simp only [mcl275FiveQGens_zero])
    · exact Or.inr (Set.mem_singleton_iff.mpr (by simp only [mcl275FiveQGens_one]))
  · rintro (rfl | rfl)
    · exact ⟨0, by simp [size_mcl275FiveQGens], by simp only [mcl275FiveQGens_zero]⟩
    · exact ⟨1, by simp [size_mcl275FiveQGens], by simp only [mcl275FiveQGens_one]⟩

theorem normalizerWitness_mcl_model :
    ∃ S : Sylow 5 mcl275P, NormalizerWitness (S : Subgroup mcl275P) := by
  obtain ⟨-, ⟨S, hS⟩, hcardQ, hexp⟩ := (R3E_McL_full_five_centralizer_structures).1
  obtain ⟨x, y, h, hx, hy, hhP, hz1, hhx, hhy⟩ := mclFive_norm_data
  refine ⟨S, ?_⟩
  rw [hS]
  have hp : Nat.Prime 5 := by norm_num
  have hxe : permOfArr 275 (mcl275FiveArr 0) = x := CFSG.RankThree.Native.permOfArr_eq_of_rep hx
  have hye : permOfArr 275 (mcl275FiveArr 1) = y := CFSG.RankThree.Native.permOfArr_eq_of_rep hy
  have hQ : mcl275FiveQ = Subgroup.closure ({x, y} : Set (Equiv.Perm (Fin 275))) := by
    rw [mcl275FiveQ, permsA_mcl275FiveQGens, hxe, hye]
  have hxQ : x ∈ mcl275FiveQ := hQ ▸ Subgroup.subset_closure (by simp)
  have hyQ : y ∈ mcl275FiveQ := hQ ▸ Subgroup.subset_closure (by simp)
  have hx5 : x ^ 5 = 1 := by
    have := Monoid.pow_exponent_eq_one (⟨x, hxQ⟩ : mcl275FiveQ)
    rw [hexp] at this
    simpa using congrArg Subtype.val this
  have hy5 : y ^ 5 = 1 := by
    have := Monoid.pow_exponent_eq_one (⟨y, hyQ⟩ : mcl275FiveQ)
    rw [hexp] at this
    simpa using congrArg Subtype.val this
  have hcard : Nat.card (Subgroup.closure ({x, y} : Set (Equiv.Perm (Fin 275)))) = 5 ^ 3 := by
    rw [← hQ, hcardQ]
    norm_num
  have hzQ : ⁅x, y⁆ ∈ mcl275FiveQ := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hxQ hyQ) (inv_mem hxQ)) (inv_mem hyQ)
  have hh : h ∈ Subgroup.normalizer ((Subgroup.closure ({x, y} : Set (Equiv.Perm (Fin 275))) :
      Subgroup (Equiv.Perm (Fin 275))) : Set (Equiv.Perm (Fin 275))) := by
    refine mem_normalizer_closure_pair ?_ ?_
    · rw [hhx, ← hQ]
      exact mul_mem (mul_mem (pow_mem hxQ 1) (pow_mem hyQ 2)) (pow_mem hzQ 0)
    · rw [hhy, ← hQ]
      exact mul_mem (mul_mem (pow_mem hxQ 1) (pow_mem hyQ 4)) (pow_mem hzQ 0)
  have hw := conjWitness_of_data hp hcard hx5 hy5 hz1 hh 1 2 1 4 0 0 hhx hhy (by decide)
    (by decide)
  rw [hQ]
  exact normalizerWitness_subgroupOf (hQ ▸ mcl275FiveQ_le_P) hhP hh hw.1 hw.2

theorem normalizerWitness_isMcL
    {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hK : CFSG.AGLEmbedding.IsSporadicGroup .McL K) (T : Sylow 5 K) :
    NormalizerWitness (T : Subgroup K) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e⟩ := nonempty_equiv_mclP hs hK
  obtain ⟨S, hS⟩ := normalizerWitness_mcl_model
  have h := @NormalizerWitness.of_sylow_equiv K mcl275P _ _ _ 5 _
  exact h e hS T

end CFSG.AGLEmbedding.KFactProofs.OrbitsCube
