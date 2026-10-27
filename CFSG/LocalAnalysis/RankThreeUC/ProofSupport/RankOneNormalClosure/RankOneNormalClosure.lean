module

public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.RankOneNormalEquality.RankOneNormalEquality
public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ResidualTwoExtension.ResidualTwoExtension

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.RankOneNormalClosure

open CFSG.LocalAnalysis.RankThreeUC

theorem normalClosureUnder_self_eq {G : Type} [Group G] [Finite G] (X B : Subgroup G)
    (hX : SourceSetting.oPrimeResidual 3 X = X)
    (hr : CFSG.Open.pRank 3 (SourceSetting.normalClosureUnder X B) ≤ 1) :
    SourceSetting.normalClosureUnder X (SourceSetting.normalClosureUnder X B) =
      SourceSetting.normalClosureUnder X B := by
  set K := SourceSetting.normalClosureUnder X B with hK
  set N := SourceSetting.normalClosureUnder X K with hN
  have hXK : X ≤ K := by
    have : X.map (MulAut.conj ((1 : B) : G)).toMonoidHom ≤ K :=
      le_iSup (fun h : B => X.map (MulAut.conj (h : G)).toMonoidHom) 1
    intro x hx
    simpa using this ⟨x, hx, rfl⟩
  have hXN : X ≤ N := by
    have : X.map (MulAut.conj ((1 : K) : G)).toMonoidHom ≤ N :=
      le_iSup (fun h : K => X.map (MulAut.conj (h : G)).toMonoidHom) 1
    intro x hx
    simpa using this ⟨x, hx, rfl⟩
  have hNK : N ≤ K := by
    refine iSup_le fun k => ?_
    rintro _ ⟨x, hx, rfl⟩
    have := K.mul_mem (K.mul_mem k.2 (hXK hx)) (K.inv_mem k.2)
    simpa using this
  have hBK : B ≤ Subgroup.normalizer (K : Set G) :=
    ResidualTwoExtension.le_normalizer_normalClosureUnder X B
  have hNres : SourceSetting.oPrimeResidual 3 N = N := by
    have := ResidualConjugateClosure.oPrimeResidual_normalClosureUnder_oPrimeResidual
      3 X K
    rwa [hX] at this
  have hNnorm : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff hNK).mpr fun n k hn hk =>
      ResidualTwoExtension.conj_mem_normalClosureUnder X K hk hn
  have hmain : ∀ b ∈ B, X.map (MulAut.conj b).toMonoidHom ≤ N := by
    intro b hb
    set Nb := N.map (MulAut.conj b).toMonoidHom with hNb
    have hbK : ∀ k : G, k ∈ K → b * k * b⁻¹ ∈ K := fun k hk =>
      ((Subgroup.mem_normalizer_iff.mp (hBK hb) k).mp hk)
    have hbK' : ∀ k : G, k ∈ K → b⁻¹ * k * b ∈ K := fun k hk => by
      have := (Subgroup.mem_normalizer_iff.mp (hBK (B.inv_mem hb)) k).mp hk
      simpa using this
    have hNbK : Nb ≤ K := by
      rintro _ ⟨n, hn, rfl⟩
      exact hbK n (hNK hn)
    haveI : (Nb.subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff hNbK).mpr fun n k hn hk => by
        obtain ⟨m, hm, rfl⟩ := hn
        have h1 : (b⁻¹ * k * b) * m * (b⁻¹ * k * b)⁻¹ ∈ N :=
          ResidualTwoExtension.conj_mem_normalClosureUnder X K (hbK' k hk) hm
        refine ⟨_, h1, ?_⟩
        simp [MulAut.conj_apply, mul_assoc]
    haveI := hNnorm
    have hNbres : SourceSetting.oPrimeResidual 3 Nb = Nb := by
      rw [hNb, ← Y2ConjugationInvariance.map_oPrimeResidual, hNres]
    have hcard : Nat.card N = Nat.card Nb :=
      (Subgroup.card_map_of_injective (MulAut.conj b).injective).symm
    have heq : N = Nb :=
      RankOneNormalEquality.normal_eq_of_card_eq hNK hNbK hr hNres hNbres hcard
    rw [heq]
    exact Subgroup.map_mono hXN
  refine le_antisymm hNK ?_
  refine iSup_le fun b => ?_
  exact hmain b b.2

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.RankOneNormalClosure
