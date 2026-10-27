module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPairTransport
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.BenderSuzuki CFSG.BenderSuzuki.PFAppendixIII

universe u v w

theorem whole_involution_card_map_mulEquiv
    {G : Type u} {F : Type v} [Group G] [Group F]
    (e : G ≃* F) (B : Subgroup G) :
    Nat.card {x : F // x ∈ B.map e.toMonoidHom ∧ IsInvolution x} =
      Nat.card {x : G // x ∈ B ∧ IsInvolution x} := by
  have hcomap : B.comap e.symm.toMonoidHom = B.map e.toMonoidHom := by
    ext x
    constructor
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      change e.symm (e y) ∈ B
      simpa only [e.symm_apply_apply, SetLike.mem_coe] using hy
  rw [← hcomap]
  exact CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair.point_involution_card_comap
    e.symm B

theorem whole_point_involution_card_eq
    {G : Type u} {Omega : Type v} [Group G] [MulAction G Omega]
    [MulAction.IsPretransitive G Omega] (b c : Omega) :
    Nat.card {x : G // x ∈ MulAction.stabilizer G c ∧ IsInvolution x} =
      Nat.card {x : G // x ∈ MulAction.stabilizer G b ∧ IsInvolution x} := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G b c
  rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact whole_involution_card_map_mulEquiv (MulAut.conj g) (MulAction.stabilizer G b)

theorem borel_index_and_whole_involution_card_of_native_action
    {G : Type u} {Omega : Type v} [Group G] [Finite G] [MulAction G Omega]
    [MulAction.IsPretransitive G Omega]
    (S : Sylow 2 G) (b : Omega) (q i : ℕ)
    (hN : Subgroup.normalizer ((S : Subgroup G) : Set G) = MulAction.stabilizer G b)
    (hdegree : Nat.card Omega = q ^ i + 1)
    (hcount : Nat.card {x : G // x ∈ MulAction.stabilizer G b ∧ IsInvolution x} = q - 1)
    (B : Subgroup G) (hB : IsBorelSubgroup B) :
    (∃ c : Omega, B = MulAction.stabilizer G c) ∧
      B.index = q ^ i + 1 ∧
      Nat.card {x : G // x ∈ B ∧ IsInvolution x} = q - 1 := by
  obtain ⟨c, hc⟩ := hB.eq_stabilizer_of_sylow_normalizer S b hN
  refine ⟨⟨c, hc⟩, ?_, ?_⟩
  · rw [hc, MulAction.index_stabilizer_of_transitive]
    exact hdegree
  · rw [hc]
    exact (whole_point_involution_card_eq b c).trans hcount

theorem borel_index_and_whole_involution_card_map_mulEquiv
    {G : Type u} {F : Type v} [Group G] [Group F] [Finite G] [Finite F]
    (e : G ≃* F) (q i : ℕ)
    (hF : ∀ B : Subgroup F, IsBorelSubgroup B →
      B.index = q ^ i + 1 ∧
        Nat.card {x : F // x ∈ B ∧ IsInvolution x} = q - 1)
    (B : Subgroup G) (hB : IsBorelSubgroup B) :
    B.index = q ^ i + 1 ∧
      Nat.card {x : G // x ∈ B ∧ IsInvolution x} = q - 1 := by
  obtain ⟨hindex, hcount⟩ := hF (B.map e.toMonoidHom) (hB.map_mulEquiv e)
  constructor
  · exact (Subgroup.index_map_equiv B e).symm.trans hindex
  · rwa [whole_involution_card_map_mulEquiv e B] at hcount

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
