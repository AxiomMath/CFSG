module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.FixBar
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.Open

variable {r : ℕ} {K : Type} [Field K]

theorem exists_standard_fixBarData [Finite K] [CharP K 2] {J : Subgroup (StatedSp r K)} {p : ℕ}
    {v : StatedSp r K} (h : FixBarData J p v) :
    ∃ (J' : Subgroup (StatedSp r K)) (v' : StatedSp r K), FixBarData J' p v' ∧
      SymplecticFlag.borelSubgroup r K ≤ J' ∧ J' ≠ SymplecticFlag.borelSubgroup r K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hNJ, hne⟩ := h.parab
  have hidx : ¬ 2 ∣ T.index := by
    have h2 := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h2
  let T' : Sylow 2 (StatedSp r K) := hT.2.1.toSylow hidx
  obtain ⟨U, hU⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 r
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (StatedSp r K) U T'
  have hTx : T = (SymplecticFlag.unipotent r K).map (MulAut.conj x).toMonoidHom := by
    have h1 : ((x • U : Sylow 2 (StatedSp r K)) : Subgroup (StatedSp r K)) = T := by
      rw [hx]; rfl
    rw [← h1, Sylow.coe_subgroup_smul, hU]
    rfl
  let e : StatedSp r K ≃* StatedSp r K := MulAut.conj x⁻¹
  have heT : T.map e.toMonoidHom = SymplecticFlag.unipotent r K := by
    rw [hTx, Subgroup.map_map]
    have : e.toMonoidHom.comp (MulAut.conj x).toMonoidHom = MonoidHom.id _ := by
      refine MonoidHom.ext fun z => ?_
      show x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = z
      group
    rw [this, Subgroup.map_id]
  have hbij : Function.Bijective e.toMonoidHom := e.bijective
  have hNmap : (Subgroup.normalizer (T : Set (StatedSp r K))).map e.toMonoidHom =
      SymplecticFlag.borelSubgroup r K := by
    rw [Subgroup.map_normalizer_eq_of_bijective T hbij, heT]
    exact SymplecticHigher.normalizer_unipotent
  refine ⟨J.map e.toMonoidHom, e v, h.map_mulEquiv e, ?_, ?_⟩
  · rw [← hNmap]
    exact Subgroup.map_mono hNJ
  · intro heq
    apply hne
    rw [← hNmap] at heq
    exact Subgroup.map_injective hbij.1 heq

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic
