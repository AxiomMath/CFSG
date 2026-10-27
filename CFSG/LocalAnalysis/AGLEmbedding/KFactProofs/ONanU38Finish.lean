module

public import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeDataAux

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Open

theorem map_conj_eq_of_normal' {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (g : G) :
    N.map (MulAut.conj g).toMonoidHom = N := by
  apply le_antisymm
  · rintro _ ⟨n, hn, rfl⟩
    exact Subgroup.Normal.conj_mem inferInstance n hn g
  · intro n hn
    refine ⟨g⁻¹ * n * g, ?_, ?_⟩
    · simpa using Subgroup.Normal.conj_mem inferInstance n hn g⁻¹
    · simp [MulAut.conj_apply, mul_assoc]

theorem normal_le_weakCore_sylow {X : Type} [Group X] [Finite X] (K : Subgroup X) [K.Normal]
    (E : Subgroup X) (hE : IsElemAbelian 3 E) (hK : K ≤ GLBWeakCore 3 E) (R : Sylow 3 X) :
    K ≤ GLBWeakCore 3 (R : Subgroup X) := by
  have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x.1 x.2)⟩
  obtain ⟨Q, hEQ⟩ := hE3.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q R
  have hRQ : (R : Subgroup X) = (Q : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    have h : ((g • Q : Sylow 3 X) : Subgroup X) = (R : Subgroup X) :=
      congrArg (fun S : Sylow 3 X => (S : Subgroup X)) hg
    rw [← h, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  have h1 : K ≤ GLBWeakCore 3 (Q : Subgroup X) :=
    hK.trans (CFSG.PreuniquenessRankFour.Helpers.weakCore_mono 3 Nat.prime_three hEQ)
  have h2 := map_glbWeakCore_le Nat.prime_three (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective (Q : Subgroup X)
  rw [← hRQ] at h2
  have h3 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h1
  rw [map_conj_eq_of_normal' K g] at h3
  exact h3.trans h2

end CFSG.AGLEmbedding.ChevOuter.U38
