module

public import CFSG.GH74.GLS.Stage2.Final.L26.GLevel

public section

namespace CFSG.GH74.GLS.Stage2.Final.L26

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final.Thm4
  CFSG.LocalAnalysis.ComponentInitial

section Sporadic

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem lemma26_of_sporadic {k : Kind} {n : ℕ} (hctx : Stage2Ctx G z k S) (h : Stage1Sporadic G z S n) :
    Lemma26 z S := by
  obtain ⟨hqs, hcen, -⟩ := h.cover
  have hqs' : IsQuasisimple (CentralizerBar z) := hqs
  have hqtop : IsQuasisimple ↥(⊤ : Subgroup (CentralizerBar z)) :=
    (isQuasisimple_congr (Subgroup.topEquiv (G := CentralizerBar z))).2 hqs'
  have hlayer : layer (CentralizerBar z) = ⊤ :=
    top_le_iff.1 (le_sSup ⟨hqtop, Subgroup.Normal.isSubnormal inferInstance⟩)
  refine lemma26_of_layer_data hctx ?_ ?_ ?_
  · rw [hlayer]
    exact le_top
  · intro K hK hKle hnc
    rcases quasisimple_normal_subgroups hqs' hK with h1 | h1
    · rw [hlayer, h1]
    · exfalso
      apply hnc
      intro x hx e _
      exact (Subgroup.mem_center_iff.mp (h1 hx) e).symm
  · rw [hlayer]
    have hinj : Function.Injective (fun x : ↥(center ↥(⊤ : Subgroup (CentralizerBar z))) =>
        (⟨Subgroup.topEquiv (x : ↥(⊤ : Subgroup (CentralizerBar z))), by
          rw [Subgroup.mem_center_iff]
          intro y
          have := Subgroup.mem_center_iff.mp x.2 (Subgroup.topEquiv.symm y)
          have h5 := congrArg (Subgroup.topEquiv (G := CentralizerBar z)) this
          simpa using h5⟩ : ↥(center (CentralizerBar z)))) := by
      intro x y hxy
      have h5 := Subtype.ext_iff.mp hxy
      exact Subtype.ext (Subgroup.topEquiv.injective (a₁ := (x : ↥(⊤ : Subgroup (CentralizerBar z))))
        (a₂ := (y : ↥(⊤ : Subgroup (CentralizerBar z)))) h5)
    have := Nat.card_le_card_of_injective _ hinj
    omega

end Sporadic

end CFSG.GH74.GLS.Stage2.Final.L26
