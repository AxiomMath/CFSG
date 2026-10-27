module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKSp4
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Symplectic

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.LocalAnalysis.ComponentInitial

theorem sp4OddMultiplierTrivial
    : Sp4OddMultiplierTrivial := by
  intro F _ _ _ _ E _ _ hperf η hη hker hodd
  obtain ⟨σ, -, -, e, he⟩ :=
    CFSG.SectionRank.EvenCover.even_symplectic_central_odd_extension_splitting (K := F) 2 hη hker
      hodd
  let φ : E →* η.ker := (MonoidHom.fst η.ker σ.range).comp e.symm.toMonoidHom
  have hcomm : ∀ x y : η.ker, x * y = y * x := by
    intro x y
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hker x.2) y).symm
  have hle : commutator E ≤ φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm _ _)
  have htop : φ.ker = ⊤ := by
    rw [eq_top_iff, ← Group.isPerfect_def.1 hperf]
    exact hle
  rw [eq_bot_iff]
  intro a ha
  have h1 : φ (e (⟨a, ha⟩, 1)) = ⟨a, ha⟩ := by simp [φ]
  have h2 : φ (e (⟨a, ha⟩, 1)) = 1 := by
    have : e (⟨a, ha⟩, 1) ∈ φ.ker := by rw [htop]; exact Subgroup.mem_top _
    exact this
  rw [h1] at h2
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val h2)

end CFSG.QuasithinUnique.Lin2
