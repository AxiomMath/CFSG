module

public import CFSG.ClassicalInvolution.Q3.Q3T7S23Y05

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7S23

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.B3C (SymplecticPhanPair)


section Fields

@[expose] def OddCoreLayer23Sp3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Q3T8.Asc77.Hyp23b Ω K K' W z u e g →
      (alphaOf (Subgroup.closure {u, z}) = ⊥ ∧
        Q3T8.Asc77.ExactLayer.exactLayer Ω e ⊔ Q3T8.Asc77.ExactLayer.exactLayer Ω u = ⊤) →
      Q3T8.Asc77.LayerOrthType Ω e 6 (piSign 3 1) → Q3T8.Asc77.LayerOrthType Ω u 5 true →
      ExactMembers Ω →
      classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω e) = ⊥ →
        classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u) = ⊥


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {z u e g : G}

theorem ySide_fields3 [IsSimpleGroup G] (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z)
    (hd : Q3T8.Asc77.Hyp23bData Ω K K' W z u e g) (hex : ExactMembers Ω)
    (hOY : classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u) = ⊥)
    (hY : Q3T8.Asc77.LayerOrthType Ω u 5 true) :
    ∃ J₁ K₃ : Subgroup G, (J₁ = conjSub g K ∨ J₁ = conjSub g K') ∧
      SymplecticPhanPair (GaloisField 3 1)
        (ModelFacts.two_ne_zero_galoisField 1 (by norm_num))
        (Q3T8.Asc77.ExactLayer.exactLayer Ω u) J₁ K₃ ∧
      K₃ ≤ Subgroup.centralizer ({z} : Set G) ∧ K₃ ≤ Subgroup.centralizer ({u} : Set G) ∧
      Commutes K K₃ ∧ Q3T8.Asc77.ExactLayer.exactLayer Ω u ≤ J₁ ⊔ K₃ ∧
      (conjSub g K ≤ Q3T8.Asc77.ExactLayer.exactLayer Ω u ∧
        conjSub g K' ≤ Q3T8.Asc77.ExactLayer.exactLayer Ω u) ∧
      ∃ w ∈ K₃, (J₁ = conjSub g K → conjSub w J₁ = conjSub g K') ∧
        (J₁ = conjSub g K' → conjSub w J₁ = conjSub g K) := by
  obtain ⟨J₁, J₂, K₃, hJ₁, hpair, hK₃z, hK₃u, hpow, hYle, hJY, hJ'Y, w, hwK₃, hw⟩ :=
    ySide5tw3 hs hd hex hOY hY
  have hne : conjSub g K ≠ conjSub g K' := fun h => hs.hne (conjSub_injective g h).symm
  refine ⟨J₁, K₃, hJ₁.imp (fun h => h.1) (fun h => h.1), hpair, hK₃z, hK₃u,
    commutes_of_pow3_centralizer hs hd hex hK₃z hK₃u hpow, hYle, ⟨hJY, hJ'Y⟩, w, hwK₃, ?_, ?_⟩
  · intro h1
    rcases hJ₁ with ⟨-, h2⟩ | ⟨h2, -⟩
    · rw [hw, h2]
    · exact absurd (h1.symm.trans h2) hne
  · intro h1
    rcases hJ₁ with ⟨h2, -⟩ | ⟨-, h2⟩
    · exact absurd (h2.symm.trans h1) hne
    · rw [hw, h2]

end Fields

end CFSG.ClassicalInvolution.Q3.Q3T7S23
