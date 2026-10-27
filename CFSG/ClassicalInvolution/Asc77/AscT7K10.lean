module

public import CFSG.ClassicalInvolution.Asc77.AscT7K9
public import CFSG.ClassicalInvolution.Asc77.AscT7HX23
public import CFSG.ClassicalInvolution.Asc77.AscT7K3

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Asc77.ExactLayer

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C23_5X_mu : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23b p f Ω K K' W z u e g →
      ∀ WY ∈ WSet (restrictFamily (exactFamily Ω u) (rLayer Ω u)),
        MuIsoE4 (restrictFamily (exactFamily Ω u) (rLayer Ω u)) WY

@[expose] def C23_5X_type : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23b p f Ω K K' W z u e g →
      (u * e ∈ zStarOf (rLayer Ω u) ∨ LayerOrthType p f Ω u 5 true ∨
        LayerOrthType p f Ω u 6 (!piSign p f))

@[expose] def C23_GammaU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23Setting p f Ω K K' z →
      Hyp23bData Ω K K' W z u e g →
        Subgroup.centralizer ({u} : Set G) ≤
          gamma2 (Subgroup.closure {u * e, u, z}) (Subgroup.centralizer ({u} : Set G))

variable {p f}

theorem c23_5X_of_parts (hμ : C23_5X_mu p f) (hT : C23_5X_type p f) : C23_5X p f := by
  intro G _ _ _ Ω K K' W z u e g h
  exact ⟨T7K.c23_5X_one_proved h.std.setting h.data, hμ G Ω K K' W z u e g h,
    hT G Ω K K' W z u e g h⟩

theorem c23_Gamma_of_u (hu : C23_GammaU p f) : C23_Gamma p f := by
  intro G _ _ _ Ω K K' W z u e g hs hd
  exact ⟨T7K.centralizer_z_le_gamma2 hs hd, hu G Ω K K' W z u e g hs hd⟩

end CFSG.ClassicalInvolution.Asc77
