module

public import CFSG.ClassicalInvolution.Asc77.AscT7W13
public import CFSG.ClassicalInvolution.Asc77.AscExactDChain

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair)

variable {p f : ℕ} [Fact p.Prime]

theorem T7Y.thm7A_of_chain23
    (hconn : C21_14_Y_conn_W p f)
    (hres : TwinSqOrth p) (h4 : Hyp22FourTwins p f) (hF : Hyp22Fuse p f)
    (hgen22 : C22_8Gen p f) (hZ : Hyp22ZStarCu p f) (hchain22 : C22_chainSettingX p f)
    (hchain23 : C23_chainX p f)
    (hcore : C24_9_core p f) (hbig : C24_8_big p f) (hpair : C24_pair p f)
    (h11 : C25_11 p f) (h16 : C25_16 p f) (h20 : C25_20_ex p f) : Thm7A p f :=
  thm7A_of_inputs₁₃ hconn hres h4 hF hgen22 hZ hchain22 hchain23 hcore hbig hpair h11 h16 h20

theorem T7Y.c23_3_of_chainX (hp2 : p ≠ 2) (hchain : C23_chainX p f) : C23_3 p f :=
  c23_3_of_inputsK (thmEWithSylow_of_nonToral f G2D4Models.g2NonToralGenerate_all)
    (c23_2_trans_proved p f) (c23_setupSetting_proved p f) c23_4X_proved c23_5X_type_proved
    c23_7_proved c23_GammaU_proved c23_9_noZX_proved c23_9_genX_proved hchain
    (spinMinus6Generated_galois hp2)

variable (p f)

@[expose] def C23_chain5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23Setting p f Ω K K' z →
      Hyp23bData Ω K K' W z u e g →
        (alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥ ∧ rLayer Ω e ⊔ rLayer Ω u = ⊤) →
        LayerOrthType p f Ω e 6 (piSign p f) → LayerOrthType p f Ω u 5 true →
          ∃ U : Fin 3 → Subgroup G, U 0 ∈ Ω ∧ Commutes (U 0) (U 2) ∧
            (∃ V, LinearBlockStandardPair (GaloisField p f) V (U 0) (U 1)) ∧
            (∃ V, SymplecticBlockPair (GaloisField p f) V (U 1) (U 2)) ∧ ⨆ k, U k = ⊤

@[expose] def C23_chain6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23Setting p f Ω K K' z →
      Hyp23bData Ω K K' W z u e g →
        (alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥ ∧ rLayer Ω e ⊔ rLayer Ω u = ⊤) →
        LayerOrthType p f Ω e 6 (piSign p f) → LayerOrthType p f Ω u 6 (!piSign p f) →
          ∃ U : Fin 3 → Subgroup G, U 0 ∈ Ω ∧ Commutes (U 0) (U 2) ∧
            (∃ V, LinearBlockStandardPair (GaloisField p f) V (U 0) (U 1)) ∧
            (∃ V, TwistedB2BlockPair (minusCoeffs_irr p f) V (U 1) (U 2)) ∧ ⨆ k, U k = ⊤

theorem c23_chainX_of_chain56 (h5 : C23_chain5 p f) (h6 : C23_chain6 p f) : C23_chainX p f := by
  intro G _ _ _ Ω K K' W z u e g hs hd hα hE hY
  rcases hY with hY | hY
  · exact Or.inl (h5 G Ω K K' W z u e g hs hd hα hE hY)
  · exact Or.inr (h6 G Ω K K' W z u e g hs hd hα hE hY)

@[expose] def C23_exact9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23Setting p f Ω K K' z →
      Hyp23bData Ω K K' W z u e g → alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥ →
        ExactMembers Ω

variable {p f}

theorem c23_chainX_of_chainEx (hex : C23_chainEx p f) (h9 : p ^ f = 9 → C23_exact9 p f) :
    C23_chainX p f := by
  intro G _ _ _ Ω K K' W z u e g hs hd hα h6 hY
  have hst := hs.stand
  have hex' : ExactMembers Ω := by
    by_cases hq9 : p ^ f = 9
    · exact h9 hq9 G Ω K K' W z u e g hs hd hα.1
    · exact ExactD.exactMembers_of_alphaOf_twin_stand hst hq9 hs.hz hs.hK' hs.hne hd.hu hd.hu2
        hd.hu1 hd.huz hα.1
  have h6' : SectionOrthType p f Ω (rLayer Ω e) 6 (piSign p f) :=
    (layerOrthType_iff_of_exactMembers hst.odd hst.five hst.hyp hex' hd.he2 6 _).mp h6
  have hY' : SectionOrthType p f Ω (rLayer Ω u) 5 true ∨
      SectionOrthType p f Ω (rLayer Ω u) 6 (!piSign p f) :=
    hY.imp ((layerOrthType_iff_of_exactMembers hst.odd hst.five hst.hyp hex' hd.hu2 5 _).mp)
      ((layerOrthType_iff_of_exactMembers hst.odd hst.five hst.hyp hex' hd.hu2 6 _).mp)
  exact hex G Ω K K' W z u e g hs hd hα h6' hY' hex'

end CFSG.ClassicalInvolution.Asc77
