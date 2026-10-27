module

public import CFSG.ClassicalInvolution.Asc77.AscExactDMain
public import CFSG.ClassicalInvolution.Asc77.AscT7BExit23
public import CFSG.ClassicalInvolution.Asc77.AscT7BExit22

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.RouteD
  CFSG.LieType.Universal
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair)

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C22_chainEx : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃ →
      (∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) →
        (SectionOrthType p f Ω (rLayer Ω (u₁ * u₂)) 6 (piSign p f) ∧
          (⨆ M ∈ twinSet Ω K, M) ⊔ rLayer Ω (u₁ * u₂) = ⊤) →
          ExactMembers Ω →
          ∃ U : Fin 4 → Subgroup G, (∀ k, U k ∈ Ω) ∧
            (∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i → Commutes (U i) (U j)) ∧
            (∀ i j : Fin 4, edgeD 4 i j →
              ∃ W, LinearBlockStandardPair (GaloisField p f) W (U i) (U j)) ∧ ⨆ k, U k = ⊤

variable {p f}

theorem Hyp22.exactMembers {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G} (h : Hyp22 p f Ω K K' K₃ z u₁ u₂ u₃)
    (h9 : p ^ f ≠ 9) (hα : alphaOf (Subgroup.closure {u₁ * u₂, z}) = ⊥) : ExactMembers Ω := by
  have hst := h.std.stand
  have hu : u₁ * u₂ ∈ K ⊔ K' := Subgroup.mul_mem_sup h.hu₁.1 h.hu₂.1
  have hBm : ∀ x ∈ Subgroup.closure ({u₁ * u₂, z, u₂ * u₃} : Set G), x * x = 1 := h.hB.2
  have hu2 : (u₁ * u₂) * (u₁ * u₂) = 1 := hBm _ (Subgroup.subset_closure (by simp))
  have hcap : ∀ w ∈ K, w ∈ K' → orderOf w ≠ 4 := by
    intro w hwK hwK' hw4
    have hA : IsPGroup 2 (Subgroup.zpowers w) :=
      IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hw4]; norm_num)
    have := hst.hyp.card_le_two_of_le_inf hst.mem h.std.hK'.1 h.std.hne.symm hA
      (Subgroup.zpowers_le.mpr hwK) (Subgroup.zpowers_le.mpr hwK')
    rw [Nat.card_zpowers, hw4] at this
    omega
  have hu₂K' := h.hu₂.1
  have hu1 : u₁ * u₂ ≠ 1 := by
    intro h1
    have : u₂ = u₁⁻¹ := eq_inv_of_mul_eq_one_right h1
    exact hcap u₂ (this ▸ K.inv_mem h.hu₁.1) hu₂K' h.hu₂.2
  have huz : u₁ * u₂ ≠ z := by
    intro h1
    have : u₂ = u₁⁻¹ * z := by rw [← h1]; group
    exact hcap u₂ (this ▸ K.mul_mem (K.inv_mem h.hu₁.1) h.std.hz.mem) hu₂K' h.hu₂.2
  exact ExactD.exactMembers_of_alphaOf_twin_stand hst h9 h.std.hz h.std.hK' h.std.hne hu hu2 hu1
    huz hα

theorem c22_chain_of_exact (h9 : p ^ f ≠ 9) (h7 : C22_7 p f) (hex : C22_chainEx p f) :
    C22_chain p f :=
  fun G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ hyp h4 h8 =>
    hex G Ω K K' K₃ z u₁ u₂ u₃ hyp h4 h8
      (hyp.exactMembers h9 (h7 G Ω K K' K₃ z u₁ u₂ u₃ hyp))

theorem c22_1_of_inputs_exact (h9 : p ^ f ≠ 9) (hE : ThmEWithSylow p f) (hz51 : Hyp22Hyp51z p f)
    (hu51 : Hyp22Hyp51u p f) (hsig : C22_4_sigma p f) (hcent : C22_4_cent p f)
    (h8 : C22_8 p f) (h7 : C22_7 p f) (hex : C22_chainEx p f) : C22_1 p f :=
  c22_1_of_inputs hE hz51 hu51 hsig hcent h8 (c22_chain_of_exact h9 h7 hex)

variable (p f)

@[expose] def C23_chainEx : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23Setting p f Ω K K' z →
      Hyp23bData Ω K K' W z u e g →
        (alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥ ∧ rLayer Ω e ⊔ rLayer Ω u = ⊤) →
        SectionOrthType p f Ω (rLayer Ω e) 6 (piSign p f) →
        (SectionOrthType p f Ω (rLayer Ω u) 5 true ∨
          SectionOrthType p f Ω (rLayer Ω u) 6 (!piSign p f)) →
          ExactMembers Ω →
          (∃ U : Fin 3 → Subgroup G, U 0 ∈ Ω ∧ Commutes (U 0) (U 2) ∧
              (∃ V, LinearBlockStandardPair (GaloisField p f) V (U 0) (U 1)) ∧
              (∃ V, SymplecticBlockPair (GaloisField p f) V (U 1) (U 2)) ∧ ⨆ k, U k = ⊤) ∨
          (∃ U : Fin 3 → Subgroup G, U 0 ∈ Ω ∧ Commutes (U 0) (U 2) ∧
              (∃ V, LinearBlockStandardPair (GaloisField p f) V (U 0) (U 1)) ∧
              (∃ V, TwistedB2BlockPair (minusCoeffs_irr p f) V (U 1) (U 2)) ∧ ⨆ k, U k = ⊤)

variable {p f}

theorem c23_chain_of_exact (h9 : p ^ f ≠ 9) (hex : C23_chainEx p f) : C23_chain p f :=
  fun G _ _ _ Ω K K' W z u e g hs hd hα h6 hY =>
    hex G Ω K K' W z u e g hs hd hα h6 hY
      (ExactD.exactMembers_of_alphaOf_twin_stand hs.stand h9 hs.hz hs.hK' hs.hne hd.hu hd.hu2 hd.hu1
        hd.huz hα.1)

theorem c23_3_of_inputs_exact (h9 : p ^ f ≠ 9) (hE : ThmEWithSylow p f) (htr : C23_2_trans p f)
    (hfuse : C23_2_fuse p f) (hsetup : C23_setupSetting p f) (h4 : C23_4 p f)
    (h5 : C23_5 p f) (h7 : C23_7 p f) (hΓ : C23_Gamma p f) (hnoZ : C23_9_noZ p f)
    (hgen : C23_9_gen p f) (hchain : C23_chainEx p f)
    (hg6 : SpinMinus6Generated (minusCoeffs_irr p f)) : C23_3 p f :=
  c23_3_of_inputs hE htr hfuse hsetup h4 h5 h7 hΓ hnoZ hgen (c23_chain_of_exact h9 hchain) hg6

end CFSG.ClassicalInvolution.Asc77
