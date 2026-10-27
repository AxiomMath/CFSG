module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Base
public import CFSG.ClassicalInvolution.Q3.Q3T7P24A01
public import CFSG.ClassicalInvolution.Q3.Q3T7P25X01
public import CFSG.ClassicalInvolution.Q3.Q3T7M00
public import CFSG.ClassicalInvolution.Uniform.UExact

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ComponentClassification
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)
open scoped MatrixGroups
namespace OmegaLie
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.OmegaLie
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
  (D : Q3T8.Asc77.OmegaLie Ω)

theorem exactMembers
    [Finite G] (hΩ : Q3T7M.HM Ω)
    (D : Q3T8.Asc77.OmegaLie Ω) : ExactMembers Ω := by
  intro L hL
  obtain ⟨i, R, hR, hLR⟩ := D.fundamental L hL
  obtain ⟨z, hz⟩ := hΩ.classical L hL
  obtain ⟨F, _, hFin, ι, hι⟩ := D.exists_sl2_range (by norm_num) i hR
  have hLψ : L = ((D.hom i).comp ι).range := by
    rw [MonoidHom.range_comp, hι, hLR]
  have hs : (Uniform.MemberType.sl2 3 1).IsSolvableType := (by norm_num : (3 : ℕ) ^ 1 = 3)
  obtain ⟨eL⟩ := hz.nonempty_equiv_sl2Three hs
  have h24 : 24 ∣ Nat.card L := by
    have := Subgroup.card_quotient_dvd_card (classicalInvolutionOddCore ↥L)
    rw [Nat.card_congr eL.toEquiv] at this
    rw [CFSG.ClassicalInvolution.natCard_sl2Three] at this
    exact this
  by_cases h4 : 4 ≤ Nat.card F
  · subst hLψ
    exact oddCore_range_eq_bot h4 _ (dvd_trans (by norm_num : 2 ∣ 24) h24)
  · have h2 : Nat.card L ≤ Nat.card SL(2, F) := by
      rw [hLψ]
      have : Function.Surjective ((D.hom i).comp ι).rangeRestrict :=
        MonoidHom.rangeRestrict_surjective _
      exact Nat.card_le_card_of_surjective _ this
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two] at h2
    have hFpos : 0 < Nat.card F := Nat.card_pos
    have hF3 : Nat.card F ≤ 3 := by omega
    have h4' : Nat.card F * (Nat.card F ^ 2 - 1) ≤ 24 := by
      interval_cases (Nat.card F) <;> norm_num
    have heq : Nat.card L = 24 :=
      Nat.le_antisymm (h2.trans h4') (Nat.le_of_dvd Nat.card_pos h24)
    exact hz.oddCore_eq_bot_of_natCard_eq (by norm_num : (3 : ℕ) ^ 1 = 3) heq
end OmegaLie
end Asc77

end

section

namespace Asc77.T3
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T3
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62
open scoped commutatorElement
variable {G : Type} [Group G]
section Members
variable {Ω : Set (Subgroup G)}

theorem omegaNbr_subset_omegaStarNbr
    [Finite G] (hΩ : Q3T8.Asc77.HypOmegaMod Ω)
    (K : Subgroup G) : omegaNbr Ω K ⊆ omegaStarNbr Ω K := Q3T6.Mu.omegaNbr_subset_omegaStarNbr hΩ K
end Members
end Asc77.T3

end

section

namespace Asc77.T3
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.T3
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62
open scoped commutatorElement
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem omegaStarNbr_symm
    [Finite G] (h62 : Q3T8.Asc77.L6_2) (hΩ : Q3T8.Asc77.HypOmegaMod Ω) {K J :
    Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : J ∈ omegaStarNbr Ω K) : K ∈ omegaStarNbr Ω J := Q3T6.Mu.omegaStarNbr_symm hΩ hK hJ h
end Asc77.T3

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

@[expose] def L7_17
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), Q3T8.Asc77.PartIHyp Ω →
    ∀ K ∈ Ω, dComp Ω K = dstarComp Ω K ∨
      ∀ W ∈ WSet Ω, MuIsoS3 Ω W ∨ MuIsoS4 Ω W ∨ MuIsoWylD4 Ω W
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.Thompson
section Boundary
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem dComp_subset_dstarComp
    (hΩ : Q3T8.Asc77.HypOmegaMod Ω) (K : Subgroup G) :
    dComp Ω K ⊆ dstarComp Ω K := Q3T6.Mu.dComp_subset_dstarComp hΩ K
end Boundary
section Connected
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson.Ctx
variable (c : Q3CL.Thompson.Ctx Ω W)
include c

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.mem_dComp_of_connected
    (hconn :
    DbarConnected Ω W) {K₁ J₁ R T : Subgroup G}
    (hK₁ : K₁ ∈ Ω) (hJ₁ : J₁ ∈ Ω) (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W)
    (hRK : IsSylow2In R K₁) (hTJ : IsSylow2In T J₁) : J₁ ∈ dComp Ω K₁ :=
  Q3T6.Mu.ctx_mem_dComp_of_connected c hconn hK₁ hJ₁ hR hT hRK hTJ
end Ctx
end Connected
end Thompson
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G]
section Transport
variable [Finite G] {Ω : Set (Subgroup G)} {K L : Subgroup G}

theorem Std7.of_twin
    {K' L' : Subgroup G} {z : G} (hs : Q3T8.Asc77.Std7 Ω K K' z)
    (hL : L ∈ twinSet Ω K) (hL' : L' ∈ twinSet Ω K) (hne : L' ≠ L) :
    Q3T8.Asc77.Std7 Ω L L' z where
  stand := hs.stand.of_mem hL.1
  disconnected := hs.disconnected
  hz := isUniqueInvolution_of_mem_twinSet hs.hz hL
  hK' := by rw [twinSet_eq_of_mem_twinSet hs.hz hL]; exact hL'
  hne := hne
  cex := hs.cex
end Transport
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

structure Hyp22 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' K₃ : Subgroup G)
    (z u₁ u₂ u₃ : G) : Prop where
  std : Q3T8.Asc77.Std7 Ω K K' z
  perp : KPerp Ω K = twinSet Ω K
  hK₃ : K₃ ∈ twinSet Ω K
  hK₃K : K₃ ≠ K
  hK₃K' : K₃ ≠ K'
  hu₁ : u₁ ∈ K ∧ orderOf u₁ = 4
  hu₂ : u₂ ∈ K' ∧ orderOf u₂ = 4
  hu₃ : u₃ ∈ K₃ ∧ orderOf u₃ = 4
  hB : IsElemAbelian2 (Subgroup.closure {u₁ * u₂, z, u₂ * u₃}) 3

@[expose] def C22_2
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃ →
      Odd (Nat.card ↥(alphaOf (Subgroup.closure {u₁ * u₂, z}))) ∧
        ∀ A : Subgroup G, A ≤ Subgroup.closure {u₁ * u₂, z, u₂ * u₃} → IsElemAbelian2 A 2 →
          alphaOf A = alphaOf (Subgroup.closure {u₁ * u₂, z})

@[expose] def C22_4
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃ →
      ∀ W ∈ WSet Ω, MuIsoWylD4 Ω W

@[expose] def C22_7
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃ →
      alphaOf (Subgroup.closure {u₁ * u₂, z}) = ⊥

@[expose] def C22_9
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃ → ConcOrTF4 G

@[expose] def C22_setup
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Q3T8.Asc77.Std7 Ω K K' z → KPerp Ω K = twinSet Ω K → KPerp Ω K ≠ {K, K'} →
      ∃ (K₃ : Subgroup G) (u₁ u₂ u₃ : G), Q3T8.Asc77.Hyp22 Ω K K' K₃ z u₁ u₂ u₃

@[expose] def C22_1
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Q3T8.Asc77.Std7 Ω K K' z → KPerp Ω K = twinSet Ω K → KPerp Ω K = {K, K'} ∨ ConcOrTF4 G

theorem c22_1_of_steps
    (hsetup : Q3T8.Asc77.C22_setup) (h9 : Q3T8.Asc77.C22_9) : Q3T8.Asc77.C22_1
    := by
  intro G _ _ _ Ω K K' z hs hperp
  by_cases h : KPerp Ω K = {K, K'}
  · exact Or.inl h
  · obtain ⟨K₃, u₁, u₂, u₃, hyp⟩ := hsetup G Ω K K' z hs hperp h
    exact Or.inr (h9 G Ω K K' K₃ z u₁ u₂ u₃ hyp)
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped commutatorElement
section Chain
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J K' : Subgroup G} {z t z' : G}

theorem exists_noncomm_of_isClassicalMember
    [Finite G] {L : Subgroup G} {w : G}
    (hw : Q3T8.Generic.IsClassicalMember L w) : ∃ x y : G, x * y ≠ y * x := by
  obtain ⟨x, -, y, -, h⟩ := Q3T8.Asc77.ih8_exists_noncomm hw
  exact ⟨x, y, h⟩
end Chain
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77

theorem l7_17_proved
    : Q3T8.Asc77.L7_17 := fun G _ _ Ω hP K hK =>
  (Classical.em _).elim Or.inl fun h => Or.inr fun W hW =>
    Q3T8.Asc77.l7_10_proved G Ω hP W hW (Q3T8.Asc77.thompsonGraphAll G Ω hP hK h hW)
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
