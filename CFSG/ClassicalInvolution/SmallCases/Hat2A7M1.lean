module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7M0
public import CFSG.ClassicalInvolution.Q3.Q3T7F25L75
public import CFSG.ClassicalInvolution.Q3.Q3T7F25PW

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false
namespace CFSG.ClassicalInvolution.Hat2A7M
abbrev _root_.CFSG.ClassicalInvolution.Hat2A7M.Asc77.Hyp25Data :=
  @CFSG.ClassicalInvolution.Asc77.Hyp25Data
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
theorem mem_kPerp_of_twin (hΩ : HypOmegaMod Ω) {K L : Subgroup G} (hK : K ∈ Ω)
    (hL : L ∈ Ω) {z : G} (hzK : IsUniqueInvolution K z) (hzL : IsUniqueInvolution L z) :
    K ∈ KPerp Ω L :=
  CFSG.ClassicalInvolution.T7F25.Asc77.mem_kPerp_of_twin hΩ hK hL hzK hzL
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
section Finite
variable [Finite G]
theorem exists_mem_of_mem_etaSet (hΩ : HypOmegaMod Ω) {S : Subgroup G} {η : Set (Subgroup G)}
    (h : η ∈ etaSet Ω S) {K : Subgroup G} (hK : K ∈ Ω) {U : Subgroup G} (hU : U ∈ UinS Ω S)
    (hUK : U ≤ K) : ∃ V ∈ η, V ≤ K :=
  CFSG.ClassicalInvolution.T7F25.Asc77.exists_mem_of_mem_etaSet hΩ h hK hU hUK
end Finite
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

structure Std7 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G) : Prop where
  stand : AscStand Ω K
  disconnected : ¬ DConnected Ω
  hz : IsUniqueInvolution K z
  hK' : K' ∈ twinSet Ω K
  hne : K' ≠ K
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

@[expose] def Hyp23 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G) : Prop :=
  Std7 Ω K K' z ∧ KPerp Ω K = {K, K'}
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
namespace T7A
open CFSG.ClassicalInvolution.Asc77.T7A
theorem isSubnormal_centralizer (hΩ : Uniform.HypOmegaModU .twoA7 Ω) {L : Subgroup G} (hL : L ∈
    Ω) {z : G}
    (hz : IsUniqueInvolution L z) : IsSubnormal L (Subgroup.centralizer ({z} : Set G)) := by
  obtain ⟨z', hz'⟩ := hΩ.classical L hL
  have hzsq : z' * z' = 1 := by
    have := pow_orderOf_eq_one z'
    rwa [hz'.orderOf_eq_two, pow_two] at this
  have hzne : z' ≠ 1 := by
    intro h
    have := hz'.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  obtain rfl : z' = z := (hz.unique z' hz'.mem hzsq).resolve_left hzne
  exact hz'.subnormal
end T7A
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

structure Hyp25 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' W : Subgroup G)
    (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G) : Prop where
  std : Hyp23 Ω K K' z
  hW : W ∈ WSet Ω
  hzW : z ∈ W
  hE4 : MuIsoE4 Ω W
  hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)
  hR' : R' ∈ RSet Ω ∧ R' ≤ K' ∧ R' ≤ (S : Subgroup G)
  hRS : ∀ X ∈ RSet Ω, X ≤ (S : Subgroup G) → X = R ∨ X = R'
  hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s
  ht : t ∈ (S : Subgroup G) ∧ t ≠ z ∧ ∃ g : G, g * z * g⁻¹ = t
  hu₁ : u₁ ∈ R ∧ orderOf u₁ = 4 ∧ ∀ r ∈ R, r * u₁ * r⁻¹ ∈ Subgroup.zpowers u₁
  hu₂ : u₂ ∈ R' ∧ orderOf u₂ = 4 ∧ ∀ r ∈ R', r * u₂ * r⁻¹ ∈ Subgroup.zpowers u₂

@[expose] def C25_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) =
        Subgroup.zpowers z

@[expose] def C25_16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), ¬ IsFAut R' a

@[expose] def C25_19 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') ∨ TwoSubgroupsFourGenerated G

@[expose] def C25_21 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') → TwoSubgroupsFourGenerated G

@[expose] def C25_setup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23 Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → MuIsoE4 Ω W →
      ∃ (S : Sylow 2 G) (R R' : Subgroup G) (t u₁ u₂ : G), Hyp25 Ω K K' W S R R' z t u₁ u₂

@[expose] def C25_E4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23 Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → MuIsoE4 Ω W → TwoSubgroupsFourGenerated G

theorem c25_E4_of_steps (hsetup : C25_setup) (h19 : C25_19) (h21 : C25_21) :
    C25_E4 := by
  intro G _ _ _ Ω K K' z hs W hW hzW hE4
  obtain ⟨S, R, R', t, u₁, u₂, hyp⟩ := hsetup G Ω K K' z hs W hW hzW hE4
  rcases h19 G Ω K K' W S R R' z t u₁ u₂ hyp with h | h
  · exact h21 G Ω K K' W S R R' z t u₁ u₂ hyp h
  · exact h
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

structure Hyp23Setting {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G) : Prop where
  stand : AscStand Ω K
  disconnected : ¬ DConnected Ω
  hz : IsUniqueInvolution K z
  hK' : K' ∈ twinSet Ω K
  hne : K' ≠ K
  perp : KPerp Ω K = {K, K'}

section

theorem _root_.CFSG.ClassicalInvolution.Hat2A7M.Asc77.AscStand.toF
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K : Subgroup G} (h : CFSG.ClassicalInvolution.Hat2A7M.Asc77.AscStand Ω K) :
    CFSG.ClassicalInvolution.T7F25.Asc77.AscStand Ω K where
  hyp := h.hyp
  aEmpty := h.aEmpty
  mem := h.mem
  trans := h.trans
  gen := h.gen
  key := Hat2A7P1.thompsonKey ⟨h.hyp, h.cls, h.aEmpty⟩
  subn := fun _ hL _ hz =>
    CFSG.ClassicalInvolution.Hat2A7M.Asc77.T7A.isSubnormal_centralizer h.modU hL hz
  nine3 := Hat2A7P1.l9_3 ⟨h.hyp, h.cls, h.aEmpty⟩

theorem _root_.CFSG.ClassicalInvolution.Hat2A7M.Asc77.Std7.toF
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' : Subgroup G} {z : G}
    (h : CFSG.ClassicalInvolution.Hat2A7M.Asc77.Std7 Ω K K' z) :
    CFSG.ClassicalInvolution.T7F25.Asc77.Std7 Ω K K' z where
  stand := h.stand.toF
  disconnected := h.disconnected
  hz := h.hz
  hK' := h.hK'
  hne := h.hne

theorem _root_.CFSG.ClassicalInvolution.Hat2A7M.Asc77.Hyp23.toF
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' : Subgroup G} {z : G}
    (h : CFSG.ClassicalInvolution.Hat2A7M.Asc77.Hyp23 Ω K K' z) :
    CFSG.ClassicalInvolution.T7F25.Asc77.Hyp23 Ω K K' z :=
  ⟨h.1.toF, h.2⟩

theorem _root_.CFSG.ClassicalInvolution.Hat2A7M.Asc77.Hyp23Setting.toF
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' : Subgroup G} {z : G}
    (h : CFSG.ClassicalInvolution.Hat2A7M.Asc77.Hyp23Setting Ω K K' z) :
    CFSG.ClassicalInvolution.T7F25.Asc77.Hyp23Setting Ω K K' z where
  stand := h.stand.toF
  disconnected := h.disconnected
  hz := h.hz
  hK' := h.hK'
  hne := h.hne
  perp := h.perp

end
section Basic
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {z u e g : G}

theorem Hyp23.setting (h : Hyp23 Ω K K' z) : Hyp23Setting Ω K K' z where
  stand := h.1.stand
  disconnected := h.1.disconnected
  hz := h.1.hz
  hK' := h.1.hK'
  hne := h.1.hne
  perp := h.2

theorem Hyp23Setting.twinSet_eq (h : Hyp23Setting Ω K K' z) : twinSet Ω K = {K, K'} :=
  CFSG.ClassicalInvolution.T7F25.Asc77.Hyp23Setting.twinSet_eq h.toF
end Basic
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
section Conversions
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z u t u₁ u₂ : G}

theorem Hyp25Data.hyp25 (h : Hyp25Data Ω K K' W S R R' z t u₁ u₂) (hs : Hyp23 Ω K K' z) :
    Hyp25 Ω K K' W S R R' z t u₁ u₂ where
  std := hs
  hW := h.hW
  hzW := h.hzW
  hE4 := h.hE4
  hR := h.hR
  hR' := h.hR'
  hRS := h.hRS
  hzS := h.hzS
  ht := h.ht
  hu₁ := h.hu₁
  hu₂ := h.hu₂
end Conversions
namespace T7C
open CFSG.ClassicalInvolution.Asc77.T7C
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
theorem isSylow2In_of_mem_RSet_of_le (hΩ : HypOmegaMod Ω) {K R : Subgroup G}
    (hK : K ∈ Ω) (hR : R ∈ RSet Ω) (hRK : R ≤ K) : IsSylow2In R K :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hR hRK
end T7C
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
namespace T75
open CFSG.ClassicalInvolution.Asc77.T75
variable {G : Type} [Group G]
theorem exists_odd_normalizer_conj {Ω : Set (Subgroup G)} [Finite G]
    (hΩ : Uniform.HypOmegaModU .twoA7 Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (_hz : IsUniqueInvolution K z) {R V U : Subgroup G} (hR : IsSylow2In R K) (_hVR : V ≤ R)
    (_hUR : U ≤ R) (_hcV : IsCyclic ↥V) (_hcU : IsCyclic ↥U) (_hV4 : Nat.card V = 4)
    (_hU4 : Nat.card U = 4) (hR8 : Nat.card R = 8) :
    ∃ y ∈ K, y ∈ Subgroup.normalizer (R : Set G) ∧ Odd (orderOf y) ∧ conjSub y V = U := by
  exfalso
  obtain ⟨w, hw⟩ := hΩ.classical K hK
  have h16 := Hat2A7P1.sylow16_of_witness hw.witness hR
  omega

theorem _root_.CFSG.ClassicalInvolution.Hat2A7M.Asc77.T75.oddConj
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : Uniform.HypOmegaModU .twoA7 Ω) : CFSG.ClassicalInvolution.T7F25.Asc77.T75.OddConj Ω :=
  fun _ hK _ hz _ _ _ hR hVR hUR hcV hcU hV4 hU4 hR8 =>
    CFSG.ClassicalInvolution.Hat2A7M.Asc77.T75.exists_odd_normalizer_conj hΩ hK hz hR hVR hUR hcV hcU hV4 hU4 hR8

section

theorem _root_.CFSG.ClassicalInvolution.Hat2A7M.Asc77.AscStand.e4All
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
    (h : CFSG.ClassicalInvolution.Hat2A7M.Asc77.AscStand Ω K) {W₀ : Subgroup G} (hW₀ : W₀ ∈ WSet Ω)
    (hE4 : MuIsoE4 Ω W₀) : ∀ W' ∈ WSet Ω, MuIsoE4 Ω W' := fun W' hW' => by
  obtain ⟨e⟩ := CFSG.ClassicalInvolution.T7F25.Asc77.l7_5_2_of h.hyp
    (CFSG.ClassicalInvolution.Hat2A7M.Asc77.T75.oddConj h.modU) hW' hW₀
  obtain ⟨f⟩ := hE4
  exact ⟨e.trans f⟩

theorem _root_.CFSG.ClassicalInvolution.Hat2A7M.Asc77.Hyp25.toF
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}
    (h : CFSG.ClassicalInvolution.Hat2A7M.Asc77.Hyp25 Ω K K' W S R R' z t u₁ u₂) :
    CFSG.ClassicalInvolution.T7F25.Asc77.Hyp25 Ω K K' W S R R' z t u₁ u₂ :=
  { h with
    std := h.std.toF
    hE4 := h.std.1.stand.e4All h.hW h.hE4 }

end
end T75
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan
    CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
    CFSG.LieType.CurtisTits CFSG.Blueprint
namespace T7C
open CFSG.ClassicalInvolution.Asc77.T7C

theorem exists_not_commute_of_stand {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K : Subgroup G} (hs : AscStand Ω K) : ∃ a b : G, a * b ≠ b * a :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7C.exists_not_commute_of_stand hs.toF
end T7C
variable {G : Type} [Group G] [IsSimpleGroup G]
end Asc77
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Asc77.T7C2

@[expose] def C25_2_t : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      ∃ t' ∈ (S : Subgroup G), (∃ g : G, g * z * g⁻¹ = t') ∧ conjSub t' R = R'

@[expose] def C25_17_idx : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥(S : Subgroup G) = 2 * Nat.card ↥(R ⊔ R') ∨
        Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R')
theorem c25_19_of_sylow (h2 : C25_2_t) (h17 : C25_17_idx) : C25_19 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  exact CFSG.ClassicalInvolution.T7F25.Asc77.c25_19_of_sylow_at hyp.toF
    (h2 G Ω K K' W S R R' z t u₁ u₂ hyp) (h17 G Ω K K' W S R R' z t u₁ u₂ hyp)
end Asc77
end
end CFSG.ClassicalInvolution.Hat2A7M
