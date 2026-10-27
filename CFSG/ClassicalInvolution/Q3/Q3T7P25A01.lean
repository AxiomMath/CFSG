module

public import CFSG.ClassicalInvolution.Q3.Q3T8Defs
public import CFSG.ClassicalInvolution.Q3.Q3T7P25A00
public import CFSG.ClassicalInvolution.Q3.Q3T7F25L75
public import CFSG.ClassicalInvolution.Asc77.AscT7BBasic
public import CFSG.ClassicalInvolution.Q3.Q3CLNine3

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

abbrev _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp25Data :=
  @CFSG.ClassicalInvolution.Asc77.Hyp25Data

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

@[expose] def L6_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), HypOmegaMod Ω →
      ∀ S : Sylow 2 G, ∀ U ∈ USet Ω, U ≤ (S : Subgroup G) → ∀ η ∈ etaG Ω,
        (∀ V ∈ η, V ≤ (S : Subgroup G)) →
          ∃! V : Subgroup G, V ∈ η ∧ (U = V ∨ (U ⊔ V) ∈ RSet Ω)
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

@[expose] def L7_5_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), Uniform.HypOmegaModU (.sl2 3 1) Ω →
      ∀ W ∈ WSet Ω, ∀ W' ∈ WSet Ω, Nonempty (↥(muGroup Ω W) ≃* ↥(muGroup Ω W'))
end Asc77

end

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

theorem HypOmegaMod.natCard_eq_of_mem_USet (hΩ : HypOmegaMod Ω) {K U V : Subgroup G}
    (hK : K ∈ Ω) (hU : U ∈ USet Ω) (hV : V ∈ USet Ω) (hUK : U ≤ K) (hVK : V ≤ K) :
    Nat.card U = Nat.card V :=
  CFSG.ClassicalInvolution.T7F25.Asc77.HypOmegaMod.natCard_eq_of_mem_USet hΩ hK hU hV hUK hVK

theorem HypOmegaMod.eq_or_sup_mem_RSet (hΩ : HypOmegaMod Ω) {K U V : Subgroup G} (hK : K ∈ Ω)
    (hU : U ∈ USet Ω) (hV : V ∈ USet Ω) (hUK : U ≤ K) (hVK : V ≤ K)
    (hT : IsPGroup 2 ↥(U ⊔ V)) : U = V ∨ (U ⊔ V ∈ RSet Ω ∧ IsSylow2In (U ⊔ V) K) :=
  CFSG.ClassicalInvolution.T7F25.Asc77.HypOmegaMod.eq_or_sup_mem_RSet hΩ hK hU hV hUK hVK hT
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
  cex : ¬ ConcOrTF4 G
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic

theorem l6_8 : L6_8 :=
  CFSG.ClassicalInvolution.T7F25.Asc77.l6_8
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
open CFSG.Open CFSG.ClassicalInvolution.Generic
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G]
section Mu
variable {Ω : Set (Subgroup G)}

theorem conjSub_mem_DSet_conj [Finite G] (hΩ : HypOmegaMod Ω) {W R : Subgroup G} (hR : R ∈ DSet Ω W)
    (g : G) : conjSub g R ∈ DSet Ω (conjSub g W) :=
  CFSG.ClassicalInvolution.T7F25.Asc77.Thompson.conjSub_mem_DSet_conj hΩ hR g

theorem conjSub_MGrp [Finite G] (hΩ : HypOmegaMod Ω) (g : G) (W : Subgroup G) :
    conjSub g (MGrp Ω W) = MGrp Ω (conjSub g W) :=
  CFSG.ClassicalInvolution.T7F25.Asc77.Thompson.conjSub_MGrp hΩ g W

noncomputable def muGroupConjEquiv [Finite G] (hΩ : HypOmegaMod Ω) (g : G) (W : Subgroup G) :
    ↥(muGroup Ω W) ≃* ↥(muGroup Ω (conjSub g W)) :=
  (MulEquiv.subgroupMap (nquotConj g (conjSub_sup_OCW g W)) (muGroup Ω W)).trans
    (MulEquiv.subgroupCongr (by
      ext q
      constructor
      · rintro ⟨q₀, hq₀, rfl⟩
        obtain ⟨m, hm, rfl⟩ := mem_muGroup_iff.mp hq₀
        have hmN : m ∈ Subgroup.normalizer (W : Set G) := MGrp_sup_le_normalizer Ω W hm
        show nquotConj g (conjSub_sup_OCW g W) (piG W m) ∈ _
        rw [nquotConj_piG g W hmN]
        refine piG_mem_muGroup ?_
        rw [← conjSub_MGrp hΩ, ← conjSub_OCW, ← Asc77.conjSub_sup]
        exact conj_mem_conjSub hm
      · intro hq
        obtain ⟨m', hm', rfl⟩ := mem_muGroup_iff.mp hq
        rw [← conjSub_MGrp hΩ, ← conjSub_OCW, ← Asc77.conjSub_sup, mem_conjSub_iff] at hm'
        refine ⟨piG W (g⁻¹ * m' * g), piG_mem_muGroup hm', ?_⟩
        have hmN : g⁻¹ * m' * g ∈ Subgroup.normalizer (W : Set G) :=
          MGrp_sup_le_normalizer Ω W hm'
        show nquotConj g (conjSub_sup_OCW g W) (piG W (g⁻¹ * m' * g)) = _
        rw [nquotConj_piG g W hmN]
        congr 1
        group))
end Mu
end Thompson
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
section Components
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
end Components
section Boundary
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
end Boundary
section GroupW
variable {G : Type} [Group G]
end GroupW
section Existence
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_W_of_mem_omegaStarNbr (hΩ : HypOmegaMod Ω)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ omegaStarNbr Ω K) :
    ∃ W ∈ WSet Ω, ∃ R ∈ DSet Ω W, ∃ T ∈ DSet Ω W, IsSylow2In R K ∧ IsSylow2In T J :=
  CFSG.ClassicalInvolution.T7F25.Asc77.Thompson.exists_W_of_mem_omegaStarNbr hΩ hK hJ
end Existence
section Connected
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77.Thompson.Ctx
variable (c : Q3CL.Thompson.Ctx Ω W)
include c
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
open scoped commutatorElement
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
namespace T7A
open CFSG.ClassicalInvolution.Asc77.T7A

theorem isSubnormal_centralizer (hΩ : Uniform.HypOmegaModU (.sl2 3 1) Ω) {L : Subgroup G} (hL : L ∈
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
      Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') ∨ ConcOrTF4 G

@[expose] def C25_21 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') → ConcOrTF4 G

@[expose] def C25_setup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23 Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → MuIsoE4 Ω W →
      ∃ (S : Sylow 2 G) (R R' : Subgroup G) (t u₁ u₂ : G), Hyp25 Ω K K' W S R R' z t u₁ u₂

@[expose] def C25_E4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Hyp23 Ω K K' z → ∀ W ∈ WSet Ω, z ∈ W → MuIsoE4 Ω W → ConcOrTF4 G

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

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AscStand.toF
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K : Subgroup G} (h : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AscStand Ω K) :
    CFSG.ClassicalInvolution.T7F25.Asc77.AscStand Ω K where
  hyp := h.hyp
  aEmpty := h.aEmpty
  mem := h.mem
  trans := h.trans
  gen := h.gen
  key := Q3.Q3CL.Sec7.l7_1Key ⟨h.hyp, h.cls, h.aEmpty⟩
  subn := fun _ hL _ hz => h.cls.isSubnormal_of_uniqueInvolution hL hz
  nine3 := Q3.Q3CL.l9_3 ⟨h.hyp, h.cls, h.aEmpty⟩

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Std7.toF
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' : Subgroup G} {z : G}
    (h : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Std7 Ω K K' z) :
    CFSG.ClassicalInvolution.T7F25.Asc77.Std7 Ω K K' z where
  stand := h.stand.toF
  disconnected := h.disconnected
  hz := h.hz
  hK' := h.hK'
  hne := h.hne

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp23.toF
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' : Subgroup G} {z : G}
    (h : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp23 Ω K K' z) :
    CFSG.ClassicalInvolution.T7F25.Asc77.Hyp23 Ω K K' z :=
  ⟨h.1.toF, h.2⟩

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp23Setting.toF
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' : Subgroup G} {z : G}
    (h : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp23Setting Ω K K' z) :
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
open scoped commutatorElement MatrixGroups
namespace T7B
open CFSG.ClassicalInvolution.Asc77.T7B
section SL2
open Matrix
variable {F : Type*} [Field F]
end SL2
section Lift
variable {G : Type} [Group G]
end Lift
section Member
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_conj_of_sq_eq (hΩ : Uniform.HypOmegaModU (.sl2 3 1) Ω) {L : Subgroup G} (hL : L ∈ Ω)
    {z : G} (hz : IsUniqueInvolution L z) {a x : G} (ha : a ∈ L) (hx : x ∈ L)
    (ha2 : a * a = z) (hx2 : x * x = z) : ∃ k ∈ L, k * a * k⁻¹ = x := by
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  obtain ⟨φ, hφs, hφk⟩ := Q3T7P25.exists_chart3 hΩ hL
  set zL : ↥L := ⟨z, hz.mem⟩ with hzL
  have hzL2 : zL * zL = 1 := Subtype.ext hz.sq
  have hφz : φ zL = -1 := by
    rcases sl2_sq_eq_one h2 (by rw [← map_mul, hzL2, map_one] : φ zL * φ zL = 1) with h | h
    · exfalso
      have hmem : zL ∈ classicalInvolutionOddCore ↥L := (hφk zL).mp h
      have hdvd : orderOf zL ∣ Nat.card ↥(classicalInvolutionOddCore ↥L) :=
        Subgroup.orderOf_dvd_natCard _ hmem
      have hodd : Odd (Nat.card ↥(classicalInvolutionOddCore ↥L)) :=
        CFSG.ComponentClassification.OddCore.odd_card ↥L
      have hord : orderOf zL = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzL2) (by
        intro h1
        exact hz.ne_one (congrArg Subtype.val h1))
      rw [hord] at hdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
    · exact h
  set aL : ↥L := ⟨a, ha⟩ with haL
  set xL : ↥L := ⟨x, hx⟩ with hxL
  have haφ : φ aL * φ aL = -1 := by
    rw [← map_mul, show aL * aL = zL from Subtype.ext ha2, hφz]
  have hxφ : φ xL * φ xL = -1 := by
    rw [← map_mul, show xL * xL = zL from Subtype.ext hx2, hφz]
  obtain ⟨g, hg⟩ := sl2_exists_conj_of_sq_eq_neg_one h2 haφ hxφ
  obtain ⟨k₀, rfl⟩ := hφs g
  set a'L : ↥L := k₀ * aL * k₀⁻¹ with ha'L
  set a' : G := (a'L : G) with ha'
  have ha'e : a' = (k₀ : G) * a * (k₀ : G)⁻¹ := rfl
  have ha'2 : a' * a' = z := by
    have e : a' * a' = (k₀ : G) * (a * a) * (k₀ : G)⁻¹ := by rw [ha'e]; group
    rw [e, ha2]
    have := hz.commute_of_mem k₀.2
    calc (k₀ : G) * z * (k₀ : G)⁻¹ = (z * (k₀ : G)) * (k₀ : G)⁻¹ := by rw [this]
      _ = z := by group
  have hn : a'L⁻¹ * xL ∈ classicalInvolutionOddCore ↥L := by
    rw [← hφk, map_mul, map_inv]
    have : φ a'L = φ xL := by
      rw [ha'L, map_mul, map_mul, map_inv]
      exact hg
    rw [this, inv_mul_cancel]
  have hnG : a'⁻¹ * x ∈ oddCoreOf L := mem_oddCoreOf_iff.mpr ⟨L.mul_mem (L.inv_mem a'L.2) hx, hn⟩
  have hodd : Odd (orderOf (a'⁻¹ * x)) := by
    have hdvd : orderOf (a'⁻¹ * x) ∣ Nat.card ↥(oddCoreOf L) := Subgroup.orderOf_dvd_natCard _ hnG
    exact (oddCoreOf_odd_natCard L).of_dvd_nat hdvd
  obtain ⟨j, hj⟩ := exists_pow_conj_of_sq_eq (a := a') (x := x) (by rw [ha'2, hx2]) hodd
  have hnL : a'⁻¹ * x ∈ L := oddCoreOf_le_self L hnG
  refine ⟨(a'⁻¹ * x) ^ j * (k₀ : G), L.mul_mem (L.pow_mem hnL j) k₀.2, ?_⟩
  calc (a'⁻¹ * x) ^ j * (k₀ : G) * a * ((a'⁻¹ * x) ^ j * (k₀ : G))⁻¹
      = (a'⁻¹ * x) ^ j * ((k₀ : G) * a * (k₀ : G)⁻¹) * ((a'⁻¹ * x) ^ j)⁻¹ := by group
    _ = x := by rw [← ha'e]; exact hj
end Member
end T7B
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
    (hΩ : Uniform.HypOmegaModU (.sl2 3 1) Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {R V U : Subgroup G} (hR : IsSylow2In R K) (hVR : V ≤ R)
    (hUR : U ≤ R) (hcV : IsCyclic ↥V) (hcU : IsCyclic ↥U) (hV4 : Nat.card V = 4)
    (hU4 : Nat.card U = 4) (hR8 : Nat.card R = 8) :
    ∃ y ∈ K, y ∈ Subgroup.normalizer (R : Set G) ∧ Odd (orderOf y) ∧ conjSub y V = U := by
  have hVK : V ≤ K := hVR.trans hR.1
  have hUK : U ≤ K := hUR.trans hR.1
  obtain ⟨a, haV, ha2, hagen⟩ := exists_gen_sq_eq hz hVK hcV hV4
  obtain ⟨x, hxU, hx2, hxgen⟩ := exists_gen_sq_eq hz hUK hcU hU4
  obtain ⟨k, hkK, hk⟩ := T7B.exists_conj_of_sq_eq hΩ hK hz (hVK haV) (hUK hxU) ha2 hx2
  have hVk : conjSub k V = U := by
    have hle : conjSub k V ≤ U := by
      intro w hw
      rw [mem_conjSub_iff] at hw
      obtain ⟨j, hj⟩ := hagen _ hw
      have hw' : w = k * (k⁻¹ * w * k) * k⁻¹ := by group
      rw [hw', hj]
      have : k * a ^ j * k⁻¹ = x ^ j := by
        rw [← hk]
        simp [conj_zpow]
      rw [this]
      exact U.zpow_mem hxU j
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [AscL62.natCard_conjSub, hU4, hV4])
  have hRV : ∀ r ∈ R, conjSub r V = V := fun r hr =>
    conjSub_eq_of_natCard_eq_two_mul hVR (by omega) hr
  have hRU : ∀ r ∈ R, conjSub r U = U := fun r hr =>
    conjSub_eq_of_natCard_eq_two_mul hUR (by omega) hr
  set H : Subgroup G := K ⊓ Subgroup.normalizer (U : Set G) with hH
  have hRH : R ≤ H := le_inf hR.1 fun r hr => mem_normalizer_iff_conjSub_eq.mpr (hRU r hr)
  have hkR : IsSylow2In (conjSub k R) K := by
    have := IsSylow2In.conj hR k
    rwa [conjSub_eq_self_of_mem hkK] at this
  have hkRH : conjSub k R ≤ H := by
    refine le_inf hkR.1 fun w hw => mem_normalizer_iff_conjSub_eq.mpr ?_
    have hr : k⁻¹ * w * k ∈ R := (mem_conjSub_iff).mp hw
    have hw' : w = k * (k⁻¹ * w * k) * k⁻¹ := by group
    calc conjSub w U = conjSub (k * (k⁻¹ * w * k) * k⁻¹) U := by rw [← hw']
      _ = conjSub k (conjSub (k⁻¹ * w * k) (conjSub k⁻¹ U)) := by rw [conjSub_mul, conjSub_mul]
      _ = conjSub k (conjSub (k⁻¹ * w * k) V) := by rw [← hVk, conjSub_inv_conjSub]
      _ = conjSub k V := by rw [hRV _ hr]
      _ = U := hVk
  have hRsyl : IsSylow2In R H :=
    ⟨hRH, hR.2.1, fun T hTH hT2 hle => hR.2.2 T (hTH.trans inf_le_left) hT2 hle⟩
  have hkRsyl : IsSylow2In (conjSub k R) H :=
    ⟨hkRH, hkR.2.1, fun T hTH hT2 hle => hkR.2.2 T (hTH.trans inf_le_left) hT2 hle⟩
  obtain ⟨n, hnH, hn⟩ := Thompson.exists_conj_of_isSylow2In hRsyl hkRsyl
  have hnU : conjSub n⁻¹ U = U := by
    have h1 : conjSub n U = U := mem_normalizer_iff_conjSub_eq.mp hnH.2
    have h2 := congrArg (conjSub n⁻¹) h1
    rw [conjSub_inv_conjSub] at h2
    exact h2.symm
  set k' : G := n⁻¹ * k with hk'
  have hk'K : k' ∈ K := K.mul_mem (K.inv_mem hnH.1) hkK
  have hk'R : conjSub k' R = R := by
    rw [hk', conjSub_mul, ← hn, conjSub_inv_conjSub]
  have hk'V : conjSub k' V = U := by
    rw [hk', conjSub_mul, hVk, hnU]
  obtain ⟨m, hmodd, hmR⟩ := exists_odd_pow hR hk'K (mem_normalizer_iff_conjSub_eq.mpr hk'R)
  refine ⟨k' ^ m, K.pow_mem hk'K m,
    (Subgroup.normalizer (R : Set G)).pow_mem (mem_normalizer_iff_conjSub_eq.mpr hk'R) m,
    hmodd, ?_⟩
  have hy : k' ^ m = k' * ((k' ^ m)⁻¹ * k')⁻¹ := by group
  rw [hy, conjSub_mul, hRV _ (R.inv_mem hmR), hk'V]

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T75.oddConj
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : Uniform.HypOmegaModU (.sl2 3 1) Ω) : CFSG.ClassicalInvolution.T7F25.Asc77.T75.OddConj Ω :=
  fun _ hK _ hz _ _ _ hR hVR hUR hcV hcU hV4 hU4 hR8 =>
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T75.exists_odd_normalizer_conj hΩ hK hz hR hVR hUR hcV hcU hV4 hU4 hR8

section

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AscStand.e4All
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
    (h : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.AscStand Ω K) {W₀ : Subgroup G} (hW₀ : W₀ ∈ WSet Ω)
    (hE4 : MuIsoE4 Ω W₀) : ∀ W' ∈ WSet Ω, MuIsoE4 Ω W' := fun W' hW' => by
  obtain ⟨e⟩ := CFSG.ClassicalInvolution.T7F25.Asc77.l7_5_2_of h.hyp
    (CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T75.oddConj h.modU) hW' hW₀
  obtain ⟨f⟩ := hE4
  exact ⟨e.trans f⟩

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp25.toF
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}
    (h : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.Hyp25 Ω K K' W S R R' z t u₁ u₂) :
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
namespace T7DR
open CFSG.ClassicalInvolution.Asc77.T7DR
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem tf4_of_index_two [IsSimpleGroup G] {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z t u₁ u₂ t' : G} (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂)
    (h2 : Nat.card ↥(S : Subgroup G) = 2 * Nat.card ↥(R ⊔ R')) (ht' : t' ∈ (S : Subgroup G))
    (hg : ∃ g : G, g * z * g⁻¹ = t') (hconj : conjSub t' R = R') :
    TwoSubgroupsFourGenerated G :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7DR.tf4_of_index_two hyp.toF h2 ht' hg hconj
end T7DR

theorem c25_19_of_sylow (h2 : C25_2_t) (h17 : C25_17_idx) : C25_19 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  by_cases h4 : Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R')
  · exact Or.inl h4
  · refine Or.inr (Or.inr ?_)
    have hidx : Nat.card ↥(S : Subgroup G) = 2 * Nat.card ↥(R ⊔ R') := by
      rcases h17 G Ω K K' W S R R' z t u₁ u₂ hyp with h | h
      · exact h
      · exact absurd h h4
    obtain ⟨t', ht'S, hg, hconj⟩ := h2 G Ω K K' W S R R' z t u₁ u₂ hyp
    exact T7DR.tf4_of_index_two hyp hidx ht'S hg hconj
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Asc77.T7C2

@[expose] def C25_20_coord : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') →
        ∃ a b s t' : G, a ∈ R ∧ b ∈ R ∧ Subgroup.closure ({a, b} : Set G) = R ∧
          b * a * b⁻¹ = a⁻¹ ∧ (∃ k : ℤ, b * b = a ^ k) ∧ s ∈ (S : Subgroup G) ∧
          t' ∈ (S : Subgroup G) ∧ (∃ g : G, g * z * g⁻¹ = t') ∧ conjSub t' R = R' ∧
          Subgroup.closure ({a, b, s, t'} : Set G) = (S : Subgroup G) ∧ s * s = 1 ∧
          s * t' = t' * s ∧ s * a * s⁻¹ = a⁻¹ ∧ s * b * s⁻¹ = b * a
namespace T7DR
open CFSG.ClassicalInvolution.Asc77.T7DR
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem tf4_of_index_four [IsSimpleGroup G] {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z t u₁ u₂ a b s t' : G}
    (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) (haR : a ∈ R) (hbR : b ∈ R)
    (hbab : b * a * b⁻¹ = a⁻¹) (hk : ∃ k : ℤ, b * b = a ^ k) (hs : s ∈ (S : Subgroup G))
    (ht' : t' ∈ (S : Subgroup G)) (hg : ∃ g : G, g * z * g⁻¹ = t') (hconj : conjSub t' R = R')
    (hSgen : Subgroup.closure ({a, b, s, t'} : Set G) = (S : Subgroup G)) (hs2 : s * s = 1)
    (hst : s * t' = t' * s) (hsa : s * a * s⁻¹ = a⁻¹) (hsb : s * b * s⁻¹ = b * a) :
    TwoSubgroupsFourGenerated G :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T7DR.tf4_of_index_four hyp.toF haR hbR hbab hk hs ht' hg
    hconj hSgen hs2 hst hsa hsb
end T7DR

theorem c25_21_of_sylow_coord (h20 : C25_20_coord) : C25_21 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp h4
  obtain ⟨a, b, s, t', haR, hbR, -, hbab, hk, hs, ht', hg, hconj, hSgen, hs2, hst, hsa, hsb⟩ :=
    h20 G Ω K K' W S R R' z t u₁ u₂ hyp h4
  exact Or.inr (T7DR.tf4_of_index_four hyp haR hbR hbab hk hs ht' hg hconj hSgen hs2 hst hsa hsb)
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
namespace T75
open CFSG.ClassicalInvolution.Asc77.T75
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

structure Data (Ω : Set (Subgroup G)) (S : Sylow 2 G)
    (η β : Set (Subgroup G)) : Prop where
  hΩ : HypOmegaMod Ω
  hU : Uniform.HypOmegaModU (.sl2 3 1) Ω
  hη : η ∈ etaSet Ω (S : Subgroup G)
  hηi : ∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η
  hβ : β ∈ etaSet Ω (S : Subgroup G)
  hβi : ∀ s ∈ (S : Subgroup G), ∀ U ∈ β, conjSub s U ∈ β

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T75.Data.toF
    {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {S : Sylow 2 G}
    {η β : Set (Subgroup G)} (D : CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T75.Data Ω S η β) :
    CFSG.ClassicalInvolution.T7F25.Asc77.T75.Data Ω S η β :=
  ⟨D.hΩ, CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T75.oddConj D.hU, D.hη, D.hηi, D.hβ, D.hβi⟩
variable {S : Sylow 2 G} {η β : Set (Subgroup G)}

theorem Data.symm (D : Data Ω S η β) : Data Ω S β η :=
  ⟨D.hΩ, D.hU, D.hβ, D.hβi, D.hη, D.hηi⟩

theorem Data.distinct (D : Data Ω S η β) {A B : Subgroup G} (hA : A ∈ η) (hB : B ∈ η)
    (hne : A ≠ B) {K : Subgroup G} (hK : K ∈ Ω) (hAK : A ≤ K) (hBK : B ≤ K) : False :=
  D.hη.2.1 A hA B hB hne K hK ⟨hAK, hBK⟩

theorem Data.commutes [Finite G] (D : Data Ω S η β) {A B : Subgroup G} (hA : A ∈ η)
    (hB : B ∈ η) : Commutes A B :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T75.Data.commutes D.toF hA hB

theorem Data.partner [Finite G] (D : Data Ω S η β) {A : Subgroup G} (hA : A ∈ USet Ω)
    (hAS : A ≤ (S : Subgroup G)) : ∃! V : Subgroup G, V ∈ η ∧ (A = V ∨ A ⊔ V ∈ RSet Ω) :=
  l6_8 G Ω D.hΩ S A hA hAS η ⟨S, D.hη, D.hηi⟩ fun _ hV => (D.hη.1 hV).2
section Local
variable [Finite G]

theorem Data.local_facts (D : Data Ω S η β) {V U : Subgroup G} (hV : V ∈ η) (hVβ : V ∉ β)
    (hU : U ∈ β) (hR : V ⊔ U ∈ RSet Ω) :
    ∃ K ∈ Ω, ∃ z : G, IsUniqueInvolution K z ∧ IsSylow2In (V ⊔ U) K ∧ z ∈ V ⊔ U ∧
      Nat.card ↥(V ⊔ U) = 8 ∧ Nat.card V = 4 ∧ Nat.card U = 4 ∧ IsCyclic ↥V ∧ IsCyclic ↥U ∧
      (∀ x ∈ V ⊔ U, (∀ r ∈ V ⊔ U, r * x = x * r) → x = 1 ∨ x = z) :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T75.Data.local_facts D.toF hV hVβ hU hR

theorem Data.commutes_local (D : Data Ω S η β) {V U K : Subgroup G} (hV : V ∈ η)
    (hU : U ∈ β) (hR : V ⊔ U ∈ RSet Ω) (hK : K ∈ Ω) (hRK : IsSylow2In (V ⊔ U) K)
    {A : Subgroup G} (hA : (A ∈ η ∧ A ≠ V) ∨ (A ∈ β ∧ A ≠ U)) : Commutes (V ⊔ U) A :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T75.Data.commutes_local D.toF hV hU hR hK hRK hA

theorem Data.le_normalizer_local (D : Data Ω S η β) {V U K : Subgroup G} (hV : V ∈ η)
    (hU : U ∈ β) (hR : V ⊔ U ∈ RSet Ω) (hK : K ∈ Ω) (hRK : IsSylow2In (V ⊔ U) K) {z : G}
    (hz : IsUniqueInvolution K z) (hzR : z ∈ V ⊔ U) {A : Subgroup G}
    (hA : (A ∈ η ∧ A ≠ V) ∨ (A ∈ β ∧ A ≠ U)) : A ≤ Subgroup.normalizer (K : Set G) :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T75.Data.le_normalizer_local D.toF hV hU hR hK hRK hz hzR hA

theorem Data.exists_local_conj (D : Data Ω S η β) {V U : Subgroup G} (hV : V ∈ η)
    (hVβ : V ∉ β) (hU : U ∈ β) (hR : V ⊔ U ∈ RSet Ω) :
    ∃ y : G, conjSub y V = U ∧ (∀ A ∈ η, A ≠ V → ∀ g ∈ A, y * g = g * y) ∧
      ∀ A ∈ β, A ≠ U → ∀ g ∈ A, y * g = g * y :=
  CFSG.ClassicalInvolution.T7F25.Asc77.T75.Data.exists_local_conj D.toF hV hVβ hU hR
end Local
end T75
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
