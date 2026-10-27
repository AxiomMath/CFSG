module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Psu
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2211
public import CFSG.ClassicalInvolution.Asc77.AscC22P16

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S16
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S16
set_option linter.unusedSectionVars false
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected
section Emb
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem conj_mem_layer
    (hΩ : Q3T8.Asc77.HypOmegaMod Ω) {u g y : G}
    (hg : g ∈ Subgroup.centralizer ({u} : Set G)) (hy : y ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω u) :
    g * y * g⁻¹ ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω u := by
  have := conj_mem_conjSub (n := g) hy
  rwa [Q3T8.Asc77.ExactLayer.conjSub_exactLayer hΩ.conjInvariant hg] at this

theorem exists_layer_emb
    (hΩ : Q3T7M.HM Ω) (u : G) :
    ∃ (H : Type) (_ : Group H) (_ : Finite H)
      (ι : (↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u) ⧸ classicalInvolutionOddCore
          ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u)) →* H)
      (π : ↥(Subgroup.centralizer ({u} : Set G)) →* H),
      Function.Injective ι ∧
      (∀ (g : ↥(Subgroup.centralizer ({u} : Set G))) (y : ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u)),
        π g * ι (y : ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u) ⧸ classicalInvolutionOddCore
            ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u)) *
          (π g)⁻¹ = ι ((⟨(g : G) * y * (g : G)⁻¹, Q3T8.Asc77.S16.conj_mem_layer hΩ g.2 y.2⟩ :
            ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u)) :
              ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u) ⧸ classicalInvolutionOddCore
                  ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u))) ∧
      (∀ y : ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u), π ⟨y,
          Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω u y.2⟩ =
        ι (y : ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u) ⧸ classicalInvolutionOddCore
            ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u))) := by
  classical
  set Y : Subgroup G := Q3T8.Asc77.ExactLayer.exactLayer Ω u with hY
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀
  set C : Subgroup G := Subgroup.centralizer ({u} : Set G) with hC
  have hYC : Y ≤ C := Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω u
  have hOnorm : ∀ g ∈ C, g ∈ Subgroup.normalizer (oddCoreOf Y : Set G) := fun g hg =>
    T7L.mem_normalizer_oddCoreOf
      (mem_normalizer_iff_conjSub_eq.mpr (Q3T8.Asc77.ExactLayer.conjSub_exactLayer hΩ.conjInvariant
          hg))
  let N₁ : Subgroup ↥C := (oddCoreOf Y).subgroupOf C
  have hN₁ : N₁.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hOnorm g g.2) n).mp hn
  have hle : N₀ ≤ N₁.comap (Subgroup.inclusion hYC) := by
    intro n hn
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact ⟨n, hn, rfl⟩
  let ι : (↥Y ⧸ N₀) →* (↥C ⧸ N₁) := QuotientGroup.map N₀ N₁ (Subgroup.inclusion hYC) hle
  have hιmk : ∀ y : ↥Y, ι (QuotientGroup.mk' N₀ y) =
      QuotientGroup.mk' N₁ (Subgroup.inclusion hYC y) := fun y => rfl
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H y =>
      have hy1 : QuotientGroup.mk' N₁ (Subgroup.inclusion hYC y) = 1 := hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hy1
      obtain ⟨hyY, hyo⟩ := mem_oddCoreOf_iff.mp hy1
      exact (QuotientGroup.eq_one_iff y).mpr hyo
  have hιmk' : ∀ y : ↥Y, ι (y : ↥Y ⧸ N₀) = ((Subgroup.inclusion hYC y : ↥C) : ↥C ⧸ N₁) :=
    fun y => rfl
  refine ⟨↥C ⧸ N₁, inferInstance, inferInstance, ι, QuotientGroup.mk' N₁, hι, ?_, ?_⟩
  · intro g y
    show (g : ↥C ⧸ N₁) * ι (y : ↥Y ⧸ N₀) * (g : ↥C ⧸ N₁)⁻¹ = _
    rw [hιmk', hιmk', ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
  · intro y
    rfl
end Emb
section Act
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {u : G}

theorem layer_act_exact
    (hΩ : Q3T7M.HM Ω) (hcpg : IsPGroup 2 (Subgroup.zpowers u))
    {H : Type} [Group H]
    {ι : (↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u) ⧸ classicalInvolutionOddCore
        ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u)) →* H}
    {π : ↥(Subgroup.centralizer ({u} : Set G)) →* H}
    (hconj : ∀ (g : ↥(Subgroup.centralizer ({u} : Set G))) (y : ↥(Q3T8.Asc77.ExactLayer.exactLayer
        Ω u)),
      π g * ι (y : ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u) ⧸ classicalInvolutionOddCore
          ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u)) *
        (π g)⁻¹ = ι ((⟨(g : G) * y * (g : G)⁻¹, Q3T8.Asc77.S16.conj_mem_layer hΩ g.2 y.2⟩ :
          ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u)) : ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u) ⧸
              classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω u)))
    {J : Subgroup G} (hJ : J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u)
    (g : ↥(Subgroup.centralizer ({u} : Set G))) (hgJ : (g : G) ∈ trivialOnQuot J) :
    ∀ x ∈ Q3T8.Asc77.T7H.exactImg Ω u J, ∃ n ∈ oddCoreOf (Q3T8.Asc77.T7H.exactImg Ω u J),
      π g * ι x * (π g)⁻¹ = ι (n * x) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hk : (y : G) ∈ Q3T8.Asc77.ExactLayer.exactCore u J := Subgroup.mem_subgroupOf.mp hy
  obtain ⟨n, hn, hnk⟩ := Q3T8.Asc77.S22.exists_odd_mul hΩ hcpg hJ g.2 hgJ hk y.2
    (Q3T8.Asc77.S16.conj_mem_layer hΩ g.2 y.2)
  refine ⟨n, hn, ?_⟩
  have e := hconj g y
  exact e.trans (congrArg ι hnk)
end Act
end S16
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped commutatorElement MatrixGroups
namespace C22P
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22P
set_option linter.unusedSectionVars false
section Abstract
variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem commutes_of_twins_bot (hΦ : Q3T8.Asc77.HypOmegaMod Φ) {M₁ M₂ : Subgroup X} {z : X}
    (hM₁ : M₁ ∈ Φ) (hM₂ : M₂ ∈ Φ) (hne : M₁ ≠ M₂) (hz₁ : IsUniqueInvolution M₁ z)
    (hz₂ : IsUniqueInvolution M₂ z) (hO : oddCoreOf M₁ = ⊥) : Commutes M₁ M₂ := by
  have h := hΦ.comm_le_oddCore_of_twin hM₁ hM₂ hne hz₁ hz₂
  rw [hO, bot_inf_eq, le_bot_iff] at h
  intro x hx y hy
  have : ⁅x, y⁆ ∈ ⁅M₁, M₂⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [h, Subgroup.mem_bot] at this
  exact commutatorElement_eq_one_iff_mul_comm.mp this
end Abstract
end C22P
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S16
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S16
set_option linter.unusedSectionVars false
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement
section Twin
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem eq_exactImg_of_twin
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    (hV3 : ∀ M ∈ twinSet Ω K, M = K ∨ M = K' ∨ M = K₃)
    {B : Subgroup (↥(Q3T8.Asc77.ExactLayer.exactLayer Ω (u₁ * u₂)) ⧸
      classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω (u₁ * u₂)))}
    (hB : B ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω (u₁ * u₂)))
    (hzY : z ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω (u₁ * u₂))
    (hzB : IsUniqueInvolution B (Q3T8.Asc77.T7H.toBar Ω (u₁ * u₂) z hzY)) :
    B = Q3T8.Asc77.T7H.exactImg Ω (u₁ * u₂) K₃ := by
  classical
  have hΩ : Q3T7M.HM Ω := h.stand.modU
  have hcpg : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one h.sq_12
  obtain ⟨R, R', R₃, j₁, j₂, hR, hR', hR₃, hu₁R, hu₂R, hu₃R, c12, c13, c23, hj₁, hj₂, e₁, e₂,
    s₁, s₂⟩ := Q3T8.Asc77.S16.exists_invert h
  have d : InvData z u₁ u₂ j₁ j₂ R R' R₃ :=
    { z2 := h.hz.sq, s₁ := h.sq₁, s₂ := h.sq₂, u₁R := hu₁R, u₂R := hu₂R, j₁R := hj₁,
      j₂R := hj₂, c₁₂ := c12, c₁₃ := c13, c₂₃ := c23, inv₁ := e₁, inv₂ := e₂, sq₁ := s₁,
      sq₂ := s₂ }
  obtain ⟨J, hJ, rfl⟩ := Q3T8.Asc77.T7H.exists_exactImg_of_mem hB
  obtain ⟨w, hw⟩ : ∃ w, IsUniqueInvolution J w := hΩ.exists_uniqueInvolution hJ.1
  set Y : Subgroup G := Q3T8.Asc77.ExactLayer.exactLayer Ω (u₁ * u₂) with hY
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hwc : w ∈ Q3T8.Asc77.ExactLayer.exactCore (u₁ * u₂) J :=
      (Q3T8.Asc77.T7H.isUniqueInvolution_exactCore hΩ hcpg hJ hw).mem
  have hwY : w ∈ Y := Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hJ hwc
  have hB' := Q3T8.Asc77.T7H.exactImg_isUnique hΩ hcpg hJ hw hwY
  have heq : Q3T8.Asc77.T7H.toBar Ω (u₁ * u₂) w hwY = Q3T8.Asc77.T7H.toBar Ω (u₁ * u₂) z hzY :=
      hB'.eq hzB
  obtain ⟨n, hn, hnw⟩ := T3Core.exists_conj_of_map_eq_of_involutions hN₀odd
    (u := (⟨w, hwY⟩ : ↥Y)) (x := (⟨z, hzY⟩ : ↥Y)) (Subtype.ext hw.sq) (Subtype.ext h.hz.sq) heq
  have hnw' : (n : G) * w * (n : G)⁻¹ = z := congrArg Subtype.val hnw
  have hncent : (n : G) ∈ Subgroup.centralizer ({u₁ * u₂} : Set G) :=
    Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω (u₁ * u₂) n.2
  have hnc : (n : G) * (u₁ * u₂) * (n : G)⁻¹ = u₁ * u₂ :=
      Q3T8.Asc77.T7H.mem_centralizer_of_mem_exactLayer
  have hJ' : conjSub (n : G) J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (u₁ * u₂) :=
    Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hncent hJ
  have hzJ' : IsUniqueInvolution (conjSub (n : G) J) z := by
    have := hw.conj (n : G)
    rwa [hnw'] at this
  have hJ'V : conjSub (n : G) J ∈ twinSet Ω K := ⟨hJ'.1, z, h.hz, hzJ'⟩
  have hJ'K₃ : conjSub (n : G) J = K₃ := by
    rcases hV3 _ hJ'V with h1 | h1 | h1
    · exfalso
      have := hJ'.2
      rw [h1] at this
      exact not_mem_trivialOnQuot_left d h.hz (hR.1 hj₁) this
    · exfalso
      have := hJ'.2
      rw [h1] at this
      exact not_mem_trivialOnQuot_right d h.hzK' (hR'.1 hj₂) this
    · exact h1
  rw [← hJ'K₃]
  exact (Q3T8.Asc77.T7H.exactImg_conjSub_odd hn hnc (K := J)).symm
end Twin
end S16
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.AscE184Sect
open CFSG.ClassicalInvolution.Asc77.T7H
namespace C22P
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22P
set_option linter.unusedSectionVars false
section Lift
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem exactImg_conjSub_layer
    {K : Subgroup G} {y : ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω c)} :
    Q3T8.Asc77.T7H.exactImg Ω c (conjSub (y : G) K) =
      conjSub (QuotientGroup.mk' (classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω
          c)) y)
        (Q3T8.Asc77.T7H.exactImg Ω c K) := by
  have hnc : (y : G) * c * (y : G)⁻¹ = c := Q3T8.Asc77.T7H.mem_centralizer_of_mem_exactLayer
  have h1 : Q3T8.Asc77.ExactLayer.exactCore c (conjSub (y : G) K) = conjSub (y : G)
      (Q3T8.Asc77.ExactLayer.exactCore c K) := by
    have := Q3T8.Asc77.ExactLayer.exactCore_conjSub (y : G) c K
    rwa [hnc] at this
  unfold Q3T8.Asc77.T7H.exactImg
  rw [h1, ← conjSub_subgroupOf, AscQuot.map_conjSub]
end Lift
end C22P
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S16
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S16
set_option linter.unusedSectionVars false
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement
section Hall
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem z_mem_layer
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) :
    z ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω (u₁ * u₂) := by
  have hΩ : Q3T7M.HM Ω := h.stand.modU
  have hcpg : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
      Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one h.sq_12
  have hK₃Ω : K₃ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (u₁ * u₂) :=
    Q3T8.Asc77.S22.mem_tqMembers_of_twin h h.hK₃ h.hK₃K h.hK₃K'
  have hzc₃ : z ∈ Q3T8.Asc77.ExactLayer.exactCore (u₁ * u₂) K₃ :=
    (Q3T8.Asc77.T7H.isUniqueInvolution_exactCore hΩ hcpg hK₃Ω h.hzK₃).mem
  exact Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK₃Ω hzc₃

theorem layer_hall [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16.M11NoInverted3] (hR1 :
    Q3T8.Asc77.S16.Z2NoD8) (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    (hV3 : ∀ M ∈ twinSet Ω K, M = K ∨ M = K' ∨ M = K₃)
    (hAall : ∀ M ∈ Ω, ∀ J ∈ omegaStarNbr Ω M,
      ∃ w, IsUniqueInvolution M w ∧ IsUniqueInvolution J w) :
    ∀ B ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω (u₁ * u₂)),
      IsUniqueInvolution B (Q3T8.Asc77.T7H.toBar Ω (u₁ * u₂) z (Q3T8.Asc77.S16.z_mem_layer h)) := by
  classical
  have hΩ : Q3T7M.HM Ω := h.stand.modU
  have hBelow : Q3T8.Generic.CITBelowU (Nat.card G) := h.stand.below
  have hu1 : u₁ * u₂ ≠ 1 :=
    (Q3T8.Asc77.T7S22.mul_ne_one_of_twins h.stand.modU h.stand.mem h.hK'.1 h.hne.symm h.hz h.hu₁.1
      h.hu₂.1 h.hu₂.2).1
  have hu₂C' : (u₁ * u₂) * u₂ = u₂ * (u₁ * u₂) := by
    calc (u₁ * u₂) * u₂ = (u₂ * u₁) * u₂ := by rw [h.comm₁₂]
      _ = u₂ * (u₁ * u₂) := by group
  have hu2 : (u₁ * u₂) * (u₁ * u₂) = 1 := h.sq_12
  have hcpg : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
      Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hu2
  have hnc : ¬ ({u₁ * u₂} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
    obtain ⟨x, -, y, -, hxy⟩ :=
      (hΩ.isQuatSub_of_mem_RSet (mem_RSet_of_isSylow2In h.stand.mem hV)).exists_not_commute
    have hucen : u₁ * u₂ ∈ Subgroup.center G := hsub (Set.mem_singleton _)
    exact hu1 (T7B.eq_one_of_central ⟨x, y, hxy⟩ (fun g' => Subgroup.mem_center_iff.mp hucen g'))
  obtain ⟨hS, hlt⟩ := Q3T8.Asc77.S22.layer_section hΩ h.stand.aEmpty hu2 hnc
  have hK₃Ω : K₃ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (u₁ * u₂) :=
      Q3T8.Asc77.S22.mem_tqMembers_of_twin h h.hK₃ h.hK₃K h.hK₃K'
  have hzY : z ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω (u₁ * u₂) := Q3T8.Asc77.S16.z_mem_layer h
  have hA3 : Q3T8.Asc77.T7H.exactImg Ω (u₁ * u₂) K₃ ∈ oddQuotientFamily
      (Q3T8.Asc77.ExactLayer.exactPair Ω (u₁ * u₂)) :=
    Q3T8.Asc77.T7H.exactImg_mem hK₃Ω
  have hzA3 : IsUniqueInvolution (Q3T8.Asc77.T7H.exactImg Ω (u₁ * u₂) K₃) (Q3T8.Asc77.T7H.toBar Ω
      (u₁ * u₂) z hzY) :=
    Q3T8.Asc77.T7H.exactImg_isUnique hΩ hcpg hK₃Ω h.hzK₃ hzY
  have hstar := Q3T8.Asc77.S22.hstar_layer hΩ hcpg hAall
  rcases Q3T8.Asc77.transSection_or_dConnected (Uniform.thm4BelowU_of_citBelowT hBelow) hlt hS with
      hconn | htrans
  · exact Q3T8.Asc77.S16.hall_of_connected hS.hyp hconn hstar hA3 hzA3
  · have hΦ : Q3T7M.HM (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω (u₁ * u₂))) :=
      htrans.hyp
    by_cases htop : (⊤ : Subgroup (↥(Q3T8.Asc77.ExactLayer.exactLayer Ω (u₁ * u₂)) ⧸
        classicalInvolutionOddCore ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω (u₁ * u₂)))) ∈
        oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω (u₁ * u₂))
    · intro B hB
      have h1 : ∀ B ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω (u₁ * u₂)), B = ⊤ := by
        intro B hB
        obtain ⟨g, hg⟩ := htrans.trans ⊤ htop B hB
        rw [← hg]
        exact conjSub_eq_self_of_mem (Subgroup.mem_top g)
      rw [h1 B hB, ← h1 _ hA3]
      exact hzA3
    · exfalso
      
      have hDE : DEdgeless (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω (u₁ * u₂))) := by
        have key : ∀ B ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω (u₁ * u₂)),
            ∀ J ∈ omegaNbr (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω (u₁ * u₂))) B,
                False := by
          intro B hB J hJ'
          have hJΦ := hJ'.1
          obtain ⟨w, hw1, hw2⟩ := hstar B hB J hJΦ
            (Q3T8.Asc77.T3.omegaNbr_subset_omegaStarNbr hΦ B hJ')
          obtain ⟨g, hg⟩ := htrans.trans _ hA3 B hB
          have hJ'Φ := hΦ.conjInvariant g⁻¹ J hJΦ
          have hwK : IsUniqueInvolution (Q3T8.Asc77.T7H.exactImg Ω (u₁ * u₂) K₃) (g⁻¹ * w * g⁻¹⁻¹)
              := by
            have := hw1.conj g⁻¹
            rwa [← hg, conjSub_inv_conjSub] at this
          have hw2' := hw2.conj g⁻¹
          rw [← hzA3.eq hwK] at hw2'
          have heq := Q3T8.Asc77.S16.eq_exactImg_of_twin h hV3 hJ'Φ hzY hw2'
          apply hJ'.2.1
          calc J = conjSub g (conjSub g⁻¹ J) := (conjSub_conjSub_inv g J).symm
            _ = B := by rw [heq, hg]
        intro B hB J hJ hadj
        rcases hadj with h1 | h1
        · exact key B hB J h1
        · exact key J hJ B h1
      
      obtain ⟨H, _, _, ι, π, hι, hconj, hπy⟩ := Q3T8.Asc77.S16.exists_layer_emb hΩ (u₁ * u₂)
      obtain ⟨R, R', R₃, j₁, j₂, hR, hR', hR₃, hu₁R, hu₂R, hu₃R, c12, c13, c23, hj₁, hj₂, e₁,
        e₂, s₁, s₂⟩ := Q3T8.Asc77.S16.exists_invert h
      have d : InvData z u₁ u₂ j₁ j₂ R R' R₃ :=
        { z2 := h.hz.sq, s₁ := h.sq₁, s₂ := h.sq₂, u₁R := hu₁R, u₂R := hu₂R, j₁R := hj₁,
          j₂R := hj₂, c₁₂ := c12, c₁₃ := c13, c₂₃ := c23, inv₁ := e₁, inv₂ := e₂, sq₁ := s₁,
          sq₂ := s₂ }
      have hu₂C : u₂ ∈ Subgroup.centralizer ({u₁ * u₂} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr hu₂C'.symm
      have hvC : j₁ * j₂ ∈ Subgroup.centralizer ({u₁ * u₂} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr d.v_comm_u
      have hzC : z ∈ Subgroup.centralizer ({u₁ * u₂} : Set G) :=
        Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω (u₁ * u₂) hzY
      set g₂ : ↥(Subgroup.centralizer ({u₁ * u₂} : Set G)) := ⟨u₂, hu₂C⟩ with hg₂
      set gv : ↥(Subgroup.centralizer ({u₁ * u₂} : Set G)) := ⟨j₁ * j₂, hvC⟩ with hgv
      have hnorm : ∀ (g : ↥(Subgroup.centralizer ({u₁ * u₂} : Set G)))
          (x : ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω (u₁ * u₂)) ⧸ classicalInvolutionOddCore
              ↥(Q3T8.Asc77.ExactLayer.exactLayer Ω (u₁ * u₂))),
          π g * ι x * (π g)⁻¹ ∈ ι.range ∧ (π g)⁻¹ * ι x * π g ∈ ι.range := by
        intro g x
        induction x using QuotientGroup.induction_on with
        | H y =>
          refine ⟨⟨_, (hconj g y).symm⟩, ?_⟩
          have h' := hconj g⁻¹ y
          rw [map_inv, inv_inv] at h'
          exact ⟨_, h'.symm⟩
      have hK_le : K ≤ trivialOnQuot K₃ :=
        Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ h.stand.mem h.hK₃.1 h.hK₃K.symm h.hz h.hzK₃
      have hK'_le : K' ≤ trivialOnQuot K₃ :=
        Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ h.hK'.1 h.hK₃.1 h.hK₃K'.symm h.hzK' h.hzK₃
      have hu₂K₃ : u₂ ∈ trivialOnQuot K₃ := hK'_le h.hu₂.1
      have hvK₃ : j₁ * j₂ ∈ trivialOnQuot K₃ :=
        (trivialOnQuot K₃).mul_mem (hK_le (hR.1 hj₁)) (hK'_le (hR'.1 hj₂))
      have haA := Q3T8.Asc77.S16.layer_act_exact hΩ hcpg hconj hK₃Ω g₂ hu₂K₃
      have hvA := Q3T8.Asc77.S16.layer_act_exact hΩ hcpg hconj hK₃Ω gv hvK₃
      have ha2 : π g₂ * π g₂ = ι (Q3T8.Asc77.T7H.toBar Ω (u₁ * u₂) z hzY) := by
        rw [← map_mul]
        have : g₂ * g₂ = ⟨z, hzC⟩ := Subtype.ext h.sq₂
        rw [this]
        exact hπy ⟨z, hzY⟩
      have hv2 : π gv * π gv = 1 := by
        rw [← map_mul]
        have : gv * gv = 1 := Subtype.ext d.sq_v
        rw [this, map_one]
      have hav : π gv * π g₂ * (π gv)⁻¹ = (π g₂)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
        congr 1
        refine Subtype.ext ?_
        show (j₁ * j₂) * u₂ * (j₁ * j₂)⁻¹ = u₂⁻¹
        exact d.v_inv_u₂
      exact Q3T8.Asc77.S16.false_of_t6_section hR1 hBelow hlt htrans htop hDE hstar ι hι (π g₂) (π
          gv)
        (hnorm g₂) (hnorm gv) hA3 hzA3 haA hvA ha2 hv2 hav
end Hall
end S16
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.AscE184Sect
open CFSG.ClassicalInvolution.Asc77.T7H
namespace C22G
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22G
set_option linter.unusedSectionVars false
section Main
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem layer_gen_psu [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C22G.PsuLayerApi3] (hΩ :
    Q3T7M.HM Ω)
    (hc2 : c * c = 1) (hLay : Q3T8.Asc77.LayerOrthType Ω c 6 false)
    {K K' L L' : Subgroup G} {z t b b' y : G}
    (hK : K ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c) (hK' : K' ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c)
        (hL : L ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c)
    (hL' : L' ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c)
    (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    (hperp : ∀ J ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω c, J ∈ KPerp Ω K → J = K ∨ J = K')
    (htL : IsUniqueInvolution L t) (htL' : IsUniqueInvolution L' t)
    (hzt : z * t = t * z) (htz : t ≠ z)
    {R R' : Subgroup G} (hR : IsSylow2In R (Q3T8.Asc77.ExactLayer.exactCore c K)) (hR' : IsSylow2In
        R' (Q3T8.Asc77.ExactLayer.exactCore c K'))
    (hRR' : Commutes R R')
    (hb : b ∈ Q3T8.Asc77.ExactLayer.exactCore c K) (hb' : b' ∈ Q3T8.Asc77.ExactLayer.exactCore c
        K') (ob : b * b = z)
    (hrel : t = b * b' * c) (hy : y ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω c) (hLy : L = conjSub y K)
    (hL'y : L' = conjSub y K') :
    Q3T8.Asc77.ExactLayer.exactLayer Ω c ≤ (L' ⊔ K ⊔ L) ⊔ oddCoreOf
        (Q3T8.Asc77.ExactLayer.exactLayer Ω c) := by
  classical
  have hcpg := Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2
  set E := Q3T8.Asc77.ExactLayer.exactLayer Ω c with hE
  set N₀ := classicalInvolutionOddCore ↥E with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥E
  have hΛ : Q3T7M.HM (Q3T8.Asc77.ExactLayer.exactPair Ω c) :=
      Q3T8.Asc77.ExactLayer.hypOmegaMod_exactPair hΩ hcpg
  have hΦ : Q3T7M.HM (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c)) :=
    Q3T8.Asc77.oddQuotHyp ↥E (Q3T8.Asc77.ExactLayer.exactPair Ω c) hΛ N₀ hN₀odd
  have hzK : z ∈ Q3T8.Asc77.ExactLayer.exactCore c K :=
      (Q3T8.Asc77.T7H.isUniqueInvolution_exactCore hΩ hcpg hK hz).mem
  have hzE : z ∈ E := Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK hzK
  have htL₀ : t ∈ Q3T8.Asc77.ExactLayer.exactCore c L :=
      (Q3T8.Asc77.T7H.isUniqueInvolution_exactCore hΩ hcpg hL htL).mem
  have htE : t ∈ E := Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hL htL₀
  have hbE : b ∈ E := Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK hb
  have hb'E : b' ∈ E := Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK' hb'
  have hcE : c ∈ E := by
    have : c = (b * b')⁻¹ * t := by rw [hrel]; group
    rw [this]
    exact E.mul_mem (E.inv_mem (E.mul_mem hbE hb'E)) htE
  have hz2 : z * z = 1 := hz.sq
  have ht2 : t * t = 1 := htL.sq
  have hA : Q3T8.Asc77.T7H.exactImg Ω c K ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c)
      := Q3T8.Asc77.T7H.exactImg_mem hK
  have hA' : Q3T8.Asc77.T7H.exactImg Ω c K' ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω
      c) := Q3T8.Asc77.T7H.exactImg_mem hK'
  have hB : Q3T8.Asc77.T7H.exactImg Ω c L ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c)
      := Q3T8.Asc77.T7H.exactImg_mem hL
  have hB' : Q3T8.Asc77.T7H.exactImg Ω c L' ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω
      c) := Q3T8.Asc77.T7H.exactImg_mem hL'
  have hzA := Q3T8.Asc77.T7H.exactImg_isUnique hΩ hcpg hK hz hzE
  have hzA' := Q3T8.Asc77.T7H.exactImg_isUnique hΩ hcpg hK' hz' hzE
  have htB := Q3T8.Asc77.T7H.exactImg_isUnique hΩ hcpg hL htL htE
  have htB' := Q3T8.Asc77.T7H.exactImg_isUnique hΩ hcpg hL' htL' htE
  have hne : Q3T8.Asc77.T7H.exactImg Ω c K ≠ Q3T8.Asc77.T7H.exactImg Ω c K' := by
    refine Q3T8.Asc77.map_ne_of_commutes_sylow (N := N₀) hΦ hN₀odd
      (M₁ := (Q3T8.Asc77.ExactLayer.exactCore c K).subgroupOf E) (M₂ :=
          (Q3T8.Asc77.ExactLayer.exactCore c K').subgroupOf E)
      (V₁ := R.subgroupOf E) (V₂ := R'.subgroupOf E)
      ⟨_, Q3T8.Asc77.ExactLayer.exactCore_mem_exactFamily hK,
          Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK, rfl⟩
      (hR.subgroupOf (Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK)) (hR'.subgroupOf
          (Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hK'))
      ?_
    intro x hx y hy
    exact Subtype.ext (hRR' x (Subgroup.mem_subgroupOf.mp hx) y (Subgroup.mem_subgroupOf.mp hy))
  have hnbA : ∀ M ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c),
      M ∈ omegaNbr (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c))
          (Q3T8.Asc77.T7H.exactImg Ω c K) → M = Q3T8.Asc77.T7H.exactImg Ω c K' := by
    intro M hM hMn
    obtain ⟨J, hJ, rfl⟩ := Q3T8.Asc77.T7H.exists_exactImg_of_mem hM
    exact Q3T8.Asc77.T7J.exactImg_nbr_eq_weak hΩ hcpg hK hperp hJ hMn
  have hbarne : Q3T8.Asc77.T7H.toBar Ω c t htE ≠ Q3T8.Asc77.T7H.toBar Ω c z hzE := fun h =>
    htz (Q3T8.Asc77.T7H.eq_of_toBar_eq htE hzE ht2 hz2 hzt.symm h)
  have hBA : Q3T8.Asc77.T7H.exactImg Ω c L ≠ Q3T8.Asc77.T7H.exactImg Ω c K := by
    intro h
    rw [h] at htB
    exact hbarne (htB.eq hzA)
  have hBA' : Q3T8.Asc77.T7H.exactImg Ω c L ≠ Q3T8.Asc77.T7H.exactImg Ω c K' := by
    intro h
    rw [h] at htB
    exact hbarne (htB.eq hzA')
  have hBB : Q3T8.Asc77.T7H.exactImg Ω c L' ≠ Q3T8.Asc77.T7H.exactImg Ω c K := by
    intro h
    rw [h] at htB'
    exact hbarne (htB'.eq hzA)
  have hBB' : Q3T8.Asc77.T7H.exactImg Ω c L' ≠ Q3T8.Asc77.T7H.exactImg Ω c K' := by
    intro h
    rw [h] at htB'
    exact hbarne (htB'.eq hzA')
  have hBn : Q3T8.Asc77.T7H.exactImg Ω c L ∉ omegaNbr (oddQuotientFamily
      (Q3T8.Asc77.ExactLayer.exactPair Ω c)) (Q3T8.Asc77.T7H.exactImg Ω c K) :=
    fun h => hBA' (hnbA _ hB h)
  have hBn' : Q3T8.Asc77.T7H.exactImg Ω c L' ∉ omegaNbr (oddQuotientFamily
      (Q3T8.Asc77.ExactLayer.exactPair Ω c)) (Q3T8.Asc77.T7H.exactImg Ω c K) :=
    fun h => hBB' (hnbA _ hB' h)
  have hgen : omegaGen (oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω c)) = ⊤ :=
    omegaGen_quotFamily_eq_top (Q3T8.Asc77.ExactLayer.exactPair Ω c) N₀
      (omegaGen_restrictFamily_eq_top (Q3T8.Asc77.ExactLayer.exactFamily Ω c) E
          (Q3T8.Asc77.ExactLayer.exactLayer_eq_iSup Ω c).symm)
  obtain ⟨t', n', ht', D, hcard, i, hit, hir⟩ := hLay
  have htn : t' = .PSU ∧ n' = 4 := (MuTab.isOrth_six_false t' n').mp ht'
  have hie : D.exp i = 1 := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · exact absurd (hit.symm.trans h) (by rw [htn.1]; decide)
  obtain ⟨P⟩ := nonempty_psuLayer_of_lieSystemData D hcard i (hit.trans htn.1)
    (hir.trans htn.2) hie hgen
  obtain ⟨RK, hRK, hKR⟩ := P.fund _ hA
  obtain ⟨RK', hRK', hKR'⟩ := P.fund _ hA'
  obtain ⟨RL, hRL, hLR⟩ := P.fund _ hB
  obtain ⟨RL', hRL', hL'R⟩ := P.fund _ hB'
  have hOK : oddCoreOf (Q3T8.Asc77.T7H.exactImg Ω c K) = ⊥ :=
      Q3T8.Asc77.C22G.PSULayer.oddCoreOf_fund3 P hRK hKR
  have hcomm : Commutes (Q3T8.Asc77.T7H.exactImg Ω c K) (Q3T8.Asc77.T7H.exactImg Ω c K') :=
    Q3T8.Asc77.C22P.commutes_of_twins_bot hΦ hA hA' hne hzA hzA' hOK
  have hcomm' : Commutes (Q3T8.Asc77.T7H.exactImg Ω c L) (Q3T8.Asc77.T7H.exactImg Ω c L') := by
    have h1 : Q3T8.Asc77.T7H.exactImg Ω c L = conjSub (QuotientGroup.mk' N₀ ⟨y, hy⟩)
        (Q3T8.Asc77.T7H.exactImg Ω c K) := by
      rw [hLy]
      exact Q3T8.Asc77.C22P.exactImg_conjSub_layer (y := ⟨y, hy⟩)
    have h2 : Q3T8.Asc77.T7H.exactImg Ω c L' = conjSub (QuotientGroup.mk' N₀ ⟨y, hy⟩)
        (Q3T8.Asc77.T7H.exactImg Ω c K') := by
      rw [hL'y]
      exact Q3T8.Asc77.C22P.exactImg_conjSub_layer (y := ⟨y, hy⟩)
    rw [h1, h2]
    exact hcomm.conjSub _
  have heC : Q3T8.Asc77.T7H.toBar Ω c c hcE ∈ Subgroup.center (↥E ⧸ N₀) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective N₀ y
    show QuotientGroup.mk' N₀ y' * QuotientGroup.mk' N₀ ⟨c, hcE⟩ =
      QuotientGroup.mk' N₀ ⟨c, hcE⟩ * QuotientGroup.mk' N₀ y'
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω c y'.2)
  have hrel' : Q3T8.Asc77.T7H.toBar Ω c t htE = Q3T8.Asc77.T7H.toBar Ω c b hbE *
      Q3T8.Asc77.T7H.toBar Ω c b' hb'E * Q3T8.Asc77.T7H.toBar Ω c c hcE := by
    have h1 : (⟨t, htE⟩ : ↥E) = ⟨b, hbE⟩ * ⟨b', hb'E⟩ * ⟨c, hcE⟩ := Subtype.ext hrel
    unfold Q3T8.Asc77.T7H.toBar
    rw [h1, map_mul, map_mul]
  have ob₁ : Q3T8.Asc77.T7H.toBar Ω c b hbE * Q3T8.Asc77.T7H.toBar Ω c b hbE = Q3T8.Asc77.T7H.toBar
      Ω c z hzE := by
    have h1 : (⟨b, hbE⟩ : ↥E) * ⟨b, hbE⟩ = ⟨z, hzE⟩ := Subtype.ext ob
    unfold Q3T8.Asc77.T7H.toBar
    rw [← map_mul, h1]
  have hne₁ : Q3T8.Asc77.T7H.exactImg Ω c K ≠ Q3T8.Asc77.T7H.exactImg Ω c L := hBA.symm
  have hnc₁ : ¬ Commutes (Q3T8.Asc77.T7H.exactImg Ω c K) (Q3T8.Asc77.T7H.exactImg Ω c L) := fun h =>
    hBn (MuTab.mem_omegaNbr_of_commutes hB hBA h)
  have hne₂ : Q3T8.Asc77.T7H.exactImg Ω c K ≠ Q3T8.Asc77.T7H.exactImg Ω c L' := hBB.symm
  have hnc₂ : ¬ Commutes (Q3T8.Asc77.T7H.exactImg Ω c K) (Q3T8.Asc77.T7H.exactImg Ω c L') := fun h
      =>
    hBn' (MuTab.mem_omegaNbr_of_commutes hB' hBB h)
  have hsup := Q3T8.Asc77.C22G.PSULayer.sup_eq_of_chain3 (Fact.out : Q3T8.Asc77.C22G.PsuLayerApi3)
      P hRK hRL hRL' hKR hKR' hLR hL'R hzA htB htB'
    (Q3T8.Asc77.T7H.mem_exactImg hb hbE) (Q3T8.Asc77.T7H.mem_exactImg hb' hb'E) ob₁ hcomm hcomm'
        (by rw [hgen]; trivial)
    (fun y _ => (Subgroup.mem_center_iff.mp heC y).symm) hrel' hne₁ hnc₁ hne₂ hnc₂
  rw [hgen] at hsup
  set S : Subgroup G := Q3T8.Asc77.ExactLayer.exactCore c L' ⊔ Q3T8.Asc77.ExactLayer.exactCore c K
      ⊔ Q3T8.Asc77.ExactLayer.exactCore c L with hS
  have hLS : Q3T8.Asc77.ExactLayer.exactCore c L ≤ S := le_sup_right
  have hKS : Q3T8.Asc77.ExactLayer.exactCore c K ≤ S := le_sup_right.trans le_sup_left
  have hL'S : Q3T8.Asc77.ExactLayer.exactCore c L' ≤ S := le_sup_left.trans le_sup_left
  have hmono : ∀ {M : Subgroup G}, M ≤ S → M.subgroupOf E ≤ S.subgroupOf E := fun hM x hx =>
    Subgroup.mem_subgroupOf.mpr (hM (Subgroup.mem_subgroupOf.mp hx))
  have m₁ : Q3T8.Asc77.T7H.exactImg Ω c L' ≤ (S.subgroupOf E).map (QuotientGroup.mk' N₀) := by
    unfold Q3T8.Asc77.T7H.exactImg
    exact Subgroup.map_mono (hmono hL'S)
  have m₂ : Q3T8.Asc77.T7H.exactImg Ω c K ≤ (S.subgroupOf E).map (QuotientGroup.mk' N₀) := by
    unfold Q3T8.Asc77.T7H.exactImg
    exact Subgroup.map_mono (hmono hKS)
  have m₃ : Q3T8.Asc77.T7H.exactImg Ω c L ≤ (S.subgroupOf E).map (QuotientGroup.mk' N₀) := by
    unfold Q3T8.Asc77.T7H.exactImg
    exact Subgroup.map_mono (hmono hLS)
  have htop : (S.subgroupOf E).map (QuotientGroup.mk' N₀) = ⊤ := by
    rw [eq_top_iff, ← hsup]
    exact sup_le (sup_le m₁ m₂) m₃
  have hlift := C22P.le_sup_oddCoreOf_of_map_eq_top htop
  refine hlift.trans (sup_le_sup_right ?_ _)
  exact sup_le_sup (sup_le_sup (Q3T8.Asc77.ExactLayer.exactCore_le_left c L')
      (Q3T8.Asc77.ExactLayer.exactCore_le_left c K))
    (Q3T8.Asc77.ExactLayer.exactCore_le_left c L)
end Main
end C22G
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected
namespace C22P
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C22P
set_option linter.unusedSectionVars false
section Proved
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' K₃ K₄ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem mem_tqMembers_of_twin (hs : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃) {M : Subgroup G}
    (hM : M ∈ twinSet Ω K) (hMK : M ≠ K) (hMK' : M ≠ K') : M ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω
        (u₁ * u₂) := by
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hzM : IsUniqueInvolution M z := isUniqueInvolution_of_mem_twinSet hs.hz hM
  have h1 : u₁ ∈ trivialOnQuot M :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hs.stand.mem hM.1 (Ne.symm hMK) hs.hz hzM hs.hu₁.1
  have h2 : u₂ ∈ trivialOnQuot M :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hs.hK'.1 hM.1 (Ne.symm hMK') hs.hzK' hzM hs.hu₂.1
  exact ⟨hM.1, Subgroup.mul_mem _ h1 h2⟩

end Proved
end C22P
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
namespace S16
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.S16
set_option linter.unusedSectionVars false
open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
    CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
    CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement
section ZStar
variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G} {z u₁ u₂ u₃ : G}

theorem zStar_of_hall
    (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    (hall : ∀ B ∈ oddQuotientFamily (Q3T8.Asc77.ExactLayer.exactPair Ω (u₁ * u₂)),
      IsUniqueInvolution B (Q3T8.Asc77.T7H.toBar Ω (u₁ * u₂) z (Q3T8.Asc77.S16.z_mem_layer h))) :
    z ∈ zStarOf (Subgroup.centralizer ({u₁ * u₂} : Set G)) := by
  classical
  have hΩ : Q3T7M.HM Ω := h.stand.modU
  have hcpg : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
      Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one h.sq_12
  have hK₃Ω : K₃ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω (u₁ * u₂) :=
      Q3T8.Asc77.S22.mem_tqMembers_of_twin h h.hK₃ h.hK₃K h.hK₃K'
  have hzY : z ∈ Q3T8.Asc77.ExactLayer.exactLayer Ω (u₁ * u₂) := Q3T8.Asc77.S16.z_mem_layer h
  set u : G := u₁ * u₂ with hudef
  set Y : Subgroup G := Q3T8.Asc77.ExactLayer.exactLayer Ω u with hY
  set N₀ : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN₀
  set C : Subgroup G := Subgroup.centralizer ({u} : Set G) with hC
  have hYC : Y ≤ C := Q3T8.Asc77.ExactLayer.exactLayer_le_centralizer Ω u
  have hOnorm : ∀ g ∈ C, g ∈ Subgroup.normalizer (oddCoreOf Y : Set G) := fun g hg =>
    T7L.mem_normalizer_oddCoreOf
      (mem_normalizer_iff_conjSub_eq.mpr (Q3T8.Asc77.ExactLayer.conjSub_exactLayer hΩ.conjInvariant
          hg))
  have hzK₃ : IsUniqueInvolution K₃ z := h.hzK₃
  have hOY : oddCoreOf Y ≤ oddCoreOf C :=
    le_oddCoreIn_of_normalizes ((oddCoreOf_le_self Y).trans hYC) (fun g hg => hOnorm g hg)
      (oddCoreOf_odd_natCard _)
  have hzC : z ∈ C := hYC hzY
  have hcomm : ∀ g ∈ C, ⁅g, z⁆ ∈ oddCoreOf Y := by
    intro g hg
    have hgK₃ : conjSub g K₃ ∈ Q3T8.Asc77.ExactLayer.tqMembers Ω u :=
        Q3T8.Asc77.ExactLayer.conjSub_mem_tqMembers hΩ.conjInvariant hg hK₃Ω
    have hzg : IsUniqueInvolution (conjSub g K₃) (g * z * g⁻¹) := hzK₃.conj g
    have hzgc : g * z * g⁻¹ ∈ Q3T8.Asc77.ExactLayer.exactCore u (conjSub g K₃) :=
      (Q3T8.Asc77.T7H.isUniqueInvolution_exactCore hΩ hcpg hgK₃ hzg).mem
    have hzgY : g * z * g⁻¹ ∈ Y := Q3T8.Asc77.ExactLayer.exactCore_le_exactLayer hgK₃ hzgc
    have hB := hall _ (Q3T8.Asc77.T7H.exactImg_mem hgK₃)
    have hB' := Q3T8.Asc77.T7H.exactImg_isUnique hΩ hcpg hgK₃ hzg hzgY
    have heq : Q3T8.Asc77.T7H.toBar Ω u z hzY = Q3T8.Asc77.T7H.toBar Ω u (g * z * g⁻¹) hzgY :=
        hB.eq hB'
    have hmem : (⟨z, hzY⟩ : ↥Y)⁻¹ * ⟨g * z * g⁻¹, hzgY⟩ ∈ N₀ := QuotientGroup.eq.mp heq
    have hmemG : z⁻¹ * (g * z * g⁻¹) ∈ oddCoreOf Y := ⟨_, hmem, rfl⟩
    have hconj := mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hzY) hmemG
    have e : z * (z⁻¹ * (g * z * g⁻¹)) * z⁻¹ = ⁅g, z⁆ := by
      simp only [commutatorElement_def]
      group
    rwa [e] at hconj
  refine Subgroup.mem_map.mpr ⟨⟨z, hzC⟩, ?_, rfl⟩
  rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
    have hc : ⁅(g : G), z⁆ ∈ oddCoreOf C := hOY (hcomm g g.2)
    obtain ⟨hcC, hco⟩ := mem_oddCoreOf_iff.mp hc
    have h1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥C)
        (g * ⟨z, hzC⟩ * g⁻¹ * ⟨z, hzC⟩⁻¹) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hco
    have h1' : ⁅QuotientGroup.mk' (classicalInvolutionOddCore ↥C) g,
        QuotientGroup.mk' (classicalInvolutionOddCore ↥C) ⟨z, hzC⟩⁆ = 1 := by
      rw [commutatorElement_def]
      simpa only [map_mul, map_inv] using h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1'

theorem layer_zStar [Fact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16.M11NoInverted3] (hR1 :
    Q3T8.Asc77.S16.Z2NoD8) (h : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    (hV3 : ∀ M ∈ twinSet Ω K, M = K ∨ M = K' ∨ M = K₃)
    (hAall : ∀ M ∈ Ω, ∀ J ∈ omegaStarNbr Ω M,
      ∃ w, IsUniqueInvolution M w ∧ IsUniqueInvolution J w) :
    z ∈ zStarOf (Subgroup.centralizer ({u₁ * u₂} : Set G)) :=
  Q3T8.Asc77.S16.zStar_of_hall h (Q3T8.Asc77.S16.layer_hall hR1 h hV3 hAall)
end ZStar
end S16
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
