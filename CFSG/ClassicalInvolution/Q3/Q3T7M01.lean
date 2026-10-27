module

public import CFSG.ClassicalInvolution.Q3.Q3T7FUE1

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Generic
open CFSG.ClassicalInvolution.Generic
open CFSG.Open CFSG.LieType CFSG.LieType.Universal
open scoped MatrixGroups
section Models
variable {K : Type} [Group K]
end Models
section Class
variable {Y : Type} [Group Y]

structure InClass (Λ : Set (Subgroup Y)) : Prop where
  nonempty : Λ.Nonempty
  conjInvariant : ConjInvariant Λ
  generated : ⨆ L ∈ Λ, L = ⊤
  classical : ∀ L ∈ Λ, ∃ z : Y, IsClassicalMember L z
end Class
section LieSystem
variable {Y : Type} [Group Y]
end LieSystem
section Components
variable {X : Type} [Group X] {Φ : Set (Subgroup X)}
namespace LieSystemData
open CFSG.ClassicalInvolution.Generic.LieSystemData
variable (D : LieSystemData 3 1 X Φ)
end LieSystemData
variable {X' : Type} [Group X']
variable {Y Y' : Type} [Group Y] [Group Y']
end Components
section Induction

theorem CITBelowU.mono {m n : ℕ} (h : m ≤ n) (hn : CITBelowU n) : CITBelowU m :=
  fun Y _ _ hY Λ hΛ => hn Y (lt_of_lt_of_le hY h) Λ hΛ
end Induction
end Generic

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
open CFSG.ComponentClassification.AschbacherTheorem3
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem l6_7On_of_l6_7 (h : L6_7) [Finite G]
    (hΩ : Q3T7M.HM Ω) : L6_7On Ω :=
  h G Ω hΩ

theorem eq_of_conjSub_le_of_l6_7 [Finite G] (h67 : L6_7On Ω)
    (hΩ : Q3T7M.HM Ω) {R Y X S : Subgroup G} (hR : R ∈ RSet Ω) (hRY : R ≤ Y)
    (hXn : ∀ y ∈ Y, conjSub y X = X) (hRX : R ⊓ X = ⊥) (hS2 : IsPGroup 2 S)
    (hRS : R ≤ S) (hSH : S ≤ X ⊔ R) {g : G} (hg : g ∈ Y) (hle : conjSub g R ≤ S) :
    conjSub g R = R :=
  CFSG.ClassicalInvolution.T7FU.Asc77.eq_of_conjSub_le_of_l6_7 h67 (⟨hΩ, hΩ.toGen⟩) hR hRY hXn hRX
    hS2 hRS hSH hg hle

theorem l6_13_on [Finite G] (hΩ : Q3T7M.HM Ω) (h67 : L6_7On Ω) :
    ∀ R ∈ RSet Ω, ∀ Y X : Subgroup G, R ≤ Y → X ≤ Y → (∀ y ∈ Y, conjSub y X = X) →
      R ⊓ X = ⊥ →
        (⨆ R' ∈ {R' : Subgroup G | (∃ y ∈ Y, R' = conjSub y R) ∧ R' ≤ R ⊔ X}, R') ≤
            R ⊔ oddCoreOf X ∧
          ⁅R, X⁆ ≤ oddCoreOf X :=
  CFSG.ClassicalInvolution.T7FU.Asc77.l6_13_on (⟨hΩ, hΩ.toGen⟩) h67
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic

@[expose] def ThmEBelow (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n →
    ∀ (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G) (R W H : Subgroup G),
      EStand Ω K S R W → EHyp Ω K W H → H = ⊤

structure MinCex {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R W H : Subgroup G) : Prop where
  stand : EStand Ω K S R W
  hyp : EHyp Ω K W H
  proper : H ≠ ⊤
  minimal : ThmEBelow (Nat.card G)

section

theorem EStand.toU {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
    {S : Sylow 2 G} {R W : Subgroup G} (h : EStand Ω K S R W) :
    CFSG.ClassicalInvolution.T7FU.Asc77.EStand (.sl2 3 1) Ω K S R W :=
  { h with hyp := ⟨h.hyp, h.hyp.toGen⟩ }

theorem MinCex.toU {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
    {S : Sylow 2 G} {R W H : Subgroup G} (c : MinCex Ω K S R W H) :
    CFSG.ClassicalInvolution.T7FU.Asc77.MinCex (.sl2 3 1) Ω K S R W H :=
  { c with stand := c.stand.toU }

section
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
  {R W H : Subgroup G}

theorem EStand.ofU {Ω' : Set (Subgroup G)} {K' : Subgroup G} {S' : Sylow 2 G}
    {R' W' : Subgroup G}
    (e : CFSG.ClassicalInvolution.T7FU.Asc77.EStand (.sl2 3 1) Ω' K' S' R' W')
    (h : EStand Ω K S R W) : EStand Ω' K' S' R' W' :=
  { e with
    hyp := e.hyp.toMod
    below := h.below
    ih := h.ih
    ob := h.ob }

theorem MinCex.ofU {Ω' : Set (Subgroup G)} {K' : Subgroup G} {S' : Sylow 2 G}
    {R' W' H' : Subgroup G}
    (c₁ : CFSG.ClassicalInvolution.T7FU.Asc77.MinCex (.sl2 3 1) Ω' K' S' R' W' H')
    (c : MinCex Ω K S R W H) : MinCex Ω' K' S' R' W' H' :=
  { stand :=
      { c₁.stand with
        hyp := c₁.stand.hyp.toMod
        below := c.stand.below
        ih := c.stand.ih
        ob := c.stand.ob }
    hyp := c₁.hyp
    proper := c₁.proper
    minimal := c.minimal }

end


end


@[expose] def ThmEWithSylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
      (R W H : Subgroup G), EStand Ω K S R W → EHyp Ω K W H → H = ⊤

@[expose] def MinCexFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex Ω K S R W H → False

theorem thmEWithSylow_of_minCexFalse (h : MinCexFalse) : ThmEWithSylow := by
  have key : ∀ n, ThmEBelow n := by
    intro n
    induction n with
    | zero =>
      intro G _ _ hG
      exact absurd hG (by omega)
    | succ n ih =>
      intro G _ _ hG Ω K S R W H hst hH
      by_cases hn : Nat.card G < n
      · exact ih G hn Ω K S R W H hst hH
      · have hGn : Nat.card G = n := by omega
        by_contra hne
        exact h G Ω K S R W H ⟨hst, hH, hne, hGn ▸ ih⟩
  intro G _ _ Ω K S R W H hst hH
  exact key (Nat.card G + 1) G (Nat.lt_succ_self _) Ω K S R W H hst hH

@[expose] def E18_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex Ω K S R W H →
      (∀ g : G, conjSub g K ∈ dstarComp Ω K → g ∈ H) ∧ ∃ J ∈ Ω, J ∉ dstarComp Ω K

@[expose] def E18_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex Ω K S R W H →
      ∀ u ∈ K, orderOf u = 4 → ∀ g : G, g * u * g⁻¹ ∈ H → g ∈ H

@[expose] def E18_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex Ω K S R W H → ∀ J ∈ Ω, ∃ g : G, conjSub g K = J

@[expose] def E18_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex Ω K S R W H → (⨆ J ∈ Ω, J) = ⊤

@[expose] def E18_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex Ω K S R W H →
      classicalInvolutionOddCore G = ⊥ ∧
        ∃ F : Subgroup G, F.Normal ∧ IsSimpleGroup ↥F ∧ (∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) ∧
          Subgroup.centralizer (F : Set G) = ⊥

section
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
  {R W H : Subgroup G}

theorem E18_6.atG (h6 : E18_6) (c : MinCex Ω K S R W H) :
    CFSG.ClassicalInvolution.T7FU.Asc77.E18_6At (.sl2 3 1) G :=
  fun _ _ _ _ _ _ c₁ => h6 G _ _ _ _ _ _ (MinCex.ofU c₁ c)

end


@[expose] def E18_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex Ω K S R W H →
      ∀ a : G, a ≠ 1 → a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H →
        ∀ g : G, g * a * g⁻¹ ∈ H → ∃ h ∈ H, h * a * h⁻¹ = g * a * g⁻¹

@[expose] def E18_8z : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex Ω K S R W H →
      ∀ z : G, IsUniqueInvolution K z → FixesUniqueCoset z H

@[expose] def E18_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex Ω K S R W H →
      ∀ z : G, IsUniqueInvolution K z → ∀ h : G, h⁻¹ * z * h ∈ (S : Subgroup G) →
        h⁻¹ * z * h ≠ z → z * (h⁻¹ * z * h) = (h⁻¹ * z * h) * z →
          FixesUniqueCoset (z * (h⁻¹ * z * h)) H

@[expose] def E18_zW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex Ω K S R W H → ∃ z : G, IsUniqueInvolution K z ∧ z ∈ W
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
section CaseA
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem e189_caseA (hΩ : Q3T7M.HM Ω) {K J : Subgroup G}
    {z t : G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (htz : t ≠ z) (hzt : z * t = t * z)
    (hnorm : conjSub t K = K) : (∃ g : G, g * t * g⁻¹ = z * t) ∨ J ∈ KPerp Ω K :=
  CFSG.ClassicalInvolution.T7FU.Asc77.e189_caseA (⟨hΩ, hΩ.toGen⟩) hK hJ hz ht htz hzt hnorm
end CaseA
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic

theorem e18_zW : E18_zW := by
  intro G _ _ Ω K S R W H c
  exact CFSG.ClassicalInvolution.T7FU.Asc77.e18_zW G Ω K S R W H c.toU
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic

theorem e18_3 (h67 : L6_7) : E18_3 := by
  intro G _ _ Ω K S R W H c
  exact CFSG.ClassicalInvolution.T7FU.Asc77.e18_3 h67 G Ω K S R W H c.toU
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T7M.HM.exists_orderOf_eq_four_of_mem_RSet {G : Type}
    [Group G] [Finite G] {Ω : Set (Subgroup G)} (hΩ : Q3T7M.HM Ω) {R : Subgroup G}
    (hR : R ∈ RSet Ω) : ∃ u ∈ R, orderOf u = 4 := by
  have hquat := hΩ.isQuatSub_of_mem_RSet hR
  obtain ⟨C, hCR, hC, hcard, -⟩ := hquat.exists_cyclic_max
  obtain ⟨J, -, -, hR2, -⟩ := mem_RSet_iff.mp hR
  have h8 := hquat.eight_le
  obtain ⟨x, hxC, hx⟩ := exists_orderOf_eq_four_of_isPGroup_of_isCyclic (hR2.to_le hCR) hC
    (by omega)
  exact ⟨x, hCR hxC, hx⟩
end Asc77

end

section

namespace Asc77.T3
open CFSG.ClassicalInvolution.Asc77.T3
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement
section Defs
variable {G : Type} [Group G]
end Defs

@[expose] def Thm3SectBelow (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n → ∀ Λ : Set (Subgroup Y),
      Q3T7M.HM Λ → ¬ DStarConnected (oddQuotientFamily Λ) → ∀ L ∈ Λ, AEmpty Λ L
section Graph
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
end Graph
section Quotient
variable {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}
end Quotient
end Asc77.T3

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic

theorem MinCex.centralizer_le {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G} (c : MinCex Ω K S R W H) {z : G}
    (hz : IsUniqueInvolution K z) : Subgroup.centralizer ({z} : Set G) ≤ H :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.centralizer_le c.toU hz

theorem MinCex.exists_centralizer_le {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G} (c : MinCex Ω K S R W H) :
    ∃ z : G, IsUniqueInvolution K z ∧ Subgroup.centralizer ({z} : Set G) ≤ H :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.exists_centralizer_le c.toU

theorem e18_1 : E18_1 := by
  intro G _ _ Ω K S R W H c
  exact CFSG.ClassicalInvolution.T7FU.Asc77.e18_1 G Ω K S R W H c.toU
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T7M.HM.isSylow2In_of_mem_RSet_of_le [Finite G] (hΩ :
    Q3T7M.HM Ω)
    {K R : Subgroup G} (hK : K ∈ Ω) (hR : R ∈ RSet Ω) (hRK : R ≤ K) : IsSylow2In R K := by
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  have h8 := hΩ.eight_le_of_mem_RSet hR
  have hJK : K = J := hΩ.eq_of_le_of_le hK hJ hRJ.2.1 (by omega) hRK hRJ.1
  exact hJK ▸ hRJ

theorem mem_dstarComp_of_mem_USet_le_W [Finite G] (hΩ : Q3T7M.HM Ω) {K J W V₀ V₁ : Subgroup G} (hK
    : K ∈ Ω) (hJ : J ∈ Ω)
    (hV₀ : V₀ ∈ USet Ω) (hV₀K : V₀ ≤ K) (hV₀W : V₀ ≤ W) (hV₁ : V₁ ∈ USet Ω) (hV₁J : V₁ ≤ J)
    (hV₁W : V₁ ≤ W) (habel : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : J ∈ dstarComp Ω K :=
  CFSG.ClassicalInvolution.T7FU.Asc77.mem_dstarComp_of_mem_USet_le_W (⟨hΩ, hΩ.toGen⟩) hK hJ hV₀
    hV₀K hV₀W hV₁ hV₁J hV₁W habel

theorem EtaAbelian.of_l6_9 [Finite G] (h : L6_9) (hΩ : Q3T7M.HM Ω) : EtaAbelian Ω :=
  fun S _ hη hinv => ((h G Ω hΩ S).2 _ hη hinv).1

theorem EtaMeet.of_l6_11 [Finite G] (h : L6_11) (hΩ : Q3T7M.HM Ω) : EtaMeet Ω :=
  fun S _ hη hηS _ hK h2 => h G Ω hΩ S _ hη hηS _ hK h2
section MinCex
variable [Finite G] {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.exists_eta (c : MinCex Ω K S R W H) (hA : EtaAbelian Ω) :
    ∃ η : Set (Subgroup G), η ∈ etaG Ω ∧ W = ⨆ V ∈ η, V ∧
      (∀ V ∈ η, V ∈ USet Ω ∧ V ≤ (S : Subgroup G)) ∧
      (∀ x ∈ W, ∀ y ∈ W, x * y = y * x) ∧ ∃ V₀ ∈ η, V₀ ≤ K :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.exists_eta c.toU hA

theorem MinCex.mem_of_conjSub_eq_W (c : MinCex Ω K S R W H) (hA : EtaAbelian Ω) {n : G}
    (hn : conjSub n W = W) : n ∈ H :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.mem_of_conjSub_eq_W c.toU hA hn

theorem MinCex.sylow_le (c : MinCex Ω K S R W H) (hA : EtaAbelian Ω) :
    (S : Subgroup G) ≤ H :=
  fun s hs => c.mem_of_conjSub_eq_W hA (c.stand.hW.2.2 s hs)

theorem MinCex.mem_of_conj_mem (c : MinCex Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {u : G} (hu : u ∈ K) (hu4 : orderOf u = 4) {g : G} (hg : g * u * g⁻¹ ∈ H) :
    g ∈ H :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.mem_of_conj_mem c.toU hA hM hu hu4 hg
end MinCex

theorem e18_2_of_l6_9_l6_11 (h69 : L6_9) (h611 : L6_11) : E18_2 := by
  intro G _ _ Ω K S R W H c
  exact CFSG.ClassicalInvolution.T7FU.Asc77.e18_2_of_l6_9_l6_11 h69 h611 G Ω K S R W H c.toU
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic

theorem e18_8z_of_e18_7 (h : E18_7) : E18_8z := by
  intro G _ _ Ω K S R W H c a hz
  have ha1 : a ≠ 1 := hz.ne_one
  have ha2 : a * a = 1 := hz.sq
  have hcent : Subgroup.centralizer ({a} : Set G) ≤ H := c.centralizer_le hz
  have haH : a ∈ H := hcent (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have h7 := h G Ω K S R W H c a ha1 ha2 hcent
  refine ⟨(1 : G) , ?_, ?_⟩
  · show a • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    exact QuotientGroup.eq.mpr (by simpa using H.inv_mem haH)
  · intro c' hc'
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c'
    have hg : g⁻¹ * a * g ∈ H := by
      have h1 : a • ((g : G) : G ⧸ H) = (g : G ⧸ H) := hc'
      rw [MulAction.Quotient.smul_mk, smul_eq_mul] at h1
      have h2 := QuotientGroup.eq.mp h1
      have : (a * g)⁻¹ * g = g⁻¹ * a⁻¹ * g := by group
      have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
      rw [this, ha'] at h2
      exact h2
    obtain ⟨k, hk, hka⟩ := h7 g⁻¹ (by simpa using hg)
    have hgk : g * k ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h3 : k * a * k⁻¹ = g⁻¹ * a * g := by simpa using hka
      calc (g * k) * a = (g * (k * a * k⁻¹)) * k := by group
        _ = a * (g * k) := by rw [h3]; group
    have : g ∈ H := by
      have h4 : g * k * k⁻¹ ∈ H := H.mul_mem (hcent hgk) (H.inv_mem hk)
      simpa using h4
    exact (QuotientGroup.eq.mpr (by simpa using H.inv_mem this)).symm
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
section General

end General
section MinCex
variable [Finite G] {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.le_H (c : MinCex Ω K S R W H) : K ≤ H :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.le_H c.toU

theorem MinCex.mem_of_conjSub_le (c : MinCex Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {g : G} (hg : conjSub g R ≤ H) : g ∈ H :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.mem_of_conjSub_le c.toU hA hM hg

theorem MinCex.normalizer_le_of_le (c : MinCex Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {Y : Subgroup G} (hRY : R ≤ Y) (hYH : Y ≤ H) :
    Subgroup.normalizer (Y : Set G) ≤ H :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.normalizer_le_of_le c.toU hA hM hRY hYH

theorem MinCex.exists_orderOf_four_mem_W (c : MinCex Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {J T : Subgroup G} (hJ : J ∈ Ω) (hT : IsSylow2In T J)
    (hTS : T ≤ (S : Subgroup G)) : ∃ u ∈ J ⊓ W, orderOf u = 4 ∧ u ∈ T :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.exists_orderOf_four_mem_W c.toU hA hM hJ hT hTS

theorem MinCex.exists_fourGroup (c : MinCex Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {K' : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hK'ne : K' ≠ K)
    {R' : Subgroup G} (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K') (hR'S : R' ≤ (S : Subgroup G)) :
    ∃ U : Subgroup G, U ≤ R ⊔ R' ∧ U ≤ W ∧ (∀ x ∈ U, ∀ y ∈ U, x * y = y * x) ∧
      (∀ x ∈ U, x * x = 1) ∧ 4 ≤ Nat.card U ∧
      ∀ e ∈ U, e ≠ 1 → Subgroup.centralizer ({e} : Set G) ≤ H :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.exists_fourGroup c.toU hA hM hK' hK'ne hR' hR'K' hR'S

theorem MinCex.oddCoreOf_le (c : MinCex Ω K S R W H) (hA : EtaAbelian Ω) (hM : EtaMeet Ω)
    {K' : Subgroup G} (hK' : K' ∈ twinSet Ω K) (hK'ne : K' ≠ K) {R' : Subgroup G}
    (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K') (hR'S : R' ≤ (S : Subgroup G)) {Y : Subgroup G}
    (hY : R ⊔ R' ≤ Y) : oddCoreOf Y ≤ H :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.oddCoreOf_le c.toU hA hM hK' hK'ne hR' hR'K' hR'S hY
end MinCex
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3T7M.HM.restrict [Finite G] (hΩ : Q3T7M.HM Ω) (Y :
    Subgroup G) :
    Q3T7M.HM (restrictFamily Ω Y) where
  conjInvariant := by
    rintro n _ ⟨L, hL, hLY, rfl⟩
    refine ⟨conjSub (n : G) L, hΩ.conjInvariant _ L hL, ?_, conjSub_subgroupOf Y n L⟩
    have := conjSub_mono (n := (n : G)) hLY
    rwa [conjSub_eq_self_of_mem n.2] at this
  classical := by
    rintro _ ⟨L, hL, hLY, rfl⟩
    obtain ⟨z, hz⟩ := hΩ.classical L hL
    exact ⟨_, hz.subgroupOf hLY⟩
  omega4 := by
    rintro _ ⟨K, hK, hKY, rfl⟩ _ ⟨J, hJ, hJY, rfl⟩ hne
    have hKJ : K ≠ J := fun h => hne (by rw [h])
    obtain ⟨h1, h2⟩ := hΩ.omega4 K hK J hJ hKJ
    have hcard : Nat.card ↥(K.subgroupOf Y ⊓ J.subgroupOf Y) = Nat.card ↥(K ⊓ J) := by
      rw [inf_subgroupOf_eq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hKY)).toEquiv
    rw [hcard]
    refine ⟨h1, fun h => ?_⟩
    have hle := h2 h
    rw [oddCoreOf_subgroupOf hKY, oddCoreOf_subgroupOf hJY]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have hab : (⁅(a : G), (b : G)⁆) ∈ ⁅K, J⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
        (Subgroup.mem_subgroupOf.mp hb)
    exact ⟨Subgroup.mem_subgroupOf.mpr (hle hab).1, Subgroup.mem_subgroupOf.mpr (hle hab).2⟩
  omega5 := by
    rintro _ ⟨K, hK, hKY, rfl⟩ _ ⟨J, hJ, hJY, rfl⟩ hne z' hz' v hv hnc hv2 hvz
    have hKJ : K ≠ J := fun h => hne (by rw [h])
    have hzK : IsUniqueInvolution K (z' : G) := isUniqueInvolution_of_subgroupOf hz' hKY
    have hvJ : (v : G) ∈ J := Subgroup.mem_subgroupOf.mp hv
    have hnc' : ¬ ∀ w ∈ J, (v : G) * w = w * (v : G) := by
      intro h
      apply hnc
      rintro ⟨w, hw⟩ hw'
      exact Subtype.ext (h w (Subgroup.mem_subgroupOf.mp hw'))
    have hv2' : IsPGroup 2 (Subgroup.zpowers (v : G)) := isPGroup_zpowers_coe_iff.mpr hv2
    have hn := hΩ.omega5 K hK J hJ hKJ (z' : G) hzK (v : G) hvJ hnc' hv2' (congrArg Subtype.val hvz)
    exact (mem_normalizer_subgroupOf_iff hKY).mp hn

theorem omegaNbr_subgroupOf [Finite G] (hΩ : Q3T7M.HM Ω) {Y K J : Subgroup G}
    (hKY : K ≤ Y) (hJY : J ≤ Y) (hJ : J ∈ Ω) (h : J ∈ omegaNbr Ω K) :
    J.subgroupOf Y ∈ omegaNbr (restrictFamily Ω Y) (K.subgroupOf Y) :=
  CFSG.ClassicalInvolution.T7FU.Asc77.omegaNbr_subgroupOf (⟨hΩ, hΩ.toGen⟩) hKY hJY hJ h

theorem AEmpty.restrict [Finite G] (hΩ : Q3T7M.HM Ω) {Y K : Subgroup G}
    (hKY : K ≤ Y) (hA : AEmpty Ω K) : AEmpty (restrictFamily Ω Y) (K.subgroupOf Y) :=
  CFSG.ClassicalInvolution.T7FU.Asc77.AEmpty.restrict (⟨hΩ, hΩ.toGen⟩) hKY hA
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
