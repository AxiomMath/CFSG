module

public import CFSG.ClassicalInvolution.Q3.Q3T7W21A02

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

@[expose] def FuzzyEdges3 {G : Type} [Group G] (Ω : Set (Subgroup G)) : Prop :=
  ∀ M ∈ Ω, ∀ N ∈ omegaNbr Ω M, ∀ a : G, IsUniqueInvolution M a →
    Balance.Bootstrap.ActsTrivOnQuot N a

structure AscStandNA {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) :
    Prop where
  modU : Q3T7M.HM Ω
  hyp : Disconnected.AschTight.HypOmegaGen Ω
  cls : Q3CL.ClassicalClause Ω
  rank : 3 ≤ CFSG.Open.twoRank G
  notFour : ¬ TwoSubgroupsFourGenerated G
  below : Q3T8.Generic.CITBelowU (Nat.card G)
  ih : Uniform.IH8T 3 1 (Nat.card G)
  mem : K ∈ Ω
  trans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J
  gen : (⨆ J ∈ Ω, J) = ⊤

theorem AscStandNA.of_mem {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K L : Subgroup G} (h : AscStandNA Ω K) (hL : L ∈ Ω) : AscStandNA Ω L where
  modU := h.modU
  hyp := h.hyp
  cls := h.cls
  rank := h.rank
  notFour := h.notFour
  below := h.below
  ih := h.ih
  mem := hL
  trans := by
    obtain ⟨g₀, hg₀⟩ := h.trans L hL
    intro J hJ
    obtain ⟨g, hg⟩ := h.trans J hJ
    refine ⟨g * g₀⁻¹, ?_⟩
    rw [conjSub_mul, ← hg₀, conjSub_inv_conjSub, hg]
  gen := h.gen

structure TwinFrameSettingNA {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G) : Prop where
  hyp : Q3T7M.HM Ω
  trans : ∀ M ∈ Ω, ∃ g : G, conjSub g K = M
  below : Q3T8.Generic.CITBelowU (Nat.card G)
  thm7 : Q3T8.Asc77.Thm7TypedBelow (Nat.card G)
  frame : Q3T8.Asc77.TwinFrameData Ω K K' z u J t

theorem TwinFrameSetting.toNA {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K K' J : Subgroup G} {z u t : G} (h : Q3T8.Asc77.TwinFrameSetting Ω K K' J z u t) :
    TwinFrameSettingNA Ω K K' J z u t :=
  ⟨h.hyp, h.trans, h.below, h.thm7, h.frame⟩

structure Std7C {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G) : Prop where
  stand : AscStandNA Ω K
  hz : IsUniqueInvolution K z
  hK' : K' ∈ twinSet Ω K
  hne : K' ≠ K
  fuzzy : FuzzyEdges3 Ω
end Asc77
end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

structure Hyp21C {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G) : Prop where
  std : Q3T8.Asc77.Std7C Ω K K' z
  hu : u ∈ K ⊔ K'
  hu2 : u * u = 1
  hu1 : u ≠ 1
  huz : u ≠ z
  hJ : J ∈ omegaOfSet Ω (twinSet Ω K)
  ht : IsUniqueInvolution J t
  htu : t * u = u * t
  hW : W ∈ WSet Ω
  hzW : z ∈ W
  htW : t ∈ W

@[expose] def C21_3C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21C Ω K K' z u J t W →
      Odd (Nat.card ↥(alphaOf (Subgroup.closure {u, z}))) ∧
        ∀ A : Subgroup G, A ≤ Subgroup.closure {z, u, t} → IsElemAbelian2 A 2 →
          alphaOf A = alphaOf (Subgroup.closure {u, z})

@[expose] def C21_setupC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G), Q3T8.Asc77.Std7C Ω K K' z → KPerp Ω K ≠ twinSet Ω K →
      ∃ (u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21C Ω K K' z u J t W
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G]
section Conversions
variable [Finite G] {Ω : Set (Subgroup G)} {K K' J W : Subgroup G}
  {z u t : G}

theorem Hyp21C.twinFrameData
    (h
    : Q3T8.Asc77.Hyp21C Ω K K' z u J t W) : Q3T8.Asc77.TwinFrameData Ω K K' z u J t where
  mem := h.std.stand.mem
  hz := h.std.hz
  hK' := h.std.hK'
  hne := h.std.hne
  hu := h.hu
  hu2 := h.hu2
  hu1 := h.hu1
  huz := h.huz
  hJ := h.hJ
  ht := h.ht
  htu := h.htu

theorem Hyp21C.of_twinFrameData
    (hs
    : Q3T8.Asc77.Std7C Ω K K' z) (h : Q3T8.Asc77.TwinFrameData Ω K K' z u J t)
    (hW : W ∈ WSet Ω) (hzW : z ∈ W) (htW : t ∈ W) : Q3T8.Asc77.Hyp21C Ω K K' z u J t W where
  std := hs
  hu := h.hu
  hu2 := h.hu2
  hu1 := h.hu1
  huz := h.huz
  hJ := h.hJ
  ht := h.ht
  htu := h.htu
  hW := hW
  hzW := hzW
  htW := htW
end Conversions
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

@[expose] def TwinFrameHyp51zC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G),
      Q3T8.Asc77.TwinFrameSettingNA Ω K K' J z u t → FuzzyEdges3 Ω →
      Hyp51At (Subgroup.closure {z, u, t}) z

@[expose] def TwinFrameHyp51tC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G),
      Q3T8.Asc77.TwinFrameSettingNA Ω K K' J z u t → FuzzyEdges3 Ω →
      Hyp51At (Subgroup.closure {z, u, t}) t ∧ Hyp51At (Subgroup.closure {z, u, t}) (t * z)

@[expose] def TwinFrameHyp51uC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G),
      Q3T8.Asc77.TwinFrameSettingNA Ω K K' J z u t → FuzzyEdges3 Ω →
      Hyp51At (Subgroup.closure {z, u, t}) u ∧ Hyp51At (Subgroup.closure {z, u, t}) (u * z) ∧
        Hyp51At (Subgroup.closure {z, u, t}) (u * t) ∧
          Hyp51At (Subgroup.closure {z, u, t}) (u * t * z)

@[expose] def TwinFrameHyp51C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G),
      Q3T8.Asc77.TwinFrameSettingNA Ω K K' J z u t → FuzzyEdges3 Ω →
      Hyp51 (Subgroup.closure {z, u, t})
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
theorem c21_setupC :
    Q3T8.Asc77.C21_setupC := by
  intro G _ _ _ Ω K K' z hs hne
  have hΩ : Q3T7M.HM Ω := hs.stand.modU
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨J, hJ, -⟩ := Q3T8.Asc77.exists_mem_omegaOfSet_twinSet hΩ hK hs.hz hne
  obtain ⟨t, ht⟩ := hΩ.exists_uniqueInvolution hJ.1
  obtain ⟨u, W, hframe, hW, hzW, htW⟩ :=
    Q3T8.Asc77.exists_twinFrameData hΩ hK hs.hz hs.hK' hs.hne hJ ht
  exact ⟨u, J, t, W, Q3T8.Asc77.Hyp21C.of_twinFrameData hs hframe hW hzW htW⟩
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
theorem Hyp21C.conj
    {K
    K' J W : Subgroup G} {z u t : G} (h : Q3T8.Asc77.Hyp21C Ω K K' z u J t W)
    (g : G) :
    Q3T8.Asc77.Hyp21C Ω (conjSub g K) (conjSub g K') (g * z * g⁻¹) (g * u * g⁻¹) (conjSub g J)
      (g * t * g⁻¹) (conjSub g W) := by
  have hΩc : ConjInvariant Ω := h.std.stand.hyp.conjInvariant
  have hinj : ∀ a b : G, g * a * g⁻¹ = g * b * g⁻¹ → a = b := fun a b hab => by
    simpa using hab
  refine
    { std :=
        { stand := h.std.stand.of_mem (hΩc g K h.std.stand.mem)
          hz := h.std.hz.conj g
          hK' := twinSet_conj hΩc h.std.hK' g
          hne := fun e => h.std.hne (conjSub_injective g e)
          fuzzy := h.std.fuzzy }
      hu := ?_
      hu2 := ?_
      hu1 := ?_
      huz := fun e => h.huz (hinj _ _ e)
      hJ := ?_
      ht := h.ht.conj g
      htu := ?_
      hW := WSet.conj hΩc h.hW g
      hzW := conj_mem_conjSub h.hzW
      htW := conj_mem_conjSub h.htW }
  · have := conj_mem_conjSub (n := g) h.hu
    rwa [T7A.conjSub_sup_eq] at this
  · calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [h.hu2]; group
  · intro e
    apply h.hu1
    have := congrArg (fun x => g⁻¹ * x * g) e
    simpa [mul_assoc] using this
  · refine ⟨hΩc g J h.hJ.1, fun L hL => ?_⟩
    have hL' : conjSub g⁻¹ L ∈ twinSet Ω K := by
      have := twinSet_conj hΩc hL g⁻¹
      rwa [conjSub_inv_conjSub] at this
    have := omegaNbr_conj hΩc (h.hJ.2 _ hL') g
    rwa [conjSub_conjSub_inv] at this
  · calc (g * t * g⁻¹) * (g * u * g⁻¹) = g * (t * u) * g⁻¹ := by group
      _ = g * (u * t) * g⁻¹ := by rw [h.htu]
      _ = (g * u * g⁻¹) * (g * t * g⁻¹) := by group
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
section C21_3

theorem TwinFrameSettingNA.of_hyp21C
    {K
    K' J W : Subgroup G} {z u t : G}
    (h : Q3T8.Asc77.Hyp21C Ω K K' z u J t W) : Q3T8.Asc77.TwinFrameSettingNA Ω K K' J z u t where
  hyp := h.std.stand.modU
  trans := h.std.stand.trans
  below := h.std.stand.below
  thm7 := h.std.stand.ih.thm7
  frame := h.twinFrameData

theorem c21_3_ofC
    (hH
    : Q3T8.Asc77.TwinFrameHyp51C) : Q3T8.Asc77.C21_3C := by
  intro G _ _ _ Ω K K' z u J t W h
  have hB : Hyp51 (Subgroup.closure ({z, u, t} : Set G)) :=
    hH G Ω K K' J z u t (Q3T8.Asc77.TwinFrameSettingNA.of_hyp21C h) h.std.fuzzy
  have hD : IsElemAbelian2 (Subgroup.closure ({u, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair h.hu2 h.std.hz.sq h.hu1 h.std.hz.ne_one h.huz
      h.twinFrameData.comm_zu.symm
  have hDB : Subgroup.closure ({u, z} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) := by
    apply Subgroup.closure_mono
    intro x hx
    rcases hx with rfl | rfl <;> simp
  exact lemma54_odd_and_eq hB hDB hD
end C21_3
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
section Alpha
variable [IsSimpleGroup G]

@[expose] def TwinNormAlphaC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Q3T8.Asc77.Hyp21C Ω K K' z u J t W →
      ∀ L ∈ twinSet Ω K, L ≤ Subgroup.normalizer (alphaOf (Subgroup.closure {u, z}) : Set G)

structure AlphaStepsC : Prop where
  h3 : Q3T8.Asc77.C21_3C
  h4 : Q3T8.Asc77.TwinNormAlphaC

theorem AlphaStepsC.alpha_zt
    (hs
    : Q3T8.Asc77.AlphaStepsC) {K K' J W : Subgroup G} {z u t : G}
    (h : Q3T8.Asc77.Hyp21C Ω K K' z u J t W) :
    alphaOf (Subgroup.closure ({z, t} : Set G)) = alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hfr := h.twinFrameData
  have hz2 : z * z = 1 := h.std.hz.sq
  have hA : IsElemAbelian2 (Subgroup.closure ({z, t} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hz2 h.ht.sq h.std.hz.ne_one h.ht.ne_one hfr.t_ne_z.symm
      (hfr.comm_zt hΩ)
  have hle : Subgroup.closure ({z, t} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) := by
    apply Subgroup.closure_mono
    intro x hx
    rcases hx with rfl | rfl <;> simp
  exact (hs.h3 G Ω K K' z u J t W h).2 _ hle hA

theorem AlphaStepsC.sup_le_normalizer
    (hs
    : Q3T8.Asc77.AlphaStepsC) {K K' J W : Subgroup G} {z u t : G}
    (h : Q3T8.Asc77.Hyp21C Ω K K' z u J t W) :
    ∀ g ∈ K ⊔ K', conjSub g (alphaOf (Subgroup.closure ({u, z} : Set G))) =
      alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hK : K ∈ Ω := h.std.stand.mem
  have h1 := hs.h4 G Ω K K' z u J t W h
  have hKn : K ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    h1 K (mem_twinSet_self hK h.std.hz)
  have hK'n : K' ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    h1 K' h.std.hK'
  intro g hg
  exact mem_normalizer_iff_conjSub_eq.mp ((sup_le hKn hK'n) hg)

theorem AlphaStepsC.alpha_eq
    (hs
    : Q3T8.Asc77.AlphaStepsC) {K K' J W J' : Subgroup G} {z u t t' : G}
    (h : Q3T8.Asc77.Hyp21C Ω K K' z u J t W) (hJ' : J' ∈ omegaOfSet Ω (twinSet Ω K))
    (ht' : IsUniqueInvolution J' t') :
    alphaOf (Subgroup.closure ({z, t'} : Set G)) = alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  obtain ⟨g, hgQ, W'', hfr, hW'', hzW'', htW''⟩ :=
    Q3T8.Asc77.exists_twinFrameData_at hΩ h.std.stand.mem h.std.hz h.std.hK' h.std.hne h.hu h.hu2
      h.hu1 h.huz hJ' ht'
  have h' : Q3T8.Asc77.Hyp21C Ω K K' z u (conjSub g J') (g * t' * g⁻¹) W'' :=
    Q3T8.Asc77.Hyp21C.of_twinFrameData h.std hfr hW'' hzW'' htW''
  have h1 := hs.alpha_zt h'
  have hgz : g * z * g⁻¹ = z := by
    have := T7A.z_comm_of_mem_sup h.std.hz (isUniqueInvolution_of_mem_twinSet h.std.hz h.std.hK')
      hgQ
    calc g * z * g⁻¹ = (g * z) * g⁻¹ := rfl
      _ = (z * g) * g⁻¹ := by rw [← this]
      _ = z := by group
  have h2 : conjSub g (Subgroup.closure ({z, t'} : Set G)) =
      Subgroup.closure ({z, g * t' * g⁻¹} : Set G) := by
    rw [T7A.conjSub_closure_pair, hgz]
  have h3 : alphaOf (Subgroup.closure ({z, g * t' * g⁻¹} : Set G)) =
      conjSub g (alphaOf (Subgroup.closure ({z, t'} : Set G))) := by
    rw [← h2, alphaOf_conjSub]
  have hgi := hs.sup_le_normalizer h g⁻¹ (Subgroup.inv_mem _ hgQ)
  have : conjSub g (alphaOf (Subgroup.closure ({z, t'} : Set G))) =
      alphaOf (Subgroup.closure ({u, z} : Set G)) := h3 ▸ h1
  calc alphaOf (Subgroup.closure ({z, t'} : Set G))
      = conjSub g⁻¹ (conjSub g (alphaOf (Subgroup.closure ({z, t'} : Set G)))) :=
        (conjSub_inv_conjSub g _).symm
    _ = conjSub g⁻¹ (alphaOf (Subgroup.closure ({u, z} : Set G))) := by rw [this]
    _ = alphaOf (Subgroup.closure ({u, z} : Set G)) := hgi

theorem AlphaStepsC.conj_alpha_of_mem_centralizer
    (hs : Q3T8.Asc77.AlphaStepsC) {K K' J W : Subgroup G}
    {z u t : G} (h : Q3T8.Asc77.Hyp21C Ω K K' z u J t W) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) :
    conjSub c (alphaOf (Subgroup.closure ({u, z} : Set G))) =
      alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hcz : c * z * c⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [this]
      _ = z := by group
  have hL : conjSub c K ∈ twinSet Ω K :=
    ⟨hΩ.conjInvariant c K hK, z, h.std.hz, hcz ▸ h.std.hz.conj c⟩
  have hc' := h.conj c
  have hJc : conjSub c J ∈ omegaOfSet Ω (twinSet Ω K) := by
    have := hc'.hJ
    rwa [twinSet_eq_of_mem_twinSet h.std.hz hL] at this
  have hB := hs.alpha_zt hc'
  rw [hcz] at hB
  have hD := hs.alpha_eq h hJc (hc'.ht)
  have hA : conjSub c (alphaOf (Subgroup.closure ({u, z} : Set G))) =
      alphaOf (Subgroup.closure ({c * u * c⁻¹, z} : Set G)) := by
    rw [← hcz, ← T7A.conjSub_closure_pair, ← alphaOf_conjSub]
    rw [hcz]
  exact hA.trans (hB.symm.trans hD)

theorem AlphaStepsC.conj_alpha_of_omegaNbr
    (hs
    : Q3T8.Asc77.AlphaStepsC) {K K' J W L : Subgroup G}
    {z u t : G} (h : Q3T8.Asc77.Hyp21C Ω K K' z u J t W) (hL : L ∈ omegaNbr Ω K) {y : G}
    (hy : conjSub y K = L) :
    conjSub y (alphaOf (Subgroup.closure ({u, z} : Set G))) =
      alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hLΩ : L ∈ Ω := hL.1
  have htL : IsUniqueInvolution L (y * z * y⁻¹) := hy ▸ h.std.hz.conj y
  by_cases htw : L ∈ twinSet Ω K
  · have hzL := isUniqueInvolution_of_mem_twinSet h.std.hz htw
    have : y * z * y⁻¹ = z := (htL.eq hzL).symm ▸ rfl
    exact hs.conj_alpha_of_mem_centralizer h (T7A.mem_centralizer_of_conj_eq this)
  · have hLmem : L ∈ omegaOfSet Ω (twinSet Ω K) :=
      Q3T8.Asc77.T7A.mem_omegaOfSet_of_mem_kPerp hΩ hK (Set.mem_insert_of_mem _ hL) htw
    have hD := hs.alpha_eq h hLmem htL
    have hy' := h.conj y
    rw [hy] at hy'
    have hKL : K ∈ omegaNbr Ω L := Q3CL.T3.omegaNbr_symm (Q3T8.Asc77.l6_2) hΩ hK hLΩ hL
    have hKnot : K ∉ twinSet Ω L := by
      rintro ⟨-, z₀, hz₀L, hz₀K⟩
      exact htw ⟨hLΩ, z₀, hz₀K, hz₀L⟩
    have hKmem : K ∈ omegaOfSet Ω (twinSet Ω L) :=
      Q3T8.Asc77.T7A.mem_omegaOfSet_of_mem_kPerp hΩ hLΩ (Set.mem_insert_of_mem _ hKL) hKnot
    have hC := hs.alpha_eq hy' hKmem h.std.hz
    have hA : conjSub y (alphaOf (Subgroup.closure ({u, z} : Set G))) =
        alphaOf (Subgroup.closure ({y * u * y⁻¹, y * z * y⁻¹} : Set G)) := by
      rw [← T7A.conjSub_closure_pair, ← alphaOf_conjSub]
    calc conjSub y (alphaOf (Subgroup.closure ({u, z} : Set G)))
        = alphaOf (Subgroup.closure ({y * u * y⁻¹, y * z * y⁻¹} : Set G)) := hA
      _ = alphaOf (Subgroup.closure ({y * z * y⁻¹, z} : Set G)) := hC.symm
      _ = alphaOf (Subgroup.closure ({z, y * z * y⁻¹} : Set G)) := by rw [Set.pair_comm]
      _ = alphaOf (Subgroup.closure ({u, z} : Set G)) := hD

theorem AlphaStepsC.conj_alpha_of_mem_dComp
    (hs : Q3T8.Asc77.AlphaStepsC) {K K' J W : Subgroup G}
    {z u t : G} (h : Q3T8.Asc77.Hyp21C Ω K K' z u J t W) :
    ∀ M ∈ dComp Ω K, ∀ x : G, conjSub x K = M →
      conjSub x (alphaOf (Subgroup.closure ({u, z} : Set G))) =
        alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hΩc : ConjInvariant Ω := hΩ.conjInvariant
  have hbase : ∀ n : G, conjSub n K = K →
      conjSub n (alphaOf (Subgroup.closure ({u, z} : Set G))) =
        alphaOf (Subgroup.closure ({u, z} : Set G)) := fun n hn =>
    hs.conj_alpha_of_mem_centralizer h (T7A.mem_centralizer_of_conj_eq (h.std.hz.conj_eq hn))
  intro M hM
  induction hM with
  | refl => exact fun x hx => hbase x hx
  | @tail b c hab hbc ih =>
    intro x' hx'
    have hbΩ : b ∈ Ω := T7A.mem_of_mem_dComp hK hab
    obtain ⟨x₀, hx₀⟩ := h.std.stand.trans b hbΩ
    have hcΩ : c ∈ Ω := hbc.1
    have hLΩ : conjSub x₀⁻¹ c ∈ Ω := hΩc _ _ hcΩ
    have hadj : dAdj Ω K (conjSub x₀⁻¹ c) := by
      have := T7A.dAdj_conjSub hΩc hbc.2 x₀⁻¹
      rwa [← hx₀, conjSub_inv_conjSub] at this
    have hLnbr : conjSub x₀⁻¹ c ∈ omegaNbr Ω K := by
      rcases hadj with h1 | h1
      · exact h1
      · exact Q3CL.T3.omegaNbr_symm (Q3T8.Asc77.l6_2) hΩ hLΩ hK h1
    obtain ⟨y, hy⟩ := h.std.stand.trans _ hLΩ
    have hyα := hs.conj_alpha_of_omegaNbr h hLnbr hy
    have hxy : conjSub (x₀ * y) K = c := by
      rw [conjSub_mul, hy, conjSub_conjSub_inv]
    have hn : conjSub ((x₀ * y)⁻¹ * x') K = K := by
      rw [conjSub_mul, hx', ← hxy, conjSub_inv_conjSub]
    have hnα := hbase _ hn
    have hx'eq : x' = x₀ * y * ((x₀ * y)⁻¹ * x') := by group
    rw [hx'eq, conjSub_mul, conjSub_mul, hnα, hyα, ih x₀ hx₀]

end Alpha
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
section Cases
variable {G : Type} [Group G] [Finite G]

theorem twinFrameHyp51_of_casesC
    (hz
    : Q3T8.Asc77.TwinFrameHyp51zC) (ht : Q3T8.Asc77.TwinFrameHyp51tC)
    (hu : Q3T8.Asc77.TwinFrameHyp51uC) : Q3T8.Asc77.TwinFrameHyp51C := by
  intro G _ _ _ Ω K K' J z u t hs hf
  have hfr := hs.frame
  have hcg := hfr.comm_gen hs.hyp
  have hzu : Commute z u := hcg z (by simp) u (by simp)
  have hzt : Commute z t := hcg z (by simp) t (by simp)
  have hut : Commute u t := hcg u (by simp) t (by simp)
  have hz2 : z * z = 1 := hfr.hz.sq
  have hu2 : u * u = 1 := hfr.hu2
  have ht2 : t * t = 1 := hfr.ht.sq
  refine ⟨Q3T8.Asc77.twinFrame_isElemAbelian hs.hyp hfr,
    Q3T8.Asc77.twinFrame_natCard_eight hs.hyp hfr, ?_⟩
  intro c hc hc1
  obtain ⟨a, b, d, rfl⟩ := T7A.mem_closure_words hz2 hu2 ht2 hzu hzt hut hc
  have hz' := hz G Ω K K' J z u t hs hf
  have ht' := ht G Ω K K' J z u t hs hf
  have hu' := hu G Ω K K' J z u t hs hf
  rw [T7A.pow_eq_pow_mod_two hz2 a, T7A.pow_eq_pow_mod_two hu2 b,
    T7A.pow_eq_pow_mod_two ht2 d] at hc1 ⊢
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    rcases Nat.mod_two_eq_zero_or_one d with hd | hd <;> rw [ha, hb, hd] at hc1 ⊢
  · exact absurd (by simp) hc1
  · simpa using ht'.1
  · simpa using hu'.1
  · simpa [hut.eq] using hu'.2.2.1
  · simpa using hz'
  · simpa [hzt.eq] using ht'.2
  · simpa [hzu.eq] using hu'.2.1
  · have e : z * u * t = u * t * z := by
      calc z * u * t = u * z * t := by rw [hzu.eq]
        _ = u * (z * t) := by rw [mul_assoc]
        _ = u * (t * z) := by rw [hzt.eq]
        _ = u * t * z := by rw [mul_assoc]
    simpa [e] using hu'.2.2.2
end Cases
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
theorem twinNormAlpha_ofC
    (h3
    : Q3T8.Asc77.C21_3C) : Q3T8.Asc77.TwinNormAlphaC := by
  intro G _ _ _ Ω K K' z u J t W h L hL
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hfr := h.twinFrameData
  have hB := Q3T8.Asc77.twinFrame_isElemAbelian hΩ hfr
  have hB8 := Q3T8.Asc77.twinFrame_natCard_eight hΩ hfr
  have h3' := (h3 G Ω K K' z u J t W h).2
  have hzu : z * u = u * z := hfr.comm_zu
  have hzt : z * t = t * z := hfr.comm_zt hΩ
  have hz2 : z * z = 1 := h.std.hz.sq
  have ht2 : t * t = 1 := h.ht.sq
  have hBC : Subgroup.closure ({z, u, t} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hzu.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm
  have hO := T7A.oddCore_le_normalizer_alpha hB hB8 hBC h3'
  intro ℓ hℓ
  have hzL := isUniqueInvolution_of_mem_twinSet h.std.hz hL
  have hℓC : ℓ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hzL.commute_of_mem hℓ).symm
  have htC : t ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm
  have hcommO := Q3T8.Asc77.T7A.commutator_twin_mem_oddCoreOf hΩ hfr hL ℓ hℓ
  have hc' : t * ℓ * t⁻¹ * ℓ⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) := by
    rwa [commutatorElement_def] at hcommO
  obtain ⟨o, hoO, hfix⟩ := T7A.exists_fixed_mul_of_odd
    (CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn (Subgroup.centralizer ({z} : Set G)))
    ht2 (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ htC)
    (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _ hℓC) hc'
  have hoC : o ∈ Subgroup.centralizer ({z} : Set G) :=
    CFSG.ClassicalInvolution.Balance.oddCoreIn_le _ hoO
  have hcz : ℓ * o ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.mul_mem _ hℓC hoC
  have hct : (ℓ * o) * t = t * (ℓ * o) := (mul_inv_eq_iff_eq_mul.mp hfix).symm
  have hE₀ : IsElemAbelian2 (Subgroup.closure ({z, t} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair hz2 ht2 h.std.hz.ne_one h.ht.ne_one hfr.t_ne_z.symm hzt
  have hE₀B : Subgroup.closure ({z, t} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) := by
    apply Subgroup.closure_mono
    intro x hx
    rcases hx with rfl | rfl <;> simp
  have hcE₀ : ℓ * o ∈ Subgroup.centralizer ((Subgroup.closure ({z, t} : Set G) : Subgroup G) :
      Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hle : Subgroup.closure ({z, t} : Set G) ≤ Subgroup.centralizer ({ℓ * o} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp
          hcz).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hct.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle he)
  have hcN := T7A.centralizer_le_normalizer_alpha hE₀ hE₀B h3' hcE₀
  have h2 : (ℓ * o) * o⁻¹ ∈ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    Subgroup.mul_mem _ hcN (Subgroup.inv_mem _ (hO hoO))
  rwa [mul_inv_cancel_right] at h2
end Asc77

end

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

@[expose] def TwinFrameHyp51tNA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G), Q3T8.Asc77.TwinFrameSettingNA Ω K K' J z u t →
      Hyp51At (Subgroup.closure {z, u, t}) t ∧ Hyp51At (Subgroup.closure {z, u, t}) (t * z)

@[expose] def TwinFrameHyp51uNA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' J : Subgroup G) (z u t : G), Q3T8.Asc77.TwinFrameSettingNA Ω K K' J z u t →
      Hyp51At (Subgroup.closure {z, u, t}) u ∧ Hyp51At (Subgroup.closure {z, u, t}) (u * z) ∧
        Hyp51At (Subgroup.closure {z, u, t}) (u * t) ∧
          Hyp51At (Subgroup.closure {z, u, t}) (u * t * z)

theorem TwinFrameHyp51tNA.toGeneric (h : Q3T8.Asc77.TwinFrameHyp51tNA) :
    Q3T8.Asc77.TwinFrameHyp51t :=
  fun G _ _ _ Ω K K' J z u t hs => h G Ω K K' J z u t hs.toNA

theorem TwinFrameHyp51uNA.toGeneric (h : Q3T8.Asc77.TwinFrameHyp51uNA) :
    Q3T8.Asc77.TwinFrameHyp51u :=
  fun G _ _ _ Ω K K' J z u t hs => h G Ω K K' J z u t hs.toNA

end Asc77
end

end CFSG.ClassicalInvolution.Q3.Q3T8
