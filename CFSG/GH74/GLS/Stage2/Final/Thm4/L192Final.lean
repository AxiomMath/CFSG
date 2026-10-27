module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.L192Star
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Final19F
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma21

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4.L192

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open CFSG.GH74.GLS.Stage2.Final.L26 (WBar_le_generalizedFitting)
open scoped commutatorElement

section Kinds

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem WBar_le_LBar (ctx : Stage2Ctx G z k S) : WBar z ≤ LBar z := by
  have hd := ctx.data
  cases hd with
  | g2 hg =>
    obtain ⟨r₁, r₂, L₁, L₂, hsh⟩ := hg.shape
    obtain ⟨hodd₁, hodd₂, hgt₁, hprod, m₁, m₂, -, h3, h4, -, -, -⟩ := hsh
    have hr₂ge : 2 ≤ r₂ := by
      obtain ⟨F, hF, hFin, hq, -⟩ := m₂
      have : 1 < Nat.card F := Finite.one_lt_card
      have hq' : Nat.card F = r₂ := hq
      omega
    have hodd := Nat.odd_iff.mp hodd₂
    rcases Nat.lt_or_ge 3 r₂ with hgt | hle
    · rw [← (h4 hgt).2]
      exact WBar_le_generalizedFitting z
    · have hr₃ : r₂ = 3 := by omega
      calc WBar z ≤ generalizedFitting (CentralizerBar z) := WBar_le_generalizedFitting z
        _ = oPrimeResidualOf 2 (LBar z) := (h3 hr₃).2
        _ ≤ LBar z := Subgroup.map_subtype_le _
  | m12 hM =>
    obtain ⟨A', -, hLeq, hresW, -, -, -⟩ := hM.L_shape
    rw [hLeq, hresW]
    exact le_sup_left
  | psp4 h =>
    obtain ⟨q, L₁, L₂, hP⟩ := h
    exact (WBar_le_generalizedFitting z).trans hP.pair.fitting.le
  | l4 ε h =>
    obtain ⟨q, L₁, L₂, hL⟩ := h
    exact (WBar_le_generalizedFitting z).trans hL.pair.fitting.le
  | mcl h =>
    obtain ⟨n, -, hS⟩ := h
    rw [hS.eq_L]
    exact le_top
  | ly h =>
    obtain ⟨n, -, hS⟩ := h
    rw [hS.eq_L]
    exact le_top

end Kinds


section Layer

variable {X : Type} [Group X] [Finite X]

theorem isPComponent_le_oPrimePResidual {J : Subgroup X} (hJ : IsPComponent 2 J) :
    J ≤ oPrimePResidual 2 X := by
  have hres : CFSG.ComponentClassification.FooteLit.oddResidualIn J = J :=
    CFSG.ComponentClassification.FooteLit.oddResidualIn_eq_self_of_isPComponent_top hJ
  have hA : J ≤ oPrimeResidual 2 X := by
    rw [← hres]
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨-, k, hk⟩
    apply Subgroup.subset_closure
    exact ⟨k, by rw [← hk]; exact pow_orderOf_eq_one g⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CFSG.GH74.GLS.Stage1.Thm6.Prod.oPrimePResidual_normal Nat.prime_two X
  refine perfect_le_of_pmod 2 (oPrimePResidual 2 X) (Λ := J) ?_ ?_
  · exact CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hJ
  · intro x hx
    obtain ⟨a, ha⟩ := exists_pow_mem_oResidual 2 (⟨x, hA hx⟩ : ↥(oPrimeResidual 2 X))
    exact ⟨a, ⟨_, ha, by simp⟩⟩

end Layer

section Centralize

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem layer_centralizes_Op (ctx : Stage2Ctx G z k S) {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hrk : CFSG.pRank r ↥(Op r (Cen z)) ≤ 2) :
    ∀ x ∈ pLayerOf 2 (Cen z), ∀ y ∈ Op r (Cen z), x * y = y * x := by
  let K : Subgroup ↥(Cen z) := (centralizer (Op r (Cen z) : Set G)).comap (Cen z).subtype
  have hle : pLayer ↥(Cen z) 2 ≤ K := by
    refine sSup_le fun J hJ => ?_
    have hJN := isPComponent_le_oPrimePResidual hJ
    have hres : CFSG.ComponentClassification.FooteLit.oddResidualIn J = J :=
      CFSG.ComponentClassification.FooteLit.oddResidualIn_eq_self_of_isPComponent_top hJ
    rw [← hres]
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨hgJ, a, ha⟩
    have hgL : ((g : ↥(Cen z)) : G) ∈ LC z := by
      obtain ⟨K, hK, -, hKmap, -⟩ := hJ
      refine Stage1.Thm6.Prod.mem_LC_of_mem_layer z (hJN hgJ) ?_
      have hgK : toBar z (g : ↥(Cen z)) ∈ K := by
        rw [← hKmap]
        exact ⟨g, hgJ, rfl⟩
      exact (le_sSup (s := {K : Subgroup (CentralizerBar z) | IsComponent K}) hK) hgK
    have hgbar : toBar z g ∈ LBar z := ⟨g, hgL, rfl⟩
    have h2 : ∃ a : ℕ, orderOf (g : G) = 2 ^ a := ⟨a, by rw [Subgroup.orderOf_coe]; exact ha⟩
    have hcomm := star ctx hr2 hrk g.2 h2 hgbar
    show (g : G) ∈ centralizer (Op r (Cen z) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm y hy).symm
  rw [pLayerOf_eq_map]
  rintro _ ⟨j, hj, rfl⟩ y hy
  exact ((Subgroup.mem_centralizer_iff.mp (hle hj)) y hy).symm

theorem S_inf_WC_centralizes_Op (ctx : Stage2Ctx G z k S) {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hrk : CFSG.pRank r ↥(Op r (Cen z)) ≤ 2) :
    ∀ s ∈ S ⊓ WC z, ∀ y ∈ Op r (Cen z), s * y = y * s := by
  rintro s ⟨hsS, hsW⟩ y hy
  have hsC : s ∈ Cen z := ctx.S_le_Cen hsS
  have hs2 : ∃ a : ℕ, orderOf s = 2 ^ a := orderOf_mem_S ctx hsS
  have hsW' : toBar z ⟨s, hsC⟩ ∈ WBar z := ⟨⟨s, hsC⟩, Subgroup.mem_subgroupOf.mpr hsW, rfl⟩
  exact star ctx hr2 hrk hsC hs2 (WBar_le_LBar ctx hsW') y hy

omit [Finite G] in
theorem comm_of_Fpi {x : G} (M : Subgroup G)
    (h : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ y ∈ Op r M, x * y = y * x) :
    ∀ f ∈ Fpi {r | r.Prime ∧ r ≠ 2} M, x * f = f * x := by
  have hle : Fpi {r | r.Prime ∧ r ≠ 2} M ≤ centralizer ({x} : Set G) := by
    refine iSup₂_le fun r hr => ?_
    have : Fact r.Prime := ⟨hr.1⟩
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (h r hr.1 hr.2 y (Op_Fm_le_Op r M hy)).symm
  intro f hf
  exact ((Subgroup.mem_centralizer_singleton_iff.mp (hle hf))).symm

end Centralize

theorem lemma19_2_thm (h171 : Prop17_1) : Lemma19_2 := by
  intro G _ _ z k S M hfail
  by_contra hne
  have hrk : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r ↥(Op r M) ≤ 2 := by
    intro r hr hr2
    by_contra h3
    exact hne ⟨r, hr, hr2, by omega⟩
  obtain ⟨hM, -⟩ := h171 G z k S M hfail.ctx hfail.fail
  subst hM
  have ctx : Stage2Ctx G z k S := hfail.ctx.ctx
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z) := ctx.sylow
  have hB1 : ∀ x ∈ pLayerOf 2 (Cen z), ∀ f ∈ (fitOdd ↥(Cen z)).map (Cen z).subtype,
      x * f = f * x := by
    intro x hx f hf
    refine comm_of_Fpi (Cen z) (fun r hr hr2 y hy => ?_) f (fitOdd_le_Fpi (Cen z) hf)
    have : Fact r.Prime := ⟨hr⟩
    exact layer_centralizes_Op ctx hr2 (hrk r hr hr2) x hx y hy
  have hB2 : ∀ x ∈ S ⊓ WC z, ∀ f ∈ (fitOdd ↥(Cen z)).map (Cen z).subtype, x * f = f * x := by
    intro x hx f hf
    refine comm_of_Fpi (Cen z) (fun r hr hr2 y hy => ?_) f (fitOdd_le_Fpi (Cen z) hf)
    have : Fact r.Prime := ⟨hr⟩
    exact S_inf_WC_centralizes_Op ctx hr2 (hrk r hr hr2) x hx y hy
  apply hfail.fail
  refine ⟨?_, fun h => absurd h (lt_irrefl _), ?_⟩
  · show pLayerOf 2 (Cen z) = Em (Cen z)
    rw [pLayerOf_eq_map, Em_eq]
    congr 1
    refine pLayer_eq_layer_of_centralizes fun j hj f hf => ?_
    have hj' : (j : G) ∈ pLayerOf 2 (Cen z) := by
      rw [pLayerOf_eq_map]
      exact ⟨j, hj, rfl⟩
    exact Subtype.ext (hB1 (j : G) hj' (f : G) ⟨f, hf, rfl⟩)
  · exact fun _ => isInternalDirectProduct_of_sylow_of_centralizes hSyl fun s hs f hf => hB2 s hs f hf

end CFSG.GH74.GLS.Stage2.Final.Thm4.L192
