module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85eBar
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2Inst
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der75Main

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

section Abstract

open CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2

variable {Y : Type} [Group Y]

theorem normalizes_first {L₁ L₂ : Subgroup Y} (hne : L₁ ≠ L₂)
    (hcomps : {K : Subgroup Y | IsComponent K} = {L₁, L₂}) {g : Y} (hg : Odd (orderOf g)) :
    g ∈ normalizer (L₁ : Set Y) := by
  have hc₁ : IsComponent L₁ := by
    have : L₁ ∈ {K : Subgroup Y | IsComponent K} := by rw [hcomps]; exact Or.inl rfl
    exact this
  have hc₂ : IsComponent L₂ := by
    have : L₂ ∈ {K : Subgroup Y | IsComponent K} := by rw [hcomps]; exact Or.inr rfl
    exact this
  have hmem : ∀ J : Subgroup Y, IsComponent J → J = L₁ ∨ J = L₂ := by
    intro J hJ
    have : J ∈ {K : Subgroup Y | IsComponent K} := hJ
    rw [hcomps] at this
    exact this
  by_contra hgn
  have h1 : cj g L₁ = L₂ := by
    rcases hmem _ (isComponent_cj g hc₁) with h | h
    · exact absurd (cj_eq_iff.1 h) hgn
    · exact h
  have h2 : cj g L₂ = L₁ := by
    rcases hmem _ (isComponent_cj g hc₂) with h | h
    · exact h
    · exfalso
      apply hne
      have := congrArg (cj g⁻¹) (h.trans h1.symm)
      rw [cj_inv_cj, cj_inv_cj] at this
      exact this.symm
  have hsq : g * g ∈ normalizer (L₁ : Set Y) := by
    rw [← cj_eq_iff, cj_mul, h1, h2]
  obtain ⟨m, hm⟩ := hg
  have hpow : g ^ (2 * m + 1) = 1 := by
    rw [← hm]; exact pow_orderOf_eq_one g
  have h3 : g ^ (2 * m) ∈ normalizer (L₁ : Set Y) := by
    rw [pow_mul]
    rw [← sq] at hsq
    exact Subgroup.pow_mem _ hsq m
  apply hgn
  have h4 : g = (g ^ (2 * m))⁻¹ := by
    have : g ^ (2 * m) * g = 1 := by rw [← pow_succ]; exact hpow
    exact eq_inv_of_mul_eq_one_right this
  rw [h4]
  exact Subgroup.inv_mem _ h3

theorem normalizes_both {L₁ L₂ : Subgroup Y} (hne : L₁ ≠ L₂)
    (hcomps : {K : Subgroup Y | IsComponent K} = {L₁, L₂}) {g : Y} (hg : Odd (orderOf g)) :
    g ∈ normalizer (L₁ : Set Y) ∧ g ∈ normalizer (L₂ : Set Y) :=
  ⟨normalizes_first hne hcomps hg, normalizes_first hne.symm (by rw [hcomps, Set.pair_comm]) hg⟩

end Abstract

section Kinds

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem lpairCtx_of_data (hz : orderOf z = 2) (hSL : SL2Pair (CentralizerBar z) L₁ L₂)
    (hsup : LBar z = L₁ ⊔ L₂) (hzbar : toBar z ⟨z, mem_Cen_self z⟩ ∈ LBar z)
    (hnorm : ∀ g : CentralizerBar z, Odd (orderOf g) →
      g ∈ normalizer (L₁ : Set (CentralizerBar z)) ∧ g ∈ normalizer (L₂ : Set (CentralizerBar z)))
    (hidx : (RC S z).relIndex S ≤ 4) : LPairCtx G z S := by
  have hcent : toBar z ⟨z, mem_Cen_self z⟩ ∈ L₁ ⊓ L₂ := by
    refine hSL.central_mem (by rw [← hsup]; exact hzbar) ?_ (orderOf_zBar hz)
    intro y _
    exact Subgroup.mem_center_iff.mp (toBar_z_mem_center z) y
  exact ⟨⟨L₁, L₂, hSL, hsup, hcent, hnorm⟩, hidx⟩

theorem lpairCtx_of_pair {q : ℕ} (hpair : Stage1Pair G z S q L₁ L₂) (hz : orderOf z = 2)
    (hidx : (RC S z).relIndex S ≤ 4) : LPairCtx G z S := by
  have hSL : SL2Pair (CentralizerBar z) L₁ L₂ :=
    { comm := hpair.prod.2.1
      card_inf := hpair.prod.2.2
      sl₁ := ⟨q, hpair.odd, hpair.sl₁⟩
      sl₂ := ⟨q, hpair.odd, hpair.sl₂⟩ }
  have hsup : LBar z = L₁ ⊔ L₂ := hpair.prod.1.symm
  have hzbar : toBar z ⟨z, mem_Cen_self z⟩ ∈ LBar z :=
    mem_barOf_iff.mpr ⟨z, mem_Cen_self z, Stage2.Bender.Thm1.z_mem_LC_of_pair hpair hz, rfl⟩
  exact lpairCtx_of_data hz hSL hsup hzbar (fun g hg => normalizes_both hpair.ne hpair.comps hg) hidx

end Kinds

theorem lpairCtx_g2 {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (hctx : Stage2Ctx G z Kind.g2 S) : LPairCtx G z S := by
  have hz : orderOf z = 2 := hctx.orderOf_z
  cases hctx.data with
  | g2 h =>
    obtain ⟨r₁, r₂, L₁, L₂, hsh⟩ := h.shape
    have hn₁ : L₁.Normal := Final.Thm6.L208g2.normal₁ hctx hsh
    have hn₂ : L₂.Normal := Final.Thm6.L208g2.normal₂ hctx hsh
    have h3r := Final.Thm6.L208g2.three_le_r₂ hsh
    obtain ⟨hodd₁, hodd₂, -, ⟨hsup, hcomm, hcard⟩, hm₁, hm₂, -, h3, h4, hidx, -, -⟩ := hsh
    have hSL : SL2Pair (CentralizerBar z) L₁ L₂ :=
      ⟨hcomm, hcard, ⟨r₁, hodd₁, hm₁⟩, ⟨r₂, hodd₂, hm₂⟩⟩
    have hF : generalizedFitting (CentralizerBar z) ≤ LBar z := by
      rcases Nat.lt_or_ge 3 r₂ with h | h
      · exact ((h4 h).2).le
      · obtain rfl : r₂ = 3 := by omega
        rw [(h3 rfl).2]
        exact Subgroup.map_subtype_le _
    have hzF : toBar z ⟨z, mem_Cen_self z⟩ ∈ generalizedFitting (CentralizerBar z) := by
      refine CFSG.centralizer_generalizedFitting_le (CentralizerBar z) ?_
      rw [Subgroup.mem_centralizer_iff]
      intro f _
      exact Subgroup.mem_center_iff.mp (toBar_z_mem_center z) f
    refine lpairCtx_of_data hz hSL hsup.symm (hF hzF) (fun g _ => ⟨?_, ?_⟩) (by omega)
    · rw [Subgroup.normalizer_eq_top_iff.2 hn₁]; exact Subgroup.mem_top g
    · rw [Subgroup.normalizer_eq_top_iff.2 hn₂]; exact Subgroup.mem_top g

theorem lpairCtx_psp4 {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (hctx : Stage2Ctx G z Kind.psp4 S) : LPairCtx G z S := by
  cases hctx.data with
  | psp4 h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    exact lpairCtx_of_pair h.pair hctx.orderOf_z (h.index.le.trans (by norm_num))

theorem lpairCtx_l4 {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} (ε : Bool)
    (hctx : Stage2Ctx G z (Kind.l4 ε) S) : LPairCtx G z S := by
  cases hctx.data with
  | l4 _ h =>
    obtain ⟨q, L₁, L₂, h⟩ := h
    exact lpairCtx_of_pair h.pair hctx.orderOf_z h.index_le

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85
