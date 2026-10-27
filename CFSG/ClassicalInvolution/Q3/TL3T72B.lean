module

public import CFSG.ClassicalInvolution.Q3.TL3T56
public import CFSG.ClassicalInvolution.Q3.TL3T72

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

namespace CHyp

variable {K J : Subgroup G} (hS : CHyp 3 IH Ω K J)
include hS

theorem maxOrbSet_eq' {n : ℕ} (hn : (5 ≤ n ∧ n ≤ 7) ∨ 9 ≤ n)
    (I' : AEIdent (orbOf (TC.nbrAdj Ω) J K) n)
    {Ks : Subgroup G} (hKs : Ks ∈ orbOf (TC.nbrAdj Ω) J K) (hKsK : Ks ≠ K)
    (hKsπ : Ks ∉ orbOf (TC.nbrAdj Ω) K J)
    (hz : ∀ z zs : G, IsUniqueInvolution K z → IsUniqueInvolution Ks zs → zs = z)
    (hKsX : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ k ∈ Ks, x * k = k * x) :
    ∀ M ∈ maxOrbSet Ω (orbOf (TC.nbrAdj Ω) K J), M = K ∨ M = Ks := by
  classical
  have hn5 : 5 ≤ n := by omega
  have hn8 : n ≠ 8 := by omega
  set P := orbOf (TC.nbrAdj Ω) J K with hP
  have hPΩ : P ⊆ Ω := hS.swap.orb_subset_omega
  have hJΩ : J ∈ Ω := hS.swap.adj.1
  have hk' : IsPGroup 2 I'.φ.ker := I'.toLabel.isPGroup_ker hS.swap.oddCore_orb_eq_bot
  have hconj' : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P := fun L hL x hx =>
    CSetting.conjSub_mem_orb hJΩ (hS.swap.pSpan_orb_le hx) hL
  have hinj' : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I'.φ = (L'.subgroupOf (pSpan P)).map I'.φ → L = L' :=
    fun L hL L' hL' h => aeIdent_eq_of_map_eq hS.hyp hS.two hPΩ hn5 I' hk' hL hL' h
  have h8 : ∀ L ∈ Ω, Nat.card L = 8 := fun L hL => by rw [hS.card L hL]; norm_num
  have hKP : K ∈ P := mem_orbOf_self J K
  have hKsB : Ks ∈ maxOrbSet Ω (orbOf (TC.nbrAdj Ω) K J) := by
    refine hS.mem_maxOrbSet_of_adj (hPΩ hKs) fun L hL => hS.nbrAdj_of_comm (hPΩ hKs)
      (hS.orb_subset_omega hL) (fun e => hKsπ (e ▸ hL)) fun a ha b hb => ?_
    exact (hKsX b (le_pSpan hL hb) a ha).symm
  obtain ⟨α, hα, b₀, hlab₀⟩ := I'.label K hKP
  obtain ⟨γ, hγ, c, hlab₁⟩ := I'.label Ks hKs
  obtain ⟨⟨zK, hzK⟩, -⟩ := hS.hyp.omega1 K hS.adj.1
  obtain ⟨⟨zKs, hzKs⟩, -⟩ := hS.hyp.omega1 Ks (hPΩ hKs)
  have hzz : zKs = zK := hz zK zKs hzK hzKs
  have e1 := I'.map_eq_zBar hn5 hKP (h8 K hS.adj.1) hlab₀ hzK
  have e2 := I'.map_eq_zBar hn5 hKs (h8 Ks (hPΩ hKs)) hlab₁ hzKs
  have hγα : γ = α := by
    apply AE.eq_of_zBar_eq hn8
    rw [← e1, ← e2]
    congr 1
    exact Subtype.ext hzz
  subst hγα
  have hc : c = !b₀ := by
    by_contra hne
    have : c = b₀ := by cases c <;> cases b₀ <;> simp_all
    subst this
    exact hKsK (hinj' Ks hKs K hKP (hlab₁.trans hlab₀.symm))
  subst hc
  rcases AEIdent.twins_or_all' hn I' hconj' hinj'
      (fun M hM => hS.mem_orb_swap_of_mem_maxOrbSet hM)
      (fun x _ ⟨M₀, hM₀, hxM₀⟩ M hM => hS.conjSub_mem_maxOrbSet hM₀ hxM₀ hM)
      hS.mem_maxOrbSet_self hKsB hγ hlab₀ hlab₁ with h | h
  · exact h
  · exfalso
    exact hS.not_comm_orb_swap fun M hM L hL => hS.comm_of_mem_maxOrbSet (h M hM) hL

theorem eq_of_comm_pSpan' {n : ℕ} (hn : (5 ≤ n ∧ n ≤ 7) ∨ 9 ≤ n)
    (I' : AEIdent (orbOf (TC.nbrAdj Ω) J K) n)
    {Ks : Subgroup G} (hKs : Ks ∈ orbOf (TC.nbrAdj Ω) J K) (hKsK : Ks ≠ K)
    (hKsπ : Ks ∉ orbOf (TC.nbrAdj Ω) K J)
    (hz : ∀ z zs : G, IsUniqueInvolution K z → IsUniqueInvolution Ks zs → zs = z)
    (hKsX : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ k ∈ Ks, x * k = k * x)
    {M : Subgroup G} (hM : M ∈ Ω)
    (hc : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ m ∈ M, x * m = m * x) : M = K ∨ M = Ks := by
  have hMπ : M ∉ orbOf (TC.nbrAdj Ω) K J := fun h =>
    hS.not_comm_self hM fun a ha b hb => hc a (le_pSpan h ha) b hb
  refine hS.maxOrbSet_eq' hn I' hKs hKsK hKsπ hz hKsX M (hS.mem_maxOrbSet_of_adj hM fun L hL =>
    hS.nbrAdj_of_comm hM (hS.orb_subset_omega hL) (fun e => hMπ (e ▸ hL)) fun a ha b hb => ?_)
  exact (hc b (le_pSpan hL hb) a ha).symm

theorem eq_of_mem_omegaNbr' {n : ℕ} (hn : (5 ≤ n ∧ n ≤ 7) ∨ 9 ≤ n)
    (I' : AEIdent (orbOf (TC.nbrAdj Ω) J K) n)
    {Ks : Subgroup G} (hKs : Ks ∈ orbOf (TC.nbrAdj Ω) J K) (hKsK : Ks ≠ K)
    (hKsπ : Ks ∉ orbOf (TC.nbrAdj Ω) K J)
    (hz : ∀ z zs : G, IsUniqueInvolution K z → IsUniqueInvolution Ks zs → zs = z)
    (hKsX : ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), ∀ k ∈ Ks, x * k = k * x)
    {M : Subgroup G} (hM : M ∈ omegaNbr Ω K) : M ∈ orbOf (TC.nbrAdj Ω) K J ∨ M = Ks := by
  by_cases hMπ : M ∈ orbOf (TC.nbrAdj Ω) K J
  · exact Or.inl hMπ
  right
  have hKM : TC.nbrAdj Ω K M := ⟨hS.adj.1, hM⟩
  have hadj : ∀ L ∈ orbOf (TC.nbrAdj Ω) K J, TC.nbrAdj Ω M L := by
    intro L hL
    have hKL : TC.nbrAdj Ω K L := adj_of_mem_orbOf hS.graphFam'.graph hS.adj hL
    have hML : M ∉ orbOf (TC.nbrAdj Ω) K L := by rwa [orbOf_eq_of_mem hL]
    have hLM := hS.graphFam'.graph.sep hKL hKM hML
    exact hS.graphFam'.graph.symm hLM
  rcases hS.maxOrbSet_eq' hn I' hKs hKsK hKsπ hz hKsX M (hS.mem_maxOrbSet_of_adj hM.1 hadj)
    with h | h
  · exact absurd h hM.2.1
  · exact h

end CHyp

end CFSG.ClassicalInvolution.Q3.TC.Thin
