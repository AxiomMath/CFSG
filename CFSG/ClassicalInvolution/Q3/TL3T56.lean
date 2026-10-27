module

public import CFSG.ClassicalInvolution.Q3.TL3T40

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

@[expose] def maxOrbSet (Ω P : Set (Subgroup G)) : Set (Subgroup G) :=
  {M | M ∈ Ω ∧ IsMaxOrb (TC.nbrAdj Ω) M P}

omit [Finite G] in
theorem pSpan_comm_of_comm {S T : Set (Subgroup G)}
    (h : ∀ M ∈ S, ∀ L ∈ T, ∀ a ∈ M, ∀ b ∈ L, a * b = b * a) :
    ∀ a ∈ pSpan S, ∀ b ∈ pSpan T, a * b = b * a := by
  have hle : pSpan S ≤ Subgroup.centralizer (pSpan T : Set G) := by
    refine pSpan_le fun M hM a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
    have hle' : pSpan T ≤ Subgroup.centralizer ({a} : Set G) :=
      pSpan_le fun L hL b hb => Subgroup.mem_centralizer_singleton_iff.mpr
        (h M hM L hL a ha b hb).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle' hb)
  intro a ha b hb
  exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm

namespace CHyp

variable {K J : Subgroup G} (hS : CHyp 3 IH Ω K J)
include hS

omit [Finite G] in
theorem mem_maxOrbSet_self : K ∈ maxOrbSet Ω (orbOf (TC.nbrAdj Ω) K J) :=
  ⟨hS.adj.1, hS.max⟩

theorem nbrAdj_of_comm {M L : Subgroup G} (hM : M ∈ Ω) (hL : L ∈ Ω) (hne : L ≠ M)
    (hc : ∀ a ∈ M, ∀ b ∈ L, a * b = b * a) : TC.nbrAdj Ω M L := by
  refine ⟨hM, (TC.mem_omegaNbr_iff hS.hyp hS.two).mpr ⟨hL, hne, ?_⟩⟩
  refine le_trans (fun l hl => ?_) (Subgroup.centralizer_le_normalizer (M : Set G))
  exact Subgroup.mem_centralizer_iff.mpr fun m hm => hc m hm l hl

theorem mem_maxOrbSet_of_adj {M : Subgroup G} (hM : M ∈ Ω)
    (hadj : ∀ L ∈ orbOf (TC.nbrAdj Ω) K J, TC.nbrAdj Ω M L) :
    M ∈ maxOrbSet Ω (orbOf (TC.nbrAdj Ω) K J) :=
  ⟨hM, (isMaxOrb_of_adj_all hS.graphFam' hS.adj.1 hS.max hadj).1⟩

theorem comm_of_mem_maxOrbSet {M : Subgroup G}
    (hM : M ∈ maxOrbSet Ω (orbOf (TC.nbrAdj Ω) K J)) {L : Subgroup G}
    (hL : L ∈ orbOf (TC.nbrAdj Ω) K J) : ∀ a ∈ M, ∀ b ∈ L, a * b = b * a :=
  comm_of_mem_omegaNbr hS.hyp hS.two hM.1 (adj_of_mem_isMaxOrb hS.graphFam' hM.2 hL).2

theorem pSpan_orb_sup_eq_top :
    pSpan (orbOf (TC.nbrAdj Ω) K J) ⊔ pSpan (orbOf (TC.nbrAdj Ω) J K) = ⊤ := by
  rw [eq_top_iff, ← hS.gen]
  refine pSpan_le fun L hL => (le_iSup_of_maxOrb hS.graphFam' hS.adj hS.max L hL).trans ?_
  refine iSup₂_le fun M hM => ?_
  rcases hM with hM | hM
  · exact (le_pSpan hM).trans le_sup_left
  · exact (le_pSpan hM).trans le_sup_right

theorem false_of_comm_both {M : Subgroup G} (hM : M ∈ Ω)
    (h₁ : ∀ L ∈ orbOf (TC.nbrAdj Ω) K J, ∀ a ∈ M, ∀ b ∈ L, a * b = b * a)
    (h₂ : ∀ L ∈ orbOf (TC.nbrAdj Ω) J K, ∀ a ∈ M, ∀ b ∈ L, a * b = b * a) : False := by
  have hcen : M ≤ Subgroup.center G := by
    intro m hm
    rw [Subgroup.mem_center_iff]
    intro g
    have hle : pSpan (orbOf (TC.nbrAdj Ω) K J) ⊔ pSpan (orbOf (TC.nbrAdj Ω) J K) ≤
        Subgroup.centralizer ({m} : Set G) := by
      refine sup_le (pSpan_le fun L hL b hb => ?_) (pSpan_le fun L hL b hb => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (h₁ L hL m hm b hb).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (h₂ L hL m hm b hb).symm
    have hg : g ∈ Subgroup.centralizer ({m} : Set G) := by
      apply hle
      rw [hS.pSpan_orb_sup_eq_top]
      exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  rw [hS.center, le_bot_iff] at hcen
  have h8 := hS.card M hM
  rw [hcen, Subgroup.card_bot] at h8
  norm_num at h8

theorem mem_orb_swap_of_mem_maxOrbSet {M : Subgroup G}
    (hM : M ∈ maxOrbSet Ω (orbOf (TC.nbrAdj Ω) K J)) : M ∈ orbOf (TC.nbrAdj Ω) J K := by
  by_cases hMK : M = K
  · subst hMK
    exact mem_orbOf_self _ _
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hJΩ : J ∈ Ω := hS.orb_subset_omega hJπ
  have hMπ : M ∉ orbOf (TC.nbrAdj Ω) K J := not_mem_of_isMaxOrb hS.graphFam' hM.2
  have hMJ : M ≠ J := fun e => hMπ (e ▸ hJπ)
  have hJM : TC.nbrAdj Ω J M := hS.nbrAdj_of_comm hJΩ hM.1 hMJ fun a ha b hb =>
    (hS.comm_of_mem_maxOrbSet hM hJπ b hb a ha).symm
  by_contra hMo
  refine hS.false_of_comm_both hM.1 (fun L hL => hS.comm_of_mem_maxOrbSet hM hL) ?_
  intro N hN a ha b hb
  have hJN : TC.nbrAdj Ω J N := adj_of_mem_orbOf hS.graphFam'.graph hS.swap.adj hN
  have hMN : M ∉ orbOf (TC.nbrAdj Ω) J N := by rwa [orbOf_eq_of_mem hN]
  have hNM := hS.graphFam'.graph.sep hJN hJM hMN
  exact (comm_of_mem_omegaNbr hS.hyp hS.two hNM.1 hNM.2 b hb a ha).symm

theorem conjSub_mem_maxOrbSet {x : G} {M₀ : Subgroup G}
    (hM₀ : M₀ ∈ maxOrbSet Ω (orbOf (TC.nbrAdj Ω) K J))
    (hx : conjSub x M₀ ∈ maxOrbSet Ω (orbOf (TC.nbrAdj Ω) K J)) {M : Subgroup G}
    (hM : M ∈ maxOrbSet Ω (orbOf (TC.nbrAdj Ω) K J)) :
    conjSub x M ∈ maxOrbSet Ω (orbOf (TC.nbrAdj Ω) K J) := by
  have h1 := isMaxOrb_conj hS.graphFam' hM₀.2 x
  have he : conjSub x '' orbOf (TC.nbrAdj Ω) K J = orbOf (TC.nbrAdj Ω) K J :=
    maxOrb_unique hS.graphFam' hx.1 h1 hx.2
  refine ⟨hS.hyp.conjInvariant x M hM.1, ?_⟩
  have h2 := isMaxOrb_conj hS.graphFam' hM.2 x
  rwa [he] at h2

theorem not_comm_orb_swap :
    ¬ ∀ M ∈ orbOf (TC.nbrAdj Ω) J K, ∀ L ∈ orbOf (TC.nbrAdj Ω) K J,
      ∀ a ∈ M, ∀ b ∈ L, a * b = b * a := by
  intro hc
  set N := pSpan (orbOf (TC.nbrAdj Ω) J K) with hN
  have hXX := pSpan_comm_of_comm hc
  have hnorm : Subgroup.normalizer (N : Set G) = ⊤ := by
    rw [eq_top_iff, ← hS.pSpan_orb_sup_eq_top]
    refine sup_le (fun x hx => ?_) Subgroup.le_normalizer
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [show x * h * x⁻¹ = h by rw [← hXX h hh x hx]; group]
      exact hh
    · intro hh
      have e := hXX _ hh x hx
      have : h = x * h * x⁻¹ :=
        calc h = x⁻¹ * (x * h * x⁻¹ * x) := by group
          _ = x⁻¹ * (x * (x * h * x⁻¹)) := by rw [e]
          _ = x * h * x⁻¹ := by group
      rw [this]
      exact hh
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hJΩ : J ∈ Ω := hS.orb_subset_omega hJπ
  obtain ⟨t, ht⟩ := hS.trans K hS.adj.1 J hJΩ
  have hKN : K ≤ N := le_pSpan (mem_orbOf_self J K)
  have hJN : J ≤ N := by
    intro j hj
    rw [← ht, mem_conjSub_iff] at hj
    have htn : t ∈ Subgroup.normalizer (N : Set G) := by rw [hnorm]; exact Subgroup.mem_top t
    have := (Subgroup.mem_normalizer_iff.mp htn (t⁻¹ * j * t)).mp (hKN hj)
    rwa [show t * (t⁻¹ * j * t) * t⁻¹ = j by group] at this
  have hcen : J ≤ Subgroup.center G := by
    intro j hj
    rw [Subgroup.mem_center_iff]
    intro g
    have hle : pSpan (orbOf (TC.nbrAdj Ω) K J) ⊔ N ≤ Subgroup.centralizer ({j} : Set G) :=
      sup_le (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr
          (hXX j (hJN hj) b hb).symm)
        (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr
          (hXX b hb j (le_pSpan hJπ hj)))
    have hg : g ∈ Subgroup.centralizer ({j} : Set G) := by
      apply hle
      rw [hS.pSpan_orb_sup_eq_top]
      exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  rw [hS.center, le_bot_iff] at hcen
  have h8 := hS.card J hJΩ
  rw [hcen, Subgroup.card_bot] at h8
  norm_num at h8

omit [Finite G] in
theorem not_comm_self {M : Subgroup G} (hM : M ∈ Ω) : ¬ ∀ a ∈ M, ∀ b ∈ M, a * b = b * a := by
  intro hc
  obtain ⟨-, P, hP, hPc⟩ := hS.hyp.omega1 M hM
  apply hPc
  exact ⟨⟨fun a b => Subtype.ext (hc a (hP.1 a.2) b (hP.1 b.2))⟩⟩

end CHyp

end CFSG.ClassicalInvolution.Q3.TC.Thin
