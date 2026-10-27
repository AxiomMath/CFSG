module

public import CFSG.ClassicalInvolution.RouteD.GapsOrthPairs
public import CFSG.ClassicalInvolution.RouteD.GapsPatternBLast
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups modelUniv InClass
  IsClassicalMember centralizingMembers)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime]

section Models

variable {m : ℕ}

theorem pairBound_oddDatum (hp2 : p ≠ 2) (hm : 4 ≤ m) (hm3 : 3 ≤ m) (hq : 5 ≤ p ^ f) :
    PairBound (Subgroup.center (spinGroup (quadOdd m (GaloisField p f))))
      (fundamentalSubgroups .POmegaOdd (oddDatum m (GaloisField p f))) (2 * m + 1) := by
  obtain ⟨hf, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have h2 : (2 : GaloisField p f) ≠ 0 := ModelFacts.two_ne_zero_galoisField f hp2
  have hdim : 9 ≤ Module.finrank (GaloisField p f) (Fin m ⊕ Fin m ⊕ Unit → GaloisField p f) := by
    rw [finrank_odd]
    omega
  have hb := pairBound_model hodd (nondegenerate_polarBilin_quadOdd m (GaloisField p f) h2) hdim
  rw [finrank_odd] at hb
  exact (centralQuot_odd hp2 hm3 hq).pairBound hb

theorem pairBound_odd (hp2 : p ≠ 2) (hm : 4 ≤ m) (hq : 5 ≤ p ^ f) :
    PairBound (Subgroup.center (modelUniv .POmegaOdd m p f Fact.out).K)
      (fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd m p f Fact.out).D) (2 * m + 1) :=
  pairBound_oddDatum hp2 hm (by omega) hq

end Models

section Nodes

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}
  {tY : StatedLieTag} {nY : ℕ} {ι : Type} {adj : ι → ι → Prop}

theorem nodes_pair_config {d : ℕ}
    (hF : PairBound (Subgroup.center (modelUniv tY nY p f Fact.out).K)
      (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) d)
    (c : TCtx p f tY nY Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 tY nY Ω z) (nd : LNodes p f adj Ω K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {b u v : ι}
    (hβb : Commutes β (nd.J b)) (hβu : Commutes β (nd.J u)) (hβv : Commutes β (nd.J v))
    (hub : u ≠ b) (hub' : ¬ LNodes.Adj adj u b) (hvb : v ≠ b) (hvb' : ¬ LNodes.Adj adj v b)
    (huv : LNodes.Adj adj u v) : 12 ≤ d := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape (nd.mem b) (nd.cl b)
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two ht.orderOf_eq_two
  have hnormK : conjSub t K = K :=
    conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  exact pair_config cx hF (A := K) (B := β) (C := nd.J u) (D := nd.J v) (wA := z) (wB := t)
    (wC := nd.w u) (wD := nd.w v) (nd.mem_loc b c.hK (nd.commK b)) (nd.mem_loc b hβ hβb)
    (nd.mem_loc b (nd.mem u) (nd.commutes_of_not_adj hub hub'))
    (nd.mem_loc b (nd.mem v) (nd.commutes_of_not_adj hvb hvb')) c.hz ht (nd.cl u) (nd.cl v) hKne
    hnKβ hzt hnormK (nd.ne_J hΩ (nd.adj_ne huv)) (nd.not_commutes_of_adj huv)
    (nd.commute_w h2 u v) (nd.conjSub_w h2 huv) (nd.commK u) (nd.commK v) hβu hβv

end Nodes

section Four

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}
  {tY : StatedLieTag} {nY : ℕ}

local macro "bidx_tac" : tactic =>
  `(tactic| first
    | (simp [LNodes.Adj, adjPath]; done)
    | (simp [LNodes.Adj, adjPath]; omega)
    | (apply fin_ne_of_val_ne; simp only; omega)
    | (left; apply Fin.ext; simp only; omega)
    | (right; apply Fin.ext; simp only; omega))

theorem path_four_all_fixed_false {d : ℕ} (hd : d < 12)
    (hF : PairBound (Subgroup.center (modelUniv tY nY p f Fact.out).K)
      (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) d)
    (c : TCtx p f tY nY Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 tY nY Ω z) (nd : LNodes p f (adjPath 4) Ω K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfix : ∀ a, Commutes β (nd.J a)) : False := by
  have := nodes_pair_config hF c hsingle hshape nd hβ ht hKβ (b := ⟨0, by omega⟩)
    (u := ⟨2, by omega⟩) (v := ⟨3, by omega⟩) (hfix _) (hfix _) (hfix _) (by bidx_tac)
    (by bidx_tac) (by bidx_tac) (by bidx_tac) (by bidx_tac)
  omega

theorem path_four_interior_false {d : ℕ} (hd : d < 12)
    (hF : PairBound (Subgroup.center (modelUniv tY nY p f Fact.out).K)
      (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) d)
    (c : TCtx p f tY nY Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 tY nY Ω z) (nd : LNodes p f (adjPath 4) Ω K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {pp : Fin 4}
    (hfix : ∀ a, a ≠ pp → Commutes β (nd.J a)) (h1 : 1 ≤ pp.val) (h2 : pp.val + 2 ≤ 4) :
    False := by
  have hpt : pp.val < 4 := pp.isLt
  have hcases : pp.val = 1 ∨ pp.val = 2 := by omega
  rcases hcases with h | h
  · have hpp : ∀ a : Fin 4, a.val ≠ 1 → a ≠ pp := fun a ha e => ha (by rw [e]; exact h)
    have := nodes_pair_config hF c hsingle hshape nd hβ ht hKβ (b := ⟨0, by omega⟩)
      (u := ⟨2, by omega⟩) (v := ⟨3, by omega⟩) (hfix _ (hpp _ (by simp)))
      (hfix _ (hpp _ (by simp))) (hfix _ (hpp _ (by simp))) (by bidx_tac) (by bidx_tac)
      (by bidx_tac) (by bidx_tac) (by bidx_tac)
    omega
  · have hpp : ∀ a : Fin 4, a.val ≠ 2 → a ≠ pp := fun a ha e => ha (by rw [e]; exact h)
    have := nodes_pair_config hF c hsingle hshape nd hβ ht hKβ (b := ⟨3, by omega⟩)
      (u := ⟨0, by omega⟩) (v := ⟨1, by omega⟩) (hfix _ (hpp _ (by simp)))
      (hfix _ (hpp _ (by simp))) (hfix _ (hpp _ (by simp))) (by bidx_tac) (by bidx_tac)
      (by bidx_tac) (by bidx_tac) (by bidx_tac)
    omega

end Four

section Six

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}
  {tY : StatedLieTag} {nY : ℕ}

local macro "bidx6_tac" : tactic =>
  `(tactic| first
    | (simp [LNodes.Adj, adjPath]; done)
    | (simp [LNodes.Adj, adjPath]; omega)
    | (apply fin_ne_of_val_ne; simp only; omega)
    | (left; apply Fin.ext; simp only; omega)
    | (right; apply Fin.ext; simp only; omega))

theorem path_interior_false_six {n : ℕ} (hn : 6 ≤ n)
    (hF : OrthGeom (Subgroup.center (modelUniv tY nY p f Fact.out).K)
      (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) (GaloisField p f))
    (c : TCtx p f tY nY Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 tY nY Ω z) (nd : LNodes p f (adjPath n) Ω K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    {pp : Fin n} (hfix : ∀ a, a ≠ pp → Commutes β (nd.J a))
    (hmov : ¬ Commutes β (nd.J pp)) (hnorm : conjSub t (nd.J pp) = nd.J pp)
    (h1 : 1 ≤ pp.val) (h2 : pp.val + 2 ≤ n) : False := by
  have hpt : pp.val < n := pp.isLt
  have hcases : pp.val = 1 ∨ pp.val = 2 ∨ pp.val = 3 ∨ 4 ≤ pp.val := by omega
  rcases hcases with h | h | h | h
  ·
    refine scenarioA hF c hsingle hshape nd hβ ht hKβ (pp := pp) (a₀ := ⟨0, by omega⟩)
      (a₁ := ⟨2, by omega⟩) (e := ⟨3, by omega⟩) (b := ⟨n - 1, by omega⟩) hfix hmov hnorm
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    bidx6_tac
  ·
    refine scenarioA hF c hsingle hshape nd hβ ht hKβ (pp := pp) (a₀ := ⟨1, by omega⟩)
      (a₁ := ⟨3, by omega⟩) (e := ⟨0, by omega⟩) (b := ⟨n - 1, by omega⟩) hfix hmov hnorm
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    bidx6_tac
  ·
    refine scenarioA hF c hsingle hshape nd hβ ht hKβ (pp := pp) (a₀ := ⟨2, by omega⟩)
      (a₁ := ⟨4, by omega⟩) (e := ⟨5, by omega⟩) (b := ⟨0, by omega⟩) hfix hmov hnorm
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    bidx6_tac
  ·
    refine scenarioA hF c hsingle hshape nd hβ ht hKβ (pp := pp)
      (a₀ := ⟨pp.val - 1, by omega⟩) (a₁ := ⟨pp.val + 1, by omega⟩)
      (e := ⟨pp.val - 2, by omega⟩) (b := ⟨0, by omega⟩) hfix hmov hnorm
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    bidx6_tac

end Six

end CFSG.ClassicalInvolution.RouteD.Gaps
