module

public import CFSG.ClassicalInvolution.Q3.Q3TWY7
public import CFSG.ClassicalInvolution.Q3.Q3TWY6
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBLocal
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBWeakNodes

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair symplecticBlockPair_map)
open scoped MatrixGroups commutatorElement

local notation "𝔽₃" => GaloisField 3 1


section Nodes

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}

theorem exists_nodes_odd_full3 {m : ℕ} (hm : 3 ≤ m) (c : TCtx3 .POmegaOdd m Ω K z) :
    ∃ j : Fin m → Subgroup G,
      (∀ a : Fin m, a.val + 1 < m → j a ∈ centralizingMembers Ω {z} ∧ j a ≠ K ∧
        ¬ locImg Ω z (j a) ≤ c.d.Q₁) ∧
      (∀ a, j a ≤ locLayer Ω z) ∧ (∀ a, Pow3 (j a)) ∧ (∀ a, Commutes K (j a)) ∧
      (∀ a b : Fin m, a.val + 1 < b.val → Commutes (j a) (j b)) ∧
      (∀ a b : Fin m, a.val + 1 = b.val → b.val + 1 < m → ∃ W : Subgroup G,
        LinearBlockStandardPair 𝔽₃ W (j a) (j b)) ∧
      (∀ a b : Fin m, a.val + 2 = m → b.val + 1 = m → ∃ W : Subgroup G,
        SymplecticBlockPair 𝔽₃ W (j a) (j b)) ∧
      (∀ a : Fin m, locImg Ω z (j a) =
        (rankOne (modelUniv .POmegaOdd m 3 1 Nat.prime_three).D.rootGroup a).map c.d.ψ) := by
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  let R : Fin (m - 1) → Subgroup (modelUniv .POmegaOdd m 3 1 Nat.prime_three).K := fun a =>
    rankOne (oddDatum m 𝔽₃).rootGroup
      (⟨a.val, by have := a.isLt; show a.val < m; omega⟩ : Fin (oddDatum m 𝔽₃).rank)
  let Rs : Subgroup (modelUniv .POmegaOdd m 3 1 Nat.prime_three).K :=
    rankOne (oddDatum m 𝔽₃).rootGroup
      (⟨m - 1, by show m - 1 < m; omega⟩ : Fin (oddDatum m 𝔽₃).rank)
  have hR : ∀ a, R a ∈ fundamentalSubgroups .POmegaOdd
      (modelUniv .POmegaOdd m 3 1 Nat.prime_three).D :=
    fun a => rankOne_mem_fundamentalSubgroups_oddDatum hm
      (by show a.val + 1 < m; have := a.isLt; omega)
  have hRc : ∀ a b : Fin (m - 1), a ≠ b → ¬ (a.val + 1 = b.val) → ¬ (b.val + 1 = a.val) →
      Commutes (R a) (R b) := by
    intro a b hab h1 h2'
    refine commutes_rankOne_oddDatum hm h2 ?_
    refine cartanB_eq_zero_of_far ?_
    have : a.val ≠ b.val := fun e => hab (Fin.ext e)
    simp only
    omega
  have hRs : ∀ a b : Fin (m - 1), a.val + 1 = b.val → ∃ W,
      LinearBlockStandardPair 𝔽₃ W (R a) (R b) := by
    intro a b hab
    have hbl := b.isLt
    exact standardPair_oddDatum_edge' (F := 𝔽₃) hm
      (i := (⟨a.val, by show a.val < m; omega⟩ : Fin m))
      (j := (⟨b.val, by show b.val < m; omega⟩ : Fin m)) hab (by show b.val + 1 < m; omega)
  obtain ⟨jl, hjl, hjlc, hjlp, hjlK⟩ := c.exists_nodes_gen3 R hR (fun a b => a.val + 1 = b.val)
    hRc hRs
  set Yl : Subgroup G := locLayer Ω z with hYl
  set O := classicalInvolutionOddCore ↥Yl with hO
  have hlY : ∀ a : Fin (m - 1), jl a ≤ Yl := fun a => le_centralizingLayer (hjl a).1
  have hlpow : ∀ a : Fin (m - 1), Pow3 (jl a) := fun a =>
    pow3_of_member3 c.hΩ c.hex (hjl a).1.1
  have hlimg : ∀ a, locImg Ω z (jl a) = (R a).map c.d.ψ := fun a => (hjl a).2.2.2
  have hjlc' : ∀ a b : Fin (m - 1), a.val + 1 < b.val → Commutes (jl a) (jl b) := fun a b hab =>
    hjlc a b (fun e => by have := congrArg Fin.val e; omega) (by omega) (by omega)
  obtain ⟨Wm, hWm⟩ := symplecticPair_oddDatum3 hm
  have hmap := symplecticBlockPair_map_central3 hWm c.d.ψ c.d.ker_le
  let a₀ : Fin (m - 1) := ⟨m - 2, by omega⟩
  have hA : Pow3 ((jl a₀).subgroupOf Yl) := pow3_subgroupOf (hlY a₀) (hlpow a₀)
  have hmap' : SymplecticBlockPair 𝔽₃ (Wm.map c.d.ψ)
      (((jl a₀).subgroupOf Yl).map (QuotientGroup.mk' O)) (Rs.map c.d.ψ) := by
    have e : ((jl a₀).subgroupOf Yl).map (QuotientGroup.mk' O) = (R a₀).map c.d.ψ := hlimg a₀
    rw [e]
    exact hmap
  obtain ⟨B, hBimg, hBpow, W', hW'⟩ := symplecticBlockPair_lift3 (O := O) c.hP1
    (CFSG.ComponentClassification.OddCore.odd_card _) c.hO3 hA hmap'
  let jS : Subgroup G := B.map Yl.subtype
  have hjSimg : locImg Ω z jS = Rs.map c.d.ψ := by
    show locImg Ω z (B.map Yl.subtype) = _
    rw [locImg_map_subtype, hBimg]
  have hjSY : jS ≤ Yl := Subgroup.map_subtype_le _
  have hjSpow : Pow3 jS := hBpow.map Yl.subtype
  have hsp : ∃ W : Subgroup G, SymplecticBlockPair 𝔽₃ W (jl a₀) jS := by
    have := symplecticBlockPair_map hW' Yl.subtype Yl.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hlY a₀)] at this
    exact ⟨_, this⟩
  have hKY : K ≤ Yl := le_centralizingLayer c.hKz
  have hKS : Commutes K jS := commutes_of_commutes_locImg_pow3 c.hP1 c.hO3 hKY hjSY
    (pow3_of_member3 c.hΩ c.hex c.hK) (by
      intro a ha b hb
      rw [hjSimg] at hb
      exact c.d.comm₀ a (c.hQ₀ ha) b (by obtain ⟨x, _, rfl⟩ := hb; exact ⟨x, rfl⟩))
  have hlS : ∀ a : Fin (m - 1), a.val + 1 < m - 1 → Commutes (jl a) jS := by
    intro a ha
    refine commutes_of_commutes_locImg_pow3 c.hP1 c.hO3 (hlY a) hjSY (hlpow a) ?_
    rw [hlimg a, hjSimg]
    refine commutes_map_hom c.d.ψ ?_
    exact commutes_rankOne_oddDatum hm h2 (cartanB_eq_zero_of_far (Or.inl (by simp only; omega)))
  let j : Fin m → Subgroup G := fun a => if h : a.val + 1 < m then jl ⟨a.val, by omega⟩ else jS
  have hjlong : ∀ a : Fin m, ∀ (h : a.val + 1 < m), j a = jl ⟨a.val, by omega⟩ := fun a h => by
    simp only [j, h, dite_true]
  have hjshort : ∀ a : Fin m, a.val + 1 = m → j a = jS := fun a h => by
    have h' : ¬ (a.val + 1 < m) := by omega
    simp only [j, h', dite_false]
  refine ⟨j, fun a ha => ?_, fun a => ?_, fun a => ?_, fun a => ?_, ?_, ?_, ?_, fun a => ?_⟩
  · rw [hjlong a ha]
    exact ⟨(hjl _).1, (hjl _).2.1, (hjl _).2.2.1⟩
  · by_cases h : a.val + 1 < m
    · rw [hjlong a h]; exact hlY _
    · rw [hjshort a (by have := a.isLt; omega)]; exact hjSY
  · by_cases h : a.val + 1 < m
    · rw [hjlong a h]; exact hlpow _
    · rw [hjshort a (by have := a.isLt; omega)]; exact hjSpow
  · by_cases h : a.val + 1 < m
    · rw [hjlong a h]; exact hjlK _
    · rw [hjshort a (by have := a.isLt; omega)]; exact hKS
  · intro a b hab
    have hbl := b.isLt
    by_cases hb : b.val + 1 < m
    · rw [hjlong a (by omega), hjlong b hb]
      exact hjlc' _ _ hab
    · rw [hjlong a (by omega), hjshort b (by omega)]
      exact hlS _ (by simp only; omega)
  · intro a b hab hb
    rw [hjlong a (by omega), hjlong b hb]
    exact hjlp _ _ (by simp only; exact hab)
  · intro a b ha hb
    rw [hjlong a (by omega), hjshort b hb]
    have e : (⟨a.val, by omega⟩ : Fin (m - 1)) = a₀ := Fin.ext (by simp only [a₀]; omega)
    rw [e]
    exact hsp
  · by_cases h : a.val + 1 < m
    · rw [hjlong a h]
      exact hlimg _
    · have h' : a.val + 1 = m := by have := a.isLt; omega
      rw [hjshort a h', hjSimg]
      have e : a = (⟨m - 1, by omega⟩ : Fin m) := Fin.ext (by simp only; omega)
      rw [e]
      rfl

end Nodes

end CFSG.ClassicalInvolution.Q3.Q3TWY
