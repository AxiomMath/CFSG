module

public import CFSG.ClassicalInvolution.Q3.Q3TY33

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.LieType CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement


section Transfer

variable {KY X : Type} [Group KY] [Group X] {π : KY →* X} {𝓕 : Set (Subgroup KY)}
  {𝓕' : Set (Subgroup X)} {Z' : Subgroup X}

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3W.CentralQuot3.chainBound0
    (h : CentralQuot3 π 𝓕 𝓕' Z') {d : ℕ} (hb : ChainBound0 Z' 𝓕' d) :
    ChainBound0 (Subgroup.center KY) 𝓕 d := by
  intro r hr c hc
  refine hb r hr (fun a => (c a).map π) ⟨fun a ha => ?_, fun a ha => ?_, fun a b hab hb' => ?_⟩
  · exact h.map_mem _ (hc.mem a ha)
  · exact h.modelAdj (hc.mem a (by omega)) (hc.mem (a + 1) ha) (hc.adj a ha)
  · exact (h.commutes_iff (hc.mem a (by omega))).mpr (hc.comm a b hab hb')

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3W.CentralQuot3.pairBound
    (h : CentralQuot3 π 𝓕 𝓕' Z') {d : ℕ} (hb : PairBound Z' 𝓕' d) :
    PairBound (Subgroup.center KY) 𝓕 d := by
  intro A hA B hB C hC D hD hAB hCD hAC hAD hBC hBD
  exact hb _ (h.map_mem A hA) _ (h.map_mem B hB) _ (h.map_mem C hC) _ (h.map_mem D hD)
    (h.modelAdj hA hB hAB) (h.modelAdj hC hD hCD) ((h.commutes_iff hA).mpr hAC)
    ((h.commutes_iff hA).mpr hAD) ((h.commutes_iff hB).mpr hBC) ((h.commutes_iff hB).mpr hBD)

end Transfer

section Plus

variable {m : ℕ}

theorem chainBound0_plusDatum3 (hm : 5 ≤ m) :
    ChainBound0 (Subgroup.center (spinGroup (quadPlus m (GaloisField 3 1))))
      (fundamentalSubgroups .POmegaPlus (plusDatum m (GaloisField 3 1) (by omega))) (2 * m) := by
  have hdim : 9 ≤ Module.finrank (GaloisField 3 1) (Fin m ⊕ Fin m → GaloisField 3 1) := by
    rw [finrank_plus]
    omega
  have hb := chainBound0_model (Q := quadPlus m (GaloisField 3 1)) odd_gf3 hdim
  rw [finrank_plus] at hb
  exact (centralQuot3_plus (by omega : 4 ≤ m)).chainBound0 hb

theorem pairBound_plusDatum3 (hm : 5 ≤ m) :
    PairBound (Subgroup.center (spinGroup (quadPlus m (GaloisField 3 1))))
      (fundamentalSubgroups .POmegaPlus (plusDatum m (GaloisField 3 1) (by omega))) (2 * m) := by
  have : NeZero m := ⟨by omega⟩
  have hdim : 9 ≤ Module.finrank (GaloisField 3 1) (Fin m ⊕ Fin m → GaloisField 3 1) := by
    rw [finrank_plus]
    omega
  have : Invertible (2 : GaloisField 3 1) := invertibleOfNonzero two_ne_zero_gf3
  have hb := pairBound_model odd_gf3 (nondegenerate_polarBilin_quadPlus m (GaloisField 3 1)) hdim
  rw [finrank_plus] at hb
  exact (centralQuot3_plus (by omega : 4 ≤ m)).pairBound hb

theorem chainBound0_plus3 (hm : 5 ≤ m) :
    ChainBound0 (Subgroup.center (modelUniv .POmegaPlus m 3 1 Nat.prime_three).K)
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D)
      (2 * m) := by
  have e := RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) (by omega : 3 ≤ m)
  rw [e]
  exact chainBound0_plusDatum3 hm

theorem pairBound_plus3 (hm : 5 ≤ m) :
    PairBound (Subgroup.center (modelUniv .POmegaPlus m 3 1 Nat.prime_three).K)
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m 3 1 Nat.prime_three).D)
      (2 * m) := by
  have e := RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) (by omega : 3 ≤ m)
  rw [e]
  exact pairBound_plusDatum3 hm

end Plus

section Witness

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} {x : G}

theorem chain0_config3 {tY : StatedLieTag} {nY : ℕ} (cx : TCtx3 tY nY Ω N x) {d : ℕ}
    (hF : ChainBound0 (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K)
      (fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D) d)
    {r : ℕ} (hr : 4 ≤ r) {c : ℕ → Subgroup G} {w : ℕ → G}
    (hc : ∀ a < r, c a ∈ centralizingMembers Ω {x})
    (hw : ∀ a < r, IsClassicalMember3 (c a) (w a))
    (hadj : ∀ a, a + 1 < r → c a ≠ c (a + 1) ∧ ¬ Commutes (c a) (c (a + 1)) ∧
      Commute (w a) (w (a + 1)) ∧ conjSub (w (a + 1)) (c a) = c a)
    (hcomm : ∀ a b, a + 1 < b → b < r → Commutes (c a) (c b)) : 2 * (r + 1) ≤ d := by
  classical
  have hcL : ∀ a < r, IsLayerMember3 cx (c a) := by
    intro a ha
    by_cases h1 : a + 1 < r
    · exact IsLayerMember3.of_not_commutes cx (hc a ha) (hc (a + 1) h1) (hadj a h1).1
        (hadj a h1).2.1
    · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      exact IsLayerMember3.of_not_commutes cx (hc (a' + 1) ha) (hc a' (by omega))
        (hadj a' (by omega)).1.symm (fun h => (hadj a' (by omega)).2.1 (commutes_symm h))
  have hex : ∀ a : ℕ, ∃ R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K, a < r →
      R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D ∧
        locImg Ω x (c a) = R.map cx.d.ψ := by
    intro a
    by_cases h : a < r
    · obtain ⟨R, hR, hlR⟩ := (hcL a h).exists_fund
      exact ⟨R, fun _ => ⟨hR, hlR⟩⟩
    · exact ⟨⊥, fun h' => absurd h' h⟩
  choose R hR using hex
  refine hF r hr R ⟨fun a ha => (hR a ha).1, fun a ha => ?_, fun a b hab hb => ?_⟩
  · exact cx.modelAdj_of_adj3 (hc a (by omega)) (hc (a + 1) ha) (hR a (by omega)).1
      (hR (a + 1) ha).1 (hR a (by omega)).2 (hR (a + 1) ha).2 (hw a (by omega)) (hw (a + 1) ha)
      (hadj a ha).1 (hadj a ha).2.1 (hadj a ha).2.2.1 (hadj a ha).2.2.2
  · exact (cx.commutes_iff_fund (hc a (by omega)) (hc b hb) (hR a (by omega)).1
      (hR a (by omega)).2 (hR b hb).2).mp (hcomm a b hab hb)

theorem pair_config3 {tY : StatedLieTag} {nY : ℕ} (cx : TCtx3 tY nY Ω N x) {d : ℕ}
    (hF : PairBound (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K)
      (fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D) d)
    {A B C D : Subgroup G} {wA wB wC wD : G} (hA : A ∈ centralizingMembers Ω {x})
    (hB : B ∈ centralizingMembers Ω {x}) (hC : C ∈ centralizingMembers Ω {x})
    (hD : D ∈ centralizingMembers Ω {x}) (hwA : IsClassicalMember3 A wA)
    (hwB : IsClassicalMember3 B wB) (hwC : IsClassicalMember3 C wC)
    (hwD : IsClassicalMember3 D wD) (hAB : A ≠ B) (hnAB : ¬ Commutes A B)
    (hcAB : Commute wA wB) (hnA : conjSub wB A = A) (hCD : C ≠ D) (hnCD : ¬ Commutes C D)
    (hcCD : Commute wC wD) (hnC : conjSub wD C = C) (hAC : Commutes A C) (hAD : Commutes A D)
    (hBC : Commutes B C) (hBD : Commutes B D) : 12 ≤ d := by
  classical
  have hAL : IsLayerMember3 cx A := IsLayerMember3.of_not_commutes cx hA hB hAB hnAB
  have hBL : IsLayerMember3 cx B :=
    IsLayerMember3.of_not_commutes cx hB hA hAB.symm (fun h => hnAB (commutes_symm h))
  have hCL : IsLayerMember3 cx C := IsLayerMember3.of_not_commutes cx hC hD hCD hnCD
  have hDL : IsLayerMember3 cx D :=
    IsLayerMember3.of_not_commutes cx hD hC hCD.symm (fun h => hnCD (commutes_symm h))
  obtain ⟨RA, hRA, hAR⟩ := hAL.exists_fund
  obtain ⟨RB, hRB, hBR⟩ := hBL.exists_fund
  obtain ⟨RC, hRC, hCR⟩ := hCL.exists_fund
  obtain ⟨RD, hRD, hDR⟩ := hDL.exists_fund
  exact hF RA hRA RB hRB RC hRC RD hRD
    (cx.modelAdj_of_adj3 hA hB hRA hRB hAR hBR hwA hwB hAB hnAB hcAB hnA)
    (cx.modelAdj_of_adj3 hC hD hRC hRD hCR hDR hwC hwD hCD hnCD hcCD hnC)
    ((cx.commutes_iff_fund hA hC hRA hAR hCR).mp hAC)
    ((cx.commutes_iff_fund hA hD hRA hAR hDR).mp hAD)
    ((cx.commutes_iff_fund hB hC hRB hBR hCR).mp hBC)
    ((cx.commutes_iff_fund hB hD hRB hBR hDR).mp hBD)

theorem chain5_false3 {tY : StatedLieTag} {nY : ℕ} (cx : TCtx3 tY nY Ω N x) {d : ℕ}
    (hF : ChainBound0 (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K)
      (fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D) d) (hd : d < 12)
    {m₀ m₁ m₂ m₃ m₄ : Subgroup G} {v₀ v₁ v₂ v₃ v₄ : G}
    (h₀ : m₀ ∈ centralizingMembers Ω {x}) (h₁ : m₁ ∈ centralizingMembers Ω {x})
    (h₂ : m₂ ∈ centralizingMembers Ω {x}) (h₃ : m₃ ∈ centralizingMembers Ω {x})
    (h₄ : m₄ ∈ centralizingMembers Ω {x}) (hw₀ : IsClassicalMember3 m₀ v₀)
    (hw₁ : IsClassicalMember3 m₁ v₁) (hw₂ : IsClassicalMember3 m₂ v₂)
    (hw₃ : IsClassicalMember3 m₃ v₃) (hw₄ : IsClassicalMember3 m₄ v₄)
    (a₀₁ : m₀ ≠ m₁ ∧ ¬ Commutes m₀ m₁ ∧ Commute v₀ v₁ ∧ conjSub v₁ m₀ = m₀)
    (a₁₂ : m₁ ≠ m₂ ∧ ¬ Commutes m₁ m₂ ∧ Commute v₁ v₂ ∧ conjSub v₂ m₁ = m₁)
    (a₂₃ : m₂ ≠ m₃ ∧ ¬ Commutes m₂ m₃ ∧ Commute v₂ v₃ ∧ conjSub v₃ m₂ = m₂)
    (a₃₄ : m₃ ≠ m₄ ∧ ¬ Commutes m₃ m₄ ∧ Commute v₃ v₄ ∧ conjSub v₄ m₃ = m₃)
    (c₀₂ : Commutes m₀ m₂) (c₀₃ : Commutes m₀ m₃) (c₀₄ : Commutes m₀ m₄)
    (c₁₃ : Commutes m₁ m₃) (c₁₄ : Commutes m₁ m₄) (c₂₄ : Commutes m₂ m₄) : False := by
  have key := chain0_config3 cx hF (r := 5) (by norm_num)
    (c := fun a => match a with | 0 => m₀ | 1 => m₁ | 2 => m₂ | 3 => m₃ | _ => m₄)
    (w := fun a => match a with | 0 => v₀ | 1 => v₁ | 2 => v₂ | 3 => v₃ | _ => v₄)
    (fun a ha => by interval_cases a <;> assumption)
    (fun a ha => by interval_cases a <;> assumption)
    (fun a ha => by
      have : a < 4 := by omega
      interval_cases a <;> assumption)
    (fun a b hab hb => by
      have : a < 4 := by omega
      interval_cases a <;> interval_cases b <;> omega)
  omega

end Witness

end CFSG.ClassicalInvolution.Q3.Q3TD
