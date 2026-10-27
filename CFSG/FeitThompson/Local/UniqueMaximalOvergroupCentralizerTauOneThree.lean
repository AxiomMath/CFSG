module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.SigmaComplementThreeHallFactors
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup
open CFSG.FeitThompson.Prep05 (centralizerIn)
open CFSG.FeitThompson.Prep09 (IsMinimalSimpleOddOrder)

universe u

variable {G : Type u} [Group G]

theorem natCard_subgroupOf_of_le {E P : Subgroup G} (h : P ≤ E) :
    Nat.card ↥(P.subgroupOf E) = Nat.card ↥P :=
  Nat.card_congr (subgroupOfEquivOfLe h).toEquiv

theorem le_of_subgroupOf_le {E X Y : Subgroup G} (hX : X ≤ E) (hY : Y ≤ E)
    (h : X.subgroupOf E ≤ Y.subgroupOf E) : X ≤ Y := by
  have h' := Subgroup.map_mono (f := E.subtype) h
  rwa [Subgroup.map_subgroupOf_eq_of_le hX, Subgroup.map_subgroupOf_eq_of_le hY] at h'

theorem ne_bot_of_natCard_prime {P : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card ↥P = p) : P ≠ ⊥ := by
  intro hbot
  rw [hbot, Subgroup.card_bot] at hcard
  exact hp.ne_one hcard.symm

theorem zpowers_eq_of_natCard_prime {P : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card ↥P = p) {x : G} (hx : x ∈ P) (hx1 : x ≠ 1) : zpowers x = P := by
  have : Fact p.Prime := ⟨hp⟩
  refine le_antisymm (zpowers_le.2 hx) fun y hy => ?_
  have hxne : (⟨x, hx⟩ : ↥P) ≠ 1 := by simpa [Subtype.ext_iff] using hx1
  obtain ⟨n, hn⟩ := mem_zpowers_of_prime_card (G := ↥P) hcard hxne (g' := ⟨y, hy⟩)
  exact ⟨n, by simpa [Subtype.ext_iff] using hn⟩

theorem isPiSubgroup_subgroupOf_of_natCard_prime {π : Set ℕ} {E P : Subgroup G} {p : ℕ}
    (hPE : P ≤ E) (hp : p.Prime) (hcard : Nat.card ↥P = p) (hmem : p ∈ π) :
    IsPiSubgroup π (P.subgroupOf E) := by
  rw [isPiSubgroup_iff, natCard_subgroupOf_of_le hPE, hcard]
  simp [hp.primeFactors, hmem]

theorem exists_isHallPiSubgroup_tau1_ge [Finite G] {M E P : Subgroup G}
    [Group.IsSolvable ↥E] (hPE : P ≤ E)
    (hπ : IsPiSubgroup (tau1Primes M) (P.subgroupOf E)) :
    ∃ E₁ : Subgroup G, E₁ ≤ E ∧ P ≤ E₁ ∧ IsHallPiSubgroup (tau1Primes M) (E₁.subgroupOf E) := by
  obtain ⟨H, hH, hPH⟩ := exists_isHallSubgroup_ge_of_isPiSubgroup hπ
  refine ⟨H.map E.subtype, map_subtype_le _, ?_, ?_⟩
  · have h := Subgroup.map_mono (f := E.subtype) hPH
    rwa [Subgroup.map_subgroupOf_eq_of_le hPE] at h
  · rw [subgroupOf_map_subtype]
    exact hH.isHallPiSubgroup

theorem FNI_tau13_nonregular_core_line_unique
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_tau13_nonfree_third_factor_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_tau13_nonregular_core_line_unique.{u} := by
  intro G _ _ hG M E hME p hp P hPE hPcard hcent q hq Q hQ hQcard
  have hG9 : IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG4 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hM : IsCoatom M := hME.isCoatom
  have hsemi := hME.semidirect
  have hEM : E ≤ M := hsemi.right_le
  have hEne : E ≠ ⊤ := fun h => hM.1 (top_le_iff.1 (h ▸ hEM))
  have hEsolv : Group.IsSolvable ↥E := hG.isSolvable_of_ne_top E hEne
  have hpprime : p.Prime := by
    rcases hp with hp' | hp'
    · exact prime_of_mem_tau1Primes hp'
    · exact prime_of_mem_tau3Primes hp'
  have hPne : P ≠ ⊥ := ne_bot_of_natCard_prime hpprime hPcard
  rcases hp with hp1 | hp3
  · obtain ⟨E₁, hE₁E, hPE₁, hHall⟩ :=
      exists_isHallPiSubgroup_tau1_ge (M := M) hPE
        (isPiSubgroup_subgroupOf_of_natCard_prime hPE hpprime hPcard hp1)
    exact (h₃ G hG9 M hM E hEM hsemi E₁ hE₁E hHall P hPE₁ hPne q hq Q hQ hQcard).1
  ·
    obtain ⟨E₁, E₂, E₃, hsplit, -⟩ :=
      FNI_sigma_complement_three_factors h₁ G hG4 M E ⟨hM, hsemi⟩
    have hPE₃ : P ≤ E₃ := by
      refine le_of_subgroupOf_le hPE hsplit.le_E₃ ?_
      have : (E₃.subgroupOf E).Normal := hsplit.outer.normal_subgroupOf
      exact hsplit.isHall_E₃.le_of_isPiSubgroup
        (isPiSubgroup_subgroupOf_of_natCard_prime hPE hpprime hPcard hp3)
    obtain ⟨x, hxP, hx1⟩ : ∃ x ∈ P, x ≠ 1 := by
      rw [Ne, eq_bot_iff_forall] at hPne
      simpa using hPne
    have hx : centralizerIn (sigmaCore M) (zpowers x) ≠ ⊥ := by
      rwa [zpowers_eq_of_natCard_prime hpprime hPcard hxP hx1]
    obtain ⟨-, hE₁ne, -, -, hfix⟩ :=
      h₂ G hG M E E₁ E₂ E₃ ⟨⟨hM, hsemi⟩, hsplit.le_E₁, hsplit.le_E₂, hsplit.le_E₃,
        hsplit.isHall_E₁, hsplit.isHall_E₂, hsplit.isHall_E₃, hsplit.outer, hsplit.inner,
        hsplit.isCyclic_E₁, hsplit.isCyclic_E₃, hsplit.le_commutator_E₃, hsplit.normal_E₂_sup_E₃,
        hsplit.centralizer_E₃⟩ ⟨x, hPE₃ hxP, hx1, hx⟩
    have key : centralizerIn (sigmaCore M) P = centralizerIn (sigmaCore M) E₁ := by
      rw [hfix P (hPE₃.trans hsplit.le_E₃) hPne, hfix E₁ hsplit.le_E₁ hE₁ne]
    rw [key] at hQ
    exact (h₃ G hG9 M hM E hEM hsemi E₁ hsplit.le_E₁ hsplit.isHall_E₁ E₁ le_rfl hE₁ne q hq Q
      hQ hQcard).1

end

end CFSG.FeitThompson.Proofs
