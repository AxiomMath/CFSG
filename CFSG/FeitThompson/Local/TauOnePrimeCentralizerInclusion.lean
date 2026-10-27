module

public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup
open CFSG.FeitThompson.Prep09

universe u

theorem inf_centralizer_le_of_inf_centralizer_le {G : Type*} [Group G] {A S : Subgroup G}
    (hAS : A ≤ S) {X Y : Set G} (h : S ⊓ centralizer X ≤ S ⊓ centralizer Y) :
    A ⊓ centralizer X ≤ A ⊓ centralizer Y :=
  le_inf inf_le_left (((inf_le_inf_right _ hAS).trans h).trans inf_le_right)

theorem FTS_tau_one_prime_centralizer_inclusion
    (h₁ : Statements.FTS_admissible_tau_one_prime_centralizer_inclusion.{u}) :
    Statements.FTS_tau_one_prime_centralizer_inclusion.{u} := by
  intro G _ _ hG M hM E hEM hsd p r hp hr hpτ P hPE hPcard R hRE hRcard
  have : Fintype G := Fintype.ofFinite G
  have := hG.isSimpleGroup
  have hamb : _root_.CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
    { odd := hG.odd_natCard
      simple := hG.isSimpleGroup
      nonabelian := hG.not_isMulCommutative
      solvable := hG.isSolvable_of_ne_top }
  have hMmem : M ∈ _root_.CFSG.FeitThompson.Prep06.maximalSubgroups G := hM
  set A : Subgroup G := _root_.CFSG.FeitThompson.Prep06.alphaCoreIn M with hA
  have hAS : A ≤ sigmaCore M :=
    map_subtype_alphaCore_le_sigmaCore hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hM
  have hRcentP : R ≤ centralizer (P : Set G) := hRE.trans inf_le_right
  have hPcentR : P ≤ centralizer (R : Set G) := Subgroup.le_centralizer_iff.mp hRcentP
  have hadm : r ∈ tau1Primes M →
      A ⊓ centralizer (P : Set G) ≤ A ⊓ centralizer (R : Set G) →
      A ⊓ centralizer (P : Set G) = A ⊓ centralizer (R : Set G) := by
    intro hrτ hle
    have hrev := h₁ G hamb M E hMmem hEM hsd.sup_eq hsd.inf_eq_bot r p hr hp hrτ R P
      (hRE.trans inf_le_left) hRcard (le_inf hPE hPcentR) hPcard
      (fun _ h => le_antisymm h hle)
    exact le_antisymm hle (inf_centralizer_le_of_inf_centralizer_le hAS hrev)
  exact h₁ G hamb M E hMmem hEM hsd.sup_eq hsd.inf_eq_bot p r hp hr hpτ P R hPE hPcard
    hRE hRcard hadm

end

end CFSG.FeitThompson.Proofs
