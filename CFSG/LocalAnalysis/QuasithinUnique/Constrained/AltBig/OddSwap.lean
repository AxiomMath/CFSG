module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.OddBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Swap
import all CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Swap

public section

namespace CFSG.QuasithinUnique.L246C127.AltBig

open Equiv Equiv.Perm Subgroup CFSG.Open
open scoped commutatorElement

variable {β : Type} [Fintype β] [DecidableEq β]

private theorem ao6_omega_fix (q : OddInv β) {e : Perm β}
    (h : ∀ x, x ≠ q.ω → e x = x ∨ e x = q.μ x) : e q.ω = q.ω := by
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y, e q.ω = y := ⟨_, rfl⟩
  have hyω : y ≠ q.ω := fun h' => hne (hy.trans h')
  rcases h y hyω with h1 | h1
  · exact hyω (e.injective (h1.trans hy.symm))
  · rcases h (q.μ y) (q.mu_ne_omega hyω) with h2 | h2
    · exact q.fpf y hyω (e.injective (h2.trans h1.symm))
    · rw [q.inv y] at h2
      exact hyω (q.mu_eq_omega_iff.1 (e.injective (h2.trans hy.symm)))

theorem tc_odd (q : OddInv β) {R : Subgroup (Perm β)}
    (hq : ∀ x, x ≠ q.ω → swap x (q.μ x) ∈ R)
    {E : Subgroup (Perm β)} (hE : IsComponentOf E R) :
    ∃ C : Finset β, 5 ≤ C.card ∧ E = altOn C := by
  have hperf : ⁅E, E⁆ = E := tcPerfectOfQuasisimple hE.2.2
  have hne : E ≠ ⊥ := tcNeBotOfQuasisimple hE.2.2
  have hcT : _root_.commutator ↥E = ⊤ := by
    obtain ⟨hc, -⟩ := hE.2.2
    exact hc
  have hsub : CFSG.Open.IsSubnormal (swapClos R) R :=
    CFSG.Open.IsSubnormal.step (swapClos_le R) (swapClos_normal R)
      (CFSG.Open.IsSubnormal.refl R)
  have hswapmem : ∀ x, x ≠ q.ω → swap x (q.μ x) ∈ swapClos R := by
    intro x hx
    have hsw : (swap x (q.μ x)).IsSwap := ⟨x, q.μ x, Ne.symm (q.fpf x hx), rfl⟩
    have hmem : swap x (q.μ x) ∈ {σ : Perm β | σ ∈ R ∧ σ.IsSwap} := And.intro (hq x hx) hsw
    unfold swapClos
    exact Subgroup.subset_closure hmem
  rcases CFSG.Quasithin.B113.component_le_or_commutator_eq_bot hE hsub with hEswap | hcomm
  ·
    have hEsub : CFSG.Open.IsSubnormal E (swapClos R) := by
      have h := CFSG.Quasithin.B113.isSubnormal_inf_of_le hE.2.1 (swapClos_le R)
      rwa [inf_of_le_right hEswap] at h
    have hEcomp : IsComponentOf E (swapClos R) := ⟨hEswap, hEsub, hE.2.2⟩
    obtain ⟨x0, -, hx0E⟩ : ∃ x, 3 ≤ (cls R x).card ∧ E ≤ altOn (cls R x) := by
      by_contra H
      have hcomm_all : ∀ x, 3 ≤ (cls R x).card → ⁅E, altOn (cls R x)⁆ = ⊥ := by
        intro x hx
        have hX : CFSG.Open.IsSubnormal (altOn (cls R x)) (swapClos R) :=
          CFSG.Open.IsSubnormal.step (altOn_le_swapClos R x) (altOn_normal R x)
            (CFSG.Open.IsSubnormal.refl (swapClos R))
        rcases CFSG.Quasithin.B113.component_le_or_commutator_eq_bot hEcomp hX with h | h
        · exact absurd ⟨x, hx, h⟩ H
        · exact h
      have hEE : ⁅E, E⁆ = ⊥ := by
        rw [← le_bot_iff, Subgroup.commutator_le]
        intro e he f hf
        rw [Subgroup.mem_bot]
        exact commutatorElement_eq_one_iff_mul_comm.2
          (comm_of_comm_alts R hEswap hcomm_all e he f hf).eq
      exact hne (hperf.symm.trans hEE)
    have hECsub : CFSG.Open.IsSubnormal E (altOn (cls R x0)) := by
      have h := CFSG.Quasithin.B113.isSubnormal_inf_of_le hEsub (altOn_le_swapClos R x0)
      rwa [inf_of_le_right hx0E] at h
    have hcard5 : 5 ≤ (cls R x0).card := by
      by_contra hlt
      have hsolv : Group.IsSolvable ↥(altOn (cls R x0)) := altOn_solvable (by omega)
      have hsolvE : Group.IsSolvable ↥E :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hx0E)
      haveI : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).2 hne
      have hlt' := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥E
      rw [hcT] at hlt'
      exact lt_irrefl _ hlt'
    have hsimple : IsSimpleGroup ↥(altOn (cls R x0)) := altOn_simple hcard5
    refine ⟨cls R x0, hcard5, ?_⟩
    rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hECsub hsimple with h | h
    · exact absurd h hne
    · exact h
  ·
    exfalso
    apply hne
    have hfix0 : ∀ e ∈ E, ∀ x, x ≠ q.ω → e x = x ∨ e x = q.μ x := by
      intro e he x hx
      have hmem : ⁅e, swap x (q.μ x)⁆ ∈ ⁅E, swapClos R⁆ :=
        Subgroup.commutator_mem_commutator he (hswapmem x hx)
      rw [hcomm, Subgroup.mem_bot] at hmem
      have hcm := commutatorElement_eq_one_iff_mul_comm.1 hmem
      have h1 : e (q.μ x) = swap x (q.μ x) (e x) := by
        have h' := congrArg (fun σ : Perm β => σ x) hcm
        simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_left] using h'
      by_cases h2 : e x = x
      · exact Or.inl h2
      by_cases h3 : e x = q.μ x
      · exact Or.inr h3
      have h4 : swap x (q.μ x) (e x) = e x := Equiv.swap_apply_of_ne_of_ne h2 h3
      rw [h4] at h1
      exact absurd (e.injective h1) (q.fpf x hx)
    have hfix : ∀ e ∈ E, ∀ x ∈ (Set.univ : Set β), e x = x ∨ e x = q.μ x := by
      intro e he x _
      by_cases hx : x = q.ω
      · exact Or.inl (by rw [hx]; exact ao6_omega_fix q (hfix0 e he))
      · exact hfix0 e he x hx
    have hall := perfect_fix_pairs_odd q hperf (W := Set.univ) hfix (fun x _ => Set.mem_univ _)
    rw [Subgroup.eq_bot_iff_forall]
    intro e he
    ext x
    simpa using hall e he x (Set.mem_univ x)

end CFSG.QuasithinUnique.L246C127.AltBig
