module

public import CFSG.Certificates.Kernel.RouteP.GeomSound
public import Certificates.Data.Kernel.RouteP.RonanRoot
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

public section

namespace CFSG.KS.RouteP

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.RouteP

theorem rootOK_spec {E : Nat → Nat} {lo hi : Nat} (h : rootOK E lo hi = true) :
    ∀ e, lo < e → e < hi → ePar (E e) < e := by
  intro e h1 h2
  have hb : e - lo - 1 < Nat.sub (Nat.sub hi lo) 1 := by
    change e - lo - 1 < hi - lo - 1
    omega
  have h3 : Nat.blt (ePar (E (lo + 1 + (e - lo - 1)))) (lo + 1 + (e - lo - 1)) = true :=
    allI_spec h (e - lo - 1) hb
  have e3 : lo + 1 + (e - lo - 1) = e := by omega
  rw [e3, Nat.blt_eq] at h3
  exact h3

theorem preconnected_of_span {V : Type*} {G : SimpleGraph V} {S : Set V} {lo hi : Nat}
    (u : Nat → V) (C : Nat → Set V) (par : Nat → Nat) (hroot : u lo ∈ S)
    (hC : ∀ e, lo ≤ e → e < hi → ∀ v ∈ C e, v ∈ S ∧ G.Adj (u e) v)
    (hpar : ∀ e, lo < e → e < hi → lo ≤ par e ∧ par e < e ∧ u e ∈ C (par e))
    (hcov : ∀ v ∈ S, ∃ e, lo ≤ e ∧ e < hi ∧ (v ∈ C e ∨ v = u e)) :
    (G.induce S).Preconnected := by
  have key : ∀ e, lo ≤ e → e < hi →
      ∃ h : u e ∈ S, (G.induce S).Reachable ⟨u lo, hroot⟩ ⟨u e, h⟩ := by
    intro e
    induction e using Nat.strong_induction_on with
    | _ e ih =>
      intro hle hhi
      rcases Nat.eq_or_lt_of_le hle with rfl | hlt
      · exact ⟨hroot, SimpleGraph.Reachable.refl _⟩
      · obtain ⟨h1, h2, h3⟩ := hpar e hlt hhi
        obtain ⟨hp, hr⟩ := ih (par e) h2 h1 (h2.trans hhi)
        obtain ⟨hS, hA⟩ := hC (par e) h1 (h2.trans hhi) (u e) h3
        have hA' : (G.induce S).Adj ⟨u (par e), hp⟩ ⟨u e, hS⟩ := hA
        exact ⟨hS, hr.trans hA'.reachable⟩
  have reach : ∀ v : S, (G.induce S).Reachable ⟨u lo, hroot⟩ v := by
    rintro ⟨v, hv⟩
    obtain ⟨e, h1, h2, hv'⟩ := hcov v hv
    obtain ⟨he, hr⟩ := key e h1 h2
    rcases hv' with hvC | rfl
    · have hA : (G.induce S).Adj ⟨u e, he⟩ ⟨v, hv⟩ := (hC e h1 h2 v hvC).2
      exact hr.trans hA.reachable
    · exact hr
  intro a b
  exact (reach a).symm.trans (reach b)

end CFSG.KS.RouteP

end
