module


public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.LinearAlgebra.CoprimeActions.AlternatingFormEvenDimension

open Module LinearMap.BilinForm Submodule

theorem exists_half_finrank {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (B : LinearMap.BilinForm F V) (hA : B.IsAlt)
    (hN : B.Nondegenerate) : ∃ n, Module.finrank F V = 2 * n := by
  have aux (F : Type _) [Field F] :
      ∀ (d : ℕ) (V : Type _) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
        (B : LinearMap.BilinForm F V), finrank F V = d → B.IsAlt → B.Nondegenerate →
        ∃ n, finrank F V = 2 * n := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
    intro V _ _ _ B hd hA hN
    by_cases hV : Subsingleton V
    · exact ⟨0, by simp [finrank_zero_of_subsingleton]⟩
    · rw [not_subsingleton_iff_nontrivial] at hV
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      obtain ⟨w, hw⟩ : ∃ w, B v w ≠ 0 := by
        by_contra h
        push Not at h
        exact hv (hN.1 v h)
      set c := B v w with hc
      have hvv : B v v = 0 := hA v
      have hww : B w w = 0 := hA w
      have hwv : B w v = -c := (hA.neg_eq v w).symm
      let W : Submodule F V := span F (Set.range ![v, w])
      have hli : LinearIndependent F ![v, w] := by
        rw [LinearIndependent.pair_iff]
        intro s t h
        have h1 := congrArg (fun x => B x w) h
        have h2 := congrArg (fun x => B v x) h
        simp [hvv, hww, hwv, ← hc] at h1 h2
        refine ⟨?_, ?_⟩
        · rcases h1 with h1 | h1
          · exact h1
          · exact absurd h1 hw
        · rcases h2 with h2 | h2
          · exact h2
          · exact absurd h2 hw
      have hW2 : finrank F W = 2 := by
        simpa using finrank_span_eq_card hli
      have hvW : v ∈ W := subset_span ⟨0, rfl⟩
      have hwW : w ∈ W := subset_span ⟨1, rfl⟩
      have hWnd : (B.restrict W).Nondegenerate := by
        have key : ∀ x : W, (∀ y : W, B x y = 0) → (x : V) = 0 := by
          intro x hx
          obtain ⟨a, b, hab⟩ := mem_span_pair.1 (by simpa [W, Set.range_comp, Matrix.range_cons] using x.2)
          have h1 := hx ⟨v, hvW⟩
          have h2 := hx ⟨w, hwW⟩
          simp only [LinearMap.BilinForm.restrict_apply] at h1 h2
          rw [← hab] at h1 h2
          simp [hvv, hww, hwv] at h1 h2
          have ha : a = 0 := by
            rcases h1 with h1 | h1
            · exact h1
            · exact absurd h1 hw
          have hb : b = 0 := by
            rcases h2 with h2 | h2
            · exact h2
            · exact absurd h2 hw
          rw [← hab, ha, hb]; simp
        refine ⟨fun x hx => Subtype.ext (key x hx), fun y hy => Subtype.ext (key y ?_)⟩
        intro z
        have := hy z
        simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at this ⊢
        exact hA.isRefl _ _ this
      have hcompl : IsCompl W (B.orthogonal W) :=
        isCompl_orthogonal_of_restrict_nondegenerate hA.isRefl hWnd
      have hfr := finrank_orthogonal hN W
      have hlt : finrank F (B.orthogonal W) < d := by
        rw [hfr, hW2, ← hd]
        have : 0 < finrank F V := Module.finrank_pos
        omega
      have hND' : (B.restrict (B.orthogonal W)).Nondegenerate := by
        rw [restrict_nondegenerate_iff_isCompl_orthogonal hA.isRefl,
          orthogonal_orthogonal hN hA.isRefl]
        exact hcompl.symm
      obtain ⟨n, hn⟩ := ih _ hlt (B.orthogonal W) (B.restrict (B.orthogonal W)) rfl
        (fun x => hA x) hND'
      refine ⟨n + 1, ?_⟩
      have := Submodule.finrank_le W
      omega
  exact aux F _ V B rfl hA hN

end CFSG.LinearAlgebra.CoprimeActions.AlternatingFormEvenDimension
