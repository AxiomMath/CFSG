module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupCertificate
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourCover

public section

namespace CFSG.LargeEvenClassification.Helpers

inductive C8FourCoverEquation where
  | identity
  | delta
  | product (h k : C8FourCode)

@[expose] def c8FourCoverEquationSupport : C8FourCoverEquation → List C8FourCode
  | .identity => [1]
  | .delta => [c8FourDelta]
  | .product h k => [h, k, c8FourCertificateProduct h k]

@[expose] def c8FourCoverEquationConstant : C8FourCoverEquation → ZMod 2
  | .identity => 0
  | .delta => 0
  | .product h k => c8FourKappa h k

@[expose] def c8FourCoverContradiction (equations : List C8FourCoverEquation) : Prop :=
  (∀ g : C8FourCode, ((equations.flatMap c8FourCoverEquationSupport).count g) % 2 = 0) ∧
    (equations.map c8FourCoverEquationConstant).sum = 1

instance c8FourCoverContradiction_decidable (equations : List C8FourCoverEquation) :
    Decidable (c8FourCoverContradiction equations) := inferInstanceAs (Decidable (
      (∀ g : C8FourCode, ((equations.flatMap c8FourCoverEquationSupport).count g) % 2 = 0) ∧
        (equations.map c8FourCoverEquationConstant).sum = 1))

theorem c8Four_even_list_sum (xs : List C8FourCode) (f : C8FourCode → ZMod 2)
    (heven : ∀ g, xs.count g % 2 = 0) : (xs.map f).sum = 0 := by
  classical
  rw [Finset.sum_list_map_count]
  apply Finset.sum_eq_zero
  intro g _
  rw [nsmul_eq_mul]
  have hcast : (xs.count g : ZMod 2) = 0 := by
    apply (ZMod.natCast_eq_zero_iff (xs.count g) 2).mpr
    exact Nat.dvd_of_mod_eq_zero (heven g)
  rw [hcast, zero_mul]

theorem c8FourCoverContradiction_excludes (H : Subgroup C8FourCode)
    (equations : List C8FourCoverEquation) (hvalid : c8FourCoverContradiction equations)
    (hsupport : ∀ equation ∈ equations, ∀ g ∈ c8FourCoverEquationSupport equation, g ∈ H) :
    ¬c8FourCompatible H := by
  classical
  rintro ⟨b, hb1, hbδ, hbmul⟩
  let values : C8FourCode → ZMod 2 := fun g => if hg : g ∈ H then b ⟨g, hg⟩ else 0
  have hequation : ∀ equation ∈ equations,
      ((c8FourCoverEquationSupport equation).map values).sum =
        c8FourCoverEquationConstant equation := by
    intro equation heq
    cases equation with
    | identity =>
      simp only [c8FourCoverEquationSupport, c8FourCoverEquationConstant,
        List.map_singleton, List.sum_singleton, values, dite_eq_left H.one_mem]
      exact hb1
    | delta =>
      have hδ := hsupport .delta heq c8FourDelta (by simp [c8FourCoverEquationSupport])
      simp only [c8FourCoverEquationSupport, List.map_singleton, List.sum_singleton,
        c8FourCoverEquationConstant, values, dite_eq_left hδ]
      exact hbδ ⟨c8FourDelta, hδ⟩ rfl
    | product h k =>
      have hh := hsupport (.product h k) heq h (by simp [c8FourCoverEquationSupport])
      have hk := hsupport (.product h k) heq k (by simp [c8FourCoverEquationSupport])
      have hprod := H.mul_mem hh hk
      have hmult := hbmul ⟨h, hh⟩ ⟨k, hk⟩
      change b ⟨h * k, hprod⟩ = b ⟨h, hh⟩ + b ⟨k, hk⟩ + c8FourKappa h k at hmult
      change values h + (values k + (values (h * k) + 0)) = c8FourKappa h k
      simp only [values, dite_eq_left hh, dite_eq_left hk, dite_eq_left hprod, add_zero]
      rw [hmult]
      have hchar (z : ZMod 2) : z + z = 0 := CharTwo.add_self_eq_zero z
      linear_combination hchar (b ⟨h, hh⟩) + hchar (b ⟨k, hk⟩)
  have hzero := c8Four_even_list_sum (equations.flatMap c8FourCoverEquationSupport) values hvalid.1
  have hsum : ∀ es : List C8FourCoverEquation,
      ((es.flatMap c8FourCoverEquationSupport).map values).sum =
        (es.map (fun e => ((c8FourCoverEquationSupport e).map values).sum)).sum := by
    intro es
    induction es with
    | nil => rfl
    | cons e es ih => simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, ih]
  rw [hsum] at hzero
  have heq : (equations.map (fun equation =>
      ((c8FourCoverEquationSupport equation).map values).sum)).sum =
      (equations.map c8FourCoverEquationConstant).sum := by
    congr 1
    exact List.map_congr_left hequation
  rw [heq, hvalid.2] at hzero
  exact one_ne_zero hzero

@[expose] def c8FourCoverObstruction0 : List C8FourCoverEquation :=
  [.delta, .product ⟨13⟩ ⟨13⟩]

theorem c8FourCoverObstruction0_valid : c8FourCoverContradiction c8FourCoverObstruction0 := by
  decide +kernel

@[expose] def c8FourCoverObstruction1 : List C8FourCoverEquation :=
  [.delta, .product ⟨19⟩ ⟨19⟩]

theorem c8FourCoverObstruction1_valid : c8FourCoverContradiction c8FourCoverObstruction1 := by
  decide +kernel

@[expose] def c8FourCoverObstruction2 : List C8FourCoverEquation :=
  [.delta, .product ⟨23⟩ ⟨23⟩]

theorem c8FourCoverObstruction2_valid : c8FourCoverContradiction c8FourCoverObstruction2 := by
  decide +kernel

@[expose] def c8FourCoverObstruction3 : List C8FourCoverEquation :=
  [.delta, .product ⟨4⟩ ⟨24⟩, .product ⟨4⟩ ⟨64⟩, .product ⟨8⟩ ⟨8⟩, .product ⟨8⟩ ⟨16⟩, .product ⟨8⟩ ⟨28⟩]

theorem c8FourCoverObstruction3_valid : c8FourCoverContradiction c8FourCoverObstruction3 := by
  decide +kernel

@[expose] def c8FourCoverObstruction4 : List C8FourCoverEquation :=
  [.delta, .product ⟨29⟩ ⟨29⟩]

theorem c8FourCoverObstruction4_valid : c8FourCoverContradiction c8FourCoverObstruction4 := by
  decide +kernel

@[expose] def c8FourCoverObstruction5 : List C8FourCoverEquation :=
  [.delta, .product ⟨44⟩ ⟨44⟩]

theorem c8FourCoverObstruction5_valid : c8FourCoverContradiction c8FourCoverObstruction5 := by
  decide +kernel

@[expose] def c8FourCoverObstruction6 : List C8FourCoverEquation :=
  [.delta, .product ⟨4⟩ ⟨27⟩, .product ⟨4⟩ ⟨33⟩, .product ⟨27⟩ ⟨31⟩, .product ⟨27⟩ ⟨33⟩, .product ⟨27⟩ ⟨46⟩]

theorem c8FourCoverObstruction6_valid : c8FourCoverContradiction c8FourCoverObstruction6 := by
  decide +kernel

@[expose] def c8FourCoverObstruction7 : List C8FourCoverEquation :=
  [.delta, .product ⟨50⟩ ⟨50⟩]

theorem c8FourCoverObstruction7_valid : c8FourCoverContradiction c8FourCoverObstruction7 := by
  decide +kernel

@[expose] def c8FourCoverObstruction8 : List C8FourCoverEquation :=
  [.delta, .product ⟨4⟩ ⟨43⟩, .product ⟨10⟩ ⟨43⟩, .product ⟨10⟩ ⟨47⟩]

theorem c8FourCoverObstruction8_valid : c8FourCoverContradiction c8FourCoverObstruction8 := by
  decide +kernel

@[expose] def c8FourCoverObstruction9 : List C8FourCoverEquation :=
  [.delta, .product ⟨54⟩ ⟨54⟩]

theorem c8FourCoverObstruction9_valid : c8FourCoverContradiction c8FourCoverObstruction9 := by
  decide +kernel

@[expose] def c8FourCoverObstruction10 : List C8FourCoverEquation :=
  [.delta, .product ⟨12⟩ ⟨16⟩, .product ⟨12⟩ ⟨28⟩, .product ⟨12⟩ ⟨57⟩, .product ⟨16⟩ ⟨37⟩, .product ⟨37⟩ ⟨12⟩]

theorem c8FourCoverObstruction10_valid : c8FourCoverContradiction c8FourCoverObstruction10 := by
  decide +kernel

@[expose] def c8FourCoverObstruction11 : List C8FourCoverEquation :=
  [.delta, .product ⟨15⟩ ⟨16⟩, .product ⟨15⟩ ⟨64⟩, .product ⟨16⟩ ⟨31⟩]

theorem c8FourCoverObstruction11_valid : c8FourCoverContradiction c8FourCoverObstruction11 := by
  decide +kernel

@[expose] def c8FourCoverObstruction12 : List C8FourCoverEquation :=
  [.delta, .product ⟨10⟩ ⟨16⟩, .product ⟨10⟩ ⟨64⟩, .product ⟨16⟩ ⟨26⟩]

theorem c8FourCoverObstruction12_valid : c8FourCoverContradiction c8FourCoverObstruction12 := by
  decide +kernel

@[expose] def c8FourCoverObstruction13 : List C8FourCoverEquation :=
  [.delta, .product ⟨60⟩ ⟨60⟩]

theorem c8FourCoverObstruction13_valid : c8FourCoverContradiction c8FourCoverObstruction13 := by
  decide +kernel

@[expose] def c8FourCoverObstruction14 : List C8FourCoverEquation :=
  [.delta, .product ⟨8⟩ ⟨101⟩, .product ⟨37⟩ ⟨8⟩, .product ⟨37⟩ ⟨64⟩]

theorem c8FourCoverObstruction14_valid : c8FourCoverContradiction c8FourCoverObstruction14 := by
  decide +kernel

@[expose] def c8FourCoverObstruction15 : List C8FourCoverEquation :=
  [.delta, .product ⟨4⟩ ⟨41⟩, .product ⟨4⟩ ⟨80⟩, .product ⟨16⟩ ⟨64⟩, .product ⟨41⟩ ⟨41⟩, .product ⟨41⟩ ⟨45⟩]

theorem c8FourCoverObstruction15_valid : c8FourCoverContradiction c8FourCoverObstruction15 := by
  decide +kernel

@[expose] def c8FourCoverObstruction16 : List C8FourCoverEquation :=
  [.delta, .product ⟨11⟩ ⟨16⟩, .product ⟨11⟩ ⟨64⟩, .product ⟨16⟩ ⟨27⟩]

theorem c8FourCoverObstruction16_valid : c8FourCoverContradiction c8FourCoverObstruction16 := by
  decide +kernel

@[expose] def c8FourCoverObstruction17 : List C8FourCoverEquation :=
  [.delta, .product ⟨4⟩ ⟨58⟩, .product ⟨4⟩ ⟨64⟩, .product ⟨11⟩ ⟨11⟩, .product ⟨11⟩ ⟨33⟩, .product ⟨11⟩ ⟨58⟩]

theorem c8FourCoverObstruction17_valid : c8FourCoverContradiction c8FourCoverObstruction17 := by
  decide +kernel

@[expose] def c8FourCoverObstruction18 : List C8FourCoverEquation :=
  [.delta, .product ⟨14⟩ ⟨16⟩, .product ⟨14⟩ ⟨64⟩, .product ⟨16⟩ ⟨30⟩]

theorem c8FourCoverObstruction18_valid : c8FourCoverContradiction c8FourCoverObstruction18 := by
  decide +kernel

@[expose] def c8FourCoverObstruction19 : List C8FourCoverEquation :=
  [.delta, .product ⟨4⟩ ⟨26⟩, .product ⟨4⟩ ⟨64⟩, .product ⟨26⟩ ⟨30⟩, .product ⟨26⟩ ⟨49⟩, .product ⟨26⟩ ⟨63⟩]

theorem c8FourCoverObstruction19_valid : c8FourCoverContradiction c8FourCoverObstruction19 := by
  decide +kernel

end CFSG.LargeEvenClassification.Helpers
