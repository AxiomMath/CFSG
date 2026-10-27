module


public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LinearAlgebra.CoprimeActions.BinaryInvariantHyperplanes

theorem not_normalized {J : Type*} [Group J] [Finite J] (X A K : Subgroup J)
    (hX : CFSG.Open.IsElemAbelian 2 X)
    (hAX : A ≤ Subgroup.normalizer (X : Set J))
    (hgen : ⁅X, A⁆ = X) (hKX : K ≤ X) (hidx : K.relIndex X = 2) :
    ¬ (A ≤ Subgroup.normalizer (K : Set J)) := by
  intro hAK
  obtain ⟨c, hcX, hc⟩ := Subgroup.relIndex_eq_two_iff.mp hidx
  have key : ∀ x ∈ X, ∀ y ∈ X, x ∉ K → y ∉ K → x * y⁻¹ ∈ K := by
    intro x hx y hy hxK hyK
    have h1 : x * c ∈ K := by
      have := hc x hx
      by_contra h
      exact this.elim (fun h' => h h'.1) (fun h' => hxK h'.1)
    have h2 : y * c ∈ K := by
      have := hc y hy
      by_contra h
      exact this.elim (fun h' => h h'.1) (fun h' => hyK h'.1)
    have := K.mul_mem h1 (K.inv_mem h2)
    simpa [mul_assoc] using this
  have hle : ⁅X, A⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro x hx a ha
    have hxa : a * x * a⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hAX ha) x).mp hx
    rw [commutatorElement_def]
    have hcomm : x * a * x⁻¹ * a⁻¹ = x * (a * x * a⁻¹)⁻¹ := by
      simp [mul_assoc]
    rw [hcomm]
    by_cases hxK : x ∈ K
    · have : a * x * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hAK ha) x).mp hxK
      exact K.mul_mem hxK (K.inv_mem this)
    · have : a * x * a⁻¹ ∉ K := fun h =>
        hxK ((Subgroup.mem_normalizer_iff.mp (hAK ha) x).mpr h)
      exact key x hx _ hxa hxK this
  rw [hgen] at hle
  have h1 : K.relIndex X = 1 := Subgroup.relIndex_eq_one.mpr hle
  omega

end CFSG.LinearAlgebra.CoprimeActions.BinaryInvariantHyperplanes
