module

public import CFSG.Blueprint.ChevalleyStrings
public import CFSG.Blueprint.ChevalleyParameterAddition
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.Blueprint.Chevalley

theorem upTransport (τ : Tag) : UpTransport τ := by
  intro i α hα hne hne' k hk
  obtain ⟨-, -, htr⟩ := root_string_transport hα i hne hne'
  obtain ⟨h1, h2, h3, h4, h5⟩ := htr k (by omega) (by exact_mod_cast hk)
  exact ⟨h1, h2, h3, by omega, by omega⟩

theorem downTransport (τ : Tag) : DownTransport τ := by
  intro i α hα hne hne' k hk
  obtain ⟨-, -, htr⟩ := root_string_transport hα i hne hne'
  have hkk : α - (k : ℤ) • Pi.single i 1 = α + (-(k : ℤ)) • Pi.single i 1 := by
    rw [neg_smul, sub_eq_add_neg]
  obtain ⟨h1, h2, h3, h4, h5⟩ := htr (-(k : ℤ)) (by omega) (by omega)
  rw [hkk]
  exact ⟨h1, h2, h3, by omega, by omega⟩

theorem simple_root_parameter_addition_of_tag (τ : Tag) (R : Type*) [CommRing R]
    (i : Fin τ.rank) :
    (∀ c d : R, xOp τ R i c * xOp τ R i d = xOp τ R i (c + d)) ∧
      (∀ c d : R, yOp τ R i c * yOp τ R i d = yOp τ R i (c + d)) ∧
      xOp τ R i 0 = 1 ∧ yOp τ R i 0 = 1 ∧
      (∀ c : R, xOp τ R i c * xOp τ R i (-c) = 1 ∧ xOp τ R i (-c) * xOp τ R i c = 1) ∧
      (∀ c : R, yOp τ R i c * yOp τ R i (-c) = 1 ∧ yOp τ R i (-c) * yOp τ R i c = 1) ∧
      Function.Injective (xOp τ R i) ∧ Function.Injective (yOp τ R i) :=
  simple_root_parameter_addition τ R (upTransport τ) (downTransport τ) i

end CFSG.Blueprint.Chevalley
