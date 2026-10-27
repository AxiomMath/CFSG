module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.BenderInterfaces
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerParab1

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
open scoped MatrixGroups commutatorElement

universe v

structure IsCompListIn {A : Type*} [Group A] (H : Subgroup A) (r : ℕ) (L : Fin r → Subgroup A) :
    Prop where
  injective : Function.Injective L
  isComp : ∀ i, IsComponentIn (L i) H
  complete : ∀ D : Subgroup A, IsComponentIn D H → ∃ i, L i = D

section Output

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

structure EvenSL2LayerOutput (H T : Subgroup (V ≃ₗ[ZMod 2] V)) (r : ℕ) (F : Type) [Field F]
    (Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)) : Prop where
  nonempty_offenders : ∃ A, IsMinOffender H A
  J_normal : ((offenderJ H).subgroupOf H).Normal
  H_eq_JT : offenderJ H ⊔ T = H
  H_eq_KT : oddGen H ⊔ T = H
  K_le_J : oddGen H ≤ offenderJ H
  r_pos : 1 ≤ r
  r_pow : ∃ k : ℕ, r = 2 ^ k
  transitive : ∀ i j, ∃ t ∈ T, (Lc i).map (MulAut.conj t).toMonoidHom = Lc j
  center_trivial : ∀ i, Subgroup.center ↥(Lc i) = ⊥
  iso : ∀ i, Nonempty (↥(Lc i) ≃* SL(2, F))
  K_eq : oddGen H = ⨆ i, Lc i
  commute : ∀ i j, i ≠ j → ⁅Lc i, Lc j⁆ = ⊥
  direct : ∀ i, Lc i ⊓ (⨆ j, ⨆ (_ : j ≠ i), Lc j) = ⊥
  rad_trivial : CFSG.solvableRadical ↥H = ⊥
  centralizer_trivial : H ⊓ Subgroup.centralizer (oddGen H : Set (V ≃ₗ[ZMod 2] V)) = ⊥
  irr : ∀ i, IsIrrQuot (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (Lc i) (commGL (Lc i) ⊤)
  faithful_W : ∀ i, ∀ x ∈ Lc i,
    (∀ v ∈ commGL (Lc i) ⊤, x v - v ∈ fixGL (Lc i)) → x = 1
  others_fix : ∀ i j, j ≠ i → ∀ x ∈ Lc j, ∀ v ∈ commGL (Lc i) ⊤, x v = v
  moving : ∀ i, ∃ A, IsMinOffender H A ∧ ⁅Lc i, A⁆ = Lc i
  offender : ∀ A, IsMinOffender H A →
    (∀ i, A ≤ Subgroup.normalizer (Lc i : Set (V ≃ₗ[ZMod 2] V))) ∧
    ∃ i, ⁅Lc i, A⁆ ≠ ⊥ ∧ (∀ j, ⁅Lc j, A⁆ ≠ ⊥ → j = i) ∧ ⁅Lc i, A⁆ = Lc i ∧
      commGL (Lc i) ⊤ ⊔ fixGL A = ⊤ ∧ commGL (Lc i ⊔ A) ⊤ = commGL (Lc i) ⊤ ∧
      (∀ a ∈ A, (∀ v ∈ commGL (Lc i) ⊤, a v - v ∈ fixGL (Lc i)) → a = 1) ∧
      commGL (Lc i) ⊤ ⊓ fixGL (Lc i) ≤ fixGL (Lc i ⊔ A) ∧
      weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A = Nat.card V ∧
      ∀ j, j ≠ i → ∀ x ∈ Lc j, ∀ a ∈ A, x * a = a * x
  upper_bound : ∀ E : Subgroup (V ≃ₗ[ZMod 2] V), E ≤ H → E ≠ ⊥ → CFSG.IsElementaryAbelian 2 E →
    weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) E ≤ Nat.card V

end Output

end CFSG.QuasithinUnique.Setup.Lift
