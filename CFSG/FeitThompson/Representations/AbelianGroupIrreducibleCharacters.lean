module

public import CFSG.FeitThompson.Representations.CharacterMultiplicitiesIrreducibility
import CFSG.FeitThompson.Representations.RegularCharacterDegreeSquareSum
import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
import CFSG.FeitThompson.Representations.TensorAndDualCharacters
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module

namespace Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

theorem isIrreducible_of_finrank_eq_one (ρ : Representation k G V) (h : finrank k V = 1) :
    ρ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  have h1 : finrank k ρ.asModule = 1 := h
  have h2 := is_simple_module_of_finrank_eq_one (K := k) (A := MonoidAlgebra k G) h1
  exact { exists_pair_ne := h2.exists_pair_ne, eq_bot_or_eq_top := h2.eq_bot_or_eq_top }

variable {A : Type*} [CommGroup A]

theorem existsUnique_smul_of_commGroup [IsAlgClosed k] (ρ : Representation k A V)
    [ρ.IsIrreducible] [FiniteDimensional k V] (a : A) : ∃! c : k, ∀ v : V, ρ a v = c • v := by
  refine existsUnique_smul_of_isIrreducible (ρ := ρ) ⟨ρ a, fun g => ?_⟩
  ext v
  simp only [LinearMap.comp_apply, ← Module.End.mul_apply, ← ρ.map_mul, mul_comm a g]

noncomputable def ofLinearChar (χ : A →* kˣ) : Representation k A k :=
  Representation.twist (Representation.trivial k A k) χ

@[simp]
theorem ofLinearChar_apply_apply (χ : A →* kˣ) (g : A) (c : k) :
    ofLinearChar χ g c = (χ g : k) * c := by
  rw [ofLinearChar, twist_apply_apply]
  simp [Representation.trivial, smul_eq_mul]

@[simp]
theorem character_ofLinearChar (χ : A →* kˣ) (g : A) :
    (ofLinearChar (k := k) χ).character g = (χ g : k) := by
  rw [ofLinearChar, character_twist]
  simp [Representation.character, Representation.trivial]

theorem isIrreducible_ofLinearChar (χ : A →* kˣ) : (ofLinearChar (k := k) χ).IsIrreducible :=
  isIrreducible_of_finrank_eq_one _ (finrank_self k)

end Representation

section Abelian

variable {A : Type*} [CommGroup A]

def linearCharFun (ψ : A →* ℂˣ) : A → ℂ := fun g => (ψ g : ℂ)

@[simp]
theorem linearCharFun_apply (ψ : A →* ℂˣ) (g : A) : linearCharFun ψ g = (ψ g : ℂ) := (rfl)

theorem linearCharFun_injective : Function.Injective (linearCharFun (A := A)) :=
  fun _ _ h => MonoidHom.ext fun g => Units.ext (congrFun h g)

theorem linearCharFun_mem_Irr (ψ : A →* ℂˣ) : linearCharFun ψ ∈ Irr A := by
  have h := character_mem_Irr_of_isIrreducible (Representation.ofLinearChar (k := ℂ) ψ)
    (Representation.isIrreducible_ofLinearChar ψ)
  have he : (Representation.ofLinearChar (k := ℂ) ψ).character = linearCharFun ψ :=
    funext fun g => Representation.character_ofLinearChar ψ g
  rwa [he] at h

theorem finrank_eq_one_of_isIrreducible {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ A V) [ρ.IsIrreducible] [FiniteDimensional ℂ V] : finrank ℂ V = 1 :=
  Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ

theorem exists_linearCharFun_eq_of_mem_Irr {χ : A → ℂ} (hχ : χ ∈ Irr A) :
    ∃ ψ : A →* ℂˣ, linearCharFun ψ = χ := by
  obtain ⟨V, hirr, rfl⟩ := mem_Irr.1 hχ
  have hi : Representation.IsIrreducible V.ρ := hirr
  have h1 : finrank ℂ V.V = 1 := finrank_eq_one_of_isIrreducible V.ρ
  obtain ⟨ψ, hψ⟩ := Representation.exists_monoidHom_units_of_finrank_eq_one V.ρ h1
  refine ⟨ψ, funext fun g => ?_⟩
  have hg : V.ρ g = (ψ g : ℂ) • LinearMap.id := by ext v; simpa using hψ g v
  rw [linearCharFun, FDRep.character, hg]
  simp [h1]

theorem Irr.apply_one_eq_one {χ : A → ℂ} (hχ : χ ∈ Irr A) : χ 1 = 1 := by
  obtain ⟨ψ, rfl⟩ := exists_linearCharFun_eq_of_mem_Irr hχ
  simp

theorem Irr_eq_range_linearCharFun : Irr A = Set.range (linearCharFun (A := A)) :=
  Set.eq_of_subset_of_subset (fun _ h => (exists_linearCharFun_eq_of_mem_Irr h).imp fun _ h => h)
    (fun _ ⟨_, hψ⟩ => hψ ▸ linearCharFun_mem_Irr _)

noncomputable def irrEquivMonoidHom : (A →* ℂˣ) ≃ Irr A :=
  Equiv.ofBijective (fun ψ => ⟨linearCharFun ψ, linearCharFun_mem_Irr ψ⟩)
    ⟨fun _ _ h => linearCharFun_injective (congrArg Subtype.val h), fun χ => by
      obtain ⟨ψ, hψ⟩ := exists_linearCharFun_eq_of_mem_Irr χ.2
      exact ⟨ψ, Subtype.ext hψ⟩⟩

@[simp]
theorem irrEquivMonoidHom_apply_apply (ψ : A →* ℂˣ) (g : A) :
    ((irrEquivMonoidHom ψ : A → ℂ)) g = (ψ g : ℂ) := (rfl)

theorem card_irrFinset [Finite A] : (irrFinset A).card = Nat.card A := by
  have h := sum_character_one_sq' (G := A)
  rw [Finset.sum_congr rfl (fun χ hχ => by
    rw [Irr.apply_one_eq_one (mem_irrFinset.1 hχ), one_pow])] at h
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact Nat.cast_injective (R := ℂ) h

theorem card_Irr_eq_card [Finite A] : Nat.card (Irr A) = Nat.card A := by
  rw [← card_irrFinset (A := A), ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Set.equivOfEq (by ext χ; simp))

theorem card_Irr_eq_card_monoidHom [Finite A] :
    Nat.card (Irr A) = Nat.card (A →* ℂˣ) ∧ Nat.card (A →* ℂˣ) = Nat.card A :=
  ⟨card_Irr_eq_card.trans (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity A ℂ).symm,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity A ℂ⟩

end Abelian

end CFSG.FeitThompson
