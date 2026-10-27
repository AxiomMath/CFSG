module
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.Representation

open Module Polynomial

variable {k A V : Type*} [Field k] [CommGroup A] [AddCommGroup V] [Module k V]
  (ρ : Representation k A V)

def characterSpace (χ : A →* kˣ) : Submodule k V :=
  ⨅ a : A, Module.End.eigenspace (ρ a) (χ a : k)

lemma characterSpace_eq_iInf (χ : A →* kˣ) :
    characterSpace ρ χ = ⨅ a : A, Module.End.eigenspace (ρ a) (χ a : k) := (rfl)

@[simp]
lemma mem_characterSpace_iff {χ : A →* kˣ} {v : V} :
    v ∈ characterSpace ρ χ ↔ ∀ a : A, ρ a v = (χ a : k) • v := by
  simp only [characterSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

lemma commute_apply (a b : A) : Commute (ρ a : Module.End k V) (ρ b) := by
  change ρ a * ρ b = ρ b * ρ a
  rw [← map_mul, ← map_mul, mul_comm]

lemma iSupIndep_iInf_eigenspace :
    iSupIndep fun c : A → k ↦ ⨅ a : A, Module.End.eigenspace (ρ a) (c a) := by
  refine (Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (fun a : A ↦ (ρ a : Module.End k V)) ?_).mono ?_
  · intro i j φ
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (commute_apply ρ j i) φ
  · intro c
    exact iInf_mono fun _ ↦ Module.End.eigenspace_le_maxGenEigenspace

lemma iSupIndep_characterSpace : iSupIndep (characterSpace ρ) := by
  have hinj : Function.Injective fun (χ : A →* kˣ) (a : A) ↦ (χ a : k) := by
    intro χ ψ h
    ext a
    exact congrFun h a
  exact (iSupIndep_iInf_eigenspace ρ).comp hinj

lemma disjoint_characterSpace {χ ψ : A →* kˣ} (h : χ ≠ ψ) :
    Disjoint (characterSpace ρ χ) (characterSpace ρ ψ) :=
  (iSupIndep_characterSpace ρ).pairwiseDisjoint h

lemma isSemisimple_apply [Finite A] (hA : (Nat.card A : k) ≠ 0) (a : A) :
    Module.End.IsSemisimple (ρ a : Module.End k V) := by
  have hord : (orderOf a : k) ≠ 0 := by
    obtain ⟨m, hm⟩ := orderOf_dvd_natCard (G := A) a
    intro h
    rw [hm, Nat.cast_mul, h, zero_mul] at hA
    exact hA rfl
  have hsq : Squarefree ((X : k[X]) ^ orderOf a - C 1) :=
    (Polynomial.separable_X_pow_sub_C (1 : k) hord one_ne_zero).squarefree
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq ?_
  have h1 : (ρ a : Module.End k V) ^ orderOf a = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  simp [h1]

lemma exists_character_of_iInf_eigenspace_ne_bot {c : A → k}
    (h : (⨅ a : A, Module.End.eigenspace (ρ a) (c a)) ≠ ⊥) :
    ∃ χ : A →* kˣ, ∀ a, (χ a : k) = c a := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hv
  have hne : ∀ a, c a ≠ 0 := by
    intro a ha
    refine hv0 ?_
    have hz : ρ a v = 0 := by rw [hv a, ha, zero_smul]
    have hv' := congrArg (ρ a⁻¹ : Module.End k V) hz
    rwa [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at hv'
  refine ⟨{ toFun := fun a ↦ Units.mk0 (c a) (hne a), map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · have h1 : c 1 • v = (1 : k) • v := by
      rw [← hv 1, map_one, Module.End.one_apply, one_smul]
    exact Units.ext (by simpa using smul_left_injective k hv0 h1)
  · intro a b
    have h1 : ρ (a * b) v = (c a * c b) • v := by
      rw [map_mul, Module.End.mul_apply, hv b, map_smul, hv a, smul_smul, mul_comm]
    rw [hv (a * b)] at h1
    exact Units.ext (by simpa using smul_left_injective k hv0 h1)
  · intro a; rfl

lemma characterSpace_eq_of_coe_eq {χ : A →* kˣ} {c : A → k} (h : ∀ a, (χ a : k) = c a) :
    characterSpace ρ χ = ⨅ a : A, Module.End.eigenspace (ρ a) (c a) := by
  simp only [characterSpace, h]

lemma iSup_characterSpace_eq_top [IsAlgClosed k] [FiniteDimensional k V] [Finite A]
    (hA : (Nat.card A : k) ≠ 0) : ⨆ χ : A →* kˣ, characterSpace ρ χ = ⊤ := by
  have htop : ⨆ c : A → k, ⨅ a : A, Module.End.eigenspace (ρ a) (c a) = ⊤ := by
    have key :=
      Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
        (fun a : A ↦ (ρ a : Module.End k V)) (fun a b _ ↦ commute_apply ρ a b)
        (fun _ ↦ Module.End.iSup_maxGenEigenspace_eq_top _)
    rw [← key]
    refine iSup_congr fun c ↦ iInf_congr fun a ↦ ?_
    exact ((isSemisimple_apply ρ hA a).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace _).symm
  refine top_unique ?_
  rw [← htop]
  refine iSup_le fun c ↦ ?_
  by_cases h : (⨅ a : A, Module.End.eigenspace (ρ a) (c a)) = ⊥
  · rw [h]; exact bot_le
  · obtain ⟨χ, hχ⟩ := exists_character_of_iInf_eigenspace_ne_bot ρ h
    exact le_iSup_of_le χ (characterSpace_eq_of_coe_eq ρ hχ).ge

lemma iSup_characterSpace_ne_bot_eq_top [IsAlgClosed k] [FiniteDimensional k V] [Finite A]
    (hA : (Nat.card A : k) ≠ 0) :
    ⨆ χ : {χ : A →* kˣ // characterSpace ρ χ ≠ ⊥}, characterSpace ρ χ.1 = ⊤ := by
  rw [← iSup_characterSpace_eq_top ρ hA]
  refine le_antisymm (iSup_le fun χ ↦ le_iSup _ χ.1) (iSup_le fun χ ↦ ?_)
  by_cases h : characterSpace ρ χ = ⊥
  · rw [h]; exact bot_le
  · exact le_iSup_of_le ⟨χ, h⟩ le_rfl

theorem directSum_characterSpace_ne_bot [DecidableEq (A →* kˣ)] [IsAlgClosed k]
    [FiniteDimensional k V] [Finite A] (hA : (Nat.card A : k) ≠ 0) :
    DirectSum.IsInternal fun χ : {χ : A →* kˣ // characterSpace ρ χ ≠ ⊥} ↦
      characterSpace ρ χ.1 :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨(iSupIndep_characterSpace ρ).comp Subtype.val_injective,
      iSup_characterSpace_ne_bot_eq_top ρ hA⟩

theorem directSum_characterSpace [DecidableEq (A →* kˣ)] [IsAlgClosed k] [FiniteDimensional k V]
    [Finite A] (hA : (Nat.card A : k) ≠ 0) : DirectSum.IsInternal (characterSpace ρ) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨iSupIndep_characterSpace ρ, iSup_characterSpace_eq_top ρ hA⟩

theorem linearIndependent_of_mem_characterSpace {ι : Type*} {χ : ι → (A →* kˣ)}
    (hχ : Function.Injective χ) {v : ι → V} (hv : ∀ i, v i ∈ characterSpace ρ (χ i))
    (hv0 : ∀ i, v i ≠ 0) : LinearIndependent k v :=
  iSupIndep.linearIndependent _ ((iSupIndep_characterSpace ρ).comp hχ) hv hv0

end CFSG.FeitThompson.Representation
