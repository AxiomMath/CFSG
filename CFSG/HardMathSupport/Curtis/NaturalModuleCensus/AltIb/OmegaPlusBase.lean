module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.Sp

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits CFSG.Open
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.SpCell
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

variable {n : ℕ} {F : Type} [Field F]

abbrev Om (n : ℕ) (F : Type) [Field F] : Subgroup (GL (Fin n ⊕ Fin n) F) :=
  StatedOmega (StatedQuadPlus n F)

theorem om_preserves {A : GL (Fin n ⊕ Fin n) F} (hA : A ∈ Om n F) (v : Fin n ⊕ Fin n → F) :
    StatedQuadPlus n F ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v) =
      StatedQuadPlus n F v :=
  orthGroup_preserves _ (statedOmega_le_orthGroup _ hA) v

theorem mem_statedSp_of_preserves [CharP F 2] {A : GL (Fin n ⊕ Fin n) F}
    (hA : ∀ v, StatedQuadPlus n F ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v) =
      StatedQuadPlus n F v) : A ∈ StatedSp n F := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
  set M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    with hM
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hpol : ∀ u v, quadPlusPolar n F (M *ᵥ u) (M *ᵥ v) = quadPlusPolar n F u v := fun u v =>
    (quadPlusForm n F).polar_map_of_Q (g := Matrix.toLin' M) (fun w => hA w) u v
  have hsymp : ∀ u v, CFSG.LocalAnalysis.ComponentInitial.pairedSympForm F n u v =
      quadPlusPolar n F u v := by
    intro u v
    rw [CFSG.LocalAnalysis.ComponentInitial.pairedSympForm_apply]
    simp only [quadPlusPolar, dotProduct, Function.comp_apply, Finset.sum_add_distrib]
    have hc : ∑ x, v (Sum.inl x) * u (Sum.inr x) = ∑ x, u (Sum.inr x) * v (Sum.inl x) :=
      Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [hc, sub_eq_add_neg, CharTwo.neg_eq]
  have hpres : ∀ u v, CFSG.LocalAnalysis.ComponentInitial.pairedSympForm F n (M *ᵥ u) (M *ᵥ v) =
      CFSG.LocalAnalysis.ComponentInitial.pairedSympForm F n u v := fun u v => by
    rw [hsymp, hsymp]
    exact hpol u v
  apply Matrix.toBilin'.injective
  refine LinearMap.ext fun u => LinearMap.ext fun v => ?_
  have h1 := hpres u v
  simp only [CFSG.LocalAnalysis.ComponentInitial.pairedSympForm] at h1
  simp only [Matrix.toBilin'_apply', Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ] at h1 ⊢
  rw [← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, ← Matrix.mul_assoc] at h1
  exact h1

theorem om_le_sp [CharP F 2] : Om n F ≤ StatedSp n F := fun _ hA =>
  mem_statedSp_of_preserves (om_preserves hA)

@[expose] def omSp [CharP F 2] : ↥(Om n F) →* ↥(StatedSp n F) :=
  Subgroup.inclusion om_le_sp

theorem omSp_injective [CharP F 2] : Function.Injective (omSp (n := n) (F := F)) :=
  Subgroup.inclusion_injective _

@[expose] def JO (n : ℕ) (F : Type) [Field F] [CharP F 2] (S : Finset ℕ) : Subgroup ↥(Om n F) :=
  (Jfl n F S).comap omSp

theorem mem_JO [CharP F 2] {S : Finset ℕ} {g : ↥(Om n F)} :
    g ∈ JO n F S ↔ omSp g ∈ Jfl n F S := Iff.rfl

@[expose] def jToJfl [CharP F 2] (S : Finset ℕ) : ↥(JO n F S) →* ↥(Jfl n F S) :=
  ((omSp (n := n) (F := F)).comp (JO n F S).subtype).codRestrict (Jfl n F S) (fun g => g.2)

theorem jToJfl_injective [CharP F 2] (S : Finset ℕ) :
    Function.Injective (jToJfl (n := n) (F := F) S) := fun _ _ h =>
  Subtype.ext (omSp_injective (congrArg Subtype.val h))

@[expose] def _root_.CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.FlagBlocks.comap
    {p : ℕ} {J : Type*} [Group J] (B : FlagBlocks p J) {J' : Type*} [Group J'] (ψ : J' →* J)
    (hψ : Function.Injective ψ) : FlagBlocks p J' where
  ι := B.ι
  H := B.H
  grp := B.grp
  ρ := fun i => (B.ρ i).comp ψ
  inj_of_pow := fun e he hall => hψ (by
    rw [map_one]
    exact B.inj_of_pow (ψ e) (by rw [← map_pow, he, map_one]) hall)

@[expose] noncomputable def blocksD [Finite F] [CharP F 2] {S : Finset ℕ}
    (hS : ∀ i ∈ S, 1 ≤ i ∧ i ≤ n) {p : ℕ} (hp0 : (p : F) ≠ 0) : FlagBlocks p ↥(JO n F S) :=
  (spFlagBlocks hS hp0).comap (jToJfl S) (jToJfl_injective S)

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell
