module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenCase
public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenFinal
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentInitial.KProperLocal
public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenPerm
public import CFSG.LocalAnalysis.OddStandard.AltStdSecStd
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

section Stage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {z : G}

@[expose] def RootDichotomy (e : L ≃* alternatingGroup (Fin n)) (z : G) : Prop :=
  ∀ (S S' : Finset (Fin n)), S.card = 3 → S'.card = 3 →
    ∀ (ψ : ↥(corr (X := G) e (altSub Sᶜ)) →* G) (ψ' : ↥(corr (X := G) e (altSub S'ᶜ)) →* G),
      IsRootLift e z S ψ → IsRootLift e z S' ψ' →
      (∀ (x : G) (hx : x ∈ corr (X := G) e (altSub Sᶜ))
          (hx' : x ∈ corr (X := G) e (altSub S'ᶜ)), ψ ⟨x, hx⟩ = ψ' ⟨x, hx'⟩) ∨
      (∀ (x : G) (hx : x ∈ corr (X := G) e (altSub Sᶜ))
          (hx' : x ∈ corr (X := G) e (altSub S'ᶜ)), ψ ⟨x, hx⟩ = z * ψ' ⟨x, hx'⟩ * z⁻¹)

end Stage

section CorrIn

variable {X : Type} [Group X] {A : Subgroup X} {n : ℕ} (e : A ≃* alternatingGroup (Fin n))

@[expose] def corrIn {T : Subgroup (Equiv.Perm (Fin n))} (hT : T ≤ alternatingGroup (Fin n)) :
    ↥T →* ↥(corr (X := X) e T) where
  toFun x := ⟨((e.symm ⟨x, hT x.2⟩ : A) : X), mem_corr_of_mem (by simp)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by
    apply Subtype.ext
    have : (⟨((a * b : ↥T) : Equiv.Perm (Fin n)), hT (a * b).2⟩ : alternatingGroup (Fin n)) =
        ⟨a, hT a.2⟩ * ⟨b, hT b.2⟩ := rfl
    show ((e.symm ⟨((a * b : ↥T) : Equiv.Perm (Fin n)), hT (a * b).2⟩ : A) : X) = _
    rw [this, map_mul]
    rfl

theorem corrIn_injective {T : Subgroup (Equiv.Perm (Fin n))} (hT : T ≤ alternatingGroup (Fin n)) :
    Function.Injective (corrIn (X := X) e hT) := by
  intro a b hab
  have h0 : ((corrIn (X := X) e hT a : ↥(corr (X := X) e T)) : X) =
      ((corrIn (X := X) e hT b : ↥(corr (X := X) e T)) : X) := congrArg Subtype.val hab
  have h1 : ((e.symm ⟨a, hT a.2⟩ : A) : X) = ((e.symm ⟨b, hT b.2⟩ : A) : X) := h0
  have h2 : e.symm ⟨a, hT a.2⟩ = e.symm ⟨b, hT b.2⟩ := Subtype.ext h1
  have h3 := e.symm.injective h2
  exact Subtype.ext (congrArg (fun w : alternatingGroup (Fin n) => (w : Equiv.Perm (Fin n))) h3)

end CorrIn

section Stage2

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {z : G}

theorem stageM_of_dichotomy (h : ExactShape z L n) (e : L ≃* alternatingGroup (Fin n))
    (hn : 11 ≤ n) (hIII : ∀ S : Finset (Fin n), S.card = 3 → CaseIIIAt e z S)
    (hdich : RootDichotomy e z) : ∃ H : Subgroup G, WreathPair L z n H := by
  have hex : ∀ S : Finset (Fin n), S.card = 3 →
      ∃ ψ : ↥(corr (X := G) e (altSub Sᶜ)) →* G, IsRootLift e z S ψ :=
    fun S hS => exists_rootLift h e (by omega) hS (hIII S hS)
  choose ψ hψ using hex
  let φ : RootFamily G n := fun S hS =>
    (ψ S hS).comp (corrIn (X := G) e (altSub_le_alternatingGroup Sᶜ))
  have ht2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.order, pow_two] at this
  have hpre : φ.IsPreWLift z (embAlt e) := by
    refine ⟨ht2, ?_, ?_, ?_⟩
    · intro S hS x
      exact (hψ S hS).diag (corrIn (X := G) e (altSub_le_alternatingGroup Sᶜ) x)
    · intro S hS x y
      exact (hψ S hS).comm _ _
    · intro S hS x hx
      have h1 := (hψ S hS).rigid _ hx
      exact corrIn_injective (X := G) e (altSub_le_alternatingGroup Sᶜ)
        (h1.trans (map_one _).symm)
  have hd : ∀ (S S' : Finset (Fin n)) (hS : S.card = 3) (hS' : S'.card = 3),
      RFSame φ S S' hS hS' ∨ RFOpp φ z S S' hS hS' := by
    intro S S' hS hS'
    rcases hdich S S' hS hS' (ψ S hS) (ψ S' hS') (hψ S hS) (hψ S' hS') with h1 | h1
    · left
      intro x hx hx'
      exact h1 _ (corrIn (X := G) e (altSub_le_alternatingGroup Sᶜ) ⟨x, hx⟩).2
        (corrIn (X := G) e (altSub_le_alternatingGroup S'ᶜ) ⟨x, hx'⟩).2
    · right
      intro x hx hx'
      exact h1 _ (corrIn (X := G) e (altSub_le_alternatingGroup Sᶜ) ⟨x, hx⟩).2
        (corrIn (X := G) e (altSub_le_alternatingGroup S'ᶜ) ⟨x, hx'⟩).2
  exact exists_wreathPair_of_dichotomy hn e hpre hd

end Stage2

end CFSG.OddStandard.AltStdSec
