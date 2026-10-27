module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KFixIso
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AInnDiag

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

section KLevel

variable {G : Type} [Group G] [Finite G]

open Lemma510Ns in
theorem kfix_klevel_layer {K : Subgroup G} {g : G}
    (hx : g ∈ Subgroup.normalizer (K : Set G)) (hg3 : g ^ 3 = 1)
    {L : Subgroup (barOf 3 K)}
    (hcomp : ∀ J : Subgroup (barOf 3 K),
      GLAPComponent 3 (fixSub (barAut 3 K ⟨g, hx⟩)) J ↔ J = L) :
    ∃ J : Subgroup G, GLAPComponent 3 (K ⊓ Cs g) J ∧ CLay K g = J ∧
      Nonempty (barOf 3 J ≃* barOf 3 L) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  set A : Subgroup ↥K := (K ⊓ Cs g).subgroupOf K with hA
  set ψ : ↥K →* barOf 3 K := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) with hψ
  have hker : Nat.Coprime 3 (Nat.card ↥(A ⊓ ψ.ker)) := coprime_ker_mk K A
  have hLcomp : GLAPComponent 3 (fixSub (barAut 3 K ⟨g, hx⟩)) L := (hcomp L).2 rfl
  obtain ⟨J₁, hJ₁, hJ₁m⟩ := exists_comp_of_fixSub hx hg3 hLcomp
  have hJc : GLAPComponent 3 (K ⊓ Cs g) (J₁.map K.subtype) :=
    comp_map_subgroupOf (inf_le_left : K ⊓ Cs g ≤ K) hJ₁
  have huniq : ∀ J' : Subgroup G, GLAPComponent 3 (K ⊓ Cs g) J' → J' = J₁.map K.subtype := by
    intro J' hJ'
    obtain ⟨J₂, hJ₂, rfl⟩ := exists_comp_subgroupOf (inf_le_left : K ⊓ Cs g ≤ K) hJ'
    have himg : J₂.map ψ = J₁.map ψ := by
      have h2 := (hcomp _).1 (comp_map_fixSub hx hg3 hJ₂)
      rw [hJ₁m]; exact h2
    have hb₁ := lcEquiv_barX hp ψ A hker hJ₁.1
    have hb₂ := lcEquiv_barX hp ψ A hker hJ₂.1
    have hbar : barX 3 A J₁ = barX 3 A J₂ := by
      apply Subgroup.map_injective (lcEquiv hp ψ A hker).injective
      show (barX 3 A J₁).map (lcMonoidHom hp ψ A hker) =
        (barX 3 A J₂).map (lcMonoidHom hp ψ A hker)
      rw [hb₁, hb₂, himg]
    rw [glaPComponent_uniqueAux hJ₁ hJ₂ hbar]
  refine ⟨J₁.map K.subtype, hJc, ?_, ?_⟩
  · exact le_antisymm (sSup_le fun J' hJ' => (huniq J' hJ').le) (le_sSup hJc)
  · have hLeq : J₁.map ψ = L := hJ₁m
    subst hLeq
    exact ⟨liftEquiv J₁⟩

open Lemma510Ns in
theorem kfix_klevel_layer_bot {K : Subgroup G} {g : G}
    (hx : g ∈ Subgroup.normalizer (K : Set G)) (hg3 : g ^ 3 = 1)
    (h : ∀ J : Subgroup (barOf 3 K), ¬ GLAPComponent 3 (fixSub (barAut 3 K ⟨g, hx⟩)) J) :
    CLay K g = ⊥ := by
  refine le_bot_iff.1 (sSup_le fun J hJ => ?_)
  obtain ⟨J₁, hJ₁, -⟩ := exists_comp_subgroupOf (inf_le_left : K ⊓ Cs g ≤ K) hJ
  exact absurd (comp_map_fixSub hx hg3 hJ₁) (h _)

end KLevel

theorem kfix_isPSLn_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) {n r : ℕ}
    (h : IsPSLn n r B) : IsPSLn n r A :=
  p9b_isPSLn_congr e.symm h

theorem kfix_isPSUn_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) {n r : ℕ}
    (h : IsPSUn n r B) : IsPSUn n r A :=
  p9b_isPSUn_congr e.symm h

@[expose] def InputL3fixCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (g : G) (r : ℕ),
    CFSG.Open.IsQuasisimple (barOf 3 K) → IsL3Raw r (barOf 3 K) → g ^ 3 = 1 →
    InducesFieldAut 3 K g → ¬ TrivOn K g →
      ∃ r0 : ℕ, r = r0 ^ 3 ∧
        ((GLAPComponent 3 (K ⊓ Cs g) (CLay K g) ∧ IsL3Raw r0 (barOf 3 (CLay K g)) ∧
          (IsPSLn 3 r (barOf 3 K) → IsPSLn 3 r0 (barOf 3 (CLay K g))) ∧
          (IsPSUn 3 r (barOf 3 K) → IsPSUn 3 r0 (barOf 3 (CLay K g)))) ∨
        (CLay K g = ⊥ ∧ r = 8 ∧ IsPSUn 3 8 (barOf 3 K)))

theorem inputL3fixCore_holds (hiso : InputL3iso) : InputL3fixCore := by
  intro G _ _ K g r hq hr hg3 hfld hT
  obtain ⟨hx, hfa⟩ := hfld
  have hα3 := Lemma510Ns.barAut_pow_three hx hg3
  have hα1 : barAut 3 K ⟨g, hx⟩ ≠ 1 := fun h => hT ⟨hx, h⟩
  have hcore : GLAPPrimeCore 3 (barOf 3 K) = ⊥ := glaPPrimeCore_quotient_eq_bot Nat.prime_three
  obtain ⟨r0, hr0, h⟩ := kfix_yfix hq hcore hiso hr hα3 hα1 hfa
  refine ⟨r0, hr0, ?_⟩
  rcases h with ⟨L, hcomp, hl, hu⟩ | ⟨hno, hr8, hP8⟩
  · obtain ⟨J, hJc, hCL, ⟨eJ⟩⟩ := kfix_klevel_layer hx hg3 hcomp
    subst hCL
    refine Or.inl ⟨hJc, ?_, fun h => kfix_isPSLn_of_mulEquiv eJ (hl h),
      fun h => kfix_isPSUn_of_mulEquiv eJ (hu h)⟩
    rcases hr with h | h
    · exact Or.inl (kfix_isPSLn_of_mulEquiv eJ (hl h))
    · exact Or.inr (kfix_isPSUn_of_mulEquiv eJ (hu h))
  · exact Or.inr ⟨kfix_klevel_layer_bot hx hg3 hno, hr8, hP8⟩

@[expose] def InndiagFieldTrivial (V : InndiagVocab) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    ∀ α : MulAut Y, IsFieldAutThree α → α ∈ V.innDiag Y → α = 1

theorem inndiagFieldTrivial_of_le {V : InndiagVocab}
    (h : ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
      ∀ α : MulAut Y, IsFieldAutThree α → α ∈ V.innDiag Y →
        Lemma54Ns.IsInnDiagThree α) : InndiagFieldTrivial V :=
  fun Y _ _ hY α hα hmem => input7_fieldInnDiag_holds Y hY α hα (h Y hY α hα hmem)

theorem inputL3fix_of_core {V : InndiagVocab} (hc : InputL3fixCore)
    (hV : InndiagFieldTrivial V) : InputL3fix V := by
  intro G _ _ K g r hq hr hg3 hfld hT
  refine ⟨?_, hc G K g r hq hr hg3 hfld hT⟩
  rintro ⟨hx, hmem⟩
  obtain ⟨hx', hfa⟩ := hfld
  exact hT ⟨hx, hV (barOf 3 K) hq (barAut 3 K ⟨g, hx⟩) hfa hmem⟩

theorem inputL3fix_holds {V : InndiagVocab} (hiso : InputL3iso) (hV : InndiagFieldTrivial V) :
    InputL3fix V :=
  inputL3fix_of_core (inputL3fixCore_holds hiso) hV

theorem inputL3fixCore_unconditional : InputL3fixCore := inputL3fixCore_holds inputL3iso_holds

theorem inputL3fix_of_inndiagFieldTrivial {V : InndiagVocab} (hV : InndiagFieldTrivial V) :
    InputL3fix V :=
  inputL3fix_holds inputL3iso_holds hV

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
