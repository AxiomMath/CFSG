module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X12
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Lab
public import CFSG.ClassicalInvolution.Q3.TL4SecIdAE5

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan AEIdent)

section Perm

@[expose] noncomputable def aePerm (n : ℕ) : AEQ n →* Equiv.Perm (Fin n) :=
  QuotientGroup.lift (piSub n) (permHom n) (by
    intro x hx
    rcases mem_piSub.mp hx with rfl | rfl
    · exact one_mem _
    · show (permHom n) (allOnes n) = 1
      rfl)

theorem aePerm_mkQ (n : ℕ) (x : Wr n) : aePerm n (mkQ n x) = x.perm := rfl

theorem alt5_not_solvable : ¬ Group.IsSolvable (alternatingGroup (Fin 5)) := by
  intro hs
  haveI := alternatingGroup.isSimpleGroup_five
  have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr hs
  let a : alternatingGroup (Fin 5) := ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
    rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  let b : alternatingGroup (Fin 5) := ⟨Equiv.swap 0 3 * Equiv.swap 3 4, by
    rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  have h := congrArg Subtype.val (hcomm a b)
  revert h
  decide

theorem ae5_not_solvable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} (I : AEIdent Φ 5) :
    ¬ Group.IsSolvable ↥(pSpan Φ) := by
  intro hs
  set θ : ↥(pSpan Φ) →* Equiv.Perm (Fin 5) := (aePerm 5).comp I.φ with hθ
  have hA5 : alternatingGroup (Fin 5) ≤ θ.range := by
    intro σ hσ
    have hmem : (⟨0, σ⟩ : Wr 5) ∈ aeSub 5 := by
      refine ⟨?_, ?_⟩
      · simp [wsum]
      · simpa [Equiv.Perm.mem_alternatingGroup] using hσ
    have : mkQ 5 ⟨0, σ⟩ ∈ I.φ.range := by
      rw [I.range_eq]
      exact Subgroup.mem_map_of_mem _ hmem
    obtain ⟨y, hy⟩ := this
    exact ⟨y, by rw [hθ, MonoidHom.comp_apply, hy, aePerm_mkQ]⟩
  haveI : Group.IsSolvable θ.range := solvable_of_surjective θ.rangeRestrict_surjective
  exact alt5_not_solvable (solvable_of_solvable_injective (f := Subgroup.inclusion hA5)
    (Subgroup.inclusion_injective hA5))

end Perm


section AE5Facts

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem ae5_center (hgen : omegaGen Φ = ⊤) (I : AEIdent Φ 5) (hker : I.φ.ker = ⊥) :
    Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  have h1 := CFSG.ClassicalInvolution.Q3.TL4.AE5.map_eq_one_of_mem_center hgen I hc
  have h2 : (⟨c, CFSG.ClassicalInvolution.Q3.TL4.AE5.mem_pSpan hgen c⟩ : ↥(pSpan Φ)) ∈ I.φ.ker := h1
  rw [hker, Subgroup.mem_bot] at h2
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val h2)

theorem ae5_fix (hS : TwinDisc.Q8Section X Φ) (I : AEIdent Φ 5) {J J' : Subgroup X} (hJ : J ∈ Φ) (hJ' : J' ∈ Φ)
    (hne : J ≠ J') {t : X} (ht : IsUniqueInvolution J t) (ht' : IsUniqueInvolution J' t)
    {β : MulAut X} (hperm : ∀ L ∈ Φ, ∃ L' ∈ Φ, L.map β.toMonoidHom = L')
    (hfixJ : ∀ y ∈ J, β y = y) (hfixJ' : ∀ y ∈ J', β y = y) : β = 1 ∨ β = MulAut.conj t := by
  have F := TwinDisc.AE5.q8Fam_of_aeIdent_n (le_refl 5) hS I
  have hgen := F.gen
  rcases TwinDisc.AE5.psi_dichotomy F I (TwinDisc.autOfTop hgen β)
    (TwinDisc.autOfTop_perm hgen β hperm) hJ hJ' hne ht ht'
    (fun y hy => Subtype.ext (hfixJ _ hy)) (fun y hy => Subtype.ext (hfixJ' _ hy)) with h | h
  · left
    ext a
    exact congrArg Subtype.val (h ⟨a, TwinDisc.mem_pSpan_of_top hgen a⟩)
  · right
    ext a
    exact h ⟨a, TwinDisc.mem_pSpan_of_top hgen a⟩

theorem secFacts_ae5 (hS : TwinDisc.Q8Section X Φ) (I : AEIdent Φ 5) (hker : I.φ.ker = ⊥) {J J' : Subgroup X}
    (hJ : J ∈ Φ) (hJ' : J' ∈ Φ) (hne : J ≠ J') {t : X} (ht : IsUniqueInvolution J t)
    (ht' : IsUniqueInvolution J' t) {P : Subgroup (MulAut X)}
    (hperm : ∀ β ∈ P, ∀ L ∈ Φ, ∃ L' ∈ Φ, L.map β.toMonoidHom = L')
    (hfixJ : ∀ β ∈ P, ∀ y ∈ J, β y = y) (hfixJ' : ∀ β ∈ P, ∀ y ∈ J', β y = y) :
    SecFacts P t ∧ ∀ β ∈ P, β = 1 ∨ β = MulAut.conj t := by
  have hfix : ∀ β ∈ P, β = 1 ∨ β = MulAut.conj t := fun β hβ =>
    ae5_fix hS I hJ hJ' hne ht ht' (hperm β hβ) (hfixJ β hβ) (hfixJ' β hβ)
  have hcen := ae5_center hS.gen I hker
  have hns : ¬ Group.IsSolvable X := by
    intro hsol
    haveI := hsol
    have hinj : Function.Injective (pSpan Φ).subtype := Subgroup.subtype_injective _
    exact ae5_not_solvable I (solvable_of_solvable_injective hinj)
  exact ⟨secFacts_of_fixTwo ht.sq hcen hns hfix, hfix⟩

end AE5Facts

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X
