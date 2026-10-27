module

public import CFSG.LieType.Multipliers.TitsCheck
public import CFSG.Sporadic.Schreier.TitsOuter

public noncomputable section

namespace CFSG.LieType.Multipliers.Tits

open CFSG.CosetTable CFSG.Sporadic.Schreier.Tits CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Open Subgroup
open scoped commutatorElement

abbrev titsRelSet : Set (FreeGroup (Fin 3)) := wordSet titsRels

@[expose] def titsW (i : Fin 3) : FreeGroup (Fin 3) := FreeGroup.mk (titsCommWord i)

theorem titsW_mem_commutator (i : Fin 3) : titsW i ∈ commutator (FreeGroup (Fin 3)) :=
  mk_commWords_mem_commutator _

private theorem mk_inv_titsCommWord (i : Fin 3) :
    FreeGroup.mk ([(i, false)] ++ titsCommWord i) = (FreeGroup.of i)⁻¹ * titsW i := by
  rw [← FreeGroup.mul_mk, titsW, FreeGroup.of, FreeGroup.inv_mk]
  rfl

theorem card_presentedGroup_le :
    Finite (PresentedGroup titsRelSet) ∧ Nat.card (PresentedGroup titsRelSet) ≤ 17971200 :=
  tits_check_rels

theorem card_presentedCover_le :
    Finite (PresentedCover titsRelSet titsW) ∧
      Nat.card (PresentedCover titsRelSet titsW) ≤ 17971200 := by
  change Finite (PresentedGroup (coverRelators titsRelSet titsW)) ∧
    Nat.card (PresentedGroup (coverRelators titsRelSet titsW)) ≤ 17971200
  rw [show titsW = fun i => FreeGroup.mk (titsCommWord i) from rfl, coverRelators_wordSet]
  exact tits_check_cover

@[expose] def abcPerm (i : ℕ) : Equiv.Perm (Fin 1755) :=
  wordIn 2 titsDGen (abcWords.getD i [])

theorem abcPerm_mem (i : ℕ) : abcPerm i ∈ titsD :=
  wordIn_mem (fun _ hj => titsDGen_mem_titsD hj) _

private theorem wordIn_congr {G : Type*} [Group G] {k : ℕ} {gs gs' : ℕ → G}
    (h : ∀ i < k, gs i = gs' i) (w : List ℤ) : wordIn k gs w = wordIn k gs' w := by
  unfold wordIn
  congr 1
  funext i
  exact h i i.2

private theorem abcPerm_eq (i : ℕ) :
    abcPerm i = wordIn 2 (fun j => permOfArr 1755 titsDerivedArrs[j]!) (abcWords.getD i []) :=
  wordIn_congr (fun _ hj => (titsDerived_perm hj).symm) _

theorem lift_titsOneWords
    {w : List (Fin 3 × Bool)} (hw : w ∈ titsOneWords) :
    FreeGroup.lift (fun i : Fin 3 => abcPerm i) (FreeGroup.mk w) = 1 := by
  rw [show (fun i : Fin 3 => abcPerm i) = fun i : Fin 3 => wordIn 2
    (fun j => permOfArr 1755 titsDerivedArrs[j]!) (abcWords.getD i.val []) from
      funext fun i => abcPerm_eq i]
  exact tits_check_perms.1 w hw

private theorem titsDGen_eq_wordIn
    {j : ℕ} (hj : j < 2) :
    titsDGen j = wordIn 3 abcPerm (titsDWords.getD j []) := by
  rw [← titsDerived_perm hj, tits_check_perms.2 j hj]
  exact wordIn_congr (fun i _ => (abcPerm_eq i).symm) _

theorem closure_abcPerm
    : closure (Set.range fun i : Fin 3 => abcPerm i) = titsD := by
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨i, rfl⟩
    exact abcPerm_mem i
  · rw [titsD, closure_le]
    rintro _ ⟨j, rfl⟩
    show titsDGen (j : ℕ) ∈ closure (Set.range fun i : Fin 3 => abcPerm i)
    rw [titsDGen_eq_wordIn j.2]
    refine wordIn_mem (fun i hi => ?_) _
    exact Subgroup.subset_closure (Set.mem_range_self (⟨i, hi⟩ : Fin 3))

@[expose] def abcGen {X : Type} [Group X] (e : X ≃* titsD) (i : Fin 3) : X :=
  e.symm ⟨abcPerm i, abcPerm_mem i⟩

private theorem coe_e_lift {X : Type} [Group X] (e : X ≃* titsD) (x : FreeGroup (Fin 3)) :
    (e (FreeGroup.lift (abcGen e) x) : Equiv.Perm (Fin 1755)) =
      FreeGroup.lift (fun i : Fin 3 => abcPerm i) x := by
  have h : (titsD.subtype.comp e.toMonoidHom).comp (FreeGroup.lift (abcGen e)) =
      FreeGroup.lift (fun i : Fin 3 => abcPerm i) :=
    FreeGroup.ext_hom _ _ fun i => by simp [abcGen]
  exact DFunLike.congr_fun h x

private theorem lift_abcGen_eq_one
    {X : Type} [Group X] (e : X ≃* titsD)
    {w : List (Fin 3 × Bool)} (hw : w ∈ titsOneWords) :
    FreeGroup.lift (abcGen e) (FreeGroup.mk w) = 1 := by
  apply e.injective
  rw [map_one]
  exact Subtype.ext ((coe_e_lift e _).trans (lift_titsOneWords hw))

private theorem closure_abcGen
    {X : Type} [Group X] (e : X ≃* titsD) :
    closure (Set.range (abcGen e)) = ⊤ := by
  have hD : closure (Set.range fun i : Fin 3 => (⟨abcPerm i, abcPerm_mem i⟩ : titsD)) =
      ⊤ := by
    apply map_injective titsD.subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, range_subtype, ← Set.range_comp]
    exact closure_abcPerm
  have hg : Set.range (abcGen e) =
      e.symm.toMonoidHom '' Set.range fun i : Fin 3 => (⟨abcPerm i, abcPerm_mem i⟩ : titsD) := by
    rw [← Set.range_comp]
    rfl
  rw [hg, ← MonoidHom.map_closure, hD]
  exact map_top_of_surjective _ e.symm.surjective

theorem isPresentation_abcGen
    {X : Type} [Group X] (e : X ≃* titsD) :
    IsPresentation (abcGen e) titsRelSet := by
  obtain ⟨hfin, hle⟩ := card_presentedGroup_le
  refine IsPresentation.of_card_le (fun r hr => ?_) (closure_abcGen e) ?_
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact lift_abcGen_eq_one e (List.mem_append_left _ hw)
  · rw [Nat.card_congr e.toEquiv, card_titsD]
    exact hle

theorem lift_titsW
    {X : Type} [Group X] (e : X ≃* titsD) (i : Fin 3) :
    FreeGroup.lift (abcGen e) (titsW i) = abcGen e i := by
  have h := lift_abcGen_eq_one e (w := [(i, false)] ++ titsCommWord i)
    (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))
  rw [mk_inv_titsCommWord, map_mul, map_inv, FreeGroup.lift_apply_of, inv_mul_eq_one] at h
  exact h.symm

theorem multiplier_of_mulEquiv_titsD
    {X : Type} [Group X] (e : X ≃* titsD) :
    commutator X = ⊤ ∧ Nonempty (griessHopfMultiplier X ≃* Unit) := by
  have hP := isPresentation_abcGen e
  have hwg := lift_titsW e
  refine ⟨(isPerfect_of_isPresentation hP titsW_mem_commutator hwg).commutator_eq_top, ?_⟩
  obtain ⟨hfin, hle⟩ := card_presentedCover_le
  have hc := card_presentedCover hP titsW_mem_commutator hwg
  rw [Nat.card_congr e.toEquiv, card_titsD] at hc
  have hpos : 0 < Nat.card (PresentedCover titsRelSet titsW) := Nat.card_pos
  have hM : Nat.card (griessHopfMultiplier X) = 1 := by omega
  obtain ⟨_, _⟩ := Nat.card_eq_one_iff_unique.1 hM
  have : Unique (griessHopfMultiplier X) := ⟨⟨1⟩, fun _ => Subsingleton.elim _ _⟩
  exact ⟨MulEquiv.ofUnique⟩

private theorem reeTitsModel_of_lieModel {T : Type} [Group T]
    (h : CFSG.Blueprint.LieModel T .Tits 0 2 1) : CFSG.Blueprint.ReeTitsModel T .Tits 2 1 :=
  (CFSG.Blueprint.LieModel.reeTitsModel h (by decide)).2

theorem multiplier_Tits
    (X : Type) [Group X]
    (h : CFSG.Blueprint.LieModel X .Tits 0 2 1) :
    commutator X = ⊤ ∧ Nonempty (griessHopfMultiplier X ≃* Unit) := by
  obtain ⟨e⟩ := titsModelEquiv X 2 1 (reeTitsModel_of_lieModel h)
  exact multiplier_of_mulEquiv_titsD e

end CFSG.LieType.Multipliers.Tits
