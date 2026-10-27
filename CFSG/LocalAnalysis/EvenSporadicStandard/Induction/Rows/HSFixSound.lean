module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HSFixData
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarModel

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Recognition.HSMultiplier

@[expose] def subsetProd {G : Type*} [Monoid G] (x : Fin 4 → G) (m : ℕ) : G :=
  (List.finRange 4).foldl (fun acc l => if m.testBit l.val then acc * x l else acc) 1

theorem map_subsetProd {G G' : Type*} [Monoid G] [Monoid G'] (f : G →* G') (x : Fin 4 → G)
    (m : ℕ) : f (subsetProd x m) = subsetProd (fun l => f (x l)) m := by
  have key : ∀ (L : List (Fin 4)) (a : G),
      f (L.foldl (fun acc l => if m.testBit l.val then acc * x l else acc) a) =
        L.foldl (fun acc l => if m.testBit l.val then acc * f (x l) else acc) (f a) := by
    intro L
    induction L with
    | nil => intro a; rfl
    | cons l L ih =>
      intro a
      simp only [List.foldl_cons]
      cases hb : m.testBit l.val
      · simpa [hb] using ih a
      · simpa [hb] using ih (a * x l)
  simpa [subsetProd] using key _ 1


theorem rep_hfxProd {Et : Fin 4 → Table} {x : Fin 4 → Equiv.Perm (Fin 11200)}
    (h : ∀ l, Rep 11200 (Et l) (x l)) (m : ℕ) :
    Rep 11200 (hfxProd Et m) (subsetProd x m) := by
  have key : ∀ (L : List (Fin 4)) (acc : Table) (a : Equiv.Perm (Fin 11200)),
      Rep 11200 acc a →
      Rep 11200 (L.foldl
        (fun acc l => if m.testBit l.val then compT 11200 acc (Et l) else acc) acc)
        (L.foldl (fun acc l => if m.testBit l.val then acc * x l else acc) a) := by
    intro L
    induction L with
    | nil => intro acc a ha; exact ha
    | cons l L ih =>
      intro acc a ha
      simp only [List.foldl_cons]
      cases hb : m.testBit l.val
      · simpa [hb] using ih acc a ha
      · simpa [hb] using ih _ _ (Rep.compT ha (h l))
  exact key _ _ _ (Rep.idT (by norm_num))

theorem hfxCheck_eq (i : Fin 4) :
    hfxCheck i = hfxCheckWith i (hfxT i) (hfxTI i) (hfxA i) (hfxAI i) (hfxEt i) (hfxEa i)
      (fun m => hfxProd (hfxEt i) m.val) := by
  unfold hfxCheck
  simp only [Array.size_ofFn, Fin.is_lt, getElem!_pos, Array.getElem_ofFn, Fin.eta]
  rfl

section Sound


@[expose] noncomputable def hfxRhoPerm (i : Fin 4) : Equiv.Perm (Fin 3850) := tp 3850 (hfxRho i)

@[expose] noncomputable def yVal (w : List (Fin 6 × Bool)) : Equiv.Perm (Fin 11200) :=
  FreeGroup.lift harYPerm (FreeGroup.mk w)

@[expose] noncomputable def hfxTPerm (i : Fin 4) (j : Fin 6) : Equiv.Perm (Fin 11200) :=
  yVal (hfxW i j)

@[expose] noncomputable def hfxAPerm (i : Fin 4) (k : Fin 6) : Equiv.Perm (Fin 11200) :=
  FreeGroup.lift (hfxTPerm i) (hsCommW k)

@[expose] noncomputable def hfxEPerm (i l : Fin 4) : Equiv.Perm (Fin 11200) := yVal (hfxE i l)

structure HfxSound (i : Fin 4) : Prop where
  pi_word : ∀ j, FreeGroup.lift harXPerm (FreeGroup.mk (hfxW i j)) =
    hfxRhoPerm i * harXPerm j * (hfxRhoPerm i)⁻¹
  fixed : ∀ l, FreeGroup.lift (hfxAPerm i) (FreeGroup.mk (hfxE i l)) = hfxEPerm i l
  sq : ∀ l, hfxEPerm i l * hfxEPerm i l = 1
  comm : ∀ l l', hfxEPerm i l * hfxEPerm i l' = hfxEPerm i l' * hfxEPerm i l
  distinct : ∀ a b : Fin 16, a ≠ b →
    subsetProd (hfxEPerm i) a.val ≠ subsetProd (hfxEPerm i) b.val

theorem hfx_sound (i : Fin 4) (h : hfxCheck i = true) : HfxSound i := by
  have hn11 : (11200 : ℕ) < 2 ^ 32 := by norm_num
  have hn38 : (3850 : ℕ) < 2 ^ 32 := by norm_num
  rw [hfxCheck_eq, hfxCheckWith] at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hperm, hinv⟩, hpi⟩, hTinv⟩, hAinv⟩, hfix⟩, hsq⟩, hcomm⟩, hdist⟩ := h
  have hρR : Rep 3850 (hfxRho i) (hfxRhoPerm i) := rep_tp hperm
  have hρI : Rep 3850 (invT 3850 (hfxRho i)) (hfxRhoPerm i)⁻¹ := Rep.inv_of_invOK hρR hinv
  have hT : ∀ j, Rep 11200 (hfxT i j) (hfxTPerm i j) := fun j =>
    rep_evalW hn11 (g := harY) (gi := harYI) (f := harYPerm) (fun j => (rep_harY j).1)
      (fun j => (rep_harY j).2) (hfxW i j)
  have hTI : ∀ j, Rep 11200 (hfxTI i j) (hfxTPerm i j)⁻¹ := fun j =>
    Rep.inv_of_invOK (hT j) (hTinv j)
  have hA : ∀ k, Rep 11200 (hfxA i k) (hfxAPerm i k) := fun k =>
    rep_evalW hn11 (g := hfxT i) (gi := hfxTI i) (f := hfxTPerm i) hT hTI (hsCommWord k)
  have hAI : ∀ k, Rep 11200 (hfxAI i k) (hfxAPerm i k)⁻¹ := fun k =>
    Rep.inv_of_invOK (hA k) (hAinv k)
  have hE : ∀ l, Rep 11200 (hfxEt i l) (hfxEPerm i l) := fun l =>
    rep_evalW hn11 (g := harY) (gi := harYI) (f := harYPerm) (fun j => (rep_harY j).1)
      (fun j => (rep_harY j).2) (hfxE i l)
  have hEa : ∀ l, Rep 11200 (hfxEa i l)
      (FreeGroup.lift (hfxAPerm i) (FreeGroup.mk (hfxE i l))) := fun l =>
    rep_evalW hn11 (g := hfxA i) (gi := hfxAI i) (f := hfxAPerm i) hA hAI (hfxE i l)
  refine ⟨fun j => ?_, fun l => ?_, fun l => ?_, fun l l' => ?_, fun a b hab hprod => ?_⟩
  · have hπ : Rep 3850 (evalW 3850 harX harXI (hfxW i j))
        (FreeGroup.lift harXPerm (FreeGroup.mk (hfxW i j))) :=
      rep_evalW hn38 (g := harX) (gi := harXI) (f := harXPerm) (fun j => (rep_harX j).1)
        (fun j => (rep_harX j).2) (hfxW i j)
    exact (tblEq_iff_eq hπ (Rep.compT (Rep.compT hρR (rep_harX j).1) hρI)).1 (hpi j)
  · exact ((tblEq_iff_eq (hE l) (hEa l)).1 (hfix l)).symm
  · exact (tblEq_iff_eq (Rep.compT (hE l) (hE l)) (Rep.idT hn11)).1 (hsq l)
  · exact (tblEq_iff_eq (Rep.compT (hE l) (hE l')) (Rep.compT (hE l') (hE l))).1 (hcomm l l')
  · have hd := hdist a b
    have hne : (a == b) = false := beq_eq_false_iff_ne.2 hab
    rw [hne, Bool.false_or, Bool.not_eq_true'] at hd
    have hra := rep_hfxProd hE a.val
    have hrb := rep_hfxProd hE b.val
    have := (tblEq_iff_eq hra hrb).2 hprod
    rw [this] at hd
    exact Bool.noConfusion hd

end Sound

end CFSG.EvenSporadicStandard.TwoHS
