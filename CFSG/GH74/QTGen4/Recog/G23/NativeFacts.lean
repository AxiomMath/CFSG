module

public import CFSG.GH74.QTGen4.Recog.G23.Native
public import Certificates.Certificate320002
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434G23Words
public meta import CFSG.RankThree.PartTwo.Sec4.T444.Item434G23Check
public meta import CFSG.RankThree.PartTwo.Sec4.T444.Item434G23Words
public meta import CFSG.GH74.QTGen4.Recog.G23.Native
public meta import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeData

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three CFSG.RankThree.PartTwo.Sec4.Item434RemG23
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U

theorem eWord_lt : ∀ i, ∀ l ∈ eWord i, l < 8 := by decide +kernel

section CodeWordCheck

theorem wordCode_eWord : ∀ i, wordCode (eWord i) = eCode i := Certificates.certificate320002.1

end CodeWordCheck

theorem rootCubes : RootCubes := by
  unfold RootCubes
  decide +kernel

noncomputable def eEl (i : Fin 6) : GL (Fin 14) (ZMod 3) := wordElem (eWord i)

theorem eEl_mem (i : Fin 6) : eEl i ∈ R3 := wordElem_mem (eWord i) (eWord_lt i)

theorem coe_eEl (i : Fin 6) : ((eEl i : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) =
    dec14 (eCode i) := by
  rw [eEl, coe_wordElem rootCubes _ (eWord_lt i), wordCode_eWord]

noncomputable def Lt (l : Fin 6 × Bool) : GL (Fin 14) (ZMod 3) :=
  if l.2 then eEl l.1 else (eEl l.1)⁻¹

theorem coe_Lt (l : Fin 6 × Bool) :
    ((Lt l : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) = dec14 (letterCode l) := by
  obtain ⟨i, b⟩ := l
  cases b
  · have hinv : dec14 (eCode i) * dec14 (eInvCode i) = 1 := by
      rw [← dec14_mul14, inv_code i, dec14_one14]
    simp only [Lt, letterCode, Bool.false_eq_true, ↓reduceIte]
    rw [Matrix.coe_units_inv, coe_eEl, Matrix.inv_eq_right_inv hinv]
  · simp only [Lt, letterCode, ↓reduceIte]
    rw [coe_eEl]

theorem coe_Lt_prod (r : List (Fin 6 × Bool)) :
    (((r.map Lt).prod : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) =
      dec14 (evalCode r) := by
  have key : ∀ (r : List (Fin 6 × Bool)) (g : GL (Fin 14) (ZMod 3)) (c : List ℕ),
      (g : Matrix (Fin 14) (Fin 14) (ZMod 3)) = dec14 c →
      ((g * (r.map Lt).prod : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) =
        dec14 (r.foldl (fun acc l => mul14 acc (letterCode l)) c) := by
    intro r
    induction r with
    | nil => intro g c h; simpa using h
    | cons l r ih =>
      intro g c h
      rw [List.map_cons, List.prod_cons, ← mul_assoc, List.foldl_cons]
      refine ih _ _ ?_
      rw [Units.val_mul, h, coe_Lt l, dec14_mul14]
  have := key r 1 one14 (by rw [Units.val_one, dec14_one14])
  rw [one_mul] at this
  exact this

theorem freeMk_eq_prod (L : List (Fin 6 × Bool)) :
    FreeGroup.mk L =
      (L.map fun l => if l.2 then FreeGroup.of l.1 else (FreeGroup.of l.1)⁻¹).prod := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    have hl : (if l.2 then FreeGroup.of l.1 else (FreeGroup.of l.1)⁻¹) = FreeGroup.mk [l] := by
      obtain ⟨x, b⟩ := l
      cases b <;> simp [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]
    rw [List.map_cons, List.prod_cons, ← ih, hl, FreeGroup.mul_mk]
    rfl

theorem lift_mk_eq (r : List (Fin 6 × Bool)) :
    FreeGroup.lift eEl (FreeGroup.mk r) = (r.map Lt).prod := by
  rw [freeMk_eq_prod, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  obtain ⟨i, b⟩ := l
  cases b <;> simp [Lt]

theorem relator_eEl (r : List (Fin 6 × Bool)) (hr : r ∈ g23Words) :
    FreeGroup.lift eEl (FreeGroup.mk r) = 1 := by
  apply Units.ext
  rw [lift_mk_eq, coe_Lt_prod, rels_code r hr, Units.val_one, dec14_one14]

theorem x1Word_eval : evalCode x1Word = x0c := Certificates.certificate320002.2.1

theorem y1Word_eval : evalCode y1Word = y0c := Certificates.certificate320002.2.2

theorem eCode_zero : eCode 0 = x1c := by decide +kernel

theorem eCode_one : eCode 1 = y1c := by decide +kernel

theorem gX1_eq : gX 1 = eEl 0 := by
  apply Units.ext
  rw [coe_gX1, coe_eEl, eCode_zero]

theorem gY1_eq : gY 1 = eEl 1 := by
  apply Units.ext
  rw [coe_gY1, coe_eEl, eCode_one]

theorem R3_le_closure : R3 ≤ Subgroup.closure (Set.range eEl) := by
  set H := Subgroup.closure (Set.range eEl) with hH
  have hLt : ∀ l, Lt l ∈ H := by
    rintro ⟨i, b⟩
    cases b
    · simp only [Lt, Bool.false_eq_true, ↓reduceIte]
      exact H.inv_mem (Subgroup.subset_closure ⟨i, rfl⟩)
    · simp only [Lt, ↓reduceIte]
      exact Subgroup.subset_closure ⟨i, rfl⟩
  have hword : ∀ r : List (Fin 6 × Bool), (r.map Lt).prod ∈ H := fun r =>
    Subgroup.list_prod_mem H fun x hx => by
      obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx
      exact hLt l
  have hgX1 : gX 1 ∈ H := by
    rw [gX1_eq]
    exact Subgroup.subset_closure ⟨0, rfl⟩
  have hgY1 : gY 1 ∈ H := by
    rw [gY1_eq]
    exact Subgroup.subset_closure ⟨1, rfl⟩
  have hgX0 : gX 0 ∈ H := by
    have h : gX 0 = (x1Word.map Lt).prod := by
      apply Units.ext
      rw [coe_gX0, coe_Lt_prod, x1Word_eval]
    rw [h]
    exact hword _
  have hgY0 : gY 0 ∈ H := by
    have h : gY 0 = (y1Word.map Lt).prod := by
      apply Units.ext
      rw [coe_gY0, coe_Lt_prod, y1Word_eval]
    rw [h]
    exact hword _
  have hgXmem : ∀ n : Fin 2, gX n ∈ H := by
    intro n
    fin_cases n
    · exact hgX0
    · exact hgX1
  have hc3 : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
  have hx : ∀ (n : Fin 2) (c : ZMod 3),
      glHom (RingEquiv.refl (ZMod 3)) (xUnit .G2 (ZMod 3) (ix n) c) ∈ H := by
    intro n c
    rcases hc3 c with rfl | rfl | rfl
    · have h0 : xUnit .G2 (ZMod 3) (ix n) 0 = 1 := Units.ext (xOp_zero _)
      rw [h0, map_one]
      exact H.one_mem
    · exact hgXmem n
    · have h2 : xUnit .G2 (ZMod 3) (ix n) 2 =
          xUnit .G2 (ZMod 3) (ix n) 1 * xUnit .G2 (ZMod 3) (ix n) 1 := by
        apply Units.ext
        simp only [Units.val_mul, coe_xUnit]
        rw [xOp_mul_xOp (upTransport .G2)]
        rfl
      rw [h2, map_mul]
      exact H.mul_mem (hgXmem n) (hgXmem n)
  have hgYmem : ∀ n : Fin 2, gY n ∈ H := by
    intro n
    fin_cases n
    · exact hgY0
    · exact hgY1
  have hy : ∀ (n : Fin 2) (c : ZMod 3),
      glHom (RingEquiv.refl (ZMod 3)) (yUnit .G2 (ZMod 3) (ix n) c) ∈ H := by
    intro n c
    rcases hc3 c with rfl | rfl | rfl
    · have h0 : yUnit .G2 (ZMod 3) (ix n) 0 = 1 := Units.ext (yOp_zero _)
      rw [h0, map_one]
      exact H.one_mem
    · exact hgYmem n
    · have h2 : yUnit .G2 (ZMod 3) (ix n) 2 =
          yUnit .G2 (ZMod 3) (ix n) 1 * yUnit .G2 (ZMod 3) (ix n) 1 := by
        apply Units.ext
        simp only [Units.val_mul, coe_yUnit]
        rw [yOp_mul_yOp (downTransport .G2)]
        rfl
      rw [h2, map_mul]
      exact H.mul_mem (hgYmem n) (hgYmem n)
  unfold R3
  rw [Subgroup.map_le_iff_le_comap, adjointGroup, Subgroup.closure_le]
  rintro g ⟨i, c, hg | hg⟩
  · obtain ⟨n, rfl⟩ : ∃ n : Fin 2, ix n = i := ⟨i, rfl⟩
    have hgu : g = xUnit .G2 (ZMod 3) (ix n) c := Units.ext hg
    show glHom (RingEquiv.refl (ZMod 3)) g ∈ H
    rw [hgu]
    exact hx n c
  · obtain ⟨n, rfl⟩ : ∃ n : Fin 2, ix n = i := ⟨i, rfl⟩
    have hgu : g = yUnit .G2 (ZMod 3) (ix n) c := Units.ext hg
    show glHom (RingEquiv.refl (ZMod 3)) g ∈ H
    rw [hgu]
    exact hy n c

set_option maxHeartbeats 400000 in
theorem exists_letters_native :
    ∃ u : Fin 6 → Ghat, SatisfiesG23Words u ∧ Subgroup.closure (Set.range u) = ⊤ := by
  let ψ : Ghat →* GL (Fin 14) (ZMod 3) := R3.subtype.comp adjointEquivR3.toMonoidHom
  have hψ : Function.Injective ψ := fun x y h => adjointEquivR3.injective (Subtype.ext h)
  let u : Fin 6 → Ghat := fun i => adjointEquivR3.symm ⟨eEl i, eEl_mem i⟩
  have hψu : ∀ i, ψ (u i) = eEl i := fun i => by simp [ψ, u]
  have hcomp : ψ.comp (FreeGroup.lift u) = FreeGroup.lift eEl :=
    FreeGroup.ext_hom _ _ fun i => by simp [hψu]
  have hrel : SatisfiesG23Words u := by
    intro r hr
    apply hψ
    have h1 := congrArg
      (fun φ : FreeGroup (Fin 6) →* GL (Fin 14) (ZMod 3) => φ (FreeGroup.mk r)) hcomp
    simp only [MonoidHom.comp_apply] at h1
    rw [map_one, h1, relator_eEl r hr]
  refine ⟨u, hrel, ?_⟩
  rw [eq_top_iff]
  intro x _
  have hmap : (Subgroup.closure (Set.range u)).map ψ = Subgroup.closure (Set.range eEl) := by
    rw [MonoidHom.map_closure, ← Set.range_comp, show ⇑ψ ∘ u = eEl from funext hψu]
  have hxmem : ψ x ∈ Subgroup.closure (Set.range eEl) := R3_le_closure (adjointEquivR3 x).2
  rw [← hmap] at hxmem
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hxmem
  exact (hψ hyx) ▸ hy

end CFSG.GH74.QTGen4.Recog.G23
