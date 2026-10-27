module

public import CFSG.Sporadic.Bridge.TwoGen
public import CFSG.Monster.B.Co2.PermArr
public import CFSG.Certificates.Kernel.Spor.PackWord

public section

namespace CFSG.KS.Pres

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen

@[expose] noncomputable def wordPK (n w : Nat) (G GI : Nat → Nat) (v : List (Nat × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn n w)
    (fun l _ acc => pcomp n w (mask w) (Bool.rec (GI l.1) (G l.1) l.2) acc) v

theorem rep_wordPK {n w : Nat} {G GI : Nat → Nat} {g : Nat → Equiv.Perm (Fin n)}
    (hG : ∀ i, Rep n (unpack n w (G i)) (g i)) (hGI : ∀ i, Rep n (unpack n w (GI i)) (g i)⁻¹)
    (hc : ∀ i, canonK n w (mask w) (n * w) (G i) = true ∧ canonK n w (mask w) (n * w) (GI i) = true)
    (hid : canonK n w (mask w) (n * w) (pidn n w) = true) (hidA : idA n = unpack n w (pidn n w)) :
    ∀ v, Rep n (unpack n w (wordPK n w G GI v)) (wordProd g v) ∧
      canonK n w (mask w) (n * w) (wordPK n w G GI v) = true
  | [] => by
    refine ⟨?_, hid⟩
    change Rep n (unpack n w (pidn n w)) (wordProd g [])
    rw [← hidA]
    simpa [wordProd] using (rep_idA (n := n))
  | l :: v => by
    obtain ⟨ih, ihc⟩ := rep_wordPK hG hGI hc hid hidA v
    obtain ⟨i, b⟩ := l
    change Rep n (unpack n w (pcomp n w (mask w) (Bool.rec (GI i) (G i) b) (wordPK n w G GI v)))
      (wordProd g ((i, b) :: v)) ∧
      canonK n w (mask w) (n * w) (pcomp n w (mask w) (Bool.rec (GI i) (G i) b)
        (wordPK n w G GI v)) = true
    have hw : wordProd g ((i, b) :: v) = (if b then g i else (g i)⁻¹) * wordProd g v := by
      simp [wordProd]
    cases b
    · refine ⟨?_, canonK_pcomp (hc i).2 ihc⟩
      rw [← compA_unpack (hc i).2 ihc, hw]
      exact rep_compA (hGI i) ih
    · refine ⟨?_, canonK_pcomp (hc i).1 ihc⟩
      rw [← compA_unpack (hc i).1 ihc, hw]
      exact rep_compA (hG i) ih

theorem relators_of_wordPK {n w : Nat} {G GI : Nat → Nat} {g : Nat → Equiv.Perm (Fin n)}
    (hG : ∀ i, Rep n (unpack n w (G i)) (g i)) (hGI : ∀ i, Rep n (unpack n w (GI i)) (g i)⁻¹)
    (hc : ∀ i, canonK n w (mask w) (n * w) (G i) = true ∧ canonK n w (mask w) (n * w) (GI i) = true)
    (hid : canonK n w (mask w) (n * w) (pidn n w) = true) (hidA : idA n = unpack n w (pidn n w))
    {rels : List (List (Nat × Bool))}
    (h : ∀ v ∈ rels, Nat.beq (wordPK n w G GI v) (pidn n w) = true) :
    ∀ v ∈ rels, wordProd g v = 1 := by
  intro v hv
  have r := (rep_wordPK hG hGI hc hid hidA v).1
  rw [Nat.eq_of_beq_eq_true (h v hv), ← hidA] at r
  exact r.unique rep_idA

theorem card_closure_le {n : Nat} (P : TauCeti.GroupPresentation) (hP : P.generatorCount = 2)
    {g0 g1 : Equiv.Perm (Fin n)} (hrel : ∀ v ∈ P.relatorLetters, wordProd (img2 g0 g1) v = 1)
    [Finite P.Group] : Nat.card (Subgroup.closure ({g0, g1} : Set (Equiv.Perm (Fin n)))) ≤
      Nat.card P.Group := by
  set K := Subgroup.closure ({g0, g1} : Set (Equiv.Perm (Fin n)))
  let x : K := ⟨g0, Subgroup.subset_closure (Set.mem_insert _ _)⟩
  let y : K := ⟨g1, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  have himg : ∀ i, ((img2 x y i : K) : Equiv.Perm (Fin n)) = img2 g0 g1 i := by
    intro i
    unfold img2
    split <;> rfl
  have hrel' : ∀ v ∈ P.relatorLetters, wordProd (img2 x y) v = 1 := by
    intro v hv
    apply Subtype.ext
    rw [coe_wordProd]
    simp only [himg]
    exact hrel v hv
  have hcl : Subgroup.closure ({x, y} : Set K) = ⊤ := by
    have h := Subgroup.closure_closure_coe_preimage (k := ({g0, g1} : Set (Equiv.Perm (Fin n))))
    have e : ((↑) : K → Equiv.Perm (Fin n)) ⁻¹' ({g0, g1} : Set (Equiv.Perm (Fin n))) = {x, y} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, x, y,
        Subtype.ext_iff]
    rw [e] at h
    exact h
  have hsurj : Function.Surjective (presHom P (img2 x y) hrel') := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hcl, Subgroup.closure_le]
    rintro g (h | h)
    · exact ⟨presGen P 0, by
        rw [presHom_presGen P (img2 x y) hrel' (by omega), h]
        simp [img2]⟩
    · rw [Set.mem_singleton_iff] at h
      exact ⟨presGen P 1, by
        rw [presHom_presGen P (img2 x y) hrel' (by omega), h]
        simp [img2]⟩
  exact Nat.card_le_card_of_surjective _ hsurj

end CFSG.KS.Pres

end
