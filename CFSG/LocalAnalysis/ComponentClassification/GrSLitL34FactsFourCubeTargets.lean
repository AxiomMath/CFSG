module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsFourCubePres
public import CFSG.RankThree.Native.HSMcLFiveCentralizers
public import CFSG.Sporadic.Schreier.ONSylowCenter
public import Certificates.Certificate22218

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.FourCube

open CFSG Subgroup CFSG.CosetTable CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native

structure WitParts : Prop where
  hs : hsWitOK = true
  on : onWitOK = true

theorem witParts : WitParts := by
  have h := Certificates.certificate22218
  simp only [fourCubeWitOK, Bool.and_eq_true] at h
  exact ⟨h.1, h.2⟩

theorem rep_foldl {n k : ℕ} {gs : Array (Array ℕ)} (hv : ∀ i < k, validA n gs[i]! = true)
    (w : List (Fin k × Bool)) {acc : Array ℕ} {g : Equiv.Perm (Fin n)} (hacc : Rep n acc g) :
    Rep n (w.foldl (fun acc l => compA n acc (if l.2 then gs[l.1.val]! else invCand n gs[l.1.val]!))
      acc) (g * signedProd (fun i : Fin k => permOfArr n gs[i.val]!) w) := by
  induction w generalizing acc g with
  | nil => simpa using hacc
  | cons l w ih =>
    rw [List.foldl_cons, signedProd_cons, ← mul_assoc]
    apply ih
    apply rep_compA hacc
    split
    · exact rep_of_validA (hv l.1.val l.1.2)
    · exact rep_inv_of_validA (hv l.1.val l.1.2)

theorem rep_wordArr {n k : ℕ} {gs : Array (Array ℕ)} (hv : ∀ i < k, validA n gs[i]! = true)
    (w : List (Fin k × Bool)) :
    Rep n (wordArr n gs w) (signedProd (fun i : Fin k => permOfArr n gs[i.val]!) w) := by
  have := rep_foldl hv w (rep_idA (n := n))
  rwa [one_mul] at this

@[expose] noncomputable def hsWitPerm (i : Fin 5) : Equiv.Perm (Fin 100) :=
    permOfArr 100 hsWit[i.val]!

theorem hs_parts :
    (∀ i < 5, validA 100 hsWit[i]! = true) ∧
      (∀ i < 5, siftA 100 hs100PLevels hs100BaseArr 0 hsWit[i]! = true) ∧
      (∀ w ∈ qRels 0, eqA 100 (wordArr 100 hsWit w) (idA 100) = true) ∧
      enumOK 100 hsWit hsKeys (enumBfs 100 hsWit hsKeys 600) = true ∧
      (enumBfs 100 hsWit hsKeys 600).pts.size = 512 := by
  have h := witParts.hs
  simp only [hsWitOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4, h5⟩ := h
  exact ⟨fun i hi => allLt_spec h1 hi, fun i hi => allLt_spec h2 hi, h3, h4, h5⟩

theorem hs_rels :
    ∀ w ∈ qRels 0, signedProd hsWitPerm w = 1 := by
  intro w hw
  exact (eqA_iff (rep_wordArr hs_parts.1 w) rep_idA).1 (hs_parts.2.2.1 w hw)

noncomputable def hsGam : Gam 0 →* Equiv.Perm (Fin 100) :=
  pgHom (qRels 0) hsWitPerm hs_rels

theorem range_hsGam :
    hsGam.range = closure (permsA 100 hsWit) := by
  rw [hsGam, range_pgHom]
  congr 1
  ext g
  simp only [Set.mem_range, permsA, Set.mem_image, Set.mem_ofPred_eq, hsWitPerm]
  have hs : hsWit.size = 5 := rfl
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, by rw [hs]; exact i.2, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, by rwa [hs] at hi⟩, rfl⟩

theorem card_range_hsGam : Nat.card hsGam.range = 512 := by
  rw [range_hsGam, (enumOK_spec (by decide) hs_parts.2.2.2.1).2.1, hs_parts.2.2.2.2]

theorem range_hsGam_le :
    hsGam.range ≤ hs100P := by
  rw [hsGam, range_pgHom, closure_le]
  rintro _ ⟨i, rfl⟩
  exact mem_hs100P_of_sift (rep_of_validA (hs_parts.1 i.val i.2)) (hs_parts.2.1 i.val i.2)

@[expose] noncomputable def onWitPerm (i : Fin 5) : Equiv.Perm (Fin 32) :=
    permOfArr 32 onWit[i.val]!

theorem on_parts :
    (∀ j < 6, validA 32 t32Gens[j]! = true) ∧ (∀ i < 5, validA 32 onWit[i]! = true) ∧
      (∀ w ∈ qRels d1, eqA 32 (wordArr 32 onWit w) (idA 32) = true) ∧
      enumOK 32 onWit onKeys (enumBfs 32 onWit onKeys 600) = true ∧
      (enumBfs 32 onWit onKeys 600).pts.size = 512 := by
  have h := witParts.on
  simp only [onWitOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, h1⟩, -⟩, h2⟩, h3⟩, h4, h5⟩ := h
  exact ⟨fun j hj => allLt_spec h1 hj, fun i hi => allLt_spec h2 hi, h3, h4, h5⟩

theorem on_rels :
    ∀ w ∈ qRels d1, signedProd onWitPerm w = 1 := by
  intro w hw
  exact (eqA_iff (rep_wordArr on_parts.2.1 w) rep_idA).1 (on_parts.2.2.1 w hw)

noncomputable def onGam : Gam d1 →* Equiv.Perm (Fin 32) :=
  pgHom (qRels d1) onWitPerm on_rels

theorem card_range_onGam : Nat.card onGam.range = 512 := by
  have h : onGam.range = closure (permsA 32 onWit) := by
    rw [onGam, range_pgHom]
    congr 1
    ext g
    simp only [Set.mem_range, permsA, Set.mem_image, Set.mem_ofPred_eq, onWitPerm]
    have hs : onWit.size = 5 := rfl
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, by rw [hs]; exact i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, by rwa [hs] at hi⟩, rfl⟩
  rw [h, (enumOK_spec (by decide) on_parts.2.2.2.1).2.1, on_parts.2.2.2.2]

theorem t32_perm_eq {j : ℕ}
    (hj : j < 6) : permOfArr 32 t32Gens[j]! = CFSG.ONSchreier.permOfArr 32 t32Gens[j]! :=
  Rep.unique (rep_of_validA (on_parts.1 j hj)) (fun x =>
    CFSG.ONSchreier.prep_t32_gens j (by rw [CFSG.ONSchreier.t32_gens_size]; exact hj) x)

theorem range_onGam_le :
    onGam.range ≤ CFSG.ONSchreier.onT32Chain.originalSubgroup := by
  rw [onGam, range_pgHom, closure_le, CFSG.ONSchreier.onT32_sub]
  rintro _ ⟨i, rfl⟩
  have hgen : ∀ j : Fin 6, permOfArr 32 t32Gens[j.val]! ∈
      Subgroup.closure ((fun j => CFSG.ONSchreier.permOfArr 32 t32Gens[j]!) '' {j | j < 6}) :=
    fun j => Subgroup.subset_closure ⟨j.val, j.2, (t32_perm_eq j.2).symm⟩
  have hw : onWitPerm i = signedProd (fun j : Fin 6 => permOfArr 32 t32Gens[j.val]!)
      (onWitWords[i.val]'(by have : onWitWords.length = 5 := rfl; omega)) := by
    apply Rep.unique (rep_of_validA (on_parts.2.1 i.val i.2))
    have hi : onWit[i.val]! = wordArr 32 t32Gens (onWitWords[i.val]'(by
        have : onWitWords.length = 5 := rfl; omega)) := by
      fin_cases i <;> rfl
    rw [hi]
    exact rep_wordArr on_parts.1 _
  rw [hw]
  exact signedProd_mem hgen _

end CFSG.ComponentClassification.GrSLit.L34Facts.FourCube
