module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WCheck
public import Certificates.Data.CFSGNative.CosetTable.Enum

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.CosetTable CFSG.EvenSporadicStandard.Fin76b

@[expose] def normCenEnumCheck (n m : ℕ) (g gE : Array Table)
    (L LE : Array Table × Array ℕ × Array ℕ) (size sizeE : ℕ) (cT : Table) : Bool :=
  enumOK n m g L size && enumOK n m gE LE sizeE && permOK n cT &&
    LE.1.any (fun y => tblEq n cT y) &&
    gE.all (fun x => g.any (fun x' => tblEq n x x')) &&
    g.all (fun m' => LE.1.all (fun y =>
      LE.1.any (fun y' => tblEq n (compT n m' y) (compT n y' m')) &&
        LE.1.any (fun y'' => tblEq n (compT n y m') (compT n m' y'')))) &&
    L.1.all (fun T => !(gE.all (fun y => commTT n T y)) || LE.1.any (fun y => tblEq n T y)) &&
    LE.1.all (fun T => !(gE.all (fun y => commTT n T y)) || tblEq n T (idT n) || tblEq n T cT)

@[expose] def normCenCheck (n m : ℕ) (g gE : Array Table) (size sizeE : ℕ) (cT : Table) : Bool :=
  normCenEnumCheck n m g gE (mulClosureS n m g 4000) (mulClosureS n m gE 4000) size sizeE cT

theorem normCenEnumCheck_spec {n m size sizeE : ℕ} (hn : n < 2 ^ 32) {g gE : Array Table}
    {L LE : Array Table × Array ℕ × Array ℕ} {cT : Table}
    (h : normCenEnumCheck n m g gE L LE size sizeE cT = true) :
    closure (tp n '' {x | x ∈ gE}) ≤ closure (tp n '' {x | x ∈ g}) ∧
    Nat.card ↥(closure (tp n '' {x | x ∈ g})) = size ∧
    Nat.card ↥(closure (tp n '' {x | x ∈ gE})) = sizeE ∧
    (∀ x ∈ closure (tp n '' {x | x ∈ g}), ∀ y ∈ closure (tp n '' {x | x ∈ gE}),
      x * y * x⁻¹ ∈ closure (tp n '' {x | x ∈ gE})) ∧
    (∀ x ∈ closure (tp n '' {x | x ∈ g}),
      (∀ y ∈ closure (tp n '' {x | x ∈ gE}), x * y = y * x) →
        x ∈ closure (tp n '' {x | x ∈ gE})) ∧
    (∀ y ∈ closure (tp n '' {x | x ∈ gE}),
      (∀ y' ∈ closure (tp n '' {x | x ∈ gE}), y * y' = y' * y) → y = 1 ∨ y = tp n cT) ∧
    Rep n cT (tp n cT) ∧ tp n cT ∈ closure (tp n '' {x | x ∈ gE}) := by
  simp only [normCenEnumCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hM, hE⟩, hcT⟩, hcTE⟩, hsub⟩, hnorm⟩, hcen⟩, hz⟩ := h
  obtain ⟨hMs, hMsize⟩ := enumOK_spec hn hM
  obtain ⟨hEs, hEsize⟩ := enumOK_spec hn hE
  have hcTrep : Rep n cT (tp n cT) := rep_tp hcT
  have hgens : ∀ x ∈ gE, Rep n x (tp n x) := fun x hx => rep_tp (hEs.perm x hx)
  have hggens : ∀ x ∈ g, Rep n x (tp n x) := fun x hx => rep_tp (hMs.perm x hx)
  have hEgen : ∀ x ∈ gE, tp n x ∈ closure (tp n '' {x | x ∈ gE}) :=
    fun x hx => subset_closure ⟨x, hx, rfl⟩
  have hle : closure (tp n '' {x | x ∈ gE}) ≤ closure (tp n '' {x | x ∈ g}) := by
    rw [closure_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [Array.all_eq_true'] at hsub
    have := hsub x hx
    rw [Array.any_eq_true'] at this
    obtain ⟨x', hx', hxx'⟩ := this
    have heq : tp n x = tp n x' := (tblEq_iff_eq (hgens x hx) (hggens x' hx')).1 hxx'
    rw [SetLike.mem_coe, heq]
    exact subset_closure ⟨x', hx', rfl⟩
  refine ⟨hle, ?_, ?_, ?_, ?_, ?_, hcTrep, ?_⟩
  · rw [hMs.card, hMsize]
  · rw [hEs.card, hEsize]
  ·
    have hgn : ∀ x ∈ g, tp n x ∈ normalizer
        ((closure (tp n '' {x | x ∈ gE}) : Subgroup (Equiv.Perm (Fin n))) :
          Set (Equiv.Perm (Fin n))) := by
      intro x hx
      rw [mem_normalizer_iff]
      intro y
      rw [Array.all_eq_true'] at hnorm
      have hxn := hnorm x hx
      rw [Array.all_eq_true'] at hxn
      constructor
      · intro hy
        obtain ⟨Ty, hTy, hrep⟩ := hEs.cover_mem hy
        have h2 := hxn Ty hTy
        rw [Bool.and_eq_true] at h2
        obtain ⟨y', hy', hyy'⟩ := Array.any_eq_true'.1 h2.1
        obtain ⟨hy'rep, hy'mem⟩ := hEs.rep_mem hy'
        have hq := (tblEq_iff_eq (Rep.compT (hggens x hx) hrep)
          (Rep.compT hy'rep (hggens x hx))).1 hyy'
        have : tp n x * y * (tp n x)⁻¹ = tablePerm n y' := by
          rw [hq, mul_inv_cancel_right]
        rw [this]
        exact hy'mem
      · intro hy
        obtain ⟨T1, hT1, hrep1⟩ := hEs.cover_mem hy
        have h2 := hxn T1 hT1
        rw [Bool.and_eq_true] at h2
        obtain ⟨y'', hy'', hyy''⟩ := Array.any_eq_true'.1 h2.2
        obtain ⟨hy''rep, hy''mem⟩ := hEs.rep_mem hy''
        have hq := (tblEq_iff_eq (Rep.compT hrep1 (hggens x hx))
          (Rep.compT (hggens x hx) hy''rep)).1 hyy''
        have h3 : y = tablePerm n y'' := by
          have : tp n x * y = tp n x * tablePerm n y'' := by
            calc tp n x * y = (tp n x * y * (tp n x)⁻¹) * tp n x := by group
              _ = tp n x * tablePerm n y'' := hq
          exact mul_left_cancel this
        rw [h3]
        exact hy''mem
    have hMle : closure (tp n '' {x | x ∈ g}) ≤ normalizer
        ((closure (tp n '' {x | x ∈ gE}) : Subgroup (Equiv.Perm (Fin n))) :
          Set (Equiv.Perm (Fin n))) := by
      rw [closure_le]
      rintro _ ⟨x, hx, rfl⟩
      exact hgn x hx
    intro x hx y hy
    have := (mem_normalizer_iff.1 (hMle hx) y).1 hy
    exact this
  ·
    intro x hx hcomm
    obtain ⟨T, hT, hrep⟩ := hMs.cover_mem hx
    rw [Array.all_eq_true'] at hcen
    have h2 := hcen T hT
    have hall : (gE.all fun y => commTT n T y) = true := by
      rw [Array.all_eq_true']
      intro y hy
      exact (commTT_iff hrep (hgens y hy)).2 (hcomm _ (hEgen y hy))
    rw [hall, Bool.not_true, Bool.false_or, Array.any_eq_true'] at h2
    obtain ⟨y, hy, hTy⟩ := h2
    obtain ⟨hyrep, hymem⟩ := hEs.rep_mem hy
    have := (tblEq_iff_eq hrep hyrep).1 hTy
    rw [this]
    exact hymem
  ·
    intro y hy hcomm
    obtain ⟨T, hT, hrep⟩ := hEs.cover_mem hy
    rw [Array.all_eq_true'] at hz
    have h2 := hz T hT
    have hall : (gE.all fun y' => commTT n T y') = true := by
      rw [Array.all_eq_true']
      intro y' hy'
      exact (commTT_iff hrep (hgens y' hy')).2 (hcomm _ (hEgen y' hy'))
    rw [hall, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h2
    rcases h2 with h2 | h2
    · left
      exact (tblEq_idT_iff hn hrep).1 h2
    · right
      exact (tblEq_iff_eq hrep hcTrep).1 h2
  ·
    obtain ⟨y, hy, hcy⟩ := Array.any_eq_true'.1 hcTE
    obtain ⟨hyrep, hymem⟩ := hEs.rep_mem hy
    have := (tblEq_iff_eq hcTrep hyrep).1 hcy
    rw [this]
    exact hymem

theorem normCenCheck_spec {n m size sizeE : ℕ} (hn : n < 2 ^ 32) {g gE : Array Table}
    {cT : Table} (h : normCenCheck n m g gE size sizeE cT = true) :
    closure (tp n '' {x | x ∈ gE}) ≤ closure (tp n '' {x | x ∈ g}) ∧
    Nat.card ↥(closure (tp n '' {x | x ∈ g})) = size ∧
    Nat.card ↥(closure (tp n '' {x | x ∈ gE})) = sizeE ∧
    (∀ x ∈ closure (tp n '' {x | x ∈ g}), ∀ y ∈ closure (tp n '' {x | x ∈ gE}),
      x * y * x⁻¹ ∈ closure (tp n '' {x | x ∈ gE})) ∧
    (∀ x ∈ closure (tp n '' {x | x ∈ g}),
      (∀ y ∈ closure (tp n '' {x | x ∈ gE}), x * y = y * x) →
        x ∈ closure (tp n '' {x | x ∈ gE})) ∧
    (∀ y ∈ closure (tp n '' {x | x ∈ gE}),
      (∀ y' ∈ closure (tp n '' {x | x ∈ gE}), y * y' = y' * y) → y = 1 ∨ y = tp n cT) ∧
    Rep n cT (tp n cT) ∧ tp n cT ∈ closure (tp n '' {x | x ∈ gE}) :=
  normCenEnumCheck_spec hn h

end CFSG.EvenSporadicStandard.M12Std.Yosh
