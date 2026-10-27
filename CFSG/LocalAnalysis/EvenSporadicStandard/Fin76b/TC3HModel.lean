module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Model
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3HCheck

public section

namespace CFSG.EvenSporadicStandard.Fin76b.TC3H

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.HypOne
open CFSG.Sporadic.Schreier.PairNative

variable {n : ℕ} {P : Subgroup (Equiv.Perm (Fin n))} {pg : Array Table}
  {gg : ℕ → Equiv.Perm (Fin n)} {sift : Table → Bool}

theorem sqxW_iff {x : Array ℕ} {xg : Equiv.Perm (Fin n)} (hx : CFSG.Monster.B.Co2.Rep n x xg)
    {w : List (Array ℕ)} {g : Equiv.Perm (Fin n)} (hw : RepW n w g) :
    sqxW n x w = true ↔ g * xg * (g * xg) = 1 := by
  have key : ∀ i : Fin n, evR w (x[evR w (x[(i : ℕ)]!)]!) = (g (xg (g (xg i))) : ℕ) := by
    intro i
    rw [hx i, hw (xg i), hx (g (xg i)), hw (xg (g (xg i)))]
  rw [sqxW, CFSG.Monster.B.Co2.allLt_iff]
  constructor
  · intro h
    refine Equiv.ext fun i => Fin.ext ?_
    have h1 := h i.val i.isLt
    rw [beq_iff_eq, key i] at h1
    exact h1
  · intro h i hi
    rw [beq_iff_eq, key ⟨i, hi⟩]
    have := congrArg (fun f : Equiv.Perm (Fin n) => (f ⟨i, hi⟩ : ℕ)) h
    exact this

theorem sqrtOK_spec (hD : GroupData n P pg gg sift) {u : Table} {U : Equiv.Perm (Fin n)}
    (hu : Rep n u U) (hU2 : U ^ 2 = 1) (hUn : ∀ p ∈ P, U * p * U⁻¹ ∈ P) {a y : Table}
    {A : Equiv.Perm (Fin n)} (ha : Rep n a A) (h : sqrtOK n sift u a y = true) :
    ∃ Y ∈ P ⊔ zpowers U, Y * Y = A := by
  simp only [sqrtOK, Bool.and_eq_true] at h
  obtain ⟨⟨hperm, hR⟩, hsq⟩ := h
  have ry := rep_tp hperm
  exact ⟨tp n y, mem_R_of_sift hD hU2 hUn hu ry hR,
    (tblEq_iff_eq (Rep.compT ry ry) ha).1 hsq⟩

theorem outerBetaFor_of_zOK (hD : GroupData n P pg gg sift) {u : Table} {U : Equiv.Perm (Fin n)}
    (hu : Rep n u U) (hU2 : U ^ 2 = 1) (hUn : ∀ p ∈ P, U * p * U⁻¹ ∈ P)
    {R : Subgroup (Equiv.Perm (Fin n))} (hR : R = P ⊔ zpowers U) {e : ↥R ≃* MulAut ↥P}
    (he : IsAutModel e) (hcard : Nat.card ↥R = 2 * Nat.card ↥P) {b z : Table}
    (hb : permOK n b = true) (hbP : tp n b ∈ P) (hz : zOK n sift u b z = true)
    (hno : ∀ d : ↥P, (d : Equiv.Perm (Fin n)) * tp n b = tp n b * d →
      (d : Equiv.Perm (Fin n)) * tp n z * ((d : Equiv.Perm (Fin n)) * tp n z) ≠ 1) :
    OuterBetaFor ↥P ⟨tp n b, hbP⟩ := by
  subst hR
  simp only [zOK, Bool.and_eq_true, Bool.not_eq_true'] at hz
  obtain ⟨⟨⟨hzp, hzs⟩, hzR⟩, hzc⟩ := hz
  have rb := rep_tp hb
  have rz := rep_tp hzp
  refine OuterBetaFor.of_model le_sup_left he hcard (mem_R_of_sift hD hU2 hUn hu rz hzR)
    (fun hP => ?_) ((commTT_iff rz rb).1 hzc) hno
  rw [← hD.sift z _ rz] at hP
  rw [hP] at hzs
  exact Bool.noConfusion hzs

end CFSG.EvenSporadicStandard.Fin76b.TC3H
