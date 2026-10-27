module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.ConjAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Sp62

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup
open scoped commutatorElement

section Certified


theorem false_of_two_covers {X : Type} [Group X] [Finite X] {L L' : Subgroup X}
    (hcomm : ⁅L, L'⁆ = ⊥) (hL : IsSp62Cover ↥L) (hL' : IsSp62Cover ↥L') {w : X}
    (hw : w * w = 1) (hwL : w ∈ normalizer (L : Set X)) (hwL' : w ∈ normalizer (L' : Set X))
    (hD : CentFacts ↥(centralizer ({w} : Set X))) : False := by
  let D : Subgroup X := centralizer ({w} : Set X)
  let A : Subgroup X := L ⊓ D
  let B : Subgroup X := L' ⊓ D
  have hAL : A ≤ L := by change L ⊓ D ≤ L; exact inf_le_left
  have hAD : A ≤ D := by change L ⊓ D ≤ D; exact inf_le_right
  have hBL' : B ≤ L' := by change L' ⊓ D ≤ L'; exact inf_le_left
  have hBD : B ≤ D := by change L' ⊓ D ≤ D; exact inf_le_right
  have hLcent : L ≤ centralizer (L' : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hA7 : 2 ^ 7 ∣ Nat.card ↥A := by
    have h := hL.two_pow_dvd_fixed (conjAut L w hwL) (conjAut_mul_self L hwL hw)
    rw [card_fixedSubgroup_conjAut L hwL] at h
    exact h
  have hB7 : 2 ^ 7 ∣ Nat.card ↥B := by
    have h := hL'.two_pow_dvd_fixed (conjAut L' w hwL') (conjAut_mul_self L' hwL' hw)
    rw [card_fixedSubgroup_conjAut L' hwL'] at h
    exact h
  let f : ↥A × ↥B →* X := MonoidHom.mk' (fun p => (p.1 : X) * (p.2 : X)) (by
    intro p q
    have hc : ((q.1 : ↥A) : X) * ((p.2 : ↥B) : X) =
        ((p.2 : ↥B) : X) * ((q.1 : ↥A) : X) :=
      (Subgroup.mem_centralizer_iff.mp (hLcent (hAL q.1.2)) ((p.2 : ↥B) : X)
        (hBL' p.2.2)).symm
    change ((p.1 : X) * (q.1 : X)) * ((p.2 : X) * (q.2 : X)) =
      ((p.1 : X) * (p.2 : X)) * ((q.1 : X) * (q.2 : X))
    calc ((p.1 : X) * (q.1 : X)) * ((p.2 : X) * (q.2 : X))
        = ((p.1 : X) * ((q.1 : X) * (p.2 : X))) * (q.2 : X) := by group
      _ = ((p.1 : X) * ((p.2 : X) * (q.1 : X))) * (q.2 : X) := by rw [hc]
      _ = ((p.1 : X) * (p.2 : X)) * ((q.1 : X) * (q.2 : X)) := by group)
  have hker_le : Nat.card f.ker ≤ Nat.card ↥(A ⊓ B) := by
    refine Nat.card_le_card_of_injective (fun x : f.ker =>
      (⟨((x.1).1 : X), ⟨(x.1).1.2, ?_⟩⟩ : ↥(A ⊓ B))) ?_
    · have hx : ((x.1).1 : X) * ((x.1).2 : X) = 1 := MonoidHom.mem_ker.mp x.2
      rw [mul_eq_one_iff_eq_inv.mp hx]
      exact B.inv_mem (x.1).2.2
    · intro x y hxy
      have h1 : ((x.1).1 : X) = ((y.1).1 : X) :=
        congrArg (fun z : ↥(A ⊓ B) => (z : X)) hxy
      have hx1 : (x.1).1 = (y.1).1 := Subtype.ext h1
      have hx2 : (x.1).2 = (y.1).2 := by
        apply Subtype.ext
        have hx : ((x.1).1 : X) * ((x.1).2 : X) = 1 := MonoidHom.mem_ker.mp x.2
        have hy : ((y.1).1 : X) * ((y.1).2 : X) = 1 := MonoidHom.mem_ker.mp y.2
        rw [mul_eq_one_iff_eq_inv'.mp hx, mul_eq_one_iff_eq_inv'.mp hy, h1]
      exact Subtype.ext (Prod.ext hx1 hx2)
  have hinf2 : Nat.card ↥(A ⊓ B) ≤ 2 := by
    let φ : ↥(A ⊓ B) → Subgroup.center ↥L := fun x =>
      ⟨⟨(x.1 : X), hAL x.2.1⟩,
        Subgroup.mem_center_iff.mpr fun g =>
          Subtype.ext (Subgroup.mem_centralizer_iff.mp (hLcent g.2) (x.1 : X) (hBL' x.2.2)).symm⟩
    have hinj : Function.Injective φ := by
      intro x y hxy
      have h1 : (x.1 : X) = (y.1 : X) :=
        congrArg (fun z : Subgroup.center ↥L => ((z : ↥L) : X)) hxy
      exact Subtype.ext h1
    exact le_trans (Nat.card_le_card_of_injective φ hinj) hL.card_center_le_two
  have hker2 : Nat.card f.ker ≤ 2 := le_trans hker_le hinf2
  have hkerpos : 0 < Nat.card f.ker :=
    Nat.card_pos_iff.mpr ⟨⟨1, by simp⟩, inferInstance⟩
  have hprod : Nat.card f.ker * Nat.card f.range = Nat.card ↥A * Nat.card ↥B := by
    have h := Subgroup.card_ker_mul_card_range f
    rwa [Nat.card_prod] at h
  have hdvd : (2 : ℕ) ^ 14 ∣ Nat.card ↥A * Nat.card ↥B := by
    have h := mul_dvd_mul hA7 hB7
    rwa [show (2 : ℕ) ^ 7 * 2 ^ 7 = 2 ^ 14 by norm_num] at h
  have h14 : (2 : ℕ) ^ 14 ∣ Nat.card f.ker * Nat.card f.range := by
    rw [hprod]
    exact hdvd
  have h13 : (2 : ℕ) ^ 13 ∣ Nat.card f.range := by
    have hk12 : Nat.card f.ker = 1 ∨ Nat.card f.ker = 2 := by omega
    rcases hk12 with hk | hk
    · rw [hk, one_mul] at h14
      exact (show (2 : ℕ) ^ 13 ∣ 2 ^ 14 by norm_num).trans h14
    · rw [hk] at h14
      have h' : 2 * 2 ^ 13 ∣ 2 * Nat.card f.range := by
        simpa only [show (2 : ℕ) ^ 14 = 2 * 2 ^ 13 by norm_num] using h14
      exact (mul_dvd_mul_iff_left (show (2 : ℕ) ≠ 0 by norm_num)).mp h'
  have hrange_le : f.range ≤ D := by
    rintro y ⟨p, rfl⟩
    change (p.1 : X) * (p.2 : X) ∈ centralizer ({w} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : (p.1 : X) * w = w * (p.1 : X) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hAD p.1.2)
    have h2 : (p.2 : X) * w = w * (p.2 : X) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hBD p.2.2)
    calc ((p.1 : X) * (p.2 : X)) * w
        = (p.1 : X) * ((p.2 : X) * w) := by group
      _ = (p.1 : X) * (w * (p.2 : X)) := by rw [h2]
      _ = ((p.1 : X) * w) * (p.2 : X) := by group
      _ = (w * (p.1 : X)) * (p.2 : X) := by rw [h1]
      _ = w * ((p.1 : X) * (p.2 : X)) := by group
  have h13D : (2 : ℕ) ^ 13 ∣ Nat.card ↥D :=
    h13.trans (Subgroup.card_dvd_of_le hrange_le)
  exact hD.not_dvd ((show (2 : ℕ) ^ 12 ∣ 2 ^ 13 by norm_num).trans h13D)

end Certified

end CFSG.EvenSporadicStandard.Co3Std.CentT
