module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3L
public import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4Merge
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55CrossParts
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop41
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop43
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop47
public import CFSG.Sporadic.Th.Simple
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PerfectCover
open scoped MatrixGroups

namespace StepH3L

theorem card_center_dvd_hopf {L X : Type} [Group L] [Group X] [Group.IsPerfect L]
    (e : L ⧸ center L ≃* X) : Nat.card (center L) ∣ Nat.card (hopfMultiplier X) := by
  let q : L →* X := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = center L := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (center L) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rw [← hker, ← map_hopfMultiplier_hopfLift q hq hker.le]
  exact Subgroup.card_map_dvd (H := hopfMultiplier X) (hopfLift q hq hker.le)

theorem odd_card_hopf_psl3 {K : Type} [Field K] [Fintype K] (hK3 : 3 ≤ Fintype.card K)
    (hodd : Odd (Fintype.card K)) : Odd (Nat.card (hopfMultiplier PSL(3, K))) := by
  have h4 : ¬(3 = 3 ∧ Fintype.card K = 4) := by
    rintro ⟨-, h⟩
    rw [h] at hodd
    exact (Nat.not_odd_iff_even.2 (by decide)) hodd
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier_of_three_le
    (n := 3) le_rfl hK3 h4
  rw [← Nat.card_congr (hopfMultiplierEquivGriess _).toEquiv, Nat.card_congr e.toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  exact Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 3 _)

end StepH3L

theorem noR_two_of_fl3d_closed {r : ℕ} {Y : Type} [Group Y] (hr : r.Prime) (hr2 : r ≠ 2)
    (hY : FL3d r Y) : NoR 2 Y := by
  intro L _ _ hL ⟨e⟩
  obtain ⟨f, hf, hLM⟩ := hY
  obtain ⟨K, _, _, hK, ⟨e'⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hLM
  have : Fintype K := Fintype.ofFinite K
  have hKc : Fintype.card K = r ^ f := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hodd : Odd (Fintype.card K) := by
    rw [hKc]
    exact (hr.odd_of_ne_two hr2).pow
  have hK3 : 3 ≤ Fintype.card K := by
    have h3 : 3 ≤ r := by
      have := hr.two_le
      rcases Nat.lt_or_ge r 3 with h | h
      · exact absurd (by omega : r = 2) hr2
      · exact h
    rw [hKc]
    calc 3 ≤ r ^ 1 := by rw [pow_one]; exact h3
      _ ≤ r ^ f := Nat.pow_le_pow_right hr.pos hf
  have : Group.IsPerfect L := hL.1
  let e2 : projectiveSL 3 K ≃* PSL(3, K) :=
    QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 3 K)
  have hd := StepH3L.card_center_dvd_hopf ((e.trans e').trans e2)
  intro h2
  exact (Nat.not_even_iff_odd.2 (StepH3L.odd_card_hopf_psl3 hK3 hodd))
    (even_iff_two_dvd.2 (h2.trans hd))

theorem ord3_fl3d_closed : Ord3 FL3d :=
  ord3_fl3d_of_noR fun _ _ _ _ hr hr2 _ hY => noR_two_of_fl3d_closed hr hr2 hY

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
