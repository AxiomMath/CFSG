module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Kind

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

namespace LiftInvsec

theorem kindFactor_ly_of_section_C {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (hctx : Stage2Ctx G z Kind.ly S) {Y : Type} [Group Y] [IsSimpleGroup Y]
    (hns : ¬ Group.IsSolvable Y) (h : IsSection Y ↥(Cen z)) : KindFactor Kind.ly Y := by
  have hbar := isSection_bar z hns h
  have hd := hctx.data
  cases hd with
  | ly hs =>
    obtain ⟨n, hn, hS⟩ := hs
    exact ⟨n, by omega, by omega, isSection_alt_of_cover hS.cover hns hbar⟩

theorem invSec_ly {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (hctx : Stage2Ctx G z Kind.ly S) {x : G} (hx2 : orderOf x = 2) {Y : Type} [Group Y]
    [IsSimpleGroup Y] (hns : ¬ Group.IsSolvable Y)
    (h : IsSection Y ↥(centralizer ({x} : Set G))) : KindFactorAll Kind.ly Y := by
  have hz2 := hctx.orderOf_z
  have hd := hctx.data
  cases hd with
  | ly hs =>
    obtain ⟨n, hn, hS⟩ := hs
    obtain ⟨c, hc⟩ := isConj_iff.mp (hS.one_class z x hz2 hx2)
    obtain ⟨e⟩ := cenConj_nonempty c hc
    exact (kindFactor_ly_of_section_C hctx hns (IsSection.of_equiv e h)).all

end LiftInvsec

theorem aframe_invsec {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (hctx : Stage2Ctx G z Kind.ly S) (H : Subgroup G) :
    ∀ x : HBar H, orderOf x = 2 → ∀ (Y : Type) [Group Y] [IsSimpleGroup Y],
      ¬ Group.IsSolvable Y → IsSection Y ↥(centralizer ({x} : Set (HBar H))) →
      KindFactorAll Kind.ly Y := by
  intro x hx2 Y _ _ hns h
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥H)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, pow_two] at this
  obtain ⟨t, ht2, htx⟩ := exists_involution_lift (pPrimeCore 2 ↥H) hodd hxx
  have hx'2 : (t : G) * (t : G) = 1 := congrArg (fun y : ↥H => (y : G)) ht2
  have hx'1 : (t : G) ≠ 1 := by
    intro h1
    have h2 : t = 1 := Subtype.ext h1
    rw [h2] at htx
    have h3 : x = 1 := htx.symm
    rw [h3, orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  have hx'ord : orderOf (t : G) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx'2) hx'1
  obtain ⟨D, f, hD, hf⟩ := csec_of_sig4B (z := (t : G)) (pPrimeCore 2 ↥H) t.2 hx'2 hodd
  have hzs : zSec (t : G) H t.2 (pPrimeCore 2 ↥H) = x := htx
  rw [← hzs] at h
  have h3 := IsSection.of_le_le hD (IsSection.of_surjective f hf h)
  exact LiftInvsec.invSec_ly hctx hx'ord hns h3

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
