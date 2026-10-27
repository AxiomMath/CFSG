module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem hbar_invsec (hInv : InvSec) {G : Type} [Group G] [Finite G] {z : G} {k : Kind}
    {S : Subgroup G} (hctx : Stage2Ctx G z k S) (H : Subgroup G) :
    ∀ x : HBar H, orderOf x = 2 → ∀ (Y : Type) [Group Y] [IsSimpleGroup Y],
      ¬ Group.IsSolvable Y → IsSection Y ↥(centralizer ({x} : Set (HBar H))) →
      KindFactorAll k Y := by
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
  exact hInv G z k S hctx (t : G) hx'ord Y hns h3

theorem invSecGroup_of_component (hInv : InvSec) {G : Type} [Group G] [Finite G] {z : G}
    {k : Kind} {S : Subgroup G} (hctx : Stage2Ctx G z k S) (H : Subgroup G)
    {J : Subgroup (HBar H)} (hJ : IsComponent J) : InvSecGroup k (↥J ⧸ center ↥J) :=
  ⟨HBar H, inferInstance, inferInstance, J, hJ, ⟨MulEquiv.refl _⟩, hbar_invsec hInv hctx H⟩

theorem InvSecGroup.of_equiv {k : Kind} {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : InvSecGroup k Y) : InvSecGroup k Y' := by
  obtain ⟨A, _, _, J, hJ, ⟨f⟩, hA⟩ := h
  exact ⟨A, inferInstance, inferInstance, J, hJ, ⟨f.trans e⟩, hA⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
