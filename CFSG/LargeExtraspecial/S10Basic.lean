module

public import CFSG.LargeExtraspecial.S10Iso
public import CFSG.LargeExtraspecial.S7Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

structure Hyp10 (S : Setting G) (g : G) (t : S.O) : Prop where
  H : Hyp4 S g
  hNo : NoA2 S g
  C : Cons311 S g
  ht : t ∈ S.Lbar g
  ht1 : t ≠ 1
  hR : Rbar S g t ≠ S.Lbar g
  hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t
  hVQ : ¬ V S g t ≤ S.Qa g
  hΩ : OmegaCase H C ht ht1 hVQ
  h4 : finrank (ZMod 2) (Vt S g t) = 4
  plus : ∃ W : Submodule (ZMod 2) (Vt S g t), finrank (ZMod 2) W = 2 ∧
    ∀ w ∈ W, w ≠ 0 → w ∈ orbitOf (RmodN S g t) (aV ht)

theorem plusType4_iff {t : S.O} {ht : t ∈ S.Lbar g} {Q : QuadraticForm (ZMod 2) (Vt S g t)}
    (hsing : ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht))) :
    PlusType4 Q ↔ ∃ W : Submodule (ZMod 2) (Vt S g t), finrank (ZMod 2) W = 2 ∧
      ∀ w ∈ W, w ≠ 0 → w ∈ orbitOf (RmodN S g t) (aV ht) := by
  constructor
  · rintro ⟨W, hW, hWs⟩
    exact ⟨W, hW, fun w hw hw0 => (hsing w hw0).mp (hWs w hw)⟩
  · rintro ⟨W, hW, hWs⟩
    refine ⟨W, hW, fun w hw => ?_⟩
    by_cases hw0 : w = 0
    · rw [hw0, map_zero]
    · exact (hsing w hw0).mpr (hWs w hw hw0)

namespace Hyp10

variable {t : S.O} (X : Hyp10 S g t)
include X

theorem haQ : g * S.z * g⁻¹ ∈ S.QG := X.H.conj_mem

theorem card_LmodN : Nat.card (LmodN S g t) = 4 := by
  rw [S7.card_LmodN_of_omegaCase X.H X.C X.ht X.ht1 X.hΩ, X.h4]
  rfl

theorem t_mem_Abar : t ∈ S.Lbar g ⊓ Nbar S g t := ⟨X.ht, self_mem_Nbar X.H X.ht⟩

theorem card_Abar : Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) = 2 ^ (S.width - 3) := by
  have h1 := card_Lbar_eq_mul X.haQ X.ht (t := t)
  rw [X.card_LmodN, X.C.card_Lbar] at h1
  have h3 : 3 ≤ S.width := X.H.two_lt_width
  have e : 2 ^ (S.width - 1) = 4 * 2 ^ (S.width - 3) := by
    rw [show S.width - 1 = (S.width - 3) + 2 by omega, pow_add]
    ring
  rw [e] at h1
  omega

theorem orderOf_t : orderOf t = 2 := by
  refine orderOf_eq_prime ?_ X.ht1
  rw [_root_.sq]
  exact S4.mul_self_of_mem_Lbar S X.haQ X.ht

theorem five_le_width : 5 ≤ S.width := by
  have hcard := X.card_Abar
  have hle : zpowers t ≤ S.Lbar g ⊓ Nbar S g t := (zpowers_le).mpr X.t_mem_Abar
  have hlt : zpowers t < S.Lbar g ⊓ Nbar S g t := lt_of_le_of_ne hle (Ne.symm X.hA)
  have h2 : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, X.orderOf_t]
  have hdvd := Subgroup.card_dvd_of_le hle
  have hne : Nat.card (zpowers t) ≠ Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) := by
    intro heq
    exact hlt.ne (Subgroup.eq_of_le_of_card_ge hle heq.ge)
  rw [h2, hcard] at hdvd hne
  have h3 : 3 ≤ S.width := X.H.two_lt_width
  obtain ⟨k, hk⟩ : ∃ k, S.width - 3 = k := ⟨_, rfl⟩
  rw [hk] at hdvd hne
  rcases k with _ | _ | k
  · norm_num at hdvd
  · exact absurd (pow_one 2).symm hne
  · omega

end Hyp10

end CFSG.LargeExtraspecial.S10
