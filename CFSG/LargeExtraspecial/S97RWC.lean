module

public import CFSG.LargeExtraspecial.S97RQuot

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.CGT.Timmesfeld75
open CFSG.Open (IsElemAbelian)

theorem map_conj_eq_of_forall_conj {H : Type*} [Group H] [Finite H] {N : Subgroup H} {x : H}
    (h : ∀ n ∈ N, x * n * x⁻¹ ∈ N) : N.map (MulAut.conj x).toMonoidHom = N :=
  Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨n, hn, rfl⟩; exact h n hn)
    (card_map_of_injective (MulAut.conj x).injective).ge

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {k : S.M} {O : Subgroup S.O}

theorem X97_le_Mbar : X97 S g k ≤ S.Mbar :=
  sup_le (S.Lbar_le_Mbar g) (S.Lbar_le_Mbar _)

namespace Hyp97

variable (X : Hyp97 S g k O)
include X

variable {j : G} (hj : S.Lbar j ≤ X97 S g k)
include hj

theorem mem_normalizer_of_mk {w : X97 S g k}
    (hw : (w : Q97 S g k) ∈ normalizer (Tj97 S g k j : Set (Q97 S g k))) :
    (w : S.O) ∈ normalizer ((S.Lbar j ⊔ O : Subgroup S.O) : Set S.O) := by
  refine mem_normalizer_iff.mpr fun v => ?_
  have hLOX : S.Lbar j ⊔ O ≤ X97 S g k := sup_le hj X.le
  by_cases hv : v ∈ X97 S g k
  · have e : (w : Q97 S g k) * ((⟨v, hv⟩ : X97 S g k) : Q97 S g k) * (w : Q97 S g k)⁻¹ =
        ((w * ⟨v, hv⟩ * w⁻¹ : X97 S g k) : Q97 S g k) := rfl
    have h1 := X.mk_mem_Tj97_iff hj ⟨v, hv⟩
    have h2 := X.mk_mem_Tj97_iff hj (w * ⟨v, hv⟩ * w⁻¹)
    rw [← e] at h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1 h2
    rw [← h1, ← h2]
    exact mem_normalizer_iff.mp hw _
  · constructor
    · exact fun h => absurd (hLOX h) hv
    · intro h
      exfalso
      apply hv
      have := mul_mem (mul_mem (inv_mem w.2) (hLOX h)) w.2
      rwa [show (w : S.O)⁻¹ * ((w : S.O) * v * (w : S.O)⁻¹) * w = v by group] at this

theorem Tj97_weaklyClosed (Hj : Hyp4 S j) (Cj : Cons311 S j) (y : Q97 S g k)
    (hle : conjSubgroup y (Tj97 S g k j) ≤ normalizer (Tj97 S g k j : Set (Q97 S g k))) :
    conjSubgroup y (Tj97 S g k j) = Tj97 S g k j := by
  induction y using QuotientGroup.induction_on with
  | H x =>
    have hL : (S.Lbar j).map (MulAut.conj (x : S.O)).toMonoidHom ≤
        normalizer ((S.Lbar j ⊔ O : Subgroup S.O) : Set S.O) := by
      rintro _ ⟨l, hl, rfl⟩
      show (x : S.O) * l * (x : S.O)⁻¹ ∈ _
      have hwX : (x : S.O) * l * (x : S.O)⁻¹ ∈ X97 S g k := mul_mem (mul_mem x.2 (hj hl))
        (inv_mem x.2)
      have hmem : ((⟨_, hwX⟩ : X97 S g k) : Q97 S g k) ∈
          conjSubgroup (x : Q97 S g k) (Tj97 S g k j) := by
        rw [X.mk_mem_conj_Tj97_iff hj]
        exact ⟨l, mem_sup_left hl, rfl⟩
      have h2 := hle hmem
      exact X.mem_normalizer_of_mk hj (w := ⟨_, hwX⟩) h2
    have hLx := map_conj_eq_of_le_normalizer Hj Cj X97_le_Mbar hj X.le X.normal X.isPGroup
      x.2 hL
    have hOx : O.map (MulAut.conj (x : S.O)).toMonoidHom = O :=
      map_conj_eq_of_forall_conj (X.normal x x.2)
    ext w
    induction w using QuotientGroup.induction_on with
    | H u =>
      rw [X.mk_mem_conj_Tj97_iff hj, X.mk_mem_Tj97_iff hj, Subgroup.map_sup, hLx, hOx]

end Hyp97

theorem Tj97_isElemAbelian {j : G} (Hj : Hyp4 S j) : IsElemAbelian 2 (Tj97 S g k j) := by
  have hL : IsElemAbelian 2 ((S.Lbar j).subgroupOf (X97 S g k)) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩
    · exact Lbar_comm S Hj.conj_mem (mem_subgroupOf.mp a.2) (mem_subgroupOf.mp b.2)
    · refine Subtype.ext ?_
      rw [Subgroup.coe_pow, pow_two]
      exact mul_self_of_mem_Lbar S Hj.conj_mem (mem_subgroupOf.mp hx)
  exact isElemAbelian_map_of_hom hL (QuotientGroup.mk' (CFSG.pCore 2 ↥(X97 S g k)))

namespace Hyp97

variable (X : Hyp97 S g k O)
include X

theorem card_Tj97_mul {j : G} (hj : S.Lbar j ≤ X97 S g k) :
    Nat.card (Tj97 S g k j) * Nat.card (S.Lbar j ⊓ O : Subgroup S.O) = Nat.card (S.Lbar j) := by
  set f : S.Lbar j →* Q97 S g k := (QuotientGroup.mk' _).comp (Subgroup.inclusion hj)
  have hrange : f.range = Tj97 S g k j := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range, Tj97]
  have hker : f.ker = O.subgroupOf (S.Lbar j) := by
    ext y
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact X.mk_eq_one_iff (x := Subgroup.inclusion hj y)
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hrange, hker, ← inf_subgroupOf_left,
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv, mul_comm] at hcard
  exact hcard

variable {j : G} (hj : S.Lbar j ≤ X97 S g k)
include hj

theorem Tj97_isWC (Hj : Hyp4 S j) (Cj : Cons311 S j)
    (hTI : ∀ x ∈ X97 S g k, (S.Lbar j ⊔ O).map (MulAut.conj x).toMonoidHom = S.Lbar j ⊔ O ∨
      (S.Lbar j ⊔ O).map (MulAut.conj x).toMonoidHom ⊓ (S.Lbar j ⊔ O) ≤ O) :
    IsWC (Tj97 S g k j) :=
  isWC_of_corBHyp (corBHyp_of_ti_of_weaklyClosed (Tj97_isElemAbelian Hj)
    (fun y => X.Tj97_isTI hj hTI y⁻¹) (fun y h => X.Tj97_weaklyClosed hj Hj Cj y⁻¹ h))

end Hyp97

end CFSG.LargeExtraspecial.S9
