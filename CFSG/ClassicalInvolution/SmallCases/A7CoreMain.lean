module

public import CFSG.ClassicalInvolution.SmallCases.A7CoreChain
public import CFSG.ClassicalInvolution.SmallCases.A7CoreBigEnd

public section

namespace CFSG.ClassicalInvolution.A7Core

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Hat2A7R CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

section Core

variable {F : Type} [Group F] [Finite F]

theorem core {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z) {J : Subgroup F} {t : F}
    (hJ : IsClassical2A7 ⊤ J t) (hne : t ≠ z) (htK : t ∈ Subgroup.normalizer (K : Set F))
    {v : F} (hvJ : v ∈ J) (hv2 : IsPGroup 2 (Subgroup.zpowers v)) (hv4 : 4 ≤ orderOf v)
    (hvz : v * z = z * v) (hvK : v * v ∈ Subgroup.normalizer (K : Set F)) :
    v ∈ Subgroup.normalizer (K : Set F) := by
  by_contra hv
  obtain ⟨s, hs⟩ := hv2.exists_card_eq
  rw [Nat.card_zpowers] at hs
  have hs2 : 2 ≤ s := by
    by_contra hlt
    have : 2 ^ s ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases Nat.eq_or_lt_of_le hs2 with h2 | h3
  · have hv4' : orderOf v = 4 := by rw [hs, ← h2]; norm_num
    exact hv (core_four hK hJ hne hvJ hv4' hvz hvK)
  · have h8 : 8 ≤ orderOf v := by
      rw [hs]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) h3
    exact big_order_contradiction hK hJ hne htK hvJ hv2 h8 hvz hvK hv

theorem mem_normalizer_of_core {J K : Subgroup F} {t z : F} (hJ : IsClassical2A7 ⊤ J t)
    (hK : IsClassical2A7 ⊤ K z) (htK : t ∈ Subgroup.normalizer (K : Set F)) {y : F}
    (hyJ : y ∈ J) (hy2 : IsPGroup 2 (Subgroup.zpowers y)) (hyz : y * z = z * y) :
    y ∈ Subgroup.normalizer (K : Set F) := by
  by_cases htz : t = z
  · subst htz
    by_cases hJK : J = K
    · subst hJK
      exact Subgroup.le_normalizer hyJ
    · exact (twin_facts hJ hK hJK).2.1 hyJ
  · by_contra hy
    obtain ⟨n, hn1, hn2⟩ := AscFusion.exists_pow_not_mem_sq_mem hy2 hy
    have hvJ : y ^ (2 ^ n) ∈ J := J.pow_mem hyJ _
    have hv2 : IsPGroup 2 (Subgroup.zpowers (y ^ (2 ^ n))) :=
      hy2.to_le (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) _))
    have hv4 : 4 ≤ orderOf (y ^ (2 ^ n)) := four_le_orderOf_of_not_mem hJ hvJ hv2 htK hn1
    have hvz : y ^ (2 ^ n) * z = z * y ^ (2 ^ n) :=
      (Commute.pow_left (show Commute y z from hyz) _).eq
    exact hn1 (core hK hJ htz htK hvJ hv2 hv4 hvz (by rwa [← pow_two]))

end Core

section Statements


theorem prop37x : Prop37x := by
  intro F _ _ _ _ J K t z hJ hK _ htK y hyJ hy2 _ hyz
  exact mem_normalizer_of_core hJ hK htK hyJ hy2 hyz

theorem a7FusionCore : A7FusionCore :=
  a7FusionCore_of_prop37x prop37x

theorem prop366i : Prop366i :=
  prop366i_of_prop37x prop37x

theorem a7Omega5 : A7Omega5 :=
  a7Omega5_of_prop37x prop37x

end Statements

end CFSG.ClassicalInvolution.A7Core
