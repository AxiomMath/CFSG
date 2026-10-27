module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TReduce
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7RCore

public section

namespace CFSG.ClassicalInvolution.Hat2A7T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Hat2A7R CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.AscFusion

section Normalizing

variable {F : Type} [Group F] [Finite F]

theorem exists_orderOf_four_of_two_group {R : Subgroup F} {u : F} (hR2 : IsPGroup 2 R)
    (hu2 : orderOf u = 2) (hcard : 2 < Nat.card R) (huniq : ∀ x ∈ R, orderOf x = 2 → x = u) :
    ∃ a ∈ R, orderOf a = 4 := by
  by_contra hcon
  push Not at hcon
  have hsub : ∀ x ∈ R, x = 1 ∨ x = u := by
    intro x hx
    obtain ⟨k, hk⟩ := hR2.exists_orderOf_eq_pow (⟨x, hx⟩ : R)
    rw [Subgroup.orderOf_mk] at hk
    rcases Nat.lt_or_ge k 2 with hlt | hge
    · interval_cases k
      · left
        rw [pow_zero, orderOf_eq_one_iff] at hk
        exact hk
      · right
        rw [pow_one] at hk
        exact huniq x hx hk
    · exfalso
      have h4 : 4 ≤ orderOf x := by
        rw [hk]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hge
      obtain ⟨j, hj⟩ := exists_pow_orderOf_eq_four (y := x)
        (hR2.to_le (Subgroup.zpowers_le.mpr hx)) h4
      exact hcon (x ^ j) (R.pow_mem hx j) hj
  have hle : R ≤ Subgroup.zpowers u := by
    intro x hx
    rcases hsub x hx with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers u
  have := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, hu2] at this
  omega

end Normalizing


section Normalizing2

variable {F : Type} [Group F] [Finite F] [IsSimpleGroup F]

theorem commOrEq_of_normalizes (core : A7FusionCore) (hnab : ∃ a b : F, a * b ≠ b * a)
    (IH : ClassicalCommuteBelow F) (P1 : ClassicalQuasisimple F) {K : Subgroup F} {z : F}
    (hK : IsClassical2A7 ⊤ K z) {g : F}
    (hzJ : z ∈ Subgroup.normalizer ((K.map (MulAut.conj g).toMonoidHom : Subgroup F) : Set F)) :
    CommOrEq K (K.map (MulAut.conj g).toMonoidHom) := by
  by_contra hbad
  have hZ : CenterTrivial F := fun x hx => center_trivial_of_simple hnab x hx
  set J : Subgroup F := K.map (MulAut.conj g).toMonoidHom with hJdef
  set u : F := g * z * g⁻¹ with hudef
  have hJ : IsClassical2A7 ⊤ J u := isClassical2A7_map_conj hK g
  have hu2 : orderOf u = 2 := hJ.orderOf_eq_two
  have hz2 : orderOf z = 2 := hK.orderOf_eq_two
  have hzz : z * z = 1 := hK.mul_self
  have hune : u ≠ z := by
    intro h
    apply hbad
    have hJz : J ≤ Subgroup.centralizer ({z} : Set F) := by
      rw [← h]
      exact hJ.le_centralizer
    exact commOrEq_of_le_centralizer hZ IH hz2 ⟨z, hK⟩ ⟨u, hJ⟩ hK.le_centralizer hJz
  obtain ⟨R, hRJ, hR2, hR8, hRz⟩ := exists_two_subgroup_centralizing hJ.witness hzJ hzz
  obtain ⟨huR, huniq⟩ := two_subgroup_unique_involution hJ hRJ hR2 (by omega)
  obtain ⟨a, haR, ha4⟩ := exists_orderOf_four_of_two_group hR2 hu2 (by omega) huniq
  have haz : a * z = z * a := (hRz a haR).symm
  have hD2 : ∀ Q : Subgroup F, IsClassical2A7 ⊤ Q z → (∃ g' : F, Q = conjSub g' K) →
      u ∈ Subgroup.normalizer (Q : Set F) := fun Q hQ _ =>
    mem_normalizer_of_commute_orderOf_four hJ hQ (hRJ haR) ha4 haz
  have htK : u ∈ Subgroup.normalizer (K : Set F) := hD2 K hK ⟨1, (conjSub_one K).symm⟩
  obtain ⟨y, hyR, hyK⟩ : ∃ y ∈ R, y ∉ Subgroup.normalizer (K : Set F) := by
    by_contra hcon
    push Not at hcon
    have hRN : R ≤ Subgroup.normalizer (K : Set F) := hcon
    have hKu : K ≤ Subgroup.centralizer ({u} : Set F) :=
      le_centralizer_of_two_group_normalizes hK (P1 K z hK) hRN hR2 (by omega) huR huniq
    exact hbad (commOrEq_of_le_centralizer hZ IH hu2 ⟨z, hK⟩ ⟨u, hJ⟩ hKu hJ.le_centralizer)
  have hy2 : IsPGroup 2 (Subgroup.zpowers y) := hR2.to_le (Subgroup.zpowers_le.mpr hyR)
  obtain ⟨n, hn1, hn2⟩ := exists_pow_not_mem_sq_mem hy2 hyK
  have hvJ : y ^ (2 ^ n) ∈ J := J.pow_mem (hRJ hyR) _
  have hv2 : IsPGroup 2 (Subgroup.zpowers (y ^ (2 ^ n))) :=
    hy2.to_le (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) _))
  have hv4 : 4 ≤ orderOf (y ^ (2 ^ n)) := four_le_orderOf_of_not_mem hJ hvJ hv2 htK hn1
  have hvz : y ^ (2 ^ n) * z = z * y ^ (2 ^ n) :=
    (Commute.pow_left (show Commute y z from (hRz y hyR).symm) _).eq
  exact hn1 (core F hnab K z hK J u hJ ⟨g, rfl⟩ hune hzJ hD2 _ hvJ hv2 hv4 hvz hn2)

end Normalizing2

@[expose] def TwinSwapExclusion : Prop :=
  ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
    ClassicalCommuteBelow F → ClassicalQuasisimple F →
    ∀ (K : Subgroup F) (z : F), IsClassical2A7 ⊤ K z →
      ¬ (Subgroup.centralizer ({z} : Set F) ≤ Subgroup.normalizer (K : Set F)) →
      ¬ Odd (Nat.card (cliqueSet K)) →
      ¬ Odd ((Subgroup.centralizer ({z} : Set F) ⊓ Subgroup.normalizer (K : Set F)).relIndex
        (Subgroup.centralizer ({z} : Set F))) →
      ∀ g : F, (g * z * g⁻¹) * z = z * (g * z * g⁻¹) →
        z ∉ Subgroup.normalizer ((K.map (MulAut.conj g).toMonoidHom : Subgroup F) : Set F) →
        CommOrEq K (K.map (MulAut.conj g).toMonoidHom)

theorem twinNoBadPairEven_of_core_of_swap (core : A7FusionCore)
    (hS : TwinSwapExclusion) : TwinNoBadPairEven := by
  intro F _ _ _ hnab IH P1 K z hK ht hm hodd g hg
  by_cases hz : z ∈ Subgroup.normalizer ((K.map (MulAut.conj g).toMonoidHom : Subgroup F) : Set F)
  · exact commOrEq_of_normalizes core hnab IH P1 hK hz
  · exact hS F hnab IH P1 K z hK ht hm hodd g hg hz

theorem twinExclusion_of_core_of_swap
    (GS : GoldschmidtStronglyClosedExponent) (core : A7FusionCore) (hS : TwinSwapExclusion) :
    TwinExclusion :=
  twinExclusion_of_inputs GS (twinNoBadPairEven_of_core_of_swap core hS)

theorem twinPairExclusion_of_core_of_swap
    (GS : GoldschmidtStronglyClosedExponent) (core : A7FusionCore) (hS : TwinSwapExclusion) :
    TwinPairExclusion := by
  intro F _ _ _ hnab IH P1 K K' z hK hK' hne hcomm
  by_cases ht : Subgroup.centralizer ({z} : Set F) ≤ Subgroup.normalizer (K : Set F)
  · exact TightSetting.false_of_goldschmidt hnab GS
      ⟨⟨hK, ht⟩, center_trivial_of_simple hnab, IH, P1⟩
  · exact twinExclusion_of_core_of_swap GS core hS F hnab IH P1 K z hK ht

end CFSG.ClassicalInvolution.Hat2A7T
