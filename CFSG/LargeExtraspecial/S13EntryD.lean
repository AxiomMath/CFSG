module

public import CFSG.LargeExtraspecial.S13EntryC
public import CFSG.LargeExtraspecial.S10EightL
public import CFSG.LargeExtraspecial.S10FourN
public import CFSG.LargeExtraspecial.S13EntryB
public import CFSG.LargeExtraspecial.S13Hyp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

section Ten

variable {P : Subgroup S.O} (hPM : P ≤ S.Mbar) (hP1 : P ≠ ⊥) (hP3 : IsPGroup 3 P)
  (hPn : ∀ m ∈ S.Mbar, ∀ p ∈ P, m * p * m⁻¹ ∈ P) (X : Hyp10 S g t) (h7 : 7 ≤ S.width)
  (hirr : ¬ S.IsReducible)
include hPM hP1 hP3 hPn X h7 hirr

theorem Nbar_commute_of : ∀ x ∈ Nbar S g t, ∀ k ∈ P, k * x = x * k := by
  have hK3 := card_eq_three_of hPM hP1 hP3 hPn X.H X.hNo X.C (by omega)
  have hfpf := fixFree_of hP1 hPn hirr
  have hPR := le_Rbar_of hPM hP1 hP3 hPn X h7 hirr
  have hbot : P ⊓ Nbar S g t = ⊥ := by
    have hdvd := Subgroup.card_dvd_of_le (inf_le_left : P ⊓ Nbar S g t ≤ P)
    rw [hK3] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left : P ⊓ Nbar S g t ≤ P)
        (by rw [h, hK3])
      apply cl_conj_z_ne_zero S X.haQ X.H.conj_ne
      refine hfpf _ fun k hk => ?_
      have hk' : k ∈ P ⊓ Nbar S g t := by rw [heq]; exact hk
      exact (Subgroup.mem_inf.mp hk').2.2 _ (cl_a_mem_Vt X.ht)
  intro x hx k hk
  have h1 : x * k * x⁻¹ * k⁻¹ ∈ P ⊓ Nbar S g t := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem (hPn x (Rbar_le_Mbar hx.1) k hk) (inv_mem hk), ?_⟩
    have e : x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) := by group
    rw [e]
    exact mul_mem hx (conj_mem_Nbar_of_mem_Rbar X.haQ (hPR hk) (inv_mem hx))
  rw [hbot, mem_bot] at h1
  calc k * x = (x * k * x⁻¹ * k⁻¹)⁻¹ * (x * k) := by group
    _ = x * k := by rw [h1, inv_one, one_mul]

theorem hyp13_of
    (hCE : CentralExtInput.{u}) (hNo : S11.NoA2All S) (hP : NoPGL25 S g) :
    Hyp13 S g P := by
  have hK3 := card_eq_three_of hPM hP1 hP3 hPn X.H X.hNo X.C (by omega)
  have hfpf := fixFree_of hP1 hPn hirr
  have h104 := timmesfeld_10_4_self hCE X h7
  obtain ⟨Xb, Yb, D⟩ := exists_dec108 hCE X h104 h7
  have hE := Ebar_eq_of hPM hP1 hP3 hPn X h7 hirr hCE D
  have hL2 := D.two_mul_card_Ebar hCE
  refine ⟨X.H, X.hNo, X.C, hNo, hirr, h7, hPM, hK3, hPn, hfpf, ?_, ?_, ?_⟩
  · intro τ hτ hτ1
    rw [hE] at hτ ⊢
    rcases (D.timmesfeld_10_8_one hCE hP hτ hτ1).1 with hR | hY
    · left
      rintro _ ⟨h, rfl, hτh⟩
      exact Ebar_le_of_Rbar_eq X D hL2.symm hR hτh
    · exact Or.inr hY
  · intro m hm hN e he
    rw [hE] at hN he ⊢
    exact D.timmesfeld_10_8_three hCE hP h7 hm hN e he
  · obtain ⟨k, hk, hb, -⟩ := X.exists_pair
    have hNc := (timmesfeld_4_7_b hCE X.H X.hNo X.C X.ht X.ht1 X.hVQ (Or.inr X.hΩ) hk hb).2.2
    refine ⟨t, X, Nbar_commute_of hPM hP1 hP3 hPn X h7 hirr,
      fun x hx y hy => hNc (Subgroup.commutator_mem_commutator hx hy), ?_⟩
    rcases timmesfeld_10_5 hCE X h104 with h6 | hk'
    · omega
    · exact hk'

end Ten

end CFSG.LargeExtraspecial.S13
