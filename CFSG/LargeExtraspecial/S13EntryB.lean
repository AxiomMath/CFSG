module

public import CFSG.LargeExtraspecial.S13EntryA
public import CFSG.LargeExtraspecial.S10EightG
public import CFSG.LargeExtraspecial.S13Lin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem exists_ne_one_of_ne_bot {X : Type*} [Group X] {H : Subgroup X} (hH : H ≠ ⊥) :
    ∃ x ∈ H, x ≠ 1 := by
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hH
  exact ⟨x, hx, fun h => hx1 (Subtype.ext h)⟩

section Ten

variable {P : Subgroup S.O} (hPM : P ≤ S.Mbar) (hP1 : P ≠ ⊥) (hP3 : IsPGroup 3 P)
  (hPn : ∀ m ∈ S.Mbar, ∀ p ∈ P, m * p * m⁻¹ ∈ P) (X : Hyp10 S g t) (h7 : 7 ≤ S.width)
  (hirr : ¬ S.IsReducible)
include hPM hP1 hP3 hPn X h7 hirr

theorem commute_t_of : ∀ p ∈ P, p * t = t * p := by
  have hK3 := card_eq_three_of hPM hP1 hP3 hPn X.H X.hNo X.C (by omega)
  have hfpf := fixFree_of hP1 hPn hirr
  rcases comm_or_inv hK3 (fun p hp => hPn t (S.Lbar_le_Mbar g X.ht) p hp) with h | h
  · exact h
  · exfalso
    obtain ⟨k, hk, hk1⟩ := exists_ne_one_of_ne_bot hP1
    have hk3 := pow_three_eq_one hK3 hk
    have hkk3 : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, hk3]; rfl
    have hfix : ∀ v, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0 :=
      fun v hv => fix_eq_zero hK3 hfpf hk hk1 v hv
    have htt : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 := by
      rw [← Subgroup.coe_mul, mul_self_of_mem_Lbar S X.haQ X.ht]; rfl
    have hinv : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) * (k : S.Qt ≃ₗ[ZMod 2] S.Qt) =
        (k : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      have e := h k hk
      have e2 : t * k = k⁻¹ * t := by rw [← e]; group
      rw [← Subgroup.coe_mul, e2, Subgroup.coe_mul, Subgroup.coe_inv]
    have hdim := two_mul_finrank_commSpace_of_inverts hkk3 hfix htt hinv
    rw [finrank_commSpace_t X, S.finrank_Qt_eq_two_mul_width] at hdim
    omega

theorem le_Rbar_of : P ≤ Rbar S g t := by
  have hK3 := card_eq_three_of hPM hP1 hP3 hPn X.H X.hNo X.C (by omega)
  have hfpf := fixFree_of hP1 hPn hirr
  have hct := commute_t_of hPM hP1 hP3 hPn X h7 hirr
  have hnorm : ∀ p ∈ P, ∀ r ∈ Rbar S g t, p * r * p⁻¹ ∈ Rbar S g t := by
    intro p hp r hr
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp (hPM hp)
    have e : S.ρ m * t * (S.ρ m)⁻¹ = t := by rw [hct _ hp]; group
    have hR := Rbar_conj (S := S) (g := g) m t
    rw [e] at hR
    rw [hR]
    exact ⟨r, hr, rfl⟩
  by_contra hle
  have hbot : P ⊓ Rbar S g t = ⊥ := by
    have hdvd := Subgroup.card_dvd_of_le (inf_le_left : P ⊓ Rbar S g t ≤ P)
    rw [hK3] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      apply hle
      have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left : P ⊓ Rbar S g t ≤ P)
        (by rw [h, hK3])
      exact heq ▸ inf_le_right
  have hcomm : ∀ p ∈ P, ∀ r ∈ Rbar S g t, p * r = r * p := by
    intro p hp r hr
    have h1 : p * r * p⁻¹ * r⁻¹ ∈ P ⊓ Rbar S g t := by
      refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (hnorm p hp r hr) (inv_mem hr)⟩
      have := hPn r (Rbar_le_Mbar hr) p⁻¹ (inv_mem hp)
      have e : p * r * p⁻¹ * r⁻¹ = p * (r * p⁻¹ * r⁻¹) := by group
      rw [e]
      exact mul_mem hp this
    rw [hbot, mem_bot] at h1
    calc p * r = p * r * p⁻¹ * r⁻¹ * (r * p) := by group
      _ = r * p := by rw [h1, one_mul]
  apply cl_conj_z_ne_zero S X.haQ X.H.conj_ne
  apply hfpf
  intro k hk
  apply fix_of_mem_normalizer X.H
  rw [mem_normalizer_iff]
  intro y
  have hc : ∀ y ∈ S.Lbar g, k * y = y * k := fun y hy => hcomm k hk y (Lbar_le_Rbar X.ht hy)
  constructor
  · intro hy
    rw [hc y hy, mul_inv_cancel_right]
    exact hy
  · intro hy
    have h2 := hc _ hy
    have e2 : k * y * k⁻¹ = y := by
      have : k * (k * y * k⁻¹) = k * y := by
        rw [h2]; group
      exact mul_left_cancel this
    rw [e2] at hy
    exact hy

theorem eq_commutator_of (hCE : CentralExtInput.{u}) {Xb Yb : Subgroup S.O}
    (D : Dec108 X Xb Yb) : P = ⁅Yb, Yb⁆ := by
  have hK3 := card_eq_three_of hPM hP1 hP3 hPn X.H X.hNo X.C (by omega)
  have hle := (D.dec.isOp_commutator hCE X).le_of P (le_Rbar_of hPM hP1 hP3 hPn X h7 hirr) hP3
    (fun r hr p hp => hPn r (Rbar_le_Mbar hr) p hp)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [D.dec.card_commutator, hK3])

theorem Ebar_eq_of (hCE : CentralExtInput.{u}) {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb) :
    Ebar S g P = S.Lbar g ⊓ Xb := by
  have hPeq := eq_commutator_of hPM hP1 hP3 hPn X h7 hirr hCE D
  obtain ⟨d, hd, hd1⟩ := exists_ne_one_of_ne_bot hP1
  ext x
  rw [mem_Ebar, mem_inf]
  constructor
  · rintro ⟨hx, hc⟩
    exact ⟨hx, D.mem_Xb_of_commute hCE (hPeq ▸ hd) hd1 hx (hc d hd).symm⟩
  · rintro ⟨hx, hxX⟩
    refine ⟨hx, fun k hk => ?_⟩
    rw [hPeq] at hk
    exact (D.dec.comm x hxX k ((D.dec.mem_commutator_iff).mp hk).1).symm

end Ten

end CFSG.LargeExtraspecial.S13
