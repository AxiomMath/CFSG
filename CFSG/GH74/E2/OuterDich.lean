
module

public import CFSG.GH74.E2.OuterDichBase

public import CFSG.GH74.E2.FrattiniRank
public import CFSG.GH74.SectionalRank
public import CFSG.Dihedral.DisconnectedInvolutionGraph.QuaternionCoordinateEquiv
public meta import Mathlib
public import Certificates.Certificate5014

public section

namespace CFSG.GH74.E2

open Subgroup

theorem card_mulAut_q8 :
    Nat.card (MulAut (QuaternionGroup 2)) = 24 :=
  Certificates.certificate5014

theorem caseA_of_card_sixteen
    {S : Type*} [Group S] [Finite S] (hS2 : IsPGroup 2 S)
    {Q T : Subgroup S} (hQn : Q.Normal) (hQ8 : Nonempty (↥Q ≃* QuaternionGroup 2))
    (hT16 : Nat.card T = 16)
    (hC : Nat.card ↥(T ⊓ Subgroup.centralizer (Q : Set S)) = 2) :
    ∀ x : S, ∃ y ∈ T, y⁻¹ * x ∈ Subgroup.centralizer (Q : Set S) := by
  classical
  have := hQn
  obtain ⟨e⟩ := hQ8
  let ρ : S →* MulAut Q := MulAut.conjNormal
  have hker : ρ.ker = Subgroup.centralizer (Q : Set S) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro h q hq
      have h1 := congrArg (fun σ : MulAut Q => (σ ⟨q, hq⟩ : S)) h
      simp only [ρ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc q * x = (x * q * x⁻¹) * x := by rw [h1]
        _ = x * q := by group
    · intro h
      ext ⟨q, hq⟩
      simp only [ρ, MulAut.conjNormal_apply, MulAut.one_apply]
      rw [← h q hq]
      group
  have hcardAut : Nat.card (MulAut Q) = 24 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact card_mulAut_q8
  have hr2 : IsPGroup 2 ρ.range := hS2.of_surjective ρ.rangeRestrict
    ρ.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hr2
  have hdvd : Nat.card ρ.range ∣ 24 := hcardAut ▸ Subgroup.card_subgroup_dvd_card ρ.range
  have hn3 : n ≤ 3 := by
    rw [hn] at hdvd
    by_contra h
    push Not at h
    have : 2 ^ 4 ∣ 24 := (pow_dvd_pow 2 h).trans hdvd
    omega
  let ρT : T →* MulAut Q := ρ.comp T.subtype
  have hkerT : ρT.ker = (Subgroup.centralizer (Q : Set S)).subgroupOf T := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hker, MonoidHom.mem_ker]
    rfl
  have hkcard : Nat.card ρT.ker = 2 := by
    rw [hkerT, ← hC]
    have h1 : (T ⊓ Subgroup.centralizer (Q : Set S)).subgroupOf T =
        (Subgroup.centralizer (Q : Set S)).subgroupOf T := Subgroup.inf_subgroupOf_left _ _
    rw [← h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hTcard := Subgroup.card_ker_mul_card_range ρT
  rw [hkcard, hT16] at hTcard
  have hRT : Nat.card ρT.range = 8 := by omega
  have hle : ρT.range ≤ ρ.range := by
    rintro _ ⟨y, rfl⟩
    exact ⟨(y : S), rfl⟩
  have hcard_ge : Nat.card ρ.range ≤ Nat.card ρT.range := by
    rw [hn, hRT]
    calc 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn3
      _ = 8 := by norm_num
  have heq : ρT.range = ρ.range := Subgroup.eq_of_le_of_card_ge hle hcard_ge
  intro x
  have hx : ρ x ∈ ρT.range := by rw [heq]; exact ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hx
  refine ⟨(y : S), y.2, ?_⟩
  rw [← hker, MonoidHom.mem_ker, map_mul, map_inv]
  have : ρ (y : S) = ρ x := hy
  rw [this, inv_mul_cancel]

end CFSG.GH74.E2
