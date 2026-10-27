module

public import CFSG.GF2Type.Smith1979.CaseIIA6
public import CFSG.GF2Type.Smith1979.CaseIIA5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.Case2

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem mult_zmod2_cases (x : Multiplicative (ZMod 2)) : x = 1 ∨ x = Multiplicative.ofAdd 1 := by
  revert x
  decide

theorem mult_zmod2_mul_self (x : Multiplicative (ZMod 2)) : x * x = 1 := by
  revert x
  decide

theorem mult_zmod2_ofAdd_ne_one : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by
  decide

theorem eq_one_or_eq_of_mem_zpowers {x : S.O} (htt : t * t = 1) (hx : x ∈ zpowers t) :
    x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, zpow_two, htt, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, htt, one_zpow, one_mul]

namespace Data

variable (D : Data S g t)
include D

@[expose] def tR : ↥(Rbar S g t) := ⟨t, Lbar_le_Rbar D.ht D.ht⟩

theorem exists_chiR : ∃ χ : ↥(Rbar S g t) →* Multiplicative (ZMod 2),
    χ D.tR = Multiplicative.ofAdd 1 := by
  obtain ⟨χ, hχ⟩ := D.exists_chi
  exact ⟨χ.comp (Subgroup.inclusion (Rbar_le_centralizer D.H.conj_mem)), hχ⟩

theorem resR_mem_alt (hCE : S4.CentralExtInput.{u}) (a : ↥(Rbar S g t))
    (ha : (a : S.O) ∈ Nbar S g t) :
    D.resR a ∈ Sp.AltGrp (omegaU t) (Vsub g t) D.spData :=
  D.Gam0_le_Alt hCE ⟨⟨(a : S.O), ha⟩, rfl⟩

variable {χ : ↥(Rbar S g t) →* Multiplicative (ZMod 2)} (hχ : χ D.tR = Multiplicative.ofAdd 1)
include hχ

theorem pair_inj (u v : ↥(Rbar S g t)) (h1 : D.resR u = D.resR v) (h2 : χ u = χ v) : u = v := by
  have hw1 : D.resR (u⁻¹ * v) = 1 := by
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  have hw2 : χ (u⁻¹ * v) = 1 := by
    rw [map_mul, map_inv, h2, inv_mul_cancel]
  rcases (D.resR_eq_one_iff (u⁻¹ * v)).mp hw1 with h | h
  · have : u⁻¹ * v = 1 := Subtype.ext h
    exact inv_mul_eq_one.mp this
  · have : u⁻¹ * v = D.tR := Subtype.ext h
    rw [this, hχ] at hw2
    exact absurd hw2 mult_zmod2_ofAdd_ne_one

theorem chi_surjective : Function.Surjective χ := by
  intro x
  rcases mult_zmod2_cases x with rfl | rfl
  · exact ⟨1, map_one χ⟩
  · exact ⟨D.tR, hχ⟩

theorem index_ker : χ.ker.index = 2 := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective χ (D.chi_surjective hχ),
    Subgroup.card_top]
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_ker (hCE : S4.CentralExtInput.{u}) : Nat.card χ.ker = 1344 := by
  have h := Subgroup.card_mul_index χ.ker
  rw [D.index_ker hχ, D.card_Rbar hCE] at h
  omega

theorem Nbar_commute (hCE : S4.CentralExtInput.{u}) (a b : ↥(Rbar S g t))
    (ha : (a : S.O) ∈ Nbar S g t) (hb : (b : S.O) ∈ Nbar S g t) : a * b = b * a := by
  refine D.pair_inj hχ _ _ ?_ ?_
  · rw [map_mul, map_mul]
    exact Sp.IsF.mul_comm' D.spData (D.resR_mem_alt hCE a ha).1 (D.resR_mem_alt hCE b hb).1
  · rw [map_mul, map_mul, mul_comm]

theorem Nbar_mul_self (hCE : S4.CentralExtInput.{u}) (a : ↥(Rbar S g t))
    (ha : (a : S.O) ∈ Nbar S g t) : a * a = 1 := by
  refine D.pair_inj hχ _ _ ?_ ?_
  · rw [map_mul, map_one]
    exact Sp.IsF.mul_self' D.spData (D.resR_mem_alt hCE a ha).1
  · rw [map_mul, map_one]
    exact mult_zmod2_mul_self _

end Data

@[expose] noncomputable def Rprime (S : Setting G) (g : G) (t : S.O)
    (χ : ↥(Rbar S g t) →* Multiplicative (ZMod 2)) : Subgroup S.O :=
  χ.ker.map (Rbar S g t).subtype

theorem mem_Rprime {χ : ↥(Rbar S g t) →* Multiplicative (ZMod 2)} {r : S.O} :
    r ∈ Rprime S g t χ ↔ ∃ hr : r ∈ Rbar S g t, χ ⟨r, hr⟩ = 1 := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨hr, h⟩
    exact ⟨⟨r, hr⟩, h, rfl⟩

theorem Rprime_le_Rbar {χ : ↥(Rbar S g t) →* Multiplicative (ZMod 2)} :
    Rprime S g t χ ≤ Rbar S g t := fun _ hr => (mem_Rprime.mp hr).1

namespace Data

variable (D : Data S g t)
include D

variable {χ : ↥(Rbar S g t) →* Multiplicative (ZMod 2)} (hχ : χ D.tR = Multiplicative.ofAdd 1)
include hχ

theorem t_notMem_Rprime : t ∉ Rprime S g t χ := by
  intro h
  obtain ⟨hr, h1⟩ := mem_Rprime.mp h
  have : (⟨t, hr⟩ : ↥(Rbar S g t)) = D.tR := rfl
  rw [this, hχ] at h1
  exact mult_zmod2_ofAdd_ne_one h1

theorem Rprime_sup : Rprime S g t χ ⊔ zpowers t = Rbar S g t := by
  have htR : t ∈ Rbar S g t := Lbar_le_Rbar D.ht D.ht
  refine le_antisymm (sup_le Rprime_le_Rbar ((zpowers_le).mpr htR)) fun r hr => ?_
  by_cases h : χ ⟨r, hr⟩ = 1
  · exact Subgroup.mem_sup_left (mem_Rprime.mpr ⟨hr, h⟩)
  · have h1 : χ ⟨r, hr⟩ = Multiplicative.ofAdd 1 := (mult_zmod2_cases _).resolve_left h
    have hrt : r * t ∈ Rbar S g t := mul_mem hr htR
    have h2 : χ ⟨r * t, hrt⟩ = 1 := by
      have : (⟨r * t, hrt⟩ : ↥(Rbar S g t)) = ⟨r, hr⟩ * D.tR := rfl
      rw [this, map_mul, h1, hχ]
      exact mult_zmod2_mul_self _
    have h3 : r * t ∈ Rprime S g t χ := mem_Rprime.mpr ⟨hrt, h2⟩
    have h4 : r = (r * t) * t⁻¹ := by group
    rw [h4]
    exact mul_mem (Subgroup.mem_sup_left h3) (Subgroup.mem_sup_right (inv_mem (mem_zpowers t)))

theorem Rprime_inf : Rprime S g t χ ⊓ zpowers t = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  rcases eq_one_or_eq_of_mem_zpowers D.htt' hx.2 with h | h
  · rw [h]
    exact one_mem _
  · exact absurd (h ▸ hx.1) (D.t_notMem_Rprime hχ)

theorem card_Rprime (hCE : S4.CentralExtInput.{u}) : Nat.card (Rprime S g t χ) = 1344 := by
  have e := Subgroup.equivMapOfInjective χ.ker (Rbar S g t).subtype Subtype.val_injective
  rw [← D.card_ker hχ hCE]
  exact (Nat.card_congr e.toEquiv).symm

theorem card_Rprime_inf_Nbar (hCE : S4.CentralExtInput.{u}) :
    Nat.card ↥(Rprime S g t χ ⊓ Nbar S g t) = 8 := by
  let χN : ↥(Nbar S g t) →* Multiplicative (ZMod 2) :=
    χ.comp (Subgroup.inclusion Nbar_le_Rbar)
  have hsurj : Function.Surjective χN := by
    intro x
    rcases mult_zmod2_cases x with rfl | rfl
    · exact ⟨1, map_one _⟩
    · exact ⟨D.tN, hχ⟩
  have h1 : χN.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective χN hsurj, Subgroup.card_top,
      Nat.card_eq_fintype_card]
    decide
  have h2 : Nat.card χN.ker = 8 := by
    have h := Subgroup.card_mul_index χN.ker
    rw [h1, D.card_Nbar hCE] at h
    omega
  have hmap : χN.ker.map (Nbar S g t).subtype = Rprime S g t χ ⊓ Nbar S g t := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨mem_Rprime.mpr ⟨Nbar_le_Rbar n.2, hn⟩, n.2⟩
    · rintro ⟨hx1, hx2⟩
      obtain ⟨hr, h⟩ := mem_Rprime.mp hx1
      exact ⟨⟨x, hx2⟩, h, rfl⟩
  rw [← hmap, ← h2]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective χN.ker (Nbar S g t).subtype
    Subtype.val_injective).toEquiv).symm

end Data

end CFSG.GF2Type.Smith1979.Case2
