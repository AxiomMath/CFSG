module

public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.OddCore
public import CFSG.GroupTheory.OddInversion
public import TauCeti.GroupTheory.Index.Two

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.OmegaPlus

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S5 CFSG.LargeExtraspecial.S7

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

private theorem conj_eq_inv_of_fixedPointFree (H : Hyp4 S g) {p : S.O}
    (hp : p ∈ S.Lbar g) (hfix : ∀ y ∈ Obar S, p * y = y * p → y = 1) :
    ∀ y ∈ Obar S, p * y * p⁻¹ = y⁻¹ := by
  classical
  have hObarOdd : Odd (Nat.card (Obar S)) := by
    rw [S7.card_Obar]
    exact S5.odd_card_timmesfeldOddCore S.Mbar
  have hMN : S.Mbar ≤ Subgroup.normalizer (Obar S : Set S.O) :=
    Subgroup.le_normalizer_iff.mpr fun s hs z hz => S7.conj_mem_Obar hs hz
  have hpN : p ∈ Subgroup.normalizer (Obar S : Set S.O) := hMN (S.Lbar_le_Mbar g hp)
  intro y hy
  by_cases hp1 : p = 1
  · subst hp1
    have hy1 : y = 1 := hfix y hy (by rw [one_mul, mul_one])
    rw [hy1, inv_one, one_mul, mul_one]
  · have hp2 : p * p = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem hp
    have hord : orderOf p = 2 := orderOf_eq_prime (by rwa [pow_two]) hp1
    obtain ⟨⟨c, j⟩, ⟨hc, hj⟩, hcj⟩ :=
      (CFSG.OddInversion.fixed_mul_inverted_bijOn hObarOdd hord hpN).surjOn hy
    have hc1 : c = 1 := by
      refine hfix c (Subgroup.mem_inf.mp hc).1 ?_
      exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2).symm
    have hyj : y = j := by
      rw [← hcj, hc1]
      exact one_mul j
    rw [hyj]
    exact hj.2

theorem isElemAbelian_Obar (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {p : S.O}
    (hp : p ∈ S.Lbar g) (hfix : ∀ y ∈ Obar S, p * y = y * p → y = 1) :
    CFSG.Open.IsElemAbelian 3 (Obar S) := by
  classical
  have hObarOdd : Odd (Nat.card (Obar S)) := by
    rw [S7.card_Obar]
    exact S5.odd_card_timmesfeldOddCore S.Mbar
  have hnorm : ∀ s ∈ S.Lbar g, ∀ z ∈ Obar S, s * z * s⁻¹ ∈ Obar S :=
    fun s hs z hz => S7.conj_mem_Obar (S.Lbar_le_Mbar g hs) hz
  have hinv : ∀ y ∈ Obar S, p * y * p⁻¹ = y⁻¹ := conj_eq_inv_of_fixedPointFree H hp hfix
  have hab : IsMulCommutative (Obar S) := TauCeti.isMulCommutative_of_conj_eq_inv hinv
  have hp2 : p * p = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem hp
  have hpinv : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp2
  have hMN : S.Mbar ≤ Subgroup.normalizer (Obar S : Set S.O) :=
    Subgroup.le_normalizer_iff.mpr fun s hs z hz => S7.conj_mem_Obar hs hz
  refine ⟨hab, ?_⟩
  obtain ⟨a, haL, b, hbL, ha1, hb1, hab_ne⟩ :=
    S5.exists_ne_one_ne_one_ne (A := S.Lbar g) (by
      have h := S5.four_le_card_Lbar H C
      omega)
  obtain ⟨t, htL, ht1, htp⟩ : ∃ t ∈ S.Lbar g, t ≠ 1 ∧ t ≠ p := by
    by_cases ha : a = p
    · exact ⟨b, hbL, hb1, fun h => hab_ne (ha.trans h.symm)⟩
    · exact ⟨a, haL, ha1, ha⟩
  have ht2 : t * t = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem htL
  have htN : t ∈ Subgroup.normalizer (Obar S : Set S.O) := hMN (S.Lbar_le_Mbar g htL)
  have htord : orderOf t = 2 := orderOf_eq_prime (by rwa [pow_two]) ht1
  have hptL : p * t ∈ S.Lbar g := (S.Lbar g).mul_mem hp htL
  have hpt1 : p * t ≠ 1 := by
    intro h
    apply htp
    calc
      t = p⁻¹ * (p * t) := by group
      _ = p := by rw [h, hpinv, mul_one]
  intro x hx
  obtain ⟨⟨c, j⟩, ⟨hc, hj⟩, hcj⟩ :=
    (CFSG.OddInversion.fixed_mul_inverted_bijOn hObarOdd htord htN).surjOn hx
  have hcO : c ∈ Obar S := (Subgroup.mem_inf.mp hc).1
  have hc3 : c ^ 3 = 1 :=
    pow_three_of_mem_inf_centralizer H hNo C S7.Obar_le_Mbar hObarOdd hnorm htL ht1 hc
  have hjO : j ∈ Obar S := hj.1
  have hjinv : t * j * t⁻¹ = j⁻¹ := hj.2
  have hpj : p * j * p⁻¹ = j⁻¹ := hinv j hjO
  have hptj : (p * t) * j * (p * t)⁻¹ = j := by
    rw [show (p * t) * j * (p * t)⁻¹ = p * (t * j * t⁻¹) * p⁻¹ by group, hjinv,
      show p * j⁻¹ * p⁻¹ = (p * j * p⁻¹)⁻¹ by group, hpj, inv_inv]
  have hjpt : j ∈ Obar S ⊓ Subgroup.centralizer ({p * t} : Set S.O) := by
    refine Subgroup.mem_inf.mpr ⟨hjO, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg (fun z => z * (p * t)) hptj
    simpa [mul_assoc] using h.symm
  have hj3 : j ^ 3 = 1 :=
    pow_three_of_mem_inf_centralizer H hNo C S7.Obar_le_Mbar hObarOdd hnorm hptL hpt1 hjpt
  have hcomm : Commute c j :=
    congrArg Subtype.val (hab.is_comm.comm ⟨c, hcO⟩ ⟨j, hjO⟩)
  calc
    x ^ 3 = (c * j) ^ 3 := by rw [hcj.symm]
    _ = c ^ 3 * j ^ 3 := hcomm.mul_pow 3
    _ = 1 := by rw [hc3, hj3, mul_one]

end CFSG.GF2Type.Smith1979.OmegaPlus

end
