module

public import CFSG.GF2Type.Smith1979.IdxFourHBasic
public import CFSG.LargeExtraspecial.S4Weak

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem card_le_two_mul_card_inf {P : Subgroup G} {j z : G} (hzz : z * z = 1)
    (hz : ∀ p ∈ P, p * z = z * p) (hconj : ∀ p ∈ P, p * j * p⁻¹ = j ∨ p * j * p⁻¹ = j * z) :
    Nat.card P ≤ 2 * Nat.card (P ⊓ centralizer ({j} : Set G) : Subgroup G) := by
  set D : Subgroup P := (centralizer ({j} : Set G)).subgroupOf P with hD
  have hmem : ∀ p : P, p ∈ D ↔ (p : G) * j * (p : G)⁻¹ = j := fun p => by
    rw [hD, mem_subgroupOf, mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  have hidx : D.index ≤ 2 := by
    by_cases h : ∃ a : P, a ∉ D
    · obtain ⟨a, ha⟩ := h
      have haj : (a : G) * j * (a : G)⁻¹ = j * z :=
        (hconj a a.2).resolve_left ((hmem a).not.mp ha)
      have h2 : D.index = 2 := by
        rw [index_eq_two_iff_exists_notMem_and]
        refine ⟨a, ha, fun b => ?_⟩
        by_cases hb : b ∈ D
        · exact Or.inr hb
        · left
          have hbj : (b : G) * j * (b : G)⁻¹ = j * z :=
            (hconj b b.2).resolve_left ((hmem b).not.mp hb)
          have hbz : (b : G) * z * (b : G)⁻¹ = z := by rw [hz b b.2, mul_inv_cancel_right]
          rw [hmem]
          calc ((b * a : P) : G) * j * ((b * a : P) : G)⁻¹
              = (b : G) * ((a : G) * j * (a : G)⁻¹) * (b : G)⁻¹ := by simp [mul_assoc]
            _ = ((b : G) * j * (b : G)⁻¹) * ((b : G) * z * (b : G)⁻¹) := by rw [haj]; group
            _ = j := by rw [hbj, hbz, mul_assoc, hzz, mul_one]
      exact h2.le
    · have htop : D = ⊤ := eq_top_iff.mpr fun x _ => by_contra fun hx => h ⟨x, hx⟩
      rw [htop, index_top]
      norm_num
  have hc : Nat.card D = Nat.card (P ⊓ centralizer ({j} : Set G) : Subgroup G) := by
    rw [hD, ← inf_subgroupOf_left]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  calc Nat.card P = D.index * Nat.card D := (index_mul_card D).symm
    _ ≤ 2 * Nat.card D := Nat.mul_le_mul_right _ hidx
    _ = _ := by rw [hc]

theorem exists_two_subgroup_centralizer (hw : S.width = 6)
    (hstab : ∀ v : S.Qt, v ≠ 0 → S.q v = 0 → 2 ^ 8 ∣ Nat.card (stab S v))
    {v₀ : S.Qt} (hv₀ : v₀ ≠ 0) (hv₀q : S.q v₀ = 0)
    {j : G} (hj : j ∈ S.QG) (hj2 : j * j = 1) (hj1 : j ≠ 1) :
    ∃ P : Subgroup G, P ≤ Subgroup.centralizer ({j} : Set G) ∧ IsPGroup 2 P ∧
      2 ^ 20 ≤ Nat.card P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv0, hvq, hvj⟩ : ∃ v : S.Qt, v ≠ 0 ∧ S.q v = 0 ∧ (j ≠ S.z → v = S.cl j) := by
    by_cases hjz : j = S.z
    · exact ⟨v₀, hv₀, hv₀q, fun h => absurd hjz h⟩
    · refine ⟨S.cl j, ?_, ?_, fun _ => rfl⟩
      · rw [Ne, S.cl_eq_zero_iff hj]
        tauto
      · rw [S.q_cl_eq_zero_iff hj, pow_two]
        exact hj2
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := stab S v) 2 (n := 8)
    (hstab v hv0 hvq)
  set Pbar : Subgroup S.O := K.map (stab S v).subtype with hPbar
  have hPbar_stab : Pbar ≤ stab S v := map_subtype_le K
  have hPbar_card : Nat.card Pbar = 2 ^ 8 := by
    rw [hPbar, card_map_of_injective (stab S v).subtype_injective, hK]
  have hPbar_Mbar : Pbar ≤ S.Mbar := hPbar_stab.trans (stab_le_Mbar v)
  set Pt := pre S Pbar with hPt
  have hPt_card : Nat.card Pt = 2 ^ 21 := by
    rw [hPt, card_pre hPbar_Mbar, hPbar_card, S.card_QG_eq_card_Q, S.card_Q_eq, hw]
    norm_num
  have hPt_p : IsPGroup 2 Pt := IsPGroup.of_card hPt_card
  by_cases hjz : j = S.z
  · refine ⟨Pt, ?_, hPt_p, ?_⟩
    · rw [hjz]
      exact pre_le_M Pbar
    · rw [hPt_card]
      exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  · have hvj' : v = S.cl j := hvj hjz
    have hconj : ∀ p ∈ Pt, p * j * p⁻¹ = j ∨ p * j * p⁻¹ = j * S.z := by
      intro p hp
      obtain ⟨hpM, hpρ⟩ := mem_pre.mp hp
      have hfix : (S.ρ ⟨p, hpM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := (hPbar_stab hpρ).2
      have hQ : p * j * p⁻¹ ∈ S.QG := S.conj_mem_QG hpM hj
      have hcl : S.cl j = S.cl (p * j * p⁻¹) := by
        rw [← S.ρ_cl ⟨p, hpM⟩ hj, ← hvj']
        exact hfix.symm
      exact (S.cl_eq_cl_iff hj hQ).mp hcl
    have hz : ∀ p ∈ Pt, p * S.z = S.z * p := fun p hp => S.z_comm (pre_le_M Pbar hp)
    have hcard := card_le_two_mul_card_inf (P := Pt) S.z_mul_z hz hconj
    refine ⟨Pt ⊓ centralizer ({j} : Set G), inf_le_right, hPt_p.to_le inf_le_left, ?_⟩
    rw [hPt_card] at hcard
    omega

end CFSG.GF2Type.Smith1979.IdxFour
