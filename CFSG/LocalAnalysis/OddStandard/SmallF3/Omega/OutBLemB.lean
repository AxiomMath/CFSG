module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutBLemD
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs
public import TauCeti.GroupTheory.OrderOfElement.PPart

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem aor_odd_mem_sup [Finite G] {H M W : Subgroup G} (hMH : M ≤ H)
    (hW : ∀ x : G, x ∈ W ↔ x ∈ H ⊓ centralizer (M : Set G) ∧ Odd (orderOf x))
    {y : G} (hyH : y ∈ H) (hy : Odd (orderOf y)) (hin : y ∈ M ⊔ centralizer (M : Set G)) :
    y ∈ M ⊔ W := by
  have hCentNorm : ∀ w ∈ centralizer (M : Set G), ∀ m ∈ M, w * m * w⁻¹ ∈ M := by
    intro w hw m hm
    have hwm : m * w = w * m := (Subgroup.mem_centralizer_iff.mp hw) m hm
    rw [← hwm, mul_inv_cancel_right]
    exact hm
  obtain ⟨m, hmM, c, hcCent, hy_eq⟩ := aor_exists_mul_of_mem_sup hCentNorm hin
  have hmH : m ∈ H := hMH hmM
  have hcH : c ∈ H := by
    have hc_eq : c = m⁻¹ * y := by rw [hy_eq]; group
    rw [hc_eq]
    exact mul_mem (inv_mem hmH) hyH
  have hcHC : c ∈ H ⊓ centralizer (M : Set G) := ⟨hcH, hcCent⟩
  have hcomm : Commute m c := (Subgroup.mem_centralizer_iff.mp hcCent) m hmM
  have hc0 : orderOf c ≠ 0 := (orderOf_pos c).ne'
  set e : ℕ := (orderOf c).factorization 2 with he
  have hb_mem : TauCeti.pFreePart 2 c ∈ H ⊓ centralizer (M : Set G) :=
    Subgroup.zpowers_le.mpr hcHC (TauCeti.pFreePart_mem_zpowers 2 c)
  have hb_odd : Odd (orderOf (TauCeti.pFreePart 2 c)) :=
    Nat.not_even_iff_odd.mp fun hev =>
      (TauCeti.not_dvd_orderOf_pFreePart Nat.prime_two hc0) (even_iff_two_dvd.mp hev)
  have hbW : TauCeti.pFreePart 2 c ∈ W := (hW _).mpr ⟨hb_mem, hb_odd⟩
  have hpart : TauCeti.pPart 2 c ^ (2 ^ e) = 1 := by
    have hord : orderOf (TauCeti.pPart 2 c) = 2 ^ e := by
      rw [TauCeti.orderOf_pPart Nat.prime_two hc0, he]
    rw [← hord]
    exact pow_orderOf_eq_one _
  have hcab : c = TauCeti.pPart 2 c * TauCeti.pFreePart 2 c :=
    (TauCeti.pPart_mul_pFreePart 2 c).symm
  have hc_pow : c ^ (2 ^ e) = TauCeti.pFreePart 2 c ^ (2 ^ e) :=
    (congrArg (fun z : G => z ^ (2 ^ e)) hcab).trans <|
      ((TauCeti.commute_pFreePart_pPart 2 c).symm.mul_pow (2 ^ e)).trans <|
        (by rw [hpart, one_mul])
  have hy_pow : y ^ (2 ^ e) = m ^ (2 ^ e) * TauCeti.pFreePart 2 c ^ (2 ^ e) :=
    (congrArg (fun z : G => z ^ (2 ^ e)) hy_eq).trans <|
      (hcomm.mul_pow (2 ^ e)).trans <| by rw [hc_pow]
  have hpow_mem : y ^ (2 ^ e) ∈ M ⊔ W := by
    rw [hy_pow]
    exact Subgroup.mul_mem_sup (Subgroup.pow_mem M hmM (2 ^ e))
      (Subgroup.pow_mem W hbW (2 ^ e))
  have hcop : Nat.Coprime (2 ^ e) (orderOf y) := hy.coprime_two_left.pow_left e
  have hmem : y ∈ Subgroup.zpowers (y ^ (2 ^ e)) := mem_zpowers_pow_iff.mpr hcop
  exact Subgroup.zpowers_le.mpr hpow_mem hmem

theorem aor_twoPrimeRes_le_of_cyclic [Finite G] (H M : Subgroup G) (hMH : M ≤ H)
    (hcyc : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ H ⊓ centralizer (M : Set G) → IsCyclic P)
    (hinner : ∀ y ∈ H, Odd (orderOf y) → y ∈ M ⊔ centralizer (M : Set G))
    (X : Subgroup G) (hX : X ≤ twoRes H) : twoPrimeRes X ≤ M := by
  obtain ⟨W, hW⟩ := aor_exists_subgroup_odd_elems (H ⊓ centralizer (M : Set G)) hcyc
  have hMW : ∀ w ∈ W, ∀ m ∈ M, w * m * w⁻¹ ∈ M := by
    intro w hw m hm
    have h := Subgroup.mem_centralizer_iff.mp ((hW w).mp hw).1.2 m hm
    rw [← h]
    simpa using hm
  have hodd : ∀ w ∈ W, Odd (orderOf w) := fun w hw => ((hW w).mp hw).2
  have hTwoRes : twoRes H ≤ M ⊔ W := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hyH, hy⟩
    exact aor_odd_mem_sup hMH hW hyH hy (hinner y hyH hy)
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨hyX, k, hk⟩
  have hP : IsPGroup 2 (zpowers y) := by
    intro ⟨z, hz⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hk, pow_orderOf_eq_one,
      one_zpow]
  have hle : zpowers y ≤ M :=
    aor_le_of_le_sup_odd hMW hodd hP (Subgroup.zpowers_le.mpr (hTwoRes (hX hyX)))
  exact hle (Subgroup.mem_zpowers y)

end CFSG.OddStandard.SmallF3.Omega
