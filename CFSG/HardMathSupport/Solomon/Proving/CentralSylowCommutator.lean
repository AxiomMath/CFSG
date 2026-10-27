module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.RingTheory.Coprime.Lemmas

public section

open scoped commutatorElement

namespace CFSG.HardMathSupport.Solomon.Proving

theorem le_commutator_sylow_of_le_center {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    (hY : commutator Y = ⊤) {Z : Subgroup Y} (hZc : Z ≤ Subgroup.center Y) (hZp : IsPGroup p Z)
    (P : Sylow p Y) : Z ≤ ⁅(P : Subgroup Y), (P : Subgroup Y)⁆ := by
  intro z hz
  have hzc : z ∈ Subgroup.center Y := hZc hz
  obtain ⟨k, hk⟩ := hZp ⟨z, hz⟩
  have hk' : z ^ p ^ k = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  let H : Subgroup Y := (P : Subgroup Y)
  let φ : H →* Abelianization H := Abelianization.of
  have hker : commutator Y ≤ (MonoidHom.transfer φ).ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have htriv : MonoidHom.transfer φ z = 1 := by
    have hg : z ∈ commutator Y := by rw [hY]; exact Subgroup.mem_top z
    exact MonoidHom.mem_ker.mp (hker hg)
  have hkey : ∀ (n : ℕ) (g₀ : Y), g₀⁻¹ * z ^ n * g₀ ∈ H → g₀⁻¹ * z ^ n * g₀ = z ^ n := by
    intro n g₀ _
    have hw : z ^ n ∈ Subgroup.center Y := Subgroup.pow_mem _ hzc n
    rw [mul_assoc, ← Subgroup.mem_center_iff.mp hw g₀, inv_mul_cancel_left]
  have htp := MonoidHom.transfer_eq_pow φ z hkey
  have hone := htp.symm.trans htriv
  have hmem : (⟨z ^ H.index, MonoidHom.transfer_eq_pow_aux z hkey⟩ : H) ∈ commutator H :=
    (QuotientGroup.eq_one_iff _).mp hone
  have hmem' : z ^ H.index ∈ ⁅H, H⁆ := by
    have h2 := Subgroup.mem_map_of_mem H.subtype hmem
    have hH : Subgroup.map H.subtype (⊤ : Subgroup H) = H := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have h3 : Subgroup.map H.subtype (commutator H) = ⁅H, H⁆ := by
      rw [commutator_def, Subgroup.map_commutator, hH]
    rw [← h3]
    exact h2
  have hcop : IsCoprime ((p ^ k : ℕ) : ℤ) (H.index : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).mpr P.not_dvd_index)
  obtain ⟨u, v, huv⟩ := hcop
  have e : v * (H.index : ℤ) + u * ((p ^ k : ℕ) : ℤ) = 1 := by rw [add_comm]; exact huv
  have hz_eq : z = (z ^ H.index) ^ v * (z ^ p ^ k) ^ u := by
    calc z = z ^ (v * (H.index : ℤ) + u * ((p ^ k : ℕ) : ℤ)) := by rw [e, zpow_one]
      _ = (z ^ H.index) ^ v * (z ^ p ^ k) ^ u := by
        rw [zpow_add, zpow_mul', zpow_mul', zpow_natCast, zpow_natCast]
  have hprod : (z ^ H.index) ^ v * (z ^ p ^ k) ^ u ∈ ⁅H, H⁆ := by
    refine Subgroup.mul_mem _ (Subgroup.zpow_mem _ hmem' v) ?_
    rw [hk', one_zpow]
    exact Subgroup.one_mem _
  rw [← hz_eq] at hprod
  exact hprod

end CFSG.HardMathSupport.Solomon.Proving

end
