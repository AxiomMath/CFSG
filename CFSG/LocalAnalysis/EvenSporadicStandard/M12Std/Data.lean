module

public import CFSG.GH74.M12.HypT2
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Data

public section

namespace CFSG.EvenSporadicStandard.M12Std

open Subgroup CFSG.Blueprint CFSG.GH74.M12 CFSG.GH74.M12.Hyp CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.M12Cover

set_option maxRecDepth 100000 in
theorem bfT_center : ∀ s ∈ BT, (∀ t ∈ BT, tmul s t = tmul t s) → s = tid ∨ s = JT := by
  decide

theorem bfS'_center {y : G12} (hy : y ∈ bfS')
    (hc : ∀ x ∈ bfS', x * y = y * x) : y = 1 ∨ y = Jelt := by
  have hty : tbl y.1 ∈ BT := mem_bfS_iff.1 hy
  have hcent : ∀ t ∈ BT, tmul (tbl y.1) t = tmul t (tbl y.1) := by
    intro t ht
    obtain ⟨n, -, hn⟩ := mem_BT_iff.1 ht
    have hσ : bfElt (n / 32) ((n / 16) % 2) ((n / 8) % 2) (n % 8) ∈ bfS := bfElt_mem _ _ _ _
    have hs : (⟨_, bfS_le_M12 hσ⟩ : G12) ∈ bfS' := hσ
    have h3 := congrArg tbl (congrArg Subtype.val (hc _ hs))
    rw [Subgroup.coe_mul, Subgroup.coe_mul, tbl_mul, tbl_mul, tbl_bfElt, ← hn] at h3
    exact h3.symm
  rcases bfT_center _ hty hcent with h | h
  · exact Or.inl (Subtype.ext (tbl_injective (by rw [h, Subgroup.coe_one, tbl_one])))
  · exact Or.inr (Subtype.ext (tbl_injective (by rw [h, ← tbl_bfJ]; rfl)))

theorem exists_conj_Jelt_m12Rep1 :
    ∃ c ∈ NativeSporadic.M12, (Jelt : Equiv.Perm (Fin 12)) = c * m12Rep1 * c⁻¹ := by
  have hord : orderOf (Jelt : Equiv.Perm (Fin 12)) = 2 := by
    rw [Subgroup.orderOf_coe]; exact orderOf_Jelt
  obtain ⟨r, hr, c, hc, hJ⟩ := m12_involution_cover.1 (Jelt : Equiv.Perm (Fin 12))
    (by simp) hord
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨c, hc, hJ⟩
  · exfalso
    have hS : bfS ≤ centralizerIn NativeSporadic.M12 (Jelt : Equiv.Perm (Fin 12)) := fun σ hσ => by
      rw [mem_centralizerIn]
      exact ⟨bfS_le_M12 hσ, congrArg Subtype.val (bfS'_comm_Jelt (s := ⟨σ, bfS_le_M12 hσ⟩) hσ)⟩
    have hcard :
        Nat.card (centralizerIn NativeSporadic.M12 (Jelt : Equiv.Perm (Fin 12))) = 240 := by
      rw [hJ, centralizerIn_conj _ hc, Subgroup.card_map_of_injective (MulAut.conj c).injective,
        card_centralizerIn_m12Rep2]
    have h64 : 64 ∣ 240 := by
      rw [← card_bfS, ← hcard]
      exact Subgroup.card_dvd_of_le hS
    omega

theorem sylowData_m12 :
    Fin76b.SylowData NativeSporadic.M12 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c0, hc0, hJ0⟩ := exists_conj_Jelt_m12Rep1
  obtain ⟨hb, hbo⟩ := m12_reps_mem m12Rep2 (by simp)
  have hord2 : ∀ a : G12, a * a = 1 → a ≠ 1 → orderOf (a : Equiv.Perm (Fin 12)) = 2 := by
    intro a ha2 ha1
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
  refine ⟨bfS', Jelt, ⟨m12Rep2, hb⟩, IsPGroup.of_card (n := 6) (by rw [card_bfS']; norm_num),
    ⟨1485, by decide, by rw [card_G12, card_bfS']⟩, Jelt_mul_self, Jelt_ne_one, Jelt_mem_bfS',
    fun x hx => bfS'_comm_Jelt hx, fun y hy hc => bfS'_center hy hc,
    ⟨Felt * Felt, Subtype.ext ?_⟩, ?_⟩
  · show bfF * bfF * (bfF * bfF) = bfF ^ 4
    simp [pow_succ, mul_assoc]
  · intro a ha2 ha1
    obtain ⟨r, hr, c, hc, hac⟩ := m12_involution_cover.1 (a : Equiv.Perm (Fin 12))
      (by simp) (hord2 a ha2 ha1)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine Or.inl ⟨⟨c * c0⁻¹, mul_mem hc (inv_mem hc0)⟩, Subtype.ext ?_⟩
      have h1 : m12Rep1 = c0⁻¹ * (Jelt : Equiv.Perm (Fin 12)) * c0 := by
        rw [hJ0]; group
      rw [hac, h1]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    · exact Or.inr ⟨⟨c, hc⟩, Subtype.ext hac⟩

end CFSG.EvenSporadicStandard.M12Std
