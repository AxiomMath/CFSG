module

public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.GLS.IVK.L2.DihedralAux2

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter

theorem ivk_1_2j : IVK_1_2j := by
  intro F _ _ hF K _ _ e N D hDT hPD hD
  obtain ⟨n₀, -, k, -, hk2, ⟨φ⟩⟩ := hD
  have hkne : NeZero k := ⟨by omega⟩
  have hPt : N.P ⊔ zpowers N.t = N.Pt := (ivk_1_2d F hF K e N).2.2.1
  have key : ∀ D' : Subgroup (MulAut K), N.P ≤ D' → D' ≤ N.Pt →
      D' = N.P ∨ D' = N.P ⊔ zpowers N.t := by
    intro D' hP hD'
    by_cases hD'P : D' ≤ N.P
    · left; exact le_antisymm hD'P hP
    · right
      rw [hPt]
      apply le_antisymm hD'
      obtain ⟨d, hdD, hdP⟩ := Set.not_subset.mp hD'P
      intro y hy
      by_cases hyP : y ∈ N.P
      · exact hP hyP
      · have hidx := P_index_two hF N
        have key2 := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨y, hy⟩ : N.Pt))
          (b := (⟨d, hD' hdD⟩ : N.Pt))
        have h3 : ((⟨y, hy⟩ : N.Pt) * (⟨d, hD' hdD⟩ : N.Pt)) ∈ N.P.subgroupOf N.Pt := by
          rw [key2]
          exact iff_of_false hyP hdP
        have h4 : y * d ∈ N.P := h3
        have : y = (y * d) * d⁻¹ := by group
        rw [this]
        exact D'.mul_mem (hP h4) (D'.inv_mem hdD)
  by_cases hin : ∀ x ∈ D, orderOf x = 2 → x ∈ N.Pt
  · exact key D hPD (DihedralAux.le_of_involutions_le D N.Pt φ hin)
  · exfalso
    push Not at hin
    obtain ⟨x, hxD, hx2, hxPt⟩ := hin
    have hRne : N.R ≠ ⊥ := by
      intro hR
      obtain ⟨d, hd, r, hr, hdr⟩ := T_decomp N x (hDT hxD)
      rw [hR, Subgroup.mem_bot] at hr
      rw [hr, mul_one] at hdr
      exact hxPt (hdr ▸ hd)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hR2 : IsPGroup 2 ↥N.R := N.T.isPGroup'.to_le (inf_le_left : N.R ≤ _)
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hR2
    have hm0 : m ≠ 0 := by
      rintro rfl
      apply hRne
      rw [pow_zero, Subgroup.card_eq_one] at hm
      exact hm
    have hdvd : 2 ∣ Nat.card ↥N.R := by
      rw [hm]; exact dvd_pow_self 2 hm0
    obtain ⟨f', hf'⟩ := exists_prime_orderOf_dvd_card' (G := ↥N.R) 2 hdvd
    set f : MulAut K := (f' : MulAut K) with hf
    have hfR : f ∈ N.R := f'.2
    have hf2 : orderOf f = 2 := by rw [hf, Subgroup.orderOf_coe]; exact hf'
    have hfT : f ∈ (N.T : Subgroup (MulAut K)) := hfR.1
    have hfF : f ∈ fieldAutSub e := hfR.2
    have hfP : f ∉ N.P := by
      intro h
      have h1 : f ∈ N.Pt ⊓ N.R := ⟨P_le_Pt N h, hfR⟩
      rw [(ivk_1_2f F hF K e N).1, Subgroup.mem_bot] at h1
      rw [h1, orderOf_one] at hf2
      omega
    rcases ivk_1_2i_c F hF K e N f hfR hf2 x (hDT hxD) hx2 with h | ⟨h, -⟩ | ⟨p, hp, hxp⟩
    · exact hxPt (P_le_Pt N h)
    · exact hxPt h
    · have hfD : f ∈ D := by
        have : f = p⁻¹ * x := by rw [hxp]; group
        rw [this]
        exact D.mul_mem (D.inv_mem (hPD hp)) hxD
      obtain ⟨n, -, k', hk'n, hk'2, ⟨φP⟩⟩ := ivk_1_2c F hF K e N
      have hk'ne : NeZero k' := ⟨by omega⟩
      have hcardP : Nat.card N.P = 2 ^ n := by
        rw [Nat.card_congr φP.toEquiv, DihedralGroup.nat_card, hk'n]
      have hRle := (ivk_1_2f F hF K e N).2 n hcardP
      have hR2le : 2 ≤ Nat.card N.R := by
        have h1 : orderOf f ∣ Nat.card ↥N.R := Subgroup.orderOf_dvd_natCard _ hfR
        rw [hf2] at h1
        exact Nat.le_of_dvd Nat.card_pos h1
      have hn3 : 3 ≤ n := by
        by_contra hlt
        have h0 : n - 2 = 0 := by omega
        rw [h0, pow_zero] at hRle
        omega
      have h4k' : 4 ∣ k' := by
        obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
        refine ⟨2 ^ j, ?_⟩
        have h8 : (2 : ℕ) ^ (j + 3) = 8 * 2 ^ j := by ring
        omega
      obtain ⟨c', hc'⟩ := DihedralAux.exists_orderOf_eq_four h4k'
      set c : N.P := φP.symm c' with hcdef
      have hc4 : orderOf (c : MulAut K) = 4 := by
        rw [Subgroup.orderOf_coe, hcdef, MulEquiv.orderOf_eq]; exact hc'
      have hcomm : f * (c : MulAut K) = (c : MulAut K) * f :=
        (N.R_cent f ⟨hfT, hfF⟩ hf2 c c.2).symm
      have hcD : (c : MulAut K) ∈ D := hPD c.2
      have hmem := DihedralAux.involution_mem_zpowers_of_comm φ
        (c := (⟨c, hcD⟩ : ↥D)) (f := (⟨f, hfD⟩ : ↥D))
        (by rw [Subgroup.orderOf_mk]; exact hc4) (by rw [Subgroup.orderOf_mk]; exact hf2)
        (Subtype.ext hcomm)
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hfc : f = (c : MulAut K) ^ j := by
        have := congrArg Subtype.val hj
        simpa using this.symm
      exact hfP (by rw [hfc]; exact zpow_mem c.2 j)

end CFSG.GH74.GLS.IVK
