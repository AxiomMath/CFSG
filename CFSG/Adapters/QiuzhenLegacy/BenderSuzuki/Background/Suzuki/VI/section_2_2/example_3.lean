module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.VI.section_2_2.example_3

public section

namespace CFSG.BenderSuzuki.Background.Suzuki.VI

universe u

open CFSG.BenderSuzuki.External.Suzuki.VI
open PFAppendixIII

theorem suzuki_chapter6_section2_2_example3_involution_mem_center
    {G : Type u} [Group G] [Finite G]
    (Q : Sylow 2 G) {n : ℕ} (hn : 3 ≤ n)
    (hQ : Nonempty (Q ≃* QuaternionGroup (2 ^ (n - 2))))
    (t : G) (ht : orderOf t = 2) :
    QuotientGroup.mk' (pPrimeCore 2 G) t ∈
      Subgroup.center (G ⧸ pPrimeCore 2 G) := by
  classical
  let N : Subgroup G := pPrimeCore 2 G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  obtain ⟨Qbar, hQbar⟩ := example3_quotient_sylow Q hQ
  have hcenter : 2 ∣ Nat.card (Subgroup.center (G ⧸ N)) := by
    simpa [N] using suzuki_chapter6_section2_2_example3 Q hn hQ
  obtain ⟨z, hzorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := Subgroup.center (G ⧸ N)) 2 hcenter
  have hzorder_ambient : orderOf (z : G ⧸ N) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hzorder
  have hzI : IsInvolution (z : G ⧸ N) := by
    have hz := orderOf_eq_prime_iff.mp hzorder_ambient
    exact ⟨hz.2, by simpa [pow_two] using hz.1⟩
  have hqtI : IsInvolution (q t) := by
    constructor
    · intro hqt
      have htN : t ∈ N := by
        apply (QuotientGroup.eq_one_iff t).mp
        simpa [q] using hqt
      let tN : N := ⟨t, htN⟩
      have htNorder : orderOf tN = 2 := by
        rw [Subgroup.orderOf_mk]
        exact ht
      have htwo_dvd : 2 ∣ Nat.card N := by
        rw [← htNorder]
        exact orderOf_dvd_natCard tN
      have hcop : Nat.Coprime 2 (Nat.card N) := by
        simpa [N] using pPrimeCore_coprime_card (G := G) (p := 2)
      exact (Nat.prime_two.coprime_iff_not_dvd.mp hcop) htwo_dvd
    · have ht_sq : t ^ (2 : ℕ) = 1 := by
        rw [← ht]
        exact pow_orderOf_eq_one t
      calc
        (q t) ^ (2 : ℕ) = q (t ^ (2 : ℕ)) := (map_pow q t 2).symm
        _ = q 1 := congrArg q ht_sq
        _ = 1 := map_one q
  have hcomm : Commute (z : G ⧸ N) (q t) := by
    rw [commute_iff_eq]
    exact (Subgroup.mem_center_iff.mp z.property (q t)).symm
  have hzt : (z : G ⧸ N) = q t :=
    example3_commuting_involutions_eq Qbar
      (example3_sylow_involution_unique Qbar hQbar) hzI hqtI hcomm
  change q t ∈ Subgroup.center (G ⧸ N)
  rw [← hzt]
  exact z.property

end CFSG.BenderSuzuki.Background.Suzuki.VI
