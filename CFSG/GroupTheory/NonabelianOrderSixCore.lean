module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section


namespace CFSG

theorem pCore_two_eq_bot_of_card_six_of_not_comm
    (Q : Type*) [Group Q] [Finite Q] (hcard : Nat.card Q = 6)
    (hnot : ¬ IsMulCommutative Q) : CFSG.pCore 2 Q = ⊥ := by
  let P := CFSG.pCore 2 Q
  have hPnormal : P.Normal := CFSG.pCore_normal
  have hPp : IsPGroup 2 P := CFSG.pCore_isPGroup
  have hPcarddvd : Nat.card P ∣ 6 := hcard ▸ Subgroup.card_subgroup_dvd_card P
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := P)).mp hPp
  have hnle : n ≤ 2 := by
    by_contra h
    have h3 : 3 ≤ n := by omega
    have h8 : 8 ∣ 2 ^ n := by
      have hd : 2 ^ 3 ∣ 2 ^ n := pow_dvd_pow 2 h3
      simpa using hd
    have h86 : 8 ∣ 6 := h8.trans (by simpa [hn] using hPcarddvd)
    norm_num at h86
  have hcases : Nat.card P = 1 ∨ Nat.card P = 2 := by
    interval_cases n
    · left; simp [hn]
    · right; simp [hn]
    · norm_num [hn] at hPcarddvd
  by_cases h1 : Nat.card P = 1
  · rw [Subgroup.eq_bot_iff_card]
    exact h1
  · have h2 : Nat.card P = 2 := by
      rcases hcases with h | h
      · exact absurd h h1
      · exact h
    have hcenter : P ≤ Subgroup.center Q := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      rcases (Nat.card_eq_two_iff' (1 : P)).mp h2 with ⟨p, hpne, huniq⟩
      have hx_cases : x = 1 ∨ x = (p : Q) := by
        by_cases hx1 : x = 1
        · exact Or.inl hx1
        · right
          have hxP : (⟨x, hx⟩ : P) ≠ 1 := by
            intro h
            apply hx1
            exact Subtype.ext_iff.mp h
          have := huniq ⟨x, hx⟩ hxP
          exact congrArg Subtype.val this
      have hcentral_p : ∀ g : Q, g * (p : Q) * g⁻¹ = (p : Q) := by
        intro g
        have hconj_mem : g * (p : Q) * g⁻¹ ∈ P := hPnormal.conj_mem (p : Q) p.2 g
        let c : P := ⟨g * (p : Q) * g⁻¹, hconj_mem⟩
        have hcne : c ≠ 1 := by
          intro hc
          apply hpne
          have hval : g * (p : Q) * g⁻¹ = 1 := congrArg Subtype.val hc
          apply Subtype.ext
          calc (p : Q) = g⁻¹ * (g * (p : Q) * g⁻¹) * g := by group
            _ = 1 := by rw [hval]; group
        have hc_eq : c = p := huniq c hcne
        exact congrArg Subtype.val hc_eq
      intro g
      rcases hx_cases with rfl | hxp
      · simp
      · subst x
        calc g * (p : Q) = (g * (p : Q) * g⁻¹) * g := by group
          _ = (p : Q) * g := by rw [hcentral_p]
    have hquotcard : Nat.card (Q ⧸ P) = 3 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup P
      rw [hcard, h2] at h
      omega
    let : Fact (Nat.Prime 3) := ⟨by decide⟩
    let : IsCyclic (Q ⧸ P) := isCyclic_of_prime_card hquotcard
    have hcomm : ∀ a b : Q, a * b = b * a :=
      commutative_of_cyclic_center_quotient (QuotientGroup.mk' P)
        (by rw [QuotientGroup.ker_mk']; exact hcenter)
    exact (hnot (isMulCommutative_iff.mpr hcomm)).elim

end CFSG
