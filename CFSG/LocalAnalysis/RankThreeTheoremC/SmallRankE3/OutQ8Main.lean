module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.OutQ8Quat
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.OutQ8Central
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Iii630Facts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.OutQ8

open Subgroup

section

variable {K : Type*} [Group K] [Finite K] {A B Y : Subgroup K} {ζ : K}

theorem conj_mem_of_gens {A' : Subgroup K} {i j : K} (x : K) (hi : x * i * x⁻¹ ∈ A')
    (hj : x * j * x⁻¹ ∈ A') : ∀ g ∈ Subgroup.closure {i, j}, x * g * x⁻¹ ∈ A' := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact hi
    · exact hj
  | one => simp
  | mul g h _ _ ihg ihh =>
    have : x * (g * h) * x⁻¹ = (x * g * x⁻¹) * (x * h * x⁻¹) := by group
    rw [this]; exact A'.mul_mem ihg ihh
  | inv g _ ih =>
    have : x * g⁻¹ * x⁻¹ = (x * g * x⁻¹)⁻¹ := by group
    rw [this]; exact A'.inv_mem ih

theorem inv_of_A_le (hA : Q8Like A ζ) (hB : QuatLike B Y ζ)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {Q : Subgroup K} (hQS : Q ≤ A ⊔ B)
    (hAQ : A ≤ Q) {x : K} {m : ℕ} (hx : x ^ m = 1) (hm : Nat.Coprime m 6)
    (hxQ : ∀ g ∈ Q, x * g * x⁻¹ ∈ Q) : ∀ g ∈ Q ⊓ B, x * g * x⁻¹ ∈ Q ⊓ B := by
  classical
  obtain ⟨i, j, hi, hj, hij, hAgen⟩ := hA.gen
  have hζB : ζ ∈ B := hB.Y_le hB.ζ_mem
  have hxm2 : Nat.Coprime m 2 := hm.coprime_dvd_right (by norm_num)
  have hxA : ∀ g ∈ A, x * g * x⁻¹ ∈ A := by
    have hiQ : x * i * x⁻¹ ∈ Q := hxQ i (hAQ hi)
    have hjQ : x * j * x⁻¹ ∈ Q := hxQ j (hAQ hj)
    have hq1 : QPair (x * i * x⁻¹) (x * j * x⁻¹) := hij.conj x
    rcases qpair_dichotomy hA hB hcomm (hQS hiQ) (hQS hjQ) hq1 with ⟨hi1, hj1⟩ | ⟨hi1, hj1⟩
    · intro g hg
      rw [hAgen] at hg
      exact conj_mem_of_gens x hi1 hj1 g hg
    · have hiQ2 : x * (x * i * x⁻¹) * x⁻¹ ∈ Q := hxQ _ hiQ
      have hjQ2 : x * (x * j * x⁻¹) * x⁻¹ ∈ Q := hxQ _ hjQ
      have hq2 : QPair (x * (x * i * x⁻¹) * x⁻¹) (x * (x * j * x⁻¹) * x⁻¹) := hq1.conj x
      rcases qpair_dichotomy hA hB hcomm (hQS hiQ2) (hQS hjQ2) hq2 with ⟨hi2, hj2⟩ | ⟨hi2, hj2⟩
      · have h2 : ∀ g ∈ A, x ^ 2 * g * (x ^ 2)⁻¹ ∈ A := by
          intro g hg
          rw [hAgen] at hg
          have e1 : x ^ 2 * i * (x ^ 2)⁻¹ = x * (x * i * x⁻¹) * x⁻¹ := by simp only [pow_two]; group
          have e2 : x ^ 2 * j * (x ^ 2)⁻¹ = x * (x * j * x⁻¹) * x⁻¹ := by simp only [pow_two]; group
          exact conj_mem_of_gens (x ^ 2) (by rw [e1]; exact hi2) (by rw [e2]; exact hj2) g hg
        exact normalizes_of_sq A x m hx hxm2 h2
      · exfalso
        refine no_commuting_qpairs_in_B hB hi1 hi2 hj2 ⟨hq1.1, hq1.2.1⟩ hq2 ?_ ?_
        · have hc : i * (x * i * x⁻¹) = (x * i * x⁻¹) * i := hcomm i hi _ hi1
          calc x * i * x⁻¹ * (x * (x * i * x⁻¹) * x⁻¹) = x * (i * (x * i * x⁻¹)) * x⁻¹ := by group
            _ = x * ((x * i * x⁻¹) * i) * x⁻¹ := by rw [hc]
            _ = x * (x * i * x⁻¹) * x⁻¹ * (x * i * x⁻¹) := by group
        · have hc : i * (x * j * x⁻¹) = (x * j * x⁻¹) * i := hcomm i hi _ hj1
          calc x * i * x⁻¹ * (x * (x * j * x⁻¹) * x⁻¹) = x * (i * (x * j * x⁻¹)) * x⁻¹ := by group
            _ = x * ((x * j * x⁻¹) * i) * x⁻¹ := by rw [hc]
            _ = x * (x * j * x⁻¹) * x⁻¹ * (x * i * x⁻¹) := by group
  have hxA' := conj_mem_inv_of_finite A x hxA
  intro g hg
  obtain ⟨hgQ, hgB⟩ := hg
  refine ⟨hxQ g hgQ, ?_⟩
  have hs : x * g * x⁻¹ ∈ A ⊔ B := hQS (hxQ g hgQ)
  apply mem_B_of_centralizes hA hζB hcomm hs
  intro a ha
  have ha' : x⁻¹ * a * x ∈ A := hxA' a ha
  have hc : (x⁻¹ * a * x) * g = g * (x⁻¹ * a * x) := hcomm _ ha' g hgB
  calc x * g * x⁻¹ * a = x * (g * (x⁻¹ * a * x)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * a * x) * g) * x⁻¹ := by rw [hc]
    _ = a * (x * g * x⁻¹) := by group

theorem inv_of_not_A_le (hA : Q8Like A ζ) (hB : QuatLike B Y ζ)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {Q : Subgroup K} (hQS : Q ≤ A ⊔ B)
    (hAQ : ¬ A ≤ Q) {u v : K} (hu : u ∈ Q) (hv : v ∈ Q) (huv : QPair u v) {x : K}
    (hxQ : ∀ g ∈ Q, x * g * x⁻¹ ∈ Q) : ∀ g ∈ Q ⊓ B, x * g * x⁻¹ ∈ Q ⊓ B := by
  classical
  set Θ : Set K := {g | g ∈ Q ∧ ∃ w ∈ Q, QPair g w} with hΘ
  have hΘB : ∀ g ∈ Θ, g ∈ B := by
    rintro g ⟨hgQ, w, hwQ, hgw⟩
    rcases qpair_dichotomy hA hB hcomm (hQS hgQ) (hQS hwQ) hgw with ⟨hg, hw⟩ | ⟨hg, hw⟩
    · exfalso
      apply hAQ
      rw [← closure_eq_of_qpair hA hg hw hgw]
      exact (Subgroup.closure_le Q).2 (by
        intro t ht
        rcases ht with rfl | rfl
        · exact hgQ
        · exact hwQ)
    · exact hg
  have hΘx : ∀ g ∈ Θ, x * g * x⁻¹ ∈ Θ := by
    rintro g ⟨hgQ, w, hwQ, hgw⟩
    exact ⟨hxQ g hgQ, x * w * x⁻¹, hxQ w hwQ, hgw.conj x⟩
  have hWx : ∀ g ∈ Subgroup.closure Θ, x * g * x⁻¹ ∈ Subgroup.closure Θ := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg => exact Subgroup.subset_closure (hΘx g hg)
    | one => simp
    | mul g h _ _ ihg ihh =>
      have : x * (g * h) * x⁻¹ = (x * g * x⁻¹) * (x * h * x⁻¹) := by group
      rw [this]; exact Subgroup.mul_mem _ ihg ihh
    | inv g _ ih =>
      have : x * g⁻¹ * x⁻¹ = (x * g * x⁻¹)⁻¹ := by group
      rw [this]; exact Subgroup.inv_mem _ ih
  have huvB : u ∈ B ∧ v ∈ B := by
    rcases qpair_dichotomy hA hB hcomm (hQS hu) (hQS hv) huv with ⟨hg, hw⟩ | h
    · exfalso
      apply hAQ
      rw [← closure_eq_of_qpair hA hg hw huv]
      exact (Subgroup.closure_le Q).2 (by
        intro t ht
        rcases ht with rfl | rfl
        · exact hu
        · exact hv)
    · exact h
  have hH : Q ⊓ B ≤ Subgroup.closure Θ := by
    have := le_closure_qpairs_of_quatLike hB (Q ⊓ B) inf_le_right (u := u) (v := v)
      ⟨hu, huvB.1⟩ ⟨hv, huvB.2⟩ huv
    refine this.trans (Subgroup.closure_mono ?_)
    rintro g ⟨⟨hgQ, hgB⟩, w, ⟨hwQ, hwB⟩, hgw⟩
    exact ⟨hgQ, w, hwQ, hgw⟩
  have hW : Subgroup.closure Θ ≤ Q ⊓ B := by
    rw [Subgroup.closure_le]
    intro g hg
    exact ⟨hg.1, hΘB g hg⟩
  have hEq : Subgroup.closure Θ = Q ⊓ B := le_antisymm hW hH
  intro g hg
  rw [← hEq] at hg ⊢
  exact hWx g hg

theorem centralizes_of_inv (hA : Q8Like A ζ) (hB : QuatLike B Y ζ) (hBp : IsPGroup 2 B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : Nat.card (A ⊓ B : Subgroup K) = 2)
    {Q : Subgroup K} (hQS : Q ≤ A ⊔ B) {x : K} {m : ℕ} (hx : x ^ m = 1)
    (hm : Nat.Coprime m 6) (hxQ : ∀ g ∈ Q, x * g * x⁻¹ ∈ Q)
    (hinv : ∀ g ∈ Q ⊓ B, x * g * x⁻¹ ∈ Q ⊓ B) : ∀ g ∈ Q, x * g * x⁻¹ = g := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAp : IsPGroup 2 A := IsPGroup.of_card (n := 3) (by rw [hA.card]; norm_num)
  have hS2 : IsPGroup 2 ↥(A ⊔ B) := isPGroup_sup hAp hBp hcomm
  have hQ2 : IsPGroup 2 ↥Q := hS2.to_le hQS
  have hxQ' := conj_mem_inv_of_finite Q x hxQ
  have hinv' := conj_mem_inv_of_finite (Q ⊓ B) x hinv
  have hP2 : IsPGroup 2 ↥(Q ⊓ B) := hQ2.to_le inf_le_left
  obtain ⟨u, v, huv⟩ := two_gen_of_quatLike hB (Q ⊓ B) inf_le_right
  have hP := centralizes_of_two_gen (Q ⊓ B) hP2 u v huv x hinv hinv' m hx hm
  have hidx := relIndex_inf_le_four hcomm hA.card hAB hQS
  have hxN : ∀ g ∈ Q, (x * g * x⁻¹ ∈ Q ⊓ B ↔ g ∈ Q ⊓ B) := by
    intro g hg
    constructor
    · intro h
      have := hinv' _ h
      simpa [mul_assoc] using this
    · exact hinv g
  have hfix := conj_coset_fixed Q (Q ⊓ B) inf_le_left hidx x hxQ hxQ' hxN m hx hm
  exact stab_centralizes Q (Q ⊓ B) inf_le_left hQ2 x m hx
    (hm.coprime_dvd_right (by norm_num)) (fun n hn => hP n hn) hfix

end

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.OutQ8

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.OutQ8 Subgroup

theorem kFactOutQ8Quaternion_holds : KFactOutQ8Quaternion := by
  intro K _ _ S S₀ R n hS hS₀S _hS₀N hRS₀ hR g hg hcop
  obtain ⟨eR⟩ := hR
  obtain ⟨A, B, ⟨eA⟩, hn, ⟨eB⟩, hcomm, hsup, hcard⟩ := hS
  obtain ⟨w, hw, hw1, hw2⟩ := exists_involution_of_card_two hcard
  have hwA : w ∈ A := hw.1
  have hwB : w ∈ B := hw.2
  have hA : Q8Like A w := q8Like_of_equiv A eA w hwA hw1 hw2
  obtain ⟨Y, hB⟩ := quatLike_of_equiv B (2 ^ (n - 2)) eB w hwB hw1 hw2
  have hBp : IsPGroup 2 B := isPGroup_two_of_equiv_quaternion B (n - 2) eB
  obtain ⟨u, v, hu, hv, huv⟩ := exists_qpair_of_equiv R eR
  have hQS : S₀ ≤ A ⊔ B := by rw [hsup]; exact hS₀S
  have hx : g ^ orderOf g = 1 := pow_orderOf_eq_one g
  have hxQ : ∀ h ∈ S₀, g * h * g⁻¹ ∈ S₀ := fun h hh => (Subgroup.mem_normalizer_iff.mp hg h).mp hh
  have hinv : ∀ h ∈ S₀ ⊓ B, g * h * g⁻¹ ∈ S₀ ⊓ B := by
    by_cases hAQ : A ≤ S₀
    · exact inv_of_A_le hA hB hcomm hQS hAQ hx hcop hxQ
    · exact inv_of_not_A_le hA hB hcomm hQS hAQ (hRS₀ hu) (hRS₀ hv) huv hxQ
  have hall := centralizes_of_inv hA hB hBp hcomm hcard hQS hx hcop hxQ hinv
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have := hall h hh
  exact (mul_inv_eq_iff_eq_mul.mp this).symm

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
