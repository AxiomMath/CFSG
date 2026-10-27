module

public import CFSG.CGT.T75H.LocalAG
public import CFSG.CGT.T75H.Bender
public import CFSG.CGT.T75H.HStruct
public import CFSG.CGT.T75H.CoprimeFour
public import CFSG.CGT.T75H.SylowData

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem oddCore_isPGroup_three (hc : Sec6Ctx T T₁ 2 1) (h48 : IsWC (barSub T (normIn T₁ T)))
    (h57 : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ h ∈ hSub T (normIn T₁ T), h * x * h⁻¹ = y)
    (h215 : Lemma215Stmt) (hI : ListWCIdentification) {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y)
    {S : Sylow 2 G} (hS : SylowData T T₁ S) {α β : G} (hα : α ∈ Cbar T T₁ S)
    (hβ : β ∈ Cbar T T₁ S) (hα1 : α ≠ 1) (hβ1 : β ≠ 1) (hne : α ≠ β) (hαα : α * α = 1)
    (hββ : β * β = 1) (hαβ : α * β = β * α) :
    ∃ N : Subgroup G, N ≤ hSub T (normIn T₁ T) ∧ N ≤ Subgroup.centralizer (T : Set G) ∧
      Odd (Nat.card N) ∧ T ⊓ N = ⊥ ∧
      (∀ c ∈ Subgroup.centralizer (T : Set G) ⊓ hSub T (normIn T₁ T),
        ∃ t ∈ T, ∃ n ∈ N, c = t * n) ∧
      (∀ s ∈ Subgroup.normalizer (T : Set G), ∀ n ∈ N, s * n * s⁻¹ ∈ N) ∧
      N.relIndex (hSub T (normIn T₁ T)) ∣ 24 ∧ IsPGroup 3 N := by
  classical
  have : Finite G := hc.hy.finite
  have : IsSimpleGroup G := hc.hy.simple
  have hna := hc.hy.nonab
  have hInd := hc.hy.ind
  obtain ⟨N, hNH, hNc, hNodd, hTN, hdec, hNnorm, hrel⟩ := exists_oddComplement hc h48 D
  have hgen := hSub_le_closure_conj hc h48 h57 D
  have hT4 : Nat.card T = 4 := by simpa using hc.hT
  have hHN : hSub T (normIn T₁ T) ≤ Subgroup.normalizer (T : Set G) :=
    hSub_le_normalizer (fun w hw => (mem_normIn.1 hw).2)
  have hαmem := mem_Cbar_iff.1 hα
  have hβmem := mem_Cbar_iff.1 hβ
  have hℓS : ℓ ∈ (S : Subgroup G) := hS.le (normIn_le_sStar D.hℓ)
  have hq3 : ∀ q : ℕ, q.Prime → 5 ≤ q → ¬ q ∣ Nat.card N := by
    intro q hq hq5 hqN
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨P, hPN, hPq, hPidx, hPS⟩ := exists_invariant_sylow_of_isPGroup_two S.isPGroup' hNodd
      (fun s hs n hn => hNnorm s (hS.norm s hs) n hn) q
    have hqodd : q ≠ 2 := by omega
    have hPodd : Odd (Nat.card P) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hPq
      rw [hk]
      exact (hq.odd_of_ne_two hqodd).pow
    have hαP : ∀ p ∈ P, α * p * α⁻¹ ∈ P := fun p hp => hPS α hαmem.1 p hp
    have hβP : ∀ p ∈ P, β * p * β⁻¹ ∈ P := fun p hp => hPS β hβmem.1 p hp
    have hgenP := le_sup_fixed_of_commuting_involutions hPodd hαα hββ hαβ hα1 hβ1 hne hαP hβP
    have hkey : ∀ γ : G, γ ≠ 1 → (∀ t ∈ T, t * γ = γ * t) → (∀ t ∈ T₁, t * γ = γ * t) →
        ∀ h ∈ P, h * γ = γ * h → h * ℓ * h⁻¹ = ℓ := by
      intro γ hγ1 hγT hγT₁ h hhP hhγ
      have hhN : h ∈ N := hPN hhP
      have hzP : ℓ * (h * ℓ * h⁻¹) ∈ P := by
        have h1 : ℓ * h * ℓ⁻¹ ∈ P := hPS ℓ hℓS h hhP
        have e : ℓ * (h * ℓ * h⁻¹) = (ℓ * h * ℓ⁻¹) * h⁻¹ := by rw [D.inv_ℓ]; group
        rw [e]
        exact P.mul_mem h1 (P.inv_mem hhP)
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hPq ⟨_, hzP⟩
      have hz : orderOf (ℓ * (h * ℓ * h⁻¹)) = q ^ k :=
        (Subgroup.orderOf_coe (⟨_, hzP⟩ : P)).trans hk
      exact local_A_G hna hInd h215 hI hT4 D hγ1 hγT hγT₁ hhγ
        (fun t ht => (Subgroup.mem_centralizer_iff.1 (hNc hhN) t ht).symm) hq hq5 hz
    have hcα : P ⊓ Subgroup.centralizer ({α} : Set G) ≤ Subgroup.centralizer ({ℓ} : Set G) := by
      rintro h ⟨hhP, hhα⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hkey α hα1 hαmem.2.1 hαmem.2.2 h hhP
        (Subgroup.mem_centralizer_singleton_iff.1 hhα)
      calc h * ℓ = (h * ℓ * h⁻¹) * h := by group
        _ = ℓ * h := by rw [this]
    have hcβ : P ⊓ Subgroup.centralizer ({β} : Set G) ≤ Subgroup.centralizer ({ℓ} : Set G) := by
      rintro h ⟨hhP, hhβ⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hkey β hβ1 hβmem.2.1 hβmem.2.2 h hhP
        (Subgroup.mem_centralizer_singleton_iff.1 hhβ)
      calc h * ℓ = (h * ℓ * h⁻¹) * h := by group
        _ = ℓ * h := by rw [this]
    have hαβ1 : α * β ≠ 1 := fun h => hne (by
      have : α = β⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact inv_eq_of_mul_eq_one_right hββ)
    have hcαβ : P ⊓ Subgroup.centralizer ({α * β} : Set G) ≤
        Subgroup.centralizer ({ℓ} : Set G) := by
      rintro h ⟨hhP, hhαβ⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm : h * (α * β) = (α * β) * h := Subgroup.mem_centralizer_singleton_iff.1 hhαβ
      have hT' : ∀ t ∈ T, t * (α * β) = (α * β) * t := fun t ht => by
        rw [← mul_assoc, hαmem.2.1 t ht, mul_assoc, hβmem.2.1 t ht, mul_assoc]
      have hT₁' : ∀ t ∈ T₁, t * (α * β) = (α * β) * t := fun t ht => by
        rw [← mul_assoc, hαmem.2.2 t ht, mul_assoc, hβmem.2.2 t ht, mul_assoc]
      have := hkey (α * β) hαβ1 hT' hT₁' h hhP hcomm
      calc h * ℓ = (h * ℓ * h⁻¹) * h := by group
        _ = ℓ * h := by rw [this]
    have hPc : P ≤ Subgroup.centralizer ({ℓ} : Set G) :=
      hgenP.trans (sup_le (sup_le hcα hcβ) hcαβ)
    have hPx : ∀ p ∈ P, p * ℓ = ℓ * p := fun p hp =>
      Subgroup.mem_centralizer_singleton_iff.1 (hPc hp)
    have hℓH : ℓ ∈ hSub T (normIn T₁ T) := le_hSub D.hℓ
    have hqHN : ¬ q ∣ N.relIndex (hSub T (normIn T₁ T)) := by
      intro hdvd
      have h24 : q ∣ 24 := hdvd.trans hrel
      have h' : q ∣ 2 ^ 3 * 3 := by norm_num; exact h24
      rcases (Nat.Prime.dvd_mul hq).1 h' with h2 | h3
      · have := Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h2)
        omega
      · have := Nat.le_of_dvd (by norm_num) h3
        omega
    exact bender_two_one hq hNH (fun h hh n hn => hNnorm h (hHN hh) n hn) hNodd hℓH D.ℓℓ hgen
      hqHN hPidx hPx hqN
  refine ⟨N, hNH, hNc, hNodd, hTN, hdec, hNnorm, hrel, ?_⟩
  have hpos : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have hpow : Nat.card N = 3 ^ (Nat.card N).primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd hpos (fun {d} hd hdN => ?_)
    have hdodd : d ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr hdN)
    by_contra hd3
    have hd5 : 5 ≤ d := by
      have h2 := hd.two_le
      have h4 : d ≠ 4 := by
        rintro rfl
        exact absurd hd (by norm_num)
      omega
    exact hq3 d hd hd5 hdN
  exact IsPGroup.of_card hpow

end CFSG.CGT.T75H
