module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshBurnside
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshFourGroup

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open Subgroup

theorem card_inf_eq_two_pow_of_normalizes {G : Type*} [Group G] [Finite G] (H S : Subgroup G)
    (hSH : ∀ s ∈ S, ∀ h ∈ H, s * h * s⁻¹ ∈ H)
    (hS : Nat.card S = 2 ^ (Nat.card G).factorization 2) :
    Nat.card (H ⊓ S : Subgroup G) = 2 ^ (Nat.card H).factorization 2 := by
  have hn : S ≤ normalizer (H : Set G) := le_normalizer_iff.2 hSH
  have hrel : H.relIndex (S ⊔ H) = H.relIndex S := by
    haveI := normal_subgroupOf_of_le_normalizer hn
    haveI := normal_subgroupOf_sup_of_le_normalizer hn
    exact Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient S H hn).toEquiv.symm
  have hM : H.relIndex S * Nat.card H = Nat.card (S ⊔ H : Subgroup G) := by
    rw [← hrel]
    have h := relIndex_mul_card (H := H) (K := S ⊔ H)
    rwa [inf_eq_left.2 le_sup_right] at h
  have hI : H.relIndex S * Nat.card (H ⊓ S : Subgroup G) = 2 ^ (Nat.card G).factorization 2 :=
    (relIndex_mul_card (H := H) (K := S)).trans hS
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hH0 : Nat.card H ≠ 0 := Nat.card_pos.ne'
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro_left _ hI)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro _ hI)
  rw [hi, hj, ← pow_add] at hI
  have hij : i + j = (Nat.card G).factorization 2 := Nat.pow_right_injective le_rfl hI
  have h1 : i + (Nat.card H).factorization 2 ≤ (Nat.card G).factorization 2 := by
    refine (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hG0).1 ?_
    have hdvd : 2 ^ i * Nat.card H ∣ Nat.card G := by
      rw [hi] at hM
      rw [hM]
      exact card_subgroup_dvd_card _
    rw [pow_add]
    exact (mul_dvd_mul_left _ (Nat.ordProj_dvd _ _)).trans hdvd
  have h2 : j ≤ (Nat.card H).factorization 2 := by
    refine (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hH0).1 ?_
    rw [← hj]
    exact card_dvd_of_le inf_le_left
  have h3 : j = (Nat.card H).factorization 2 := by omega
  rw [hj, h3]

theorem centralizer_eq_of_fourGroup {G : Type*} [Group G] [Finite G]
    (A S L : Subgroup G) (e u : G)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAS : A ≤ S) (hSL : S ≤ L)
    (hLA : ∀ ℓ ∈ L, ∀ a ∈ A, ℓ * a * ℓ⁻¹ ∈ A)
    (hS : Nat.card S = 2 ^ (Nat.card G).factorization 2)
    (hCS : ∀ y ∈ S, (∀ a ∈ A, y * a = a * y) → y ∈ A)
    (heL : e ∈ L) (huL : u ∈ L) (he2 : e * e = 1) (hu2 : u * u = 1) (heu : e * u = u * e)
    (hCe : ∀ y : G, (∀ a ∈ A, y * a = a * y) → y * e = e * y → Odd (orderOf y) → y = 1)
    (hfu : ∃ ℓ ∈ L, ℓ * e * ℓ⁻¹ = u) (hfue : ∃ ℓ ∈ L, ℓ * e * ℓ⁻¹ = u * e) :
    ∀ y : G, (∀ a ∈ A, y * a = a * y) → y ∈ A := by
  obtain ⟨H, hH⟩ : ∃ H : Subgroup G, ∀ y : G, y ∈ H ↔ ∀ a ∈ A, y * a = a * y :=
    ⟨Subgroup.centralizer (A : Set G), fun y => by
      rw [Subgroup.mem_centralizer_iff]
      exact ⟨fun h a ha => (h a ha).symm, fun h a ha => (h a ha).symm⟩⟩
  have hAH : A ≤ H := fun a ha => (hH a).2 fun b hb => hAcomm a ha b hb
  have hLH : ∀ ℓ ∈ L, ∀ y ∈ H, ℓ * y * ℓ⁻¹ ∈ H := by
    intro ℓ hℓ y hy
    have hy' := (hH y).1 hy
    refine (hH _).2 fun a ha => ?_
    have ha' : ℓ⁻¹ * a * ℓ ∈ A := by simpa using hLA ℓ⁻¹ (L.inv_mem hℓ) a ha
    calc ℓ * y * ℓ⁻¹ * a = ℓ * (y * (ℓ⁻¹ * a * ℓ)) * ℓ⁻¹ := by group
      _ = ℓ * ((ℓ⁻¹ * a * ℓ) * y) * ℓ⁻¹ := by rw [hy' _ ha']
      _ = a * (ℓ * y * ℓ⁻¹) := by group
  have hinf : H ⊓ S = A :=
    le_antisymm (fun y hy => hCS y hy.2 ((hH y).1 hy.1)) (le_inf hAH hAS)
  have hA : Nat.card A = 2 ^ (Nat.card H).factorization 2 := by
    have h := card_inf_eq_two_pow_of_normalizes H S (fun s hs y hy => hLH s (hSL hs) y hy) hS
    rwa [hinf] at h
  obtain ⟨K, hKH, hKodd, hKcard, -⟩ := exists_normal_twoComplement H A hAH
    (fun a ha h hh => ((hH h).1 hh a ha).symm) hA
  have hLK : ∀ ℓ ∈ L, ∀ k ∈ K, ℓ * k * ℓ⁻¹ ∈ K := by
    intro ℓ hℓ k hk
    have hkH : k ∈ H := hKH hk
    refine (hKodd _ (hLH ℓ hℓ k hkH)).2 ?_
    have hsc : SemiconjBy ℓ k (ℓ * k * ℓ⁻¹) := (inv_mul_cancel_right (ℓ * k) ℓ).symm
    rw [← hsc.orderOf_eq]
    exact (hKodd k hkH).1 hk
  have hKe : ∀ k ∈ K, e * k = k * e → k = 1 := fun k hk hek =>
    hCe k ((hH k).1 (hKH hk)) hek.symm ((hKodd k (hKH hk)).1 hk)
  have hconj : ∀ ℓ ∈ L, ∀ k ∈ K, (ℓ * e * ℓ⁻¹) * k = k * (ℓ * e * ℓ⁻¹) → k = 1 := by
    intro ℓ hℓ k hk hcomm
    have hk' : ℓ⁻¹ * k * ℓ ∈ K := by simpa using hLK ℓ⁻¹ (L.inv_mem hℓ) k hk
    have h1 : ℓ⁻¹ * k * ℓ = 1 := by
      refine hKe _ hk' ?_
      calc e * (ℓ⁻¹ * k * ℓ) = ℓ⁻¹ * ((ℓ * e * ℓ⁻¹) * k) * ℓ := by group
        _ = ℓ⁻¹ * (k * (ℓ * e * ℓ⁻¹)) * ℓ := by rw [hcomm]
        _ = (ℓ⁻¹ * k * ℓ) * e := by group
    calc k = ℓ * (ℓ⁻¹ * k * ℓ) * ℓ⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hK : K = ⊥ := by
    refine eq_bot_of_fourGroup K e u he2 hu2 heu (hLK e heL) (hLK u huL) hKe ?_ ?_
    · obtain ⟨ℓ, hℓ, hℓe⟩ := hfu
      intro k hk hcomm
      exact hconj ℓ hℓ k hk (by rw [hℓe]; exact hcomm)
    · obtain ⟨ℓ, hℓ, hℓe⟩ := hfue
      intro k hk hcomm
      exact hconj ℓ hℓ k hk (by rw [hℓe, ← heu]; exact hcomm)
  have hKone : Nat.card K = 1 := by rw [hK]; exact card_bot
  have hHA : A = H := eq_of_le_of_card_ge hAH (by rw [hKcard, hKone, mul_one])
  intro y hy
  rw [hHA]
  exact (hH y).2 hy

end CFSG.EvenSporadicStandard.M12Std.Yosh
