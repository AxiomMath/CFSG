module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Prod
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75N8
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Sec44
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Sec45a
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Conj

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

section Sec45

variable {S : Type} [Group S] [Finite S]

theorem card_normalizer_le_32_aux (hS : IsPGroup 2 S) {A E : Subgroup S}
    (hA : IsElemAbelian 2 A) (hA8 : Nat.card A = 8)
    (hCA : Subgroup.centralizer (A : Set S) ≤ A) (hAn : ¬ A.Normal)
    (hE : IsElemAbelian 2 E) (hE8 : Nat.card E = 8) (hEn : E.Normal)
    (hAE4 : Nat.card (A ⊓ E : Subgroup S) = 4)
    (hno : ∀ (F : Subgroup S) (z : S), ¬ Cfg2 S E F z)
    (hN64 : Nat.card (Subgroup.normalizer (A : Set S)) ≤ 64)
    (hNnc : Nat.card (Subgroup.normalizer (A : Set S)) = 64 →
      ∃ s ∈ Subgroup.normalizer (A : Set S), ∃ t ∈ Subgroup.normalizer (A : Set S),
        s * t * s⁻¹ * t⁻¹ ∉ A) :
    Nat.card (Subgroup.normalizer (A : Set S)) ≤ 32 := by
  classical
  by_contra hbig
  have hbig : 32 < Nat.card (Subgroup.normalizer (A : Set S)) := not_le.mp hbig
  set N : Subgroup S := Subgroup.normalizer (A : Set S) with hNdef
  have hAN : A ≤ N := Subgroup.le_normalizer
  obtain ⟨hEN, hAE16, hsub⟩ := sub_E8_of_AE hA hA8 hE hE8 hEn hAE4 hCA
  have hEN' : E ≤ N := hEN
  have hN2 : IsPGroup 2 N := hS.to_subgroup N
  have hN64' : Nat.card N = 64 := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hN2
    have hm6 : m = 6 := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have : 2 ^ m ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      · have : 2 ^ 7 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    rw [hm, hm6]
    norm_num
  obtain ⟨s, hsN, t₀, ht₀N, hst⟩ := hNnc hN64'
  have hANA : ∀ n ∈ N, ∀ a ∈ A, n * a * n⁻¹ ∈ A := fun n hn a ha =>
    (Subgroup.mem_normalizer_iff.mp hn a).mp ha
  have hNtop : N ≠ ⊤ := fun h => hAn (Subgroup.normalizer_eq_top_iff.mp h)
  have : Group.IsNilpotent S := hS.isNilpotent
  obtain ⟨t, htNN, htN⟩ : ∃ t ∈ Subgroup.normalizer (N : Set S), t ∉ N := by
    have hlt : N < Subgroup.normalizer (N : Set S) :=
      Group.normalizerCondition_of_isNilpotent N (lt_top_iff_ne_top.mpr hNtop)
    exact SetLike.exists_of_lt hlt
  have htN_conj : ∀ n, n ∈ N ↔ t * n * t⁻¹ ∈ N := Subgroup.mem_normalizer_iff.mp htNN
  have htN_conj' : ∀ n ∈ N, t⁻¹ * n * t ∈ N := by
    intro n hn
    refine (htN_conj (t⁻¹ * n * t)).mpr ?_
    have e : t * (t⁻¹ * n * t) * t⁻¹ = n := by group
    rw [e]
    exact hn
  set B : Subgroup S := conjSub t A with hBdef
  have hBN : B ≤ N := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_conjSub_iff.mp hx
    exact (htN_conj a).mp (hAN ha)
  have hNB : ∀ n ∈ N, ∀ b ∈ B, n * b * n⁻¹ ∈ B := by
    intro n hn b hb
    obtain ⟨a, ha, rfl⟩ := mem_conjSub_iff.mp hb
    have hn' : t⁻¹ * n * t ∈ N := htN_conj' n hn
    have h1 : (t⁻¹ * n * t) * a * (t⁻¹ * n * t)⁻¹ ∈ A := hANA _ hn' a ha
    have e : n * (t * a * t⁻¹) * n⁻¹ = t * ((t⁻¹ * n * t) * a * (t⁻¹ * n * t)⁻¹) * t⁻¹ := by
      group
    rw [e]
    exact conj_mem_conjSub h1
  have hBA_ne : B ≠ A := fun h => htN (conjSub_eq_iff.mp h)
  have hB8 : Nat.card B = 8 := (card_conjSub t A).trans hA8
  have hBel : IsElemAbelian 2 B := isElemAbelian_conjSub t hA
  have hCB : Subgroup.centralizer (B : Set S) ≤ B := centralizer_conjSub_le t hCA
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ A ⊓ B := by
    intro a ha b hb
    refine ⟨?_, ?_⟩
    · have h1 : b * a⁻¹ * b⁻¹ ∈ A := hANA b (hBN hb) a⁻¹ (A.inv_mem ha)
      have : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
      rw [this]
      exact A.mul_mem ha h1
    · exact B.mul_mem (hNB a (hAN ha) b hb) (B.inv_mem hb)
  have hABdvd : Nat.card (A ⊓ B : Subgroup S) ∣ 8 := by
    rw [← hA8]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hAB_ne1 : Nat.card (A ⊓ B : Subgroup S) ≠ 1 := by
    intro h1
    have hbot : A ⊓ B = ⊥ := (Subgroup.eq_bot_iff_card _).mpr h1
    have hBle : B ≤ A := by
      intro b hb
      apply hCA
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h2 : a * b * a⁻¹ * b⁻¹ ∈ A ⊓ B := hcomm a ha b hb
      rw [hbot, Subgroup.mem_bot] at h2
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = b * a := by rw [h2, one_mul]
    exact hBA_ne (Subgroup.eq_of_le_of_card_ge hBle (by rw [hA8, hB8]))
  have hAB_ne8 : Nat.card (A ⊓ B : Subgroup S) ≠ 8 := by
    intro h8
    have hAeq : A ⊓ B = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, hA8])
    have hBeq : A ⊓ B = B := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h8, hB8])
    exact hBA_ne (hBeq.symm.trans hAeq)
  have hABc : Nat.card (A ⊓ B : Subgroup S) = 2 ∨ Nat.card (A ⊓ B : Subgroup S) = 4 := by
    generalize Nat.card (A ⊓ B : Subgroup S) = c at hABdvd hAB_ne1 hAB_ne8
    have hc : c ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hABdvd, by norm_num⟩
    have : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [this] at hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with h | h | h | h
    · exact absurd h hAB_ne1
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hAB_ne8
  rcases hABc with hAB2 | hAB4
  ·
    have hBE : Nat.card (B ⊓ E : Subgroup S) = 4 := by
      rw [hBdef, card_inf_conjSub t A hEn]
      exact hAE4
    obtain ⟨F, z, hcfg⟩ := cfg2_of_AB A B E hA hA8 hBel hB8 hE hE8 hEn hCA hCB hAB2 hAE4 hBE hcomm
    exact hno F z hcfg
  ·
    have hAB_le : A ≤ Subgroup.normalizer (B : Set S) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact hNB a (hAN ha) x hx
      · intro hx
        have := hNB a⁻¹ (hAN (A.inv_mem ha)) _ hx
        have e : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
        rwa [e] at this
    have hAB16 : Nat.card (A ⊔ B : Subgroup S) = 16 := by
      have h := card_sup_mul_card_inf A B hAB_le
      rw [hAB4, hA8, hB8] at h
      omega
    have hM₁n : ∀ n ∈ N, ∀ x ∈ A ⊔ E, n * x * n⁻¹ ∈ A ⊔ E := by
      intro n hn x hx
      obtain ⟨a, ha, e, he, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
      have e1 : n * (a * e) * n⁻¹ = (n * a * n⁻¹) * (n * e * n⁻¹) := by group
      rw [e1]
      exact Subgroup.mul_mem_sup (hANA n hn a ha) (hEn.conj_mem e he n)
    have hM₂n : ∀ n ∈ N, ∀ x ∈ A ⊔ B, n * x * n⁻¹ ∈ A ⊔ B := by
      intro n hn x hx
      have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right A B hAB_le
      have hx' : x ∈ (↑(A ⊔ B) : Set S) := hx
      rw [hcoe] at hx'
      obtain ⟨a, ha, b, hb, rfl⟩ := hx'
      have e1 : n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) := by group
      show n * (a * b) * n⁻¹ ∈ A ⊔ B
      rw [e1]
      exact Subgroup.mul_mem_sup (hANA n hn a ha) (hNB n hn b hb)
    have hM := eq_of_normal_index_two (N := N) (A := A) (M₁ := A ⊔ E) (M₂ := A ⊔ B) hAN hANA
      (by rw [hN64', hA8]) ⟨s, hsN, t₀, ht₀N, hst⟩ le_sup_left (sup_le hAN hEN') hM₁n
      (by rw [hAE16, hA8]) le_sup_left (sup_le hAN hBN) hM₂n (by rw [hAB16, hA8])
    have hBle : B ≤ A ⊔ E := by
      rw [hM]
      exact le_sup_right
    rcases hsub B hBle hBel hB8 with hBA | hBE
    · exact hBA_ne hBA
    ·
      have hAE : A ≤ E := by
        intro x hx
        have h1 : t * x * t⁻¹ ∈ B := conj_mem_conjSub hx
        rw [hBE] at h1
        have h2 := hEn.conj_mem _ h1 t⁻¹
        have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
        rwa [e] at h2
      have : A ⊓ E = A := inf_eq_left.mpr hAE
      rw [this, hA8] at hAE4
      omega

theorem card_normalizer_le_32 (hS : IsPGroup 2 S) {A E : Subgroup S}
    (hA : IsElemAbelian 2 A) (hA8 : Nat.card A = 8)
    (hCA : Subgroup.centralizer (A : Set S) ≤ A) (hAn : ¬ A.Normal)
    (hE : IsElemAbelian 2 E) (hE8 : Nat.card E = 8) (hEn : E.Normal)
    (hAE4 : Nat.card (A ⊓ E : Subgroup S) = 4)
    (hno : ∀ (F : Subgroup S) (z : S), ¬ Cfg2 S E F z) :
    Nat.card (Subgroup.normalizer (A : Set S)) ≤ 32 :=
  card_normalizer_le_32_aux hS hA hA8 hCA hAn hE hE8 hEn hAE4 hno
    (card_normalizer_A_le hS hA hA8 hCA).1 (card_normalizer_A_le hS hA hA8 hCA).2

end Sec45

end CFSG.EvenSporadicStandard.Fin76b
