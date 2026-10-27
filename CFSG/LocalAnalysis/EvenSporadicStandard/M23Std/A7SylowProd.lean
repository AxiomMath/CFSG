module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.WreathSylow
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.ABGLocalTools

theorem card_inf_centralizer_of_card_eight {Y : Type*} [Group Y] [Finite Y] {Q : Subgroup Y}
    (hQ : Nat.card Q = 8) {a : Y} (ha : a ∈ Q) (ha2 : a * a = 1) :
    4 ≤ Nat.card ↥(Q ⊓ centralizer ({a} : Set Y)) ∧
      (Nat.card ↥(Q ⊓ centralizer ({a} : Set Y)) = 4 →
        ∀ g ∈ Q ⊓ centralizer ({a} : Set Y), g * g = 1) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 3) (by rw [hQ]; norm_num)
  have hnt : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.1 (by rw [hQ]; norm_num)
  have hcn : Nontrivial (center Q) := hQp.center_nontrivial
  obtain ⟨⟨c, hcc⟩, hc1⟩ := exists_ne (1 : center Q)
  set C := Q ⊓ centralizer ({a} : Set Y)
  set Z := Q ⊓ centralizer (Q : Set Y)
  have hCQ : C ≤ Q := inf_le_left
  have hZc : ∀ z ∈ Z, ∀ q ∈ Q, q * z = z * q := fun z hz q hq =>
    mem_centralizer_iff.1 hz.2 q hq
  have hZC : Z ≤ C := fun z hz => ⟨hz.1, mem_centralizer_singleton_iff.2 (hZc z hz a ha).symm⟩
  have haC : a ∈ C := ⟨ha, mem_centralizer_singleton_iff.2 rfl⟩
  have hcZ : (c : Y) ∈ Z :=
    ⟨c.2, mem_centralizer_iff.2 fun q hq => congrArg Subtype.val (mem_center_iff.1 hcc ⟨q, hq⟩)⟩
  have hZne : 2 ≤ Nat.card Z := by
    have : Z ≠ ⊥ := by
      intro h
      rw [h, mem_bot] at hcZ
      exact hc1 (Subtype.ext (Subtype.ext hcZ))
    exact (one_lt_card_iff_ne_bot Z).2 this
  by_cases haZ : a ∈ Z
  · have hCQ' : C = Q :=
      le_antisymm hCQ fun q hq => ⟨hq, mem_centralizer_singleton_iff.2 (hZc a haZ q hq)⟩
    rw [hCQ', hQ]
    exact ⟨by norm_num, fun h => absurd h (by norm_num)⟩
  · set H := zpowers a ⊔ Z
    have hZH : Z ≤ H := le_sup_right
    have haH : a ∈ H := mem_sup_left (mem_zpowers a)
    have hHC : H ≤ C := sup_le (zpowers_le.2 haC) hZC
    have hZcard : Nat.card Z < Nat.card H := by
      by_contra hnot
      exact haZ ((eq_of_le_of_card_ge hZH (not_lt.1 hnot)) ▸ haH)
    have hH4 : 4 ≤ Nat.card H := by
      obtain ⟨k, hk⟩ := card_dvd_of_le hZH
      rw [hk] at hZcard ⊢
      rcases k with _ | _ | k
      · simp at hZcard
      · simp at hZcard
      · nlinarith
    have hHC' : Nat.card H ≤ Nat.card C := card_le_of_le hHC
    refine ⟨hH4.trans hHC', fun h4 => ?_⟩
    have hH4' : Nat.card H = 4 := le_antisymm (h4 ▸ hHC') hH4
    have hHeq : H = C := eq_of_le_of_card_ge hHC (by omega)
    have hZ2 : Nat.card Z = 2 := by
      have hdvd : Nat.card Z ∣ 4 := hH4' ▸ card_dvd_of_le hZH
      obtain ⟨m, hm⟩ : ∃ m, Nat.card Z = m := ⟨_, rfl⟩
      rw [hm] at hdvd hZne hZcard ⊢
      have hm4 : m < 4 := hH4' ▸ hZcard
      interval_cases m
      · rfl
      · omega
    have hZsq : ∀ z ∈ Z, z * z = 1 := by
      intro z hz
      have := Subgroup.orderOf_dvd_natCard Z hz
      rw [hZ2] at this
      rw [← pow_two]
      exact orderOf_dvd_iff_pow_eq_one.1 this
    have hZcent : Z ≤ centralizer (zpowers a : Set Y) := by
      intro z hz
      rw [mem_centralizer_iff]
      rintro u ⟨k, rfl⟩
      exact (Commute.zpow_left (show Commute a z from hZc z hz a ha) k).eq
    intro g hg
    rw [← hHeq] at hg
    obtain ⟨u, hu, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hZcent hg
    have hu2 : u * u = 1 := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hu
      rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, ha2, one_zpow]
    have hzu : u * z = z * u := mem_centralizer_iff.1 (hZcent hz) u hu
    calc u * z * (u * z) = u * (z * u) * z := by group
      _ = u * (u * z) * z := by rw [hzu]
      _ = (u * u) * (z * z) := by group
      _ = 1 := by rw [hu2, hZsq z hz, one_mul]

theorem card_eq_eight_of_isSylowOf_alternating {Y : Type*} [Group Y] [Finite Y]
    {N Q : Subgroup Y} (e : Nonempty (N ≃* alternatingGroup (Fin 7))) (hQ : IsSylowOf 2 Q N) :
    Nat.card Q = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := e
  have hN : Nat.card N = 2520 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp only [Fintype.card_fin]
    decide
  have hf : (2520 : ℕ).factorization 2 = 3 := by
    have h : (2520 : ℕ) = 2 ^ 3 * 315 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [hQ.card_eq, hN, hf]
  norm_num

theorem natCard_sup_eq_mul {Y : Type*} [Group Y] {H₁ H₂ : Subgroup Y}
    (hcomm : H₂ ≤ centralizer (H₁ : Set Y)) (hdisj : Disjoint H₁ H₂) :
    Nat.card ↥(H₁ ⊔ H₂) = Nat.card H₁ * Nat.card H₂ := by
  rw [← Nat.card_prod]
  exact (Nat.card_congr (mulEquivProdSup hcomm hdisj).toEquiv).symm

theorem sylow_prod_centralizer {Y : Type} [Group Y] [Finite Y] {N1 N2 T : Subgroup Y}
    (e1 : Nonempty (N1 ≃* alternatingGroup (Fin 7)))
    (e2 : Nonempty (N2 ≃* alternatingGroup (Fin 7)))
    (hcomm : ∀ a ∈ N1, ∀ b ∈ N2, a * b = b * a) (hdisj : Disjoint N1 N2)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (N1 ⊔ N2)) {y : Y} (hy : y ∈ T) (hy2 : y * y = 1) :
    16 ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({y} : Set Y)) ∧
      (Nat.card ↥(T ⊓ Subgroup.centralizer ({y} : Set Y)) = 16 →
        ∀ g ∈ T ⊓ Subgroup.centralizer ({y} : Set Y), g * g = 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h12 : N2 ≤ centralizer (N1 : Set Y) := fun b hb =>
    mem_centralizer_iff.2 fun a ha => hcomm a ha b hb
  have h21 : N1 ≤ centralizer (N2 : Set Y) := fun a ha =>
    mem_centralizer_iff.2 fun b hb => (hcomm a ha b hb).symm
  have hQ1 : IsSylowOf 2 (T ⊓ N1) N1 := hT.inf_of_le_normalizer le_sup_left
    (sup_le le_normalizer (h12.trans (centralizer_le_normalizer _)))
  have hQ2 : IsSylowOf 2 (T ⊓ N2) N2 := hT.inf_of_le_normalizer le_sup_right
    (sup_le (h21.trans (centralizer_le_normalizer _)) le_normalizer)
  have hc1 := card_eq_eight_of_isSylowOf_alternating e1 hQ1
  have hc2 := card_eq_eight_of_isSylowOf_alternating e2 hQ2
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_mem_of_isSylowOf_sup hcomm hdisj hT hy
  have haN : a ∈ N1 := (mem_inf.1 ha).2
  have hbN : b ∈ N2 := (mem_inf.1 hb).2
  have hba : b * a = a * b := (hcomm a haN b hbN).symm
  have hsq : a * a * (b * b) = 1 :=
    calc a * a * (b * b) = a * (a * b) * b := by group
      _ = a * (b * a) * b := by rw [hba]
      _ = a * b * (a * b) := by group
      _ = 1 := hy2
  have ha2 : a * a = 1 := by
    have h1 : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left hsq
    refine Subgroup.disjoint_def.1 hdisj (mul_mem haN haN) ?_
    rw [h1]
    exact inv_mem (mul_mem hbN hbN)
  have hb2 : b * b = 1 := by rwa [ha2, one_mul] at hsq
  obtain ⟨hA1, hB1⟩ := card_inf_centralizer_of_card_eight hc1 ha ha2
  obtain ⟨hA2, hB2⟩ := card_inf_centralizer_of_card_eight hc2 hb hb2
  set H₁ := (T ⊓ N1) ⊓ centralizer ({a} : Set Y)
  set H₂ := (T ⊓ N2) ⊓ centralizer ({b} : Set Y)
  have hH₁N : H₁ ≤ N1 := fun x hx => hx.1.2
  have hH₂N : H₂ ≤ N2 := fun x hx => hx.1.2
  have hH₁c : H₁ ≤ T ⊓ centralizer ({a * b} : Set Y) := by
    rintro x ⟨⟨hxT, hxN⟩, hxa⟩
    refine ⟨hxT, mem_centralizer_singleton_iff.2 ?_⟩
    have hxa' : x * a = a * x := mem_centralizer_singleton_iff.1 hxa
    have hxb : x * b = b * x := hcomm x hxN b hbN
    calc x * (a * b) = (x * a) * b := by group
      _ = a * x * b := by rw [hxa']
      _ = a * (x * b) := by group
      _ = a * (b * x) := by rw [hxb]
      _ = a * b * x := by group
  have hH₂c : H₂ ≤ T ⊓ centralizer ({a * b} : Set Y) := by
    rintro x ⟨⟨hxT, hxN⟩, hxb⟩
    refine ⟨hxT, mem_centralizer_singleton_iff.2 ?_⟩
    have hxb' : x * b = b * x := mem_centralizer_singleton_iff.1 hxb
    have hxa : a * x = x * a := hcomm a haN x hxN
    calc x * (a * b) = (x * a) * b := by group
      _ = (a * x) * b := by rw [hxa]
      _ = a * (x * b) := by group
      _ = a * (b * x) := by rw [hxb']
      _ = a * b * x := by group
  have hsup : H₁ ⊔ H₂ ≤ T ⊓ centralizer ({a * b} : Set Y) := sup_le hH₁c hH₂c
  have hcent : H₂ ≤ centralizer (H₁ : Set Y) := fun x hx =>
    mem_centralizer_iff.2 fun h hh => hcomm h (hH₁N hh) x (hH₂N hx)
  have hcard : Nat.card ↥(H₁ ⊔ H₂) = Nat.card H₁ * Nat.card H₂ :=
    natCard_sup_eq_mul hcent (hdisj.mono hH₁N hH₂N)
  have hle : Nat.card ↥(H₁ ⊔ H₂) ≤ Nat.card ↥(T ⊓ centralizer ({a * b} : Set Y)) :=
    card_le_of_le hsup
  refine ⟨?_, fun h16 => ?_⟩
  · calc 16 = 4 * 4 := by norm_num
      _ ≤ Nat.card H₁ * Nat.card H₂ := Nat.mul_le_mul hA1 hA2
      _ = Nat.card ↥(H₁ ⊔ H₂) := hcard.symm
      _ ≤ _ := hle
  · have h44 : Nat.card H₁ = 4 ∧ Nat.card H₂ = 4 := by
      rw [h16, hcard] at hle
      constructor <;> nlinarith
    have hHeq : H₁ ⊔ H₂ = T ⊓ centralizer ({a * b} : Set Y) :=
      eq_of_le_of_card_ge hsup (by rw [hcard, h44.1, h44.2, h16])
    intro g hg
    rw [← hHeq] at hg
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hcent hg
    have hu2 := hB1 h44.1 u hu
    have hv2 := hB2 h44.2 v hv
    have huv : u * v = v * u := hcomm u (hH₁N hu) v (hH₂N hv)
    calc u * v * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [huv]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [hu2, hv2, one_mul]

end CFSG.EvenSporadicStandard.M23Std
