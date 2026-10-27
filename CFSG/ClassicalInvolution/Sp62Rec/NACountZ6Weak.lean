module

public import CFSG.ClassicalInvolution.Sp62Rec.ModelCR1NA

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.Open

namespace Z6NA

section Seven


theorem card_modEq_one_seven {B : Subgroup ↥N0} (hBA : B ≤ A0.subgroupOf N0) (hBn : B.Normal) :
    Nat.card B ≡ 1 [MOD 7] := by
  obtain ⟨x0, hx0N, hx07, -, hfix⟩ := exists_fpf_seven
  set x : ↥N0 := ⟨x0, hx0N⟩ with hx
  have hxB : x ∈ Subgroup.normalizer (B : Set ↥N0) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hBn]
    exact Subgroup.mem_top _
  set φ : MulAut ↥B := Subgroup.normalizerMonoidHom B ⟨x, hxB⟩ with hφ
  have hx7 : x ^ 7 = 1 := Subtype.ext (by simpa using hx07)
  have hφ7 : φ ^ 7 = 1 := by
    rw [hφ, ← map_pow]
    have : (⟨x, hxB⟩ : ↥(Subgroup.normalizer (B : Set ↥N0))) ^ 7 = 1 := Subtype.ext hx7
    rw [this, map_one]
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hp : IsPGroup 7 (Subgroup.zpowers φ) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hφ7
  have hmod := hp.card_modEq_card_fixedPoints (α := ↥B)
  have hfixed : MulAction.fixedPoints (Subgroup.zpowers φ) ↥B = {1} := by
    ext b
    simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro h
      have hb : φ b = b := h ⟨φ, Subgroup.mem_zpowers φ⟩
      have hb' : x * (b : ↥N0) * x⁻¹ = b := congrArg Subtype.val hb
      have hcomm : (b : ↥N0) * x = x * b := by
        calc (b : ↥N0) * x = (x * b * x⁻¹) * x := by rw [hb']
          _ = x * b := by group
      have h1 := hfix ((b : ↥N0) : StatedSp 3 (ZMod 2)) (Subgroup.mem_subgroupOf.mp (hBA b.2))
        (congrArg Subtype.val hcomm)
      exact Subtype.ext (Subtype.ext h1)
    · rintro rfl g
      exact smul_one _
  rw [hfixed] at hmod
  simpa using hmod

theorem card_one_eight_sixtyfour {B : Subgroup ↥N0} (hBA : B ≤ A0.subgroupOf N0)
    (hBn : B.Normal) : Nat.card B = 1 ∨ Nat.card B = 8 ∨ Nat.card B = 64 := by
  have h7 := card_modEq_one_seven hBA hBn
  have hd : Nat.card B ∣ 2 ^ 6 := by
    have := Subgroup.card_dvd_of_le hBA
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe A0_le_N0).toEquiv, card_A0] at this
    norm_num
    exact this
  obtain ⟨k, hk, hkB⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  rw [hkB] at h7 ⊢
  interval_cases k
  · exact Or.inl rfl
  · exact absurd h7 (by decide)
  · exact absurd h7 (by decide)
  · exact Or.inr (Or.inl rfl)
  · exact absurd h7 (by decide)
  · exact absurd h7 (by decide)
  · exact Or.inr (Or.inr rfl)

end Seven

section Weak


theorem nu_sub {G : Type} [Group G] [Finite G] {A X : Subgroup G} (hA : IsE64 A)
    (hXN : X ≤ Subgroup.normalizer (A : Set G)) (ν : ↥X →* ↥N0)
    (hsurj : Function.Surjective ν) (hker : Nat.card ν.ker ≤ 2)
    (hAX : 32 ≤ Nat.card ↥(A ⊓ X)) :
    A ≤ X ∧ (A.subgroupOf X).map ν = A0.subgroupOf N0 ∧ Disjoint (A.subgroupOf X) ν.ker := by
  set K := A.subgroupOf X with hK
  have hKn : K.Normal :=
    ⟨fun k hk g => (Subgroup.mem_normalizer_iff.mp (hXN g.2) (k : G)).mp hk⟩
  have hKcard : Nat.card K = Nat.card ↥(A ⊓ X) := by
    rw [hK, ← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ X ≤ X)).toEquiv]
  have hAinf : Nat.card ↥(A ⊓ X) ∣ 2 ^ 6 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : A ⊓ X ≤ A)
    rw [hA.2.2] at this
    norm_num
    exact this
  set f : ↥K →* ↥N0 := ν.comp K.subtype with hf
  have hrange : f.range = K.map ν := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard : Nat.card K = Nat.card f.range * Nat.card f.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h1
    exact h1
  have hkerf : Nat.card f.ker ≤ 2 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun k : ↥f.ker => (⟨k.1.1, k.2⟩ : ↥ν.ker)) ?_) hker
    intro k l hkl
    have h := congrArg (fun y : ↥ν.ker => (y : ↥X)) hkl
    exact Subtype.ext (Subtype.ext h)
  have hkerpos : 0 < Nat.card f.ker := Nat.card_pos
  have hBn : (K.map ν).Normal := hKn.map ν hsurj
  have hKdvd : Nat.card K ∣ 2 ^ 6 := hKcard ▸ hAinf
  have hBdvd : Nat.card f.range ∣ 2 ^ 6 :=
    (Dvd.intro _ hcard.symm).trans hKdvd
  have hBp : IsPGroup 2 (K.map ν) := by
    rw [← hrange]
    exact IsPGroup.of_card_dvd_pow hBdvd
  have hBle : K.map ν ≤ A0.subgroupOf N0 := le_A0_subgroupOf hBn hBp
  have hB := card_one_eight_sixtyfour hBle hBn
  rw [← hrange] at hB
  have hK32 : 32 ≤ Nat.card K := hKcard ▸ hAX
  have hK64 : Nat.card K ≤ 64 := by
    have := Nat.le_of_dvd (by norm_num) hKdvd
    simpa using this
  have hB64 : Nat.card f.range = 64 := by
    rcases hB with h | h | h
    · rw [h] at hcard
      omega
    · rw [h] at hcard
      omega
    · exact h
  have hker1 : Nat.card f.ker = 1 := by
    rw [hB64] at hcard
    omega
  have hK64' : Nat.card K = 64 := by
    rw [hcard, hB64, hker1]
  have hA64 : Nat.card ↥(A ⊓ X) = 64 := hKcard ▸ hK64'
  have hAle : A ≤ X := by
    have hAeq : A ⊓ X = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hA.2.2, hA64])
    rw [← hAeq]
    exact inf_le_right
  have hA0card : Nat.card (A0.subgroupOf N0) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe A0_le_N0).toEquiv, card_A0]
  have hbot : f.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ hker1
  refine ⟨hAle, ?_, ?_⟩
  · refine Subgroup.eq_of_le_of_card_ge hBle ?_
    rw [← hrange, hB64, hA0card]
  · rw [disjoint_iff, eq_bot_iff]
    intro k hk
    have hk' : (⟨k, hk.1⟩ : ↥K) ∈ f.ker := hk.2
    rw [hbot, Subgroup.mem_bot] at hk'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hk')

end Weak

end Z6NA

end CFSG.ClassicalInvolution.Sp62Rec
