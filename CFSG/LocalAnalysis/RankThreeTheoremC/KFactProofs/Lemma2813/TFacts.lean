module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.HypB

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

section B

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem TT_le_pCoreOf (X : Subgroup A) : TT X ≤ pCoreOf 2 X := omegaCenter_le _

theorem normalizer_le_normalizer_TT (X : Subgroup A) :
    normalizer (X : Set A) ≤ normalizer (TT X : Set A) :=
  (normalizer_le_normalizer_pCoreOf (le_refl _)).trans
    (normalizer_le_normalizer_omegaCenter (pCoreOf 2 X))

theorem TT_comm (X : Subgroup A) {a b : A} (ha : a ∈ TT X) (hb : b ∈ TT X) :
    a * b = b * a :=
  (mem_omegaCenter.1 ha).2.1 b (mem_omegaCenter.1 hb).1

theorem TT_sq (X : Subgroup A) {a : A} (ha : a ∈ TT X) : a ^ 2 = 1 :=
  (mem_omegaCenter.1 ha).2.2

theorem pCoreOf_comm_TT (X : Subgroup A) {q t : A} (hq : q ∈ pCoreOf 2 X) (ht : t ∈ TT X) :
    q * t = t * q :=
  ((mem_omegaCenter.1 ht).2.1 q hq).symm

theorem mem_T0_iff (X : Subgroup A) {t : A} :
    t ∈ T0 X ↔ t ∈ TT X ∧ ∀ x ∈ X, x * t = t * x := by
  show t ∈ TT X ⊓ centralizer (X : Set A) ↔ _
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  rfl

theorem Hyp2813.mem_omegaCenter_S_iff (h : Hyp2813 X K R P) {v : A} :
    v ∈ omegaCenter (pCoreOf 2 P) ↔ v ∈ TT X ∧ ∀ s ∈ pCoreOf 2 P, s * v = v * s := by
  constructor
  · intro hv
    obtain ⟨hvS, hvC, hv2⟩ := mem_omegaCenter.1 hv
    have hvX : v ∈ X := h.P_le (pCoreOf_le_self P hvS)
    have hvQ : v ∈ pCoreOf 2 X := h.charTwo (Subgroup.mem_inf.2 ⟨hvX,
      Subgroup.mem_centralizer_iff.2 fun q hq => (hvC q (h.pCore_X_le_pCore_P hq)).symm⟩)
    exact ⟨mem_omegaCenter.2 ⟨hvQ, fun q hq => hvC q (h.pCore_X_le_pCore_P hq), hv2⟩,
      fun s hs => (hvC s hs).symm⟩
  · rintro ⟨hvT, hvC⟩
    have hvQ : v ∈ pCoreOf 2 X := TT_le_pCoreOf X hvT
    exact mem_omegaCenter.2
      ⟨h.pCore_X_le_pCore_P hvQ, fun s hs => (hvC s hs).symm, TT_sq X hvT⟩

theorem Hyp2813.mem_omegaCenter_R_iff (h : Hyp2813 X K R P) {z : A} :
    z ∈ omegaCenter R ↔ z ∈ TT X ∧ ∀ r ∈ R, r * z = z * r := by
  constructor
  · intro hz
    obtain ⟨hzR, hzC, hz2⟩ := mem_omegaCenter.1 hz
    have hzX : z ∈ X := h.R_le hzR
    have hzQ : z ∈ pCoreOf 2 X := h.charTwo (Subgroup.mem_inf.2 ⟨hzX,
      Subgroup.mem_centralizer_iff.2 fun q hq => (hzC q (h.pCore_X_le_R hq)).symm⟩)
    exact ⟨mem_omegaCenter.2 ⟨hzQ, fun q hq => hzC q (h.pCore_X_le_R hq), hz2⟩,
      fun r hr => (hzC r hr).symm⟩
  · rintro ⟨hzT, hzC⟩
    have hzQ : z ∈ pCoreOf 2 X := TT_le_pCoreOf X hzT
    exact mem_omegaCenter.2 ⟨h.pCore_X_le_R hzQ, fun r hr => (hzC r hr).symm, TT_sq X hzT⟩

theorem Hyp2813.maximal_P (h : Hyp2813 X K R P) {Y : Subgroup A} (h1 : P ≤ Y) (h2 : Y ≤ X) :
    Y = P ∨ Y = X := by
  have hmul := Subgroup.relIndex_mul_relIndex P Y X h1 h2
  have h7 : P.relIndex X = 7 := h.P_index
  rw [h7] at hmul
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 (Dvd.intro _ hmul) with h1' | h7'
  · left
    exact le_antisymm (Subgroup.relIndex_eq_one.1 h1') h1
  · right
    rw [h7'] at hmul
    have : Y.relIndex X = 1 := by omega
    exact le_antisymm h2 (Subgroup.relIndex_eq_one.1 this)

theorem tf_card_mul_index {H L : Subgroup A} (hHL : H ≤ L) :
    Nat.card H * (H.subgroupOf L).index = Nat.card L := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv]
  exact Subgroup.card_mul_index _

theorem Hyp2813.card_R (h : Hyp2813 X K R P) :
    Nat.card R = Nat.card (pCoreOf 2 X) * 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).1 h.R_two
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := 2)).1 (isPGroup_pCoreOf X)
  have hRX := tf_card_mul_index h.R_le
  have hodd : Nat.Coprime 2 (R.subgroupOf X).index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h.R_sylow
  obtain ⟨m, hm⟩ : ∃ m, (R.subgroupOf X).index = m := ⟨_, rfl⟩
  rw [hm] at hRX hodd
  rw [h.card_X, ha, hb] at hRX
  have e1 : 2 ^ a * m = 2 ^ (b + 3) * 21 := by rw [hRX]; ring
  have hc21 : Nat.Coprime (2 ^ a) 21 := Nat.Coprime.pow_left _ (by norm_num)
  have hcm : Nat.Coprime (2 ^ (b + 3)) m := Nat.Coprime.pow_left _ hodd
  have d1 : 2 ^ a ∣ 2 ^ (b + 3) := hc21.dvd_of_dvd_mul_right ⟨m, e1.symm⟩
  have d2 : 2 ^ (b + 3) ∣ 2 ^ a := hcm.dvd_of_dvd_mul_right ⟨21, e1⟩
  have := Nat.dvd_antisymm d1 d2
  rw [ha, hb, this]
  ring

theorem Hyp2813.card_P (h : Hyp2813 X K R P) :
    Nat.card P = Nat.card (pCoreOf 2 X) * 24 := by
  have h1 := tf_card_mul_index h.P_le
  rw [h.P_index, h.card_X] at h1
  omega

theorem Hyp2813.D_card (h : Hyp2813 X K R P) {D : Subgroup A} (hDP : D ≤ P)
    (hD3 : IsPGroup 3 D) (hDi : ¬ 3 ∣ (D.subgroupOf P).index) : Nat.card D = 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 3)).1 hD3
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := 2)).1 (isPGroup_pCoreOf X)
  have hDP' := tf_card_mul_index hDP
  have hm3 : Nat.Coprime 3 (D.subgroupOf P).index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hDi
  obtain ⟨m, hm⟩ : ∃ m, (D.subgroupOf P).index = m := ⟨_, rfl⟩
  rw [hm] at hDP' hm3
  rw [h.card_P, ha, hb] at hDP'
  have hc : Nat.Coprime (3 ^ a) (2 ^ (b + 3)) := Nat.Coprime.pow _ _ (by norm_num)
  have d1 : 3 ^ a ∣ 3 :=
    hc.dvd_of_dvd_mul_left ⟨m, by rw [hDP']; ring⟩
  have d3 : 3 ∣ 3 ^ a := hm3.dvd_of_dvd_mul_right ⟨2 ^ b * 8, by rw [hDP']; ring⟩
  rcases (Nat.dvd_prime Nat.prime_three).1 d1 with h1 | h3
  · exfalso
    rw [h1] at d3
    omega
  · rw [ha]
    exact h3

theorem Hyp2813.P_eq_sup (h : Hyp2813 X K R P) {D : Subgroup A} (hDP : D ≤ P)
    (hD3 : IsPGroup 3 D) (hDi : ¬ 3 ∣ (D.subgroupOf P).index) : R ⊔ D = P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup : R ⊔ D ≤ P := sup_le h.R_le_P hDP
  have hD := h.D_card hDP hD3 hDi
  have hR := h.card_R
  have hP := h.card_P
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := 2)).1 (isPGroup_pCoreOf X)
  have d1 : Nat.card R ∣ Nat.card ↥(R ⊔ D) := Subgroup.card_dvd_of_le le_sup_left
  have d2 : Nat.card D ∣ Nat.card ↥(R ⊔ D) := Subgroup.card_dvd_of_le le_sup_right
  have hcop : Nat.Coprime (Nat.card R) (Nat.card D) := by
    rw [hD, hR, hb]
    exact Nat.Coprime.mul_left (Nat.Coprime.pow_left b (by norm_num)) (by norm_num)
  have d3 : Nat.card R * Nat.card D ∣ Nat.card ↥(R ⊔ D) := hcop.mul_dvd_of_dvd_of_dvd d1 d2
  have hPeq : Nat.card P = Nat.card R * Nat.card D := by rw [hP, hR, hD]; ring
  have hle : Nat.card P ≤ Nat.card ↥(R ⊔ D) := by
    rw [hPeq]
    exact Nat.le_of_dvd Nat.card_pos d3
  exact Subgroup.eq_of_le_of_card_ge hsup hle

theorem Hyp2813.D_cyclic (h : Hyp2813 X K R P) {D : Subgroup A} (hDP : D ≤ P)
    (hD3 : IsPGroup 3 D) (hDi : ¬ 3 ∣ (D.subgroupOf P).index) :
    ∃ d₀ ∈ D, D = zpowers d₀ ∧ orderOf d₀ = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.D_card hDP hD3 hDi
  haveI : IsCyclic D := isCyclic_of_prime_card hD
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := D)
  have hDeq : D = zpowers (g : A) := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
      exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact D.zpow_mem g.2 k
  refine ⟨g, g.2, hDeq, ?_⟩
  rw [← Nat.card_zpowers, ← hDeq, hD]

end B

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813
