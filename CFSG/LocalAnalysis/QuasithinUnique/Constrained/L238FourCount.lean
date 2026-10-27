
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourCountN
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourCountBasic

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace L238

section Basic

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mk_mem_img {X B : Subgroup G} {x : ↥X} (hx : (x : G) ∈ B) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥X) x ∈ modO2Image X B :=
  Subgroup.mem_map.2 ⟨x, hx, rfl⟩

omit [Finite G] in
theorem mul_comm_of_commutator_eq_bot {Y : Type*} [Group Y] {H K : Subgroup Y}
    (h : ⁅H, K⁆ = ⊥) {u v : Y} (hu : u ∈ H) (hv : v ∈ K) : u * v = v * u := by
  have h1 : ⁅u, v⁆ ∈ ⁅H, K⁆ := Subgroup.commutator_mem_commutator hu hv
  rw [h, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

theorem mk_not_mem_zpowers_of_alt3 {X A B : Subgroup G} (hX : CharTwo X) (hA : IsBlock2 X A)
    (hB : IsBlock2 X B) (hA3 : IsAltType A 3) (hB3 : IsAltType B 3) (hne : A ≠ B)
    {c d : ↥X} (hc : (c : G) ∈ A) (hd : (d : G) ∈ B) (oc : orderOf c = 3) (od : orderOf d = 3) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥X) d ∉
      Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥X) c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  obtain ⟨cA, hcA⟩ := S14110.A4Data.of_isShort2 hA.1 hA3
  obtain ⟨cB, hcB⟩ := S14110.A4Data.of_isShort2 hB.1 hB3
  have hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := by
    rcases S14110.commute_or_eq_of_isSubnormal hX hA.2.1 hB.2.1 hA.2.2 hB.2.2 hcA hcB with
      h | h
    · exact absurd h hne
    · exact h
  have hcd : Commute c d := Subtype.ext (hcomm _ hc _ hd)
  have hq : (c ^ k)⁻¹ * d ∈ CFSG.pCore 2 ↥X := by
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥X), MonoidHom.mem_ker, map_mul, map_inv,
      map_zpow, hk, inv_mul_cancel]
  set q : ↥X := (c ^ k)⁻¹ * d with hqdef
  have hd' : d = c ^ k * q := by rw [hqdef]; group
  have hcq : Commute c q :=
    ((Commute.refl c).zpow_right k).inv_right.mul_right hcd
  have hckq : Commute (c ^ k) q := hcq.zpow_left k
  have c3 : c ^ 3 = 1 := by rw [← oc]; exact pow_orderOf_eq_one c
  have hck3 : (c ^ k) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, c3, one_zpow]
  have hd3 : d ^ 3 = 1 := by rw [← od]; exact pow_orderOf_eq_one d
  have hq3 : q ^ 3 = 1 := by
    have : d ^ 3 = (c ^ k) ^ 3 * q ^ 3 := by rw [hd']; exact hckq.mul_pow 3
    rw [hck3, one_mul] at this
    rw [← this, hd3]
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (G := ↥X) (p := 2)) ⟨q, hq⟩
  have hm' : q ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have hqo : orderOf q = 1 :=
    Nat.eq_one_of_dvd_coprimes (a := 3) (b := 2 ^ m) (Nat.Coprime.pow_right _ (by norm_num))
      (orderOf_dvd_of_pow_eq_one hq3) (orderOf_dvd_of_pow_eq_one hm')
  have hq1 : q = 1 := orderOf_eq_one_iff.1 hqo
  have hdc : d = c ^ k := by rw [hd', hq1, mul_one]
  have hdA : (d : G) ∈ A := by
    rw [hdc]
    exact Subgroup.zpow_mem A hc k
  have hd1 : (d : G) = 1 :=
    hcA.center (d : G) hdA (fun l hl => (hcomm l hl (d : G) hd).symm)
  have : d = 1 := Subtype.ext hd1
  rw [this, orderOf_one] at od
  omega

end Basic

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem commute_img {X B B' : Subgroup G} (hX : CharTwo X)
    (h37 : A37Statement (↥X ⧸ CFSG.pCore 2 ↥X)) (h : IsChiBlock X B) (h' : IsChiBlock X B')
    (hne : B ≠ B') :
    ∀ u ∈ modO2Image X B, ∀ v ∈ modO2Image X B', u * v = v * u := by
  intro u hu v hv
  by_cases hB3 : IsAltType B 3
  · by_cases hB3' : IsAltType B' 3
    · have hu' : u ∈ (B.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) := hu
      have hv' : v ∈ (B'.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) := hv
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hu'
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hv'
      obtain ⟨cA, hcA⟩ := S14110.A4Data.of_isShort2 h.1.1 hB3
      obtain ⟨cB, hcB⟩ := S14110.A4Data.of_isShort2 h'.1.1 hB3'
      rcases S14110.commute_or_eq_of_isSubnormal hX h.1.2.1 h'.1.2.1 h.1.2.2 h'.1.2.2 hcA hcB with
        hEq | hc
      · exact absurd hEq hne
      · rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hc _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hb))
    · exact (mul_comm_of_commutator_eq_bot (commute_img_NA h' hB3' h.1 hB3) hv hu).symm
  · by_cases hB3' : IsAltType B' 3
    · exact mul_comm_of_commutator_eq_bot (commute_img_NA h hB3 h'.1 hB3') hu hv
    · exact mul_comm_of_commutator_eq_bot (commute_img_NN h37 h h' hB3 hB3' hne) hu hv

theorem no_three_of_N_first {X B₁ B₂ B₃ : Subgroup G} (hX : CharTwo X)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) ≤ 2)
    (h37 : A37Statement (↥X ⧸ CFSG.pCore 2 ↥X))
    (h₁ : IsChiBlock X B₁) (h₂ : IsChiBlock X B₂) (h₃ : IsChiBlock X B₃)
    (n₁ : ¬ IsAltType B₁ 3) (h12 : B₁ ≠ B₂) (h13 : B₁ ≠ B₃) (h23 : B₂ ≠ B₃) : False := by
  obtain ⟨x₁, hx₁, ho₁⟩ := exists_orderOf_three h₁.1.2.1 (C1GN.three_dvd_card_of_isChiBlock h₁)
  obtain ⟨x₂, hx₂, ho₂⟩ := exists_orderOf_three h₂.1.2.1 (C1GN.three_dvd_card_of_isChiBlock h₂)
  obtain ⟨x₃, hx₃, ho₃⟩ := exists_orderOf_three h₃.1.2.1 (C1GN.three_dvd_card_of_isChiBlock h₃)
  have m₁ := mk_mem_img (X := X) hx₁
  have m₂ := mk_mem_img (X := X) hx₂
  have m₃ := mk_mem_img (X := X) hx₃
  have c₁₂ : Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥X) x₁) (QuotientGroup.mk' (CFSG.pCore 2 ↥X) x₂) :=
    commute_img hX h37 h₁ h₂ h12 _ m₁ _ m₂
  have c₁₃ : Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥X) x₁) (QuotientGroup.mk' (CFSG.pCore 2 ↥X) x₃) :=
    commute_img hX h37 h₁ h₃ h13 _ m₁ _ m₃
  have c₂₃ : Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥X) x₂) (QuotientGroup.mk' (CFSG.pCore 2 ↥X) x₃) :=
    commute_img hX h37 h₂ h₃ h23 _ m₂ _ m₃
  have o₁ := orderOf_mk_pCore_eq_three (X := X) ho₁
  have o₃ := orderOf_mk_pCore_eq_three (X := X) ho₃
  refine false_of_three_commuting hrk (orderOf_mk_pCore_eq_three ho₂) o₃ o₁ c₁₂ c₁₃ c₂₃ ?_ ?_
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    by_cases a₃ : IsAltType B₃ 3
    · by_cases a₂ : IsAltType B₂ 3
      · exact mk_not_mem_zpowers_of_alt3 hX h₂.1 h₃.1 a₂ a₃ h23 hx₂ hx₃ ho₂ ho₃ hmem
      · have hmem2 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) x₃ ∈ modO2Image X B₂ :=
          (Subgroup.zpowers_le.2 m₂) hmem
        have h1 := center_img_trivial h₂ a₂ hmem2
          (fun u hu => commute_img hX h37 h₃ h₂ h23.symm _ m₃ u hu)
        rw [h1, orderOf_one] at o₃
        omega
    · have h1 := center_img_trivial h₃ a₃ m₃ (fun u hu => by
        rw [← hk]
        exact (Commute.zpow_left (commute_img hX h37 h₂ h₃ h23 _ m₂ u hu) k).eq)
      rw [h1, orderOf_one] at o₃
      omega
  · intro hmem
    have h1 := center_img_trivial h₁ n₁ m₁ (fun u hu => by
      have hle : Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥X) x₂) ⊔
          Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥X) x₃) ≤ Subgroup.centralizer {u} := by
        refine sup_le ?_ ?_
        · refine Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun h hh => ?_)
          rw [Set.mem_singleton_iff.1 hh]
          exact commute_img hX h37 h₁ h₂ h12 u hu _ m₂
        · refine Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun h hh => ?_)
          rw [Set.mem_singleton_iff.1 hh]
          exact commute_img hX h37 h₁ h₃ h13 u hu _ m₃
      exact (Subgroup.mem_centralizer_iff.1 (hle hmem) u rfl).symm)
    rw [h1, orderOf_one] at o₁
    omega

theorem not_three_alt3 {X A B C : Subgroup G} (hX : CharTwo X)
    (hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) ≤ 2)
    (hA : IsChiBlock X A) (hB : IsChiBlock X B) (hC : IsChiBlock X C)
    (a : IsAltType A 3) (b : IsAltType B 3) (c : IsAltType C 3)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) : False := by
  have comm : ∀ {P Q : Subgroup G}, IsBlock2 X P → IsBlock2 X Q → IsAltType P 3 → IsAltType Q 3 →
      P ≠ Q → ⁅P, Q⁆ = ⊥ := by
    intro P Q hP hQ hP3 hQ3 hne
    obtain ⟨cP, hcP⟩ := S14110.A4Data.of_isShort2 hP.1 hP3
    obtain ⟨cQ, hcQ⟩ := S14110.A4Data.of_isShort2 hQ.1 hQ3
    rcases S14110.commute_or_eq_of_isSubnormal hX hP.2.1 hQ.2.1 hP.2.2 hQ.2.2 hcP hcQ with h | h
    · exact absurd h hne
    · rw [eq_bot_iff, Subgroup.commutator_le]
      intro x hx y hy
      exact Subgroup.mem_bot.2 (commutatorElement_eq_one_iff_mul_comm.2 (h x hx y hy))
  exact three_blocks_false_cat hX3 hA.1.2.1 hB.1.2.1 hC.1.2.1
    ⟨hA.1.1.2.1, hB.1.1.2.1, hC.1.1.2.1⟩
    ⟨C1GN.three_dvd_card_of_isChiBlock hA, C1GN.three_dvd_card_of_isChiBlock hB,
      C1GN.three_dvd_card_of_isChiBlock hC⟩ hAB hAC hBC
    ⟨comm hA.1 hB.1 a b hAB, comm hA.1 hC.1 a c hAC, comm hB.1 hC.1 b c hBC⟩

theorem not_three_chiBlocks {X A B C : Subgroup G} (hX : CharTwo X)
    (hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) ≤ 2)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) ≤ 2)
    (h37 : A37Statement (↥X ⧸ CFSG.pCore 2 ↥X)) (hA : IsChiBlock X A) (hB : IsChiBlock X B)
    (hC : IsChiBlock X C) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) : False := by
  by_cases hA3 : IsAltType A 3
  · by_cases hB3 : IsAltType B 3
    · by_cases hC3 : IsAltType C 3
      · exact not_three_alt3 hX hX3 hA hB hC hA3 hB3 hC3 hAB hAC hBC
      · exact no_three_of_N_first hX hrk h37 hC hA hB hC3 hAC.symm hBC.symm hAB
    · exact no_three_of_N_first hX hrk h37 hB hA hC hB3 hAB.symm hBC hAC
  · exact no_three_of_N_first hX hrk h37 hA hB hC hA3 hAB hAC hBC

end Assembly

end L238

end CFSG.QuasithinUnique
