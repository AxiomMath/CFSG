module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Misc
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem odd_card_oddCore' (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem not_prime_of_two_dvd {n : ℕ} (h2 : 2 ∣ n) (hne : n ≠ 2) : ¬ n.Prime := by
  intro hp
  rcases hp.eq_two_or_odd' with h | ho
  · exact hne h
  · exact ho.not_two_dvd_nat h2

theorem eq_of_commuting_involutions_of_cyclic_sylow {H : Type} [Group H] [Finite H]
    (hcyc : ∀ P : Sylow 2 H, IsCyclic ↥(P : Subgroup H)) {a b : H} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : a * b = b * a) : a = b := by
  classical
  let A : Subgroup H := Subgroup.zpowers a
  let B : Subgroup H := Subgroup.zpowers b
  have hAcard : Nat.card A = 2 := by
    change Nat.card (Subgroup.zpowers a) = 2
    rw [Nat.card_zpowers, ha]
  have hBcard : Nat.card B = 2 := by
    change Nat.card (Subgroup.zpowers b) = 2
    rw [Nat.card_zpowers, hb]
  have hA : IsPGroup 2 A := IsPGroup.of_card (n := 1) (by rw [hAcard]; norm_num)
  have hB : IsPGroup 2 B := IsPGroup.of_card (n := 1) (by rw [hBcard]; norm_num)
  have hBcent : B ≤ Subgroup.centralizer ({a} : Set H) := by
    change Subgroup.zpowers b ≤ Subgroup.centralizer ({a} : Set H)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hab
  have hAcent : A ≤ Subgroup.centralizer (B : Set H) := by
    change Subgroup.zpowers a ≤ Subgroup.centralizer (B : Set H)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.mp (hBcent hy)) a (Set.mem_singleton a)).symm
  have hAB : A ≤ Subgroup.normalizer (B : Set H) :=
    hAcent.trans (Subgroup.centralizer_le_normalizer (B : Set H))
  have hsup : IsPGroup 2 (A ⊔ B : Subgroup H) :=
    IsPGroup.to_sup_of_normal_right' hA hB hAB
  obtain ⟨P, hP⟩ := hsup.exists_le_sylow
  have hPcyc : IsCyclic ↥(P : Subgroup H) := hcyc P
  have hAle : A ≤ (P : Subgroup H) := le_sup_left.trans hP
  have hBle : B ≤ (P : Subgroup H) := le_sup_right.trans hP
  haveI : IsCyclic ↥(P : Subgroup H) := hPcyc
  have hcardA' : Nat.card (A.subgroupOf (P : Subgroup H)) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAle).toEquiv, hAcard]
  have hcardB' : Nat.card (B.subgroupOf (P : Subgroup H)) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBle).toEquiv, hBcard]
  have hABeq : A.subgroupOf (P : Subgroup H) = B.subgroupOf (P : Subgroup H) :=
    (IsCyclic.subgroup_eq_iff_card_eq).mpr (by rw [hcardA', hcardB'])
  have haP : a ∈ (P : Subgroup H) := hAle (Subgroup.mem_zpowers a)
  have hmemA : (⟨a, haP⟩ : ↥(P : Subgroup H)) ∈ A.subgroupOf (P : Subgroup H) := by
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_zpowers a
  have hmemB : (⟨a, haP⟩ : ↥(P : Subgroup H)) ∈ B.subgroupOf (P : Subgroup H) := by
    rw [← hABeq]
    exact hmemA
  have haB : a ∈ B := by
    rw [Subgroup.mem_subgroupOf] at hmemB
    exact hmemB
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha
    exact absurd ha (by norm_num)
  change a ∈ Subgroup.zpowers b at haB
  rw [mem_zpowers_iff_mem_range_orderOf, hb] at haB
  rw [Finset.mem_image] at haB
  obtain ⟨i, hi, hia⟩ := haB
  rw [Finset.mem_range] at hi
  have hi01 : i = 0 ∨ i = 1 := by omega
  rcases hi01 with rfl | rfl
  · simp at hia
    exact absurd hia.symm ha1
  · simpa using hia.symm

theorem not_injective_quaternion_of_cyclic_sylow {H : Type} [Group H] [Finite H]
    (hcyc : ∀ P : Sylow 2 H, IsCyclic ↥(P : Subgroup H)) (f : QuaternionGroup 2 →* H) :
    ¬ Function.Injective f := by
  intro hf
  have hQcard : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hQ2 : IsPGroup 2 (QuaternionGroup 2) :=
    IsPGroup.of_card (n := 3) (by rw [hQcard]; norm_num)
  have hrange : IsPGroup 2 f.range :=
    hQ2.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨P, hP⟩ := hrange.exists_le_sylow
  have hPcyc : IsCyclic ↥(P : Subgroup H) := hcyc P
  letI : IsCyclic ↥(P : Subgroup H) := hPcyc
  have hcomm : ∀ x y : QuaternionGroup 2, f (x * y) = f (y * x) := by
    intro x y
    have hxP : f x ∈ (P : Subgroup H) := hP (MonoidHom.mem_range.mpr ⟨x, rfl⟩)
    have hyP : f y ∈ (P : Subgroup H) := hP (MonoidHom.mem_range.mpr ⟨y, rfl⟩)
    have hxy : (⟨f x, hxP⟩ : ↥(P : Subgroup H)) * ⟨f y, hyP⟩ =
        (⟨f y, hyP⟩ : ↥(P : Subgroup H)) * ⟨f x, hxP⟩ := mul_comm' _ _
    calc f (x * y) = f x * f y := map_mul f x y
      _ = f y * f x := congrArg Subtype.val hxy
      _ = f (y * x) := (map_mul f y x).symm
  have hforall : ∀ x y : QuaternionGroup 2, x * y = y * x := fun x y => hf (hcomm x y)
  exact absurd (hforall (QuaternionGroup.a 1) (QuaternionGroup.xa 0)) (by decide)

theorem center_le_oddCore_of_pOmegaPlus [Finite G] {Y : Subgroup G}
    (h : LieModel (↥Y ⧸ oddCore ↥Y) .POmegaPlus 4 3 1) : center ↥Y ≤ oddCore ↥Y := by
  let N : Subgroup ↥Y := oddCore ↥Y
  let π : ↥Y →* (↥Y ⧸ N) := QuotientGroup.mk' N
  have hmodel := h.statedClassicalModel_of_ne_zero (by norm_num : (4 : ℕ) ≠ 0)
  have hcard : Nat.card (↥Y ⧸ N) = 4952179814400 := by
    rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := ↥Y ⧸ N)
      (show (3 : ℕ) ≠ 2 by norm_num) hmodel).2.2.2.2.1 rfl]
    decide +kernel
  have hsimple : IsSimpleGroup (↥Y ⧸ N) :=
    (CFSG.LieType.Simplicity.fam_classical_converse (↥Y ⧸ N)
      ⟨.POmegaPlus, 4, 3, 1, hmodel⟩).2.2
  have hcenter : Subgroup.center (↥Y ⧸ N) = ⊥ := by
    by_contra hne
    have htop : Subgroup.center (↥Y ⧸ N) = ⊤ :=
      (hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (↥Y ⧸ N))).resolve_left hne
    haveI : IsMulCommutative (↥Y ⧸ N) := Subgroup.center_eq_top_iff.mp htop
    have hprime : Nat.Prime (Nat.card (↥Y ⧸ N)) := Group.is_simple_iff_prime_card.mp hsimple
    rw [hcard] at hprime
    exact (not_prime_of_two_dvd (by norm_num) (by norm_num)) hprime
  intro x hx
  have hle : (Subgroup.center ↥Y).map π ≤ Subgroup.center (↥Y ⧸ N) :=
    Subgroup.map_center_le_center (QuotientGroup.mk'_surjective N)
  have hxmap : π x ∈ (Subgroup.center ↥Y).map π := Subgroup.mem_map_of_mem π hx
  have hxbot : π x ∈ (⊥ : Subgroup (↥Y ⧸ N)) := by
    rw [← hcenter]
    exact hle hxmap
  have hxker : x ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    exact Subgroup.mem_bot.mp hxbot
  have hxN : x ∈ N := by
    rw [← QuotientGroup.ker_mk' N]
    exact hxker
  exact hxN

theorem not_forall_commute_of_pOmegaPlus [Finite G] {Y : Subgroup G}
    (h : LieModel (↥Y ⧸ oddCore ↥Y) .POmegaPlus 4 3 1) {x : G} (hx : orderOf x = 2) (hxY : x ∈ Y) :
    ¬ ∀ a ∈ Y, a * x = x * a := by
  intro hcomm
  have hxY' : (⟨x, hxY⟩ : ↥Y) ∈ Subgroup.center ↥Y := by
    rw [Subgroup.mem_center_iff]
    intro a
    apply Subtype.ext
    show (a : G) * x = x * (a : G)
    exact hcomm a.1 a.2
  have hxO : (⟨x, hxY⟩ : ↥Y) ∈ oddCore ↥Y := center_le_oddCore_of_pOmegaPlus h hxY'
  have horder : orderOf (⟨x, hxY⟩ : ↥Y) = 2 := by
    rw [Subgroup.orderOf_mk x hxY, hx]
  have hdvd : 2 ∣ Nat.card (oddCore ↥Y) := by
    rw [← horder]
    exact (oddCore ↥Y).orderOf_dvd_natCard hxO
  exact (odd_card_oddCore' ↥Y).not_two_dvd_nat hdvd

theorem false_of_isTwoU43_of_pOmegaPlus {Q : Type} [Group Q] [Finite Q] (h₁ : IsTwoU43 Q)
    (h₂ : LieModel Q .POmegaPlus 4 3 1) : False := by
  have hcard₁ : Nat.card Q = 6531840 := card_of_isTwoU43 h₁
  have hcard₂ : Nat.card Q = 4952179814400 := by
    have hmodel := h₂.statedClassicalModel_of_ne_zero (by norm_num : (4 : ℕ) ≠ 0)
    rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (G := Q)
      (show (3 : ℕ) ≠ 2 by norm_num) hmodel).2.2.2.2.1 rfl]
    decide +kernel
  omega

end CFSG.OddStandard.SmallF3.Omega
