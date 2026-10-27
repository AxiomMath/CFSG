module

public import CFSG.CharacterTheory.TwoRankLowerBound.Helpers

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

private theorem zpow_eq_one_or_self' {G : Type*} [Group G] {a : G} (ha : a ^ 2 = 1) (k : ℤ) :
    a ^ k = 1 ∨ a ^ k = a := by
  have hsq : a * a = 1 := by rw [← pow_two]; exact ha
  have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
  have hpow : a ^ k = a ^ (k % 2) := by
    conv_lhs => rw [hk]
    rw [zpow_add, zpow_mul, zpow_two, hsq, one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hpow, h, zpow_zero]
  · right
    rw [hpow, h, zpow_one]

private theorem isMulCommutative_of_card_le_three {H : Type*} [Group H] [Finite H]
    (hcard : Nat.card H ≤ 3) : IsMulCommutative H := by
  have hpos : 0 < Nat.card H := Nat.card_pos
  interval_cases hc : Nat.card H
  · haveI : Subsingleton H := Finite.card_le_one_iff_subsingleton.mp (by omega)
    exact isMulCommutative_iff.mpr fun a b => Subsingleton.elim _ _
  · haveI : IsCyclic H := isCyclic_of_prime_card (p := 2) hc
    infer_instance
  · haveI : IsCyclic H := isCyclic_of_prime_card (p := 3) hc
    infer_instance

theorem four_le_card_inf_centralizer_of_mem {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsSimpleGroup ↥L) (hnab : ∃ x y : L, x * y ≠ y * x) {a : G} (haL : a ∈ L)
    (ha : a ^ 2 = 1) :
    4 ≤ Nat.card ↥(L ⊓ centralizer ({a} : Set G)) := by
  classical
  let C : Subgroup G := L ⊓ Subgroup.centralizer ({a} : Set G)
  change 4 ≤ Nat.card ↥C
  by_contra hgoal
  rw [not_le] at hgoal
  by_cases ha1 : a = 1
  ·
    have hCL : C = L := by
      ext g
      constructor
      · intro hg; exact hg.1
      · intro hg
        refine ⟨hg, ?_⟩
        rw [ha1]
        exact Subgroup.mem_centralizer_singleton_iff.mpr (by simp)
    have hLcomm : IsMulCommutative ↥L := by
      apply isMulCommutative_of_card_le_three
      have h := hgoal
      rw [hCL] at h
      omega
    obtain ⟨x, y, hxy⟩ := hnab
    exact hxy (isMulCommutative_iff.mp hLcomm x y)
  ·
    have horder : orderOf a = 2 := orderOf_eq_prime (p := 2) ha ha1
    have hzp_le_C : Subgroup.zpowers a ≤ C := by
      rw [Subgroup.zpowers_le]
      exact ⟨haL, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have h2dvd : 2 ∣ Nat.card ↥C := by
      have h := Subgroup.card_dvd_of_le hzp_le_C
      rwa [Nat.card_zpowers, horder] at h
    have hCcard : Nat.card ↥C = 2 := by
      obtain ⟨k, hk⟩ := h2dvd
      have h2le : 2 ≤ Nat.card ↥C := by
        have h := Subgroup.card_le_of_le hzp_le_C
        rwa [Nat.card_zpowers, horder] at h
      omega
    have hCeq : C = Subgroup.zpowers a := by
      have h' : Subgroup.zpowers a = C := by
        apply Subgroup.eq_of_le_of_card_ge hzp_le_C
        rw [Nat.card_zpowers, horder]
        exact le_of_eq hCcard
      exact h'.symm
    let a' : ↥L := ⟨a, haL⟩
    have ha'2 : a' ^ 2 = 1 := by
      apply Subtype.ext
      simpa [a'] using ha
    have ha'ne : a' ≠ 1 := by
      intro h
      exact ha1 (by simpa [a'] using congrArg (fun x : ↥L => (x : G)) h)
    have ha'ord : orderOf a' = 2 := orderOf_eq_prime (p := 2) ha'2 ha'ne
    have hZp : IsPGroup 2 (Subgroup.zpowers a') := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, ha'ord]
      norm_num
    obtain ⟨P, hleP⟩ := hZp.exists_le_sylow
    have ha'P : a' ∈ (P : Subgroup ↥L) := hleP (Subgroup.mem_zpowers a')
    haveI : IsSimpleGroup ↥L := hL
    have heven : Even (Nat.card ↥L) := by
      have h := orderOf_dvd_natCard a'
      rw [ha'ord] at h
      exact even_iff_two_dvd.mpr h
    have hnotcyc : ¬ IsCyclic ↥(P : Subgroup ↥L) :=
      CFSG.TwoRankLowerBound.Helpers.sylow_two_not_isCyclic_of_nonabelian_simple
        ↥L hnab heven P
    have hPnt : Nontrivial ↥(P : Subgroup ↥L) :=
      ⟨⟨a', ha'P⟩, 1, fun h => ha'ne (by simpa using congrArg Subtype.val h)⟩
    haveI : Nontrivial ↥(P : Subgroup ↥L) := hPnt
    have hcenter_ne : Subgroup.center ↥(P : Subgroup ↥L) ≠ ⊥ :=
      (P.isPGroup'.bot_lt_center).ne'
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcenter_ne
    let zP : ↥(P : Subgroup ↥L) := z
    let zL : ↥L := zP
    let zg : G := zL
    have hzPcenter : zP ∈ Subgroup.center ↥(P : Subgroup ↥L) := z.2
    have hcomm : zL * a' = a' * zL := by
      have h := Subgroup.mem_center_iff.mp hzPcenter (⟨a', ha'P⟩ : ↥(P : Subgroup ↥L))
      have h' := congrArg (Subtype.val : ↥(P : Subgroup ↥L) → ↥L) h
      simpa using h'.symm
    have hzg_comm : zg * a = a * zg := by
      have h := congrArg (fun x : ↥L => (x : G)) hcomm
      simpa [zL, zg, a'] using h
    have hzg_memC : zg ∈ C := by
      refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr hzg_comm⟩
      exact zL.property
    have hzg_ne : zg ≠ 1 := by
      have hzP_ne : zP ≠ 1 := fun h => hz1 (Subtype.ext h)
      have hzL_ne : zL ≠ 1 := fun h => hzP_ne (Subtype.ext h)
      exact fun h => hzL_ne (Subtype.ext h)
    have hzg_zpow : zg ∈ Subgroup.zpowers a := by
      rw [← hCeq]
      exact hzg_memC
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzg_zpow
    have hzga : zg = a := by
      rcases zpow_eq_one_or_self' ha k with h | h
      · exact absurd (hk ▸ h) hzg_ne
      · exact hk ▸ h
    have hzP_eq : zP = (⟨a', ha'P⟩ : ↥(P : Subgroup ↥L)) := by
      apply Subtype.ext
      apply Subtype.ext
      exact hzga
    have hcenter_aP : (⟨a', ha'P⟩ : ↥(P : Subgroup ↥L)) ∈
        Subgroup.center ↥(P : Subgroup ↥L) := by
      rw [← hzP_eq]
      exact hzPcenter
    have hmemC : ∀ p : ↥(P : Subgroup ↥L), ((p : ↥L) : G) ∈ C := by
      intro p
      refine ⟨(p : ↥L).property, ?_⟩
      have h := Subgroup.mem_center_iff.mp hcenter_aP p
      have h' := congrArg (Subtype.val : ↥(P : Subgroup ↥L) → ↥L) h
      have h'' := congrArg (fun x : ↥L => (x : G)) h'
      exact Subgroup.mem_centralizer_singleton_iff.mpr h''
    have hcardP : Nat.card ↥(P : Subgroup ↥L) ≤ Nat.card ↥C :=
      Nat.card_le_card_of_injective
        (fun p : ↥(P : Subgroup ↥L) => (⟨((p : ↥L) : G), hmemC p⟩ : ↥C)) (by
          intro p q hpq
          have h1 : ((p : ↥L) : G) = ((q : ↥L) : G) :=
            congrArg (Subtype.val : ↥C → G) hpq
          exact Subtype.ext (Subtype.ext h1))
    have hPcard2 : Nat.card ↥(P : Subgroup ↥L) ≤ 2 := by
      simpa [hCcard] using hcardP
    have h2dvdP : 2 ∣ Nat.card ↥(P : Subgroup ↥L) := by
      have h := Subgroup.card_dvd_of_le hleP
      rwa [Nat.card_zpowers, ha'ord] at h
    have hP2ge : 2 ≤ Nat.card ↥(P : Subgroup ↥L) :=
      Nat.le_of_dvd Nat.card_pos h2dvdP
    have hPeq : (P : Subgroup ↥L) = Subgroup.zpowers a' := by
      have h' : Subgroup.zpowers a' = (P : Subgroup ↥L) := by
        apply Subgroup.eq_of_le_of_card_ge hleP
        rw [Nat.card_zpowers, ha'ord]
        exact hPcard2
      exact h'.symm
    have hcycP : IsCyclic ↥(P : Subgroup ↥L) := by
      rw [hPeq]
      infer_instance
    exact hnotcyc hcycP

end CFSG.OddStandard.AltStdSec.SwapPartner
