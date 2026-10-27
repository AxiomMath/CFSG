module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Subgroup

section Preimage

variable {Y : Type*} [Group Y] (O : Subgroup Y) [O.Normal]

theorem a6grp_normal_dichotomy {L : Subgroup (Y ⧸ O)} [L.Normal] [IsSimpleGroup L]
    {N : Subgroup Y} [N.Normal] (hN : N ≤ L.comap (QuotientGroup.mk' O)) :
    N ≤ O ∨ N ⊔ O = L.comap (QuotientGroup.mk' O) := by
  have hsurj : Function.Surjective (QuotientGroup.mk' O) := QuotientGroup.mk'_surjective O
  haveI : (N.map (QuotientGroup.mk' O)).Normal := Subgroup.Normal.map inferInstance _ hsurj
  haveI : ((N.map (QuotientGroup.mk' O)).subgroupOf L).Normal :=
    Subgroup.Normal.subgroupOf inferInstance L
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((N.map (QuotientGroup.mk' O)).subgroupOf L) with h | h
  · left
    intro n hn
    have h1 : (⟨QuotientGroup.mk' O n, hN hn⟩ : L) ∈
        (N.map (QuotientGroup.mk' O)).subgroupOf L := ⟨n, hn, rfl⟩
    rw [h] at h1
    exact (QuotientGroup.eq_one_iff n).mp (congrArg Subtype.val (Subgroup.mem_bot.mp h1))
  · right
    apply le_antisymm
    · refine sup_le hN (fun o ho => ?_)
      show (QuotientGroup.mk o : Y ⧸ O) ∈ L
      rw [(QuotientGroup.eq_one_iff o).mpr ho]
      exact one_mem L
    · intro g hg
      have h1 : (⟨QuotientGroup.mk' O g, hg⟩ : L) ∈
          (N.map (QuotientGroup.mk' O)).subgroupOf L := by
        rw [h]; trivial
      obtain ⟨n, hn, hng⟩ := h1
      have h2 : n⁻¹ * g ∈ O := QuotientGroup.eq.mp hng
      have h3 : g = n * (n⁻¹ * g) := by group
      rw [h3]
      exact mul_mem (mem_sup_left hn) (mem_sup_right h2)

theorem a6grp_oddCore_le_center {L : Subgroup (Y ⧸ O)} [L.Normal] [IsSimpleGroup L] {z : Y}
    (hzJ : z ∈ L.comap (QuotientGroup.mk' O)) (hzO : z ∉ O)
    (habel : ∀ a ∈ O, ∀ b ∈ O, a * b = b * a) (hzc : ∀ o ∈ O, z * o = o * z) :
    ∀ j ∈ L.comap (QuotientGroup.mk' O), ∀ o ∈ O, j * o = o * j := by
  set J := L.comap (QuotientGroup.mk' O) with hJ
  haveI : J.Normal := Subgroup.Normal.comap inferInstance _
  have hOJ : O ≤ J := fun o ho => by
    show (QuotientGroup.mk o : Y ⧸ O) ∈ L
    rw [(QuotientGroup.eq_one_iff o).mpr ho]
    exact one_mem L
  let C : Subgroup Y := centralizer (O : Set Y) ⊓ J
  haveI : (centralizer (O : Set Y)).Normal := Subgroup.normal_centralizer
  haveI : C.Normal := inferInstance
  have hzC : z ∈ C := ⟨mem_centralizer_iff.mpr fun o ho => (hzc o ho).symm, hzJ⟩
  rcases a6grp_normal_dichotomy O (inf_le_right : C ≤ J) with h | h
  · exact absurd (h hzC) hzO
  · have hOC : O ≤ C := fun o ho =>
      ⟨mem_centralizer_iff.mpr fun a ha => habel a ha o ho, hOJ ho⟩
    have hCeq : C = J := (sup_eq_left.mpr hOC).symm.trans h
    intro j hj o ho
    have hjC : j ∈ C := hCeq ▸ hj
    exact (mem_centralizer_iff.mp hjC.1 o ho).symm

theorem a6grp_map_eq {L : Subgroup (Y ⧸ O)} {N : Subgroup Y}
    (h : N ⊔ O = L.comap (QuotientGroup.mk' O)) : N.map (QuotientGroup.mk' O) = L := by
  have h1 : (N ⊔ O).map (QuotientGroup.mk' O) = L := by
    rw [h]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O) L
  rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] at h1

theorem a6grp_equiv_of_inf_eq_bot {L : Subgroup (Y ⧸ O)} {N : Subgroup Y}
    (h : N ⊔ O = L.comap (QuotientGroup.mk' O)) (hbot : N ⊓ O = ⊥) : Nonempty (N ≃* L) := by
  have hNJ : N ≤ L.comap (QuotientGroup.mk' O) := h ▸ le_sup_left
  let f : N →* L := ((QuotientGroup.mk' O).domRestrict N).codRestrict L (fun j => hNJ j.2)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro j hj
    have h1 : QuotientGroup.mk' O (j : Y) = 1 := congrArg Subtype.val hj
    have h2 : (j : Y) ∈ O := (QuotientGroup.eq_one_iff (j : Y)).mp h1
    have h3 : (j : Y) ∈ N ⊓ O := ⟨j.2, h2⟩
    rw [hbot, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  have hsurj : Function.Surjective f := by
    intro l
    have hl : (l : Y ⧸ O) ∈ N.map (QuotientGroup.mk' O) := by
      rw [a6grp_map_eq O h]; exact l.2
    obtain ⟨n, hn, hnl⟩ := hl
    exact ⟨⟨n, hn⟩, Subtype.ext hnl⟩
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩⟩

theorem a6grp_mem_of_sq {J N : Subgroup Y} [N.Normal] (hJ : N ⊔ O = J) (hbot : N ⊓ O = ⊥)
    (hodd : Odd (Nat.card O)) (hc : ∀ j ∈ J, ∀ o ∈ O, j * o = o * j) {z : Y} (hzJ : z ∈ J)
    (hz2 : z * z = 1) : z ∈ N := by
  obtain ⟨j, hj, o, ho, hjo⟩ := Subgroup.mem_sup_of_normal_left.mp (hJ ▸ hzJ)
  have hjJ : j ∈ J := hJ ▸ mem_sup_left hj
  have hoj : j * o = o * j := hc j hjJ o ho
  have hcom : Commute j o := hoj
  have h1 : o * o = (j * j)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    calc j * j * (o * o) = (j * o) ^ 2 := by rw [hcom.mul_pow, sq, sq]
      _ = 1 := by rw [hjo, sq]; exact hz2
  have h2 : o * o ∈ N ⊓ O :=
    Subgroup.mem_inf.mpr ⟨by rw [h1]; exact inv_mem (mul_mem hj hj), mul_mem ho ho⟩
  rw [hbot, Subgroup.mem_bot] at h2
  have h3 : orderOf o ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h2)
  have h4 : o = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h5 | h5
    · exact orderOf_eq_one_iff.mp h5
    · exfalso
      have h6 : Odd (orderOf o) := hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard O ho)
      rw [h5] at h6
      exact absurd h6 (by decide)
  rw [h4, mul_one] at hjo
  exact hjo ▸ hj

theorem a6grp_J0_perfect {L : Subgroup (Y ⧸ O)} [L.Normal] [IsSimpleGroup L] [Group.IsPerfect L]
    (hodd : Odd (Nat.card O)) {t x : Y} (hxJ : x ∈ L.comap (QuotientGroup.mk' O)) (hxO : x ∉ O)
    (htx : t * x = x * t) (hinv : ∀ o ∈ O, t * o * t⁻¹ = o⁻¹) :
    normalClosure ({x} : Set Y) ⊔ O = L.comap (QuotientGroup.mk' O) ∧
      Group.IsPerfect (normalClosure ({x} : Set Y)) := by
  set J := L.comap (QuotientGroup.mk' O) with hJ
  set ψ := QuotientGroup.mk' O with hψ
  haveI : J.Normal := Subgroup.Normal.comap inferInstance ψ
  set J₀ := normalClosure ({x} : Set Y) with hJ₀
  have hJ₀J : J₀ ≤ J := normalClosure_le_normal (by simpa using hxJ)
  have hxJ₀ : x ∈ J₀ := subset_normalClosure (Set.mem_singleton x)
  have hJ₀O : J₀ ⊔ O = J := by
    rcases a6grp_normal_dichotomy O hJ₀J with h | h
    · exact absurd (h hxJ₀) hxO
    · exact h
  refine ⟨hJ₀O, ?_⟩
  have hmapJ₀ : J₀.map ψ = L := a6grp_map_eq O hJ₀O
  let D : Subgroup Y := ⁅J₀, J₀⁆
  haveI hDn : D.Normal := Subgroup.commutator_normal J₀ J₀
  have hDJ₀ : D ≤ J₀ := Subgroup.commutator_le_right J₀ J₀
  have hDO : D ⊔ O = J := by
    have h1 : D.map ψ = L := by
      show (⁅J₀, J₀⁆ : Subgroup Y).map ψ = L
      rw [Subgroup.map_commutator, hmapJ₀]
      exact Subgroup.commutator_eq_self
    have h2 := Subgroup.comap_map_eq ψ D
    rw [h1, QuotientGroup.ker_mk'] at h2
    exact h2.symm
  have hxD : x ∈ D := by
    have hxDO : x ∈ D ⊔ O := hDO ▸ hxJ
    obtain ⟨d, hd, o, ho, hdo⟩ := Subgroup.mem_sup_of_normal_left.mp hxDO
    have hd' : t * d * t⁻¹ ∈ D := hDn.conj_mem d hd t
    have h1 : d * o = (t * d * t⁻¹) * o⁻¹ := by
      calc d * o = x := hdo
        _ = t * x * t⁻¹ := by rw [htx]; group
        _ = (t * d * t⁻¹) * (t * o * t⁻¹) := by rw [← hdo]; group
        _ = (t * d * t⁻¹) * o⁻¹ := by rw [hinv o ho]
    have h2 : (t * d * t⁻¹)⁻¹ * d = o⁻¹ * o⁻¹ := by
      calc (t * d * t⁻¹)⁻¹ * d = (t * d * t⁻¹)⁻¹ * (d * o) * o⁻¹ := by group
        _ = (t * d * t⁻¹)⁻¹ * ((t * d * t⁻¹) * o⁻¹) * o⁻¹ := by rw [h1]
        _ = o⁻¹ * o⁻¹ := by group
    have h3 : o⁻¹ * o⁻¹ ∈ D := h2 ▸ mul_mem (inv_mem hd') hd
    have h4 : o * o ∈ D := by simpa [mul_inv_rev] using inv_mem h3
    have hoddo : Odd (orderOf o) := hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard O ho)
    obtain ⟨k, hk⟩ := hoddo
    have h5 : o = (o * o) ^ (k + 1) := by
      have h6 : o ^ (2 * k + 1) = 1 := hk ▸ pow_orderOf_eq_one o
      calc o = o ^ (2 * k + 1) * o := by rw [h6, one_mul]
        _ = o ^ (2 * (k + 1)) := by rw [← pow_succ, show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
        _ = (o * o) ^ (k + 1) := by rw [pow_mul, sq]
    have hoD : o ∈ D := h5 ▸ pow_mem h4 (k + 1)
    exact hdo ▸ mul_mem hd hoD
  have hJ₀D : J₀ ≤ D := normalClosure_le_normal (by simpa using hxD)
  exact Subgroup.isPerfect_iff.mpr (le_antisymm hDJ₀ hJ₀D)

end Preimage

section PGroups

theorem a6grp_comm_of_pGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Type*} [Group Q]
    (hQ : IsPGroup p Q) (hdvd : Nat.card Q ∣ 360) : ∀ a b : Q, a * b = b * a := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite Q := Nat.finite_of_card_ne_zero (fun h => by rw [h] at hdvd; omega)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  have hk2 : k ≤ 2 := by
    by_contra hlt
    have h3 : p ^ 3 ∣ 360 := (pow_dvd_pow p (by omega : 3 ≤ k)).trans (hk ▸ hdvd)
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have h4 : p ^ 3 ≤ 360 := Nat.le_of_dvd (by norm_num) h3
    have hp7 : p ≤ 7 := by
      by_contra hgt
      have : 8 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
      omega
    interval_cases p <;> first | omega | (exfalso; revert hp; decide) | skip
  interval_cases k
  · haveI : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
    exact fun a b => Subsingleton.elim _ _
  · haveI : IsCyclic Q := isCyclic_of_prime_card (by simpa using hk)
    exact fun a b => (IsCyclic.isMulCommutative (α := Q)).is_comm.comm a b
  · exact fun a b =>
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq hk).is_comm.comm a b

end PGroups


end CFSG.LocalAnalysis.EvenBN.Tits.I21L
