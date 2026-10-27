module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.CoverKlein
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.CoverQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.CoverPerf

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog Equiv

variable {Y : Type*} [Group Y] [Finite Y] {w : Y} {π : Y →* Perm (Fin 5)}

theorem tableVII_cover_inv_mem_comm (hC : TableVIICover Y w π) {x : Y} (hx : x ∈ commutator Y)
    (hx2 : x ^ 2 = 1) : x = 1 ∨ x = w := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hx1, hxw⟩ := h
  obtain ⟨x₂, hx₂mem, hx₂2, hcomm, hπx₂1, hπx₂x⟩ :=
    tableVII_cover_klein hC hx hx2 hx1 hxw
  let Γ := ↥(commutator Y)
  let N : Subgroup Γ := (Subgroup.zpowers w).subgroupOf (commutator Y)
  let x' : Γ := ⟨x, hx⟩
  let x₂' : Γ := ⟨x₂, hx₂mem⟩
  have hΓ : Nat.card Γ = 120 := tableVII_cover_card_comm hC
  have hN : N.Normal :=
    (Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr (by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (tableVII_cover_central hC g).symm))).subgroupOf (commutator Y)
  have hN2 : Nat.card N = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC.le_comm).toEquiv, Nat.card_zpowers,
      orderOf_eq_prime hC.sq hC.ne_one]
  have hx'2 : x' ^ 2 = 1 := by
    apply Subtype.ext
    show x ^ 2 = 1
    exact hx2
  have hx₂'2 : x₂' ^ 2 = 1 := by
    apply Subtype.ext
    show x₂ ^ 2 = 1
    exact hx₂2
  have hcomm' : x' * x₂' = x₂' * x' := by
    apply Subtype.ext
    show x * x₂ = x₂ * x
    exact hcomm
  have hx'N : x' ∉ N := by
    intro hmem
    rw [Subgroup.mem_subgroupOf] at hmem
    have hmem' : x ∈ Subgroup.zpowers w := hmem
    rcases (tableVII_cover_mem_zpowers hC).mp hmem' with h1 | hw
    · exact hx1 h1
    · exact hxw hw
  have hx₂'N : x₂' ∉ N := by
    intro hmem
    rw [Subgroup.mem_subgroupOf] at hmem
    have hmem' : x₂ ∈ Subgroup.zpowers w := hmem
    exact hπx₂1 ((tableVII_cover_pi_eq_one hC).mpr
      ((tableVII_cover_mem_zpowers hC).mp hmem'))
  have hxx₂'N : x' * x₂' ∉ N := by
    intro hmem
    rw [Subgroup.mem_subgroupOf] at hmem
    have hmem' : x * x₂ ∈ Subgroup.zpowers w := hmem
    have hπ : π (x * x₂) = 1 :=
      (tableVII_cover_pi_eq_one hC).mpr ((tableVII_cover_mem_zpowers hC).mp hmem')
    rw [map_mul] at hπ
    have hxx : x * x = 1 := by rw [← pow_two]; exact hx2
    have haa : π x * π x = 1 := by rw [← map_mul, hxx, map_one]
    have hinv : (π x)⁻¹ = π x := mul_eq_one_iff_inv_eq.mp haa
    exact hπx₂x ((eq_inv_of_mul_eq_one_right hπ).trans hinv)
  obtain ⟨D, hND_inf, hND_sup⟩ :=
    tableVII_exists_compl hΓ N hN hN2 hx'2 hx₂'2 hcomm' hx'N hx₂'N hxx₂'N
  let K : Subgroup Y := D.map (commutator Y).subtype
  have hK : K ≤ commutator Y := Subgroup.map_subtype_le D
  have hKw : K ⊓ Subgroup.zpowers w = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => ?_
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyK, hyw⟩ := hy
    rw [Subgroup.mem_map] at hyK
    obtain ⟨d, hdD, hd_eq⟩ := hyK
    have hd_eq' : (d : Y) = y := hd_eq
    have hdN : d ∈ N := by
      rw [Subgroup.mem_subgroupOf]
      show (d : Y) ∈ Subgroup.zpowers w
      rw [hd_eq']
      exact hyw
    have hdmem : d ∈ N ⊓ D := ⟨hdN, hdD⟩
    rw [hND_inf, Subgroup.mem_bot] at hdmem
    rw [← hd_eq']
    simp [hdmem]
  have htop : (⊤ : Subgroup Γ).map (commutator Y).subtype = commutator Y := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmap : (N ⊔ D).map (commutator Y).subtype = Subgroup.zpowers w ⊔ K := by
    change ((Subgroup.zpowers w).subgroupOf (commutator Y) ⊔ D).map (commutator Y).subtype =
      Subgroup.zpowers w ⊔ D.map (commutator Y).subtype
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hC.le_comm]
  have hsup : Subgroup.zpowers w ⊔ K = commutator Y := by
    rw [← hmap, hND_sup, htop]
  exact tableVII_cover_no_compl hC K hK hKw hsup

theorem tableVII_cover_sign_of_inv (hC : TableVIICover Y w π) {x : Y} (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) (hxw : x ≠ w) : Perm.sign (π x) = -1 := by
  rcases Int.units_eq_one_or (Perm.sign (π x)) with h | h
  · exfalso
    have hxmem : x ∈ commutator Y := (tableVII_cover_mem_comm hC).mpr h
    rcases tableVII_cover_inv_mem_comm hC hxmem hx2 with h1 | hw
    · exact hx1 h1
    · exact hxw hw
  · exact h

end CFSG.EvenSporadicStandard.HNRecog.Section3
