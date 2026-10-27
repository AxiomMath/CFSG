module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open Subgroup

theorem card_center_of_nonabelian_card_p_cube {p : ℕ} [hp : Fact p.Prime] {T : Type*}
    [Group T] (hc : Nat.card T = p ^ 3) (hnc : ¬ IsMulCommutative T) :
    Nat.card (center T) = p := by
  have hTp : IsPGroup p T := IsPGroup.of_card hc
  have hfin : Finite T :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hp.out.ne_zero)
  have hgt : 1 < Nat.card T := by
    rw [hc]
    exact one_lt_pow₀ hp.out.one_lt (by norm_num)
  have hnt : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp hgt
  have hZnt : Nontrivial (center T) := hTp.center_nontrivial
  have h1 : 1 < Nat.card (center T) := Finite.one_lt_card_iff_nontrivial.mpr hZnt
  have hdvd : Nat.card (center T) ∣ p ^ 3 := hc ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
  interval_cases i
  · rw [pow_zero] at hci
    omega
  · simpa using hci
  · exfalso
    have hq : Nat.card (T ⧸ center T) = p := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center T)
      rw [hc, hci] at h
      apply Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos 2)
      rw [← h]
      ring
    have : IsCyclic (T ⧸ center T) := isCyclic_of_prime_card hq
    exact hnc (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (center T)) (by rw [QuotientGroup.ker_mk']))
  · exfalso
    have htop : center T = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hci, hc])
    have hall : ∀ a : T, a ∈ center T := fun a => by
      rw [htop]
      exact mem_top a
    exact hnc ⟨⟨fun a b => (mem_center_iff.mp (hall a) b).symm⟩⟩

theorem card_inf_centralizer_of_nonabelian_card_p_cube {p : ℕ} [Fact p.Prime] {G : Type*}
    [Group G] {T : Subgroup G} (hcard : Nat.card T = p ^ 3) (hnc : ¬ IsMulCommutative T) :
    Nat.card (T ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) = p := by
  have hmap : (center ↥T).map T.subtype = T ⊓ Subgroup.centralizer (T : Set G) := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact congrArg Subtype.val (mem_center_iff.mp hy ⟨h, hh⟩)
    · intro hx
      obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_map.mpr ⟨⟨x, hxT⟩, ?_, rfl⟩
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC (g : G) g.2)
  rw [← hmap, Subgroup.card_map_of_injective T.subtype_injective]
  exact card_center_of_nonabelian_card_p_cube hcard hnc

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
