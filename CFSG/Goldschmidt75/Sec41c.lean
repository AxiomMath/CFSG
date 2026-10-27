module

public import CFSG.Goldschmidt75.Sec41b

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_sylow_of_mem_center (T : Sylow 2 G) {n : G} (hn : n ∈ center G)
    (hn2 : orderOf n = 2) : n ∈ (T : Subgroup G) := by
  have : (zpowers n).Normal := normal_of_le_center (zpowers_le.mpr hn)
  have hp := (isPGroup_zpowers hn2).to_sup_of_normal_left T.isPGroup'
  have h := T.is_maximal' hp le_sup_right
  rw [← h]
  exact mem_sup_left (mem_zpowers n)

theorem minimal_normal_central (hO : goldschmidtOddCore G = ⊥) {N S : Subgroup G}
    (hNn : N.Normal) (hN1 : N ≠ ⊥) (hmin : ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N)
    (hS : IsPGroup 2 S) (hG : centralizer (N : Set G) ⊔ S = ⊤) :
    N ≤ center G ∧ Nat.card N = 2 := by
  have := hNn
  have hCn : (centralizer (N : Set G)).Normal := Subgroup.normal_centralizer
  have hZ₀n : (N ⊓ centralizer (N : Set G)).Normal := Subgroup.normal_inf_normal _ _
  have hab : N ≤ centralizer (N : Set G) := by
    rcases hmin _ hZ₀n inf_le_left with h | h
    · exfalso
      have hNp : IsPGroup 2 N := by
        intro n
        obtain ⟨k, hk⟩ := exists_two_pow_mem hS hG n
        refine ⟨k, Subtype.ext ?_⟩
        have hmem : (n : G) ^ (2 ^ k) ∈ N ⊓ centralizer (N : Set G) := ⟨pow_mem n.2 _, hk⟩
        rw [h, mem_bot] at hmem
        simpa using hmem
      have : Nontrivial N := (nontrivial_iff_ne_bot N).mpr hN1
      have hZ := hNp.center_nontrivial
      obtain ⟨z, hz1⟩ := exists_ne (1 : center N)
      have hzC : ((z : N) : G) ∈ N ⊓ centralizer (N : Set G) :=
        ⟨(z : N).2, mem_centralizer_iff.mpr fun m hm =>
          congrArg Subtype.val (mem_center_iff.mp z.2 ⟨m, hm⟩)⟩
      rw [h, mem_bot] at hzC
      exact hz1 (Subtype.ext (Subtype.ext hzC))
    · exact h.symm.le.trans inf_le_right
  have hNab : IsMulCommutative N := isMulCommutative_iff.mpr fun a b =>
    Subtype.ext (mem_centralizer_iff.mp (hab b.2) a a.2)
  have hNp : IsPGroup 2 N := CFSG.isPGroup_of_nilpotent_normal N hNn inferInstance
    (by rwa [← goldschmidtOddCore_eq_pPrimeCore])
  have hPp : IsPGroup 2 (N ⊔ S : Subgroup G) := hNp.to_sup_of_normal_left hS
  have hNP : (N.subgroupOf (N ⊔ S)).Normal := Subgroup.normal_subgroupOf
  have hNP1 : N.subgroupOf (N ⊔ S) ≠ ⊥ := by
    intro h
    apply hN1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, mem_sup_left hx⟩ : (N ⊔ S : Subgroup G)) ∈ N.subgroupOf (N ⊔ S) := hx
    rw [h, mem_bot] at this
    exact (mem_bot).mpr (congrArg Subtype.val this)
  have : Group.IsNilpotent (N ⊔ S : Subgroup G) := hPp.isNilpotent
  obtain ⟨z, hz, hz1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hNP1)
  have hzN : ((z : (N ⊔ S : Subgroup G)) : G) ∈ N := hz.1
  have hzZ : ((z : (N ⊔ S : Subgroup G)) : G) ∈ center G := by
    have hle : centralizer (N : Set G) ⊔ S ≤
        centralizer ({((z : (N ⊔ S : Subgroup G)) : G)} : Set G) := by
      refine sup_le (fun c hc => mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp hc _ hzN).symm) (fun s hs => ?_)
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mem_center_iff.mp hz.2 ⟨s, mem_sup_right hs⟩)
    rw [mem_center_iff]
    intro g
    exact mem_centralizer_singleton_iff.mp (hle (hG ▸ mem_top g))
  have hNZ : N ≤ center G := by
    rcases hmin (N ⊓ center G) (Subgroup.normal_inf_normal _ _) inf_le_left with h | h
    · exfalso
      have hmem : ((z : (N ⊔ S : Subgroup G)) : G) ∈ N ⊓ center G := ⟨hzN, hzZ⟩
      rw [h, mem_bot] at hmem
      exact (hz1 (Subtype.ext hmem)).elim
    · exact h.symm.le.trans inf_le_right
  refine ⟨hNZ, ?_⟩
  have : Nontrivial N := (nontrivial_iff_ne_bot N).mpr hN1
  obtain ⟨k, hk, hcard⟩ := hNp.nontrivial_iff_card.mp inferInstance
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 2
    (by rw [hcard]; exact dvd_pow_self 2 (by omega))
  have hxN : zpowers (x : G) ≤ N := zpowers_le.mpr x.2
  have hxn : (zpowers (x : G)).Normal := normal_of_le_center (hxN.trans hNZ)
  rcases hmin _ hxn hxN with h | h
  · exfalso
    have : (x : G) ∈ zpowers (x : G) := mem_zpowers _
    rw [h, mem_bot] at this
    have hx1 : x = 1 := Subtype.ext this
    rw [hx1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  · rw [← h, Nat.card_zpowers, Subgroup.orderOf_coe, hx]

end CFSG.Goldschmidt75
