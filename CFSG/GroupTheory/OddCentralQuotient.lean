module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GroupTheory

theorem eq_of_sup_eq_of_le_center {G : Type*} [Group G] {N A B : Subgroup G}
    (hN : N ≤ Subgroup.center G) (hodd : Odd (Nat.card N)) (hA : IsPGroup 2 A)
    (hB : IsPGroup 2 B) (h : A ⊔ N = B ⊔ N) : A = B := by
  haveI : N.Normal := Subgroup.normal_of_le_center hN
  have key : ∀ {A B : Subgroup G}, IsPGroup 2 A → IsPGroup 2 B → A ⊔ N = B ⊔ N → A ≤ B := by
    intro A B hA hB hAB a ha
    have ha' : a ∈ B ⊔ N := hAB ▸ Subgroup.mem_sup_left ha
    rw [Subgroup.mem_sup_of_normal_right] at ha'
    obtain ⟨b, hb, z, hz, hza⟩ := ha'
    obtain ⟨n, hn⟩ := hA ⟨a, ha⟩
    obtain ⟨m, hm⟩ := hB ⟨b, hb⟩
    have hna : a ^ 2 ^ (n + m) = 1 := by
      rw [pow_add, pow_mul, show a ^ 2 ^ n = 1 by simpa using congrArg Subtype.val hn, one_pow]
    have hmb : b ^ 2 ^ (n + m) = 1 := by
      rw [pow_add, mul_comm, pow_mul,
        show b ^ 2 ^ m = 1 by simpa using congrArg Subtype.val hm, one_pow]
    have hzpow : z ^ 2 ^ (n + m) = 1 := by
      have hc : a ^ 2 ^ (n + m) = b ^ 2 ^ (n + m) * z ^ 2 ^ (n + m) := by
        rw [← hza]
        exact (Commute.mul_pow (Subgroup.mem_center_iff.mp (hN hz) b) _)
      rw [hna, hmb, one_mul] at hc
      exact hc.symm
    have hcop : Nat.Coprime (2 ^ (n + m)) (Nat.card N) :=
      Nat.Coprime.pow_left (n + m) hodd.coprime_two_left
    have hz1 : z = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hzpow) (Subgroup.orderOf_dvd_natCard _ hz))
    rw [← hza, hz1, mul_one]
    exact hb
  exact le_antisymm (key hA hB h) (key hB hA h.symm)

theorem eq_of_map_mk_eq_of_le_center {G : Type*} [Group G] {N A B : Subgroup G} [N.Normal]
    (hN : N ≤ Subgroup.center G) (hodd : Odd (Nat.card N)) (hA : IsPGroup 2 A)
    (hB : IsPGroup 2 B) (h : A.map (QuotientGroup.mk' N) = B.map (QuotientGroup.mk' N)) :
    A = B := by
  refine eq_of_sup_eq_of_le_center hN hodd hA hB ?_
  have h' := congrArg (Subgroup.comap (QuotientGroup.mk' N)) h
  rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h'

theorem eq_bot_of_isNilpotent_quotient_center {Y : Type*} [Group Y] [Finite Y]
    (hY : ∀ N : Subgroup Y, N.Normal → Group.IsNilpotent N → N ≤ Subgroup.center Y)
    (N : Subgroup (Y ⧸ Subgroup.center Y)) (hN : N.Normal) (hnil : Group.IsNilpotent N) :
    N = ⊥ := by
  let M : Subgroup Y := N.comap (QuotientGroup.mk' (Subgroup.center Y))
  have hMn : M.Normal := hN.comap _
  have hMnil : Group.IsNilpotent M := by
    refine Subgroup.isNilpotent_of_ker_le_center
      ((QuotientGroup.mk' (Subgroup.center Y)).subgroupComap N) ?_
    intro x hx
    have hx1 : QuotientGroup.mk' (Subgroup.center Y) (x : Y) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxc : (x : Y) ∈ Subgroup.center Y := by
      rw [← QuotientGroup.ker_mk' (Subgroup.center Y)]
      exact MonoidHom.mem_ker.mpr hx1
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxc (y : Y))
  have hMZ : M ≤ Subgroup.center Y := hY M hMn hMnil
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Y) y
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff x).mpr (hMZ hy)

end CFSG.GroupTheory
