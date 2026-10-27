module

public import CFSG.GH74.Generic.S45.L1310
public import CFSG.GH74.Generic.S45.LAltCore
public import CFSG.GH74.Generic.S45.LAltL2
public import CFSG.GH74.Generic.S45.LAlt6

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.GH74.GLS Subgroup
open CFSG.GH74.Generic.S45.LAlt

theorem card_eq_sixty_or_threeSixty {N q : ℕ} (hN : N ∣ 360) (hq5 : 5 ≤ q) (hqodd : Odd q)
    (h : N * 2 = q * (q ^ 2 - 1)) : N = 60 ∨ N = 360 := by
  have hN360 : N ≤ 360 := Nat.le_of_dvd (by norm_num) hN
  have hq9 : q ≤ 9 := by
    by_contra hgt
    push Not at hgt
    have h1 : 10 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : 10 * (10 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right h1 1)
    omega
  obtain ⟨k, hk⟩ := hqodd
  interval_cases q
  · left
    norm_num at h
    omega
  · omega
  · exfalso
    norm_num at h
    have h168 : N = 168 := by omega
    subst h168
    norm_num at hN
  · omega
  · right
    norm_num at h
    omega

theorem alt_core_six {K : Type} [Group K] [Finite K] (hKp : Group.IsPerfect K)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6)) (y : MulAut K) (hy : orderOf y = 2)
    (L : Subgroup K) (hLfix : ∀ l ∈ L, y l = l) (hLs : IsSimpleGroup ↥L)
    (hLnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hq : ∃ q : ℕ, 5 ≤ q ∧ Odd q ∧ Nat.card ↥L * 2 = q * (q ^ 2 - 1)) : False := by
  classical
  obtain ⟨yb, hπy, hyb1, -⟩ := LAlt.exists_induced hKp e y hy
  have hπker := LAlt.ker_projAlt e
  set π := LAlt.projAlt e with hπdef
  have hLinj : Function.Injective (π.comp L.subtype) := LAlt.inj_restrict π hπker hLs hLnab
  let Lb : Subgroup (alternatingGroup (Fin 6)) := L.map π
  let eL : ↥L ≃* ↥Lb :=
    MulEquiv.ofBijective (π.subgroupMap L)
      ⟨fun a b hab => hLinj (by
        have h1 := Subtype.ext_iff.1 hab
        exact h1), π.subgroupMap_surjective L⟩
  have hLbcard : Nat.card ↥Lb = Nat.card ↥L := (Nat.card_congr eL.toEquiv).symm
  have hfix : ∀ l ∈ Lb, yb l = l := by
    rintro _ ⟨l, hl, rfl⟩
    rw [← hπy, hLfix l hl]
  have hdvd : Nat.card ↥Lb ∣ 360 := by
    have h1 := Subgroup.card_subgroup_dvd_card Lb
    have h2 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    rwa [h2] at h1
  obtain ⟨q, hq5, hqodd, hqcard⟩ := hq
  have hcard : Nat.card ↥Lb = 60 ∨ Nat.card ↥Lb = 360 :=
    card_eq_sixty_or_threeSixty hdvd hq5 hqodd (hLbcard ▸ hqcard)
  rcases hcard with h60 | h360
  · exact hyb1 (LAlt.aut_alt6_eq_one_of_fixes_index_six yb Lb h60 hfix)
  · have htop : Lb = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [h360, Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    apply hyb1
    refine MulEquiv.ext fun a => ?_
    exact hfix a (htop ▸ Subgroup.mem_top a)

theorem b_1310_alt : B_1310_alt := by
  intro K _ _ y L hyp ⟨n, hn5, ⟨e⟩⟩
  obtain ⟨hK, hy, hL, -, hL2, hA, -, -⟩ := hyp
  have hKp : Group.IsPerfect K := hK.1.1
  have hz2 : IsPGroup 2 (Subgroup.center K) := by
    rw [hK.2.1]
    exact CFSG.pCore_isPGroup
  obtain ⟨hLs, hLnab, ⟨v, hv⟩, q, hq5, hqodd, hqcard, -⟩ := LAlt.hasL2Model_data hL2
  have hLfix : ∀ l ∈ L, y l = l := fun l hl => hL hl y (Subgroup.mem_zpowers y)
  have hno4 : ∀ m : K, y m = m → ¬ 4 ∣ orderOf m := fun m hm =>
    LAlt.not_four_dvd_orderOf (M := fixSub (zpowers y)) hA (fix_mem_zpowers hm)
  by_cases h6 : n = 6
  · subst h6
    exact alt_core_six hKp e y hy L hLfix hLs hLnab ⟨q, hq5, hqodd, hqcard⟩
  · have hn' : n = 5 ∨ 7 ≤ n := by omega
    exact LAlt.alt_core hKp hn' e hz2 y hy L hLfix hLs hLnab
      ⟨(v : K), v.2, by rw [Subgroup.orderOf_coe]; exact hv⟩ hno4

end CFSG.GH74.Generic.S45
