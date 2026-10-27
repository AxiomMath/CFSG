module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Frob
public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.SecTwoDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup

section Elementary

variable {Y : Type*} [Group Y]

theorem p21_centralizer_le_normalizer_zpowers (t : Y) :
    centralizer ({t} : Set Y) ≤ normalizer ((zpowers t : Subgroup Y) : Set Y) := by
  have h : centralizer ({t} : Set Y) = centralizer ((zpowers t : Subgroup Y) : Set Y) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [h]
  exact Subgroup.centralizer_le_normalizer _

theorem p21_closure_pair (a b : Y) : closure ({a, b} : Set Y) = zpowers a ⊔ zpowers b := by
  rw [← Set.singleton_union, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    ← Subgroup.zpowers_eq_closure]

theorem p21_closure_three (t u x : Y) :
    closure ({t, u, x} : Set Y) = zpowers t ⊔ (zpowers x ⊔ zpowers u) := by
  rw [← Set.singleton_union, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    p21_closure_pair, sup_comm (zpowers u)]

end Elementary

section SecTwo

variable {Y : Type*} [Group Y] [Finite Y]

theorem p21_secTwoHyp {t u x : Y} (htt : t * t = 1) (ht1 : t ≠ 1) (hF : P5.IsF20 x u)
    (hdisj : Disjoint (zpowers t) (zpowers x ⊔ zpowers u))
    (hcent : centralizer ({t} : Set Y) = zpowers t ⊔ (zpowers x ⊔ zpowers u)) :
    SecTwoHyp Y t u := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu_c : u ∈ centralizer ({t} : Set Y) := by
    rw [hcent]
    exact mem_sup_right (mem_sup_right (mem_zpowers u))
  have hcom : t * u = u * t := (mem_centralizer_singleton_iff.1 hu_c).symm
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have hdisj' : Disjoint (zpowers t) (zpowers u) := hdisj.mono_right le_sup_right
  have hR : secTwoR t u = zpowers t ⊔ zpowers u := p21_closure_pair t u
  have hcn := p21_centralizer_le_normalizer_zpowers t
  have hRcard : Nat.card (secTwoR t u) = 8 := by
    rw [hR, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
      (((zpowers_le).2 hu_c).trans hcn) hdisj', Nat.card_zpowers, Nat.card_zpowers, ht2,
      hF.orderOf_y]
  have hCcard : Nat.card (centralizer ({t} : Set Y)) = 40 := by
    have hle : zpowers x ⊔ zpowers u ≤ centralizer ({t} : Set Y) := by
      rw [hcent]
      exact le_sup_right
    rw [hcent, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
      (hle.trans hcn) hdisj, Nat.card_zpowers, ht2]
    have h20 : Nat.card (zpowers x ⊔ zpowers u : Subgroup Y) = 20 := hF.card_F20
    rw [h20]
  have hsq : u ^ 2 ≠ t := by
    intro h
    have h1 : t ∈ zpowers t := mem_zpowers t
    have h2 : t ∈ zpowers x ⊔ zpowers u := by
      rw [← h]
      exact mem_sup_right (Subgroup.pow_mem _ (mem_zpowers u) 2)
    exact ht1 (Subgroup.disjoint_def.1 hdisj h1 h2)
  refine ⟨ht2, hF.orderOf_y, hcom, hsq, ?_, ?_, ?_⟩
  · rw [hR, hcent]
    exact sup_le_sup_left le_sup_right _
  · exact IsPGroup.of_card (n := 3) (by rw [hRcard]; norm_num)
  · intro P hPC hP2 hRP
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    have h40 : Nat.card P ∣ 40 := hCcard ▸ Subgroup.card_dvd_of_le hPC
    have h8 : 8 ∣ Nat.card P := hRcard ▸ Subgroup.card_dvd_of_le hRP
    rw [hk] at h40 h8
    have hle : 2 ^ k ≤ 40 := Nat.le_of_dvd (by norm_num) h40
    have hk6 : k < 6 := by
      by_contra hk6
      have := Nat.pow_le_pow_right (show 2 > 0 by norm_num) (not_lt.1 hk6)
      omega
    have hP8 : Nat.card P = 8 := by
      rw [hk]
      interval_cases k <;> simp_all
    exact (Subgroup.eq_of_le_of_card_ge hRP (by rw [hRcard, hP8])).symm

end SecTwo

section Transfer

variable {Γ : Type*} [Group Γ] (K : Subgroup Γ)

theorem p21_map_subtype_three (t u x : ↥K) :
    (zpowers t ⊔ (zpowers x ⊔ zpowers u)).map K.subtype =
      zpowers (t : Γ) ⊔ (zpowers (x : Γ) ⊔ zpowers (u : Γ)) := by
  rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
    MonoidHom.map_zpowers]
  rfl

theorem p21_transfer_cent {t u x : ↥K}
    (hB : centralizer ({(t : Γ)} : Set Γ) ⊓ K =
      zpowers (t : Γ) ⊔ (zpowers (x : Γ) ⊔ zpowers (u : Γ))) :
    centralizer ({t} : Set ↥K) = zpowers t ⊔ (zpowers x ⊔ zpowers u) := by
  have hmap := p21_map_subtype_three K t u x
  rw [← hB] at hmap
  ext a
  constructor
  · intro ha
    have h1 : K.subtype a ∈ centralizer ({(t : Γ)} : Set Γ) ⊓ K :=
      Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 ha)), a.2⟩
    rw [← hmap] at h1
    exact (Subgroup.mem_map_iff_mem K.subtype_injective).1 h1
  · intro ha
    have h1 : K.subtype a ∈ (zpowers t ⊔ (zpowers x ⊔ zpowers u)).map K.subtype :=
      Subgroup.mem_map_of_mem _ ha
    rw [hmap] at h1
    exact mem_centralizer_singleton_iff.2
      (Subtype.ext (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 h1).1))

theorem p21_transfer_disjoint {t u x : ↥K}
    (hC : zpowers (t : Γ) ⊓ (zpowers (x : Γ) ⊔ zpowers (u : Γ)) = ⊥) :
    Disjoint (zpowers t) (zpowers x ⊔ zpowers u) := by
  rw [Subgroup.disjoint_def]
  intro a h1 h2
  have e1 : K.subtype a ∈ zpowers (t : Γ) := by
    have := Subgroup.mem_map_of_mem K.subtype h1
    rwa [MonoidHom.map_zpowers] at this
  have e2 : K.subtype a ∈ zpowers (x : Γ) ⊔ zpowers (u : Γ) := by
    have := Subgroup.mem_map_of_mem K.subtype h2
    rwa [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at this
  have : K.subtype a ∈ (⊥ : Subgroup Γ) := hC ▸ Subgroup.mem_inf.2 ⟨e1, e2⟩
  exact Subtype.ext (Subgroup.mem_bot.1 this)

theorem p21_zpowers_subgroupOf (x : ↥K) : (zpowers (x : Γ)).subgroupOf K = zpowers x := by
  ext a
  rw [Subgroup.mem_subgroupOf, mem_zpowers_iff, mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp⟩

end Transfer

end CFSG.LocalAnalysis.EvenBN.Tits.N
