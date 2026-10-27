module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYHsSpec

public section

namespace CFSG.EvenSporadicStandard.HSStd.FiveY

open Subgroup CFSG.RankThree.Native

section Pi

variable {G : Type} [Group G] {t : G}

@[expose] noncomputable def piHom (θ : OuterSection t ≃* ↥hs100R) :
    ↥(centralizer ({t} : Set G)) →* ↥hs100R :=
  θ.toMonoidHom.comp (QuotientGroup.mk' (vSub t))

theorem piHom_apply (θ : OuterSection t ≃* ↥hs100R) (x : ↥(centralizer ({t} : Set G))) :
    piHom θ x = θ (QuotientGroup.mk x) := rfl

theorem piHom_surjective (θ : OuterSection t ≃* ↥hs100R) : Function.Surjective (piHom θ) :=
  θ.surjective.comp (QuotientGroup.mk'_surjective _)

theorem piHom_eq_one_iff (θ : OuterSection t ≃* ↥hs100R) (x : ↥(centralizer ({t} : Set G))) :
    piHom θ x = 1 ↔ x ∈ vSub t := by
  rw [piHom_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem orderOf_piHom_three (ht2 : t * t = 1) (ht1 : t ≠ 1) (θ : OuterSection t ≃* ↥hs100R)
    {x : ↥(centralizer ({t} : Set G))} (hx : orderOf x = 3) : orderOf (piHom θ x) = 3 := by
  have h3 : piHom θ x ^ 3 = 1 := by
    rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have hne : piHom θ x ≠ 1 := by
    intro h1
    have hmem := (piHom_eq_one_iff θ x).1 h1
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
    have hsq : vElem t * vElem t = 1 := Subtype.ext ht2
    rcases zpow_involution hsq k with h | h
    · rw [h] at hk
      rw [← hk, orderOf_one] at hx
      omega
    · rw [h] at hk
      rw [← hk, orderOf_vElem ht2 ht1] at hx
      omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime h3 hne

end Pi

section Counting


variable {G : Type} [Group G] [Finite G] {t : G}

theorem card_cent_ty_le (ht2 : t * t = 1) (ht1 : t ≠ 1) (θ : OuterSection t ≃* ↥hs100R) {y : G}
    (hyt : y ∈ centralizer ({t} : Set G)) (hy3 : orderOf y = 3) :
    Nat.card ↥(centralizer ({t} : Set G) ⊓ centralizer ({y} : Set G)) ≤ 1440 := by
  set N := centralizer ({t} : Set G) with hN
  set yN : ↥N := ⟨y, hyt⟩ with hyN
  rw [← card_centralizer_subtype N yN]
  set π := piHom θ with hπ
  set C := centralizer ({yN} : Set ↥N) with hC
  set f : ↥C →* ↥hs100R := π.comp C.subtype with hf
  have hyNord : orderOf yN = 3 := (Subgroup.orderOf_mk y hyt).trans hy3
  have hπy : orderOf (π yN) = 3 := orderOf_piHom_three ht2 ht1 θ hyNord
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h1
  have hrange : f.range ≤ centralizer ({π yN} : Set ↥hs100R) := by
    rintro _ ⟨c, rfl⟩
    rw [mem_centralizer_singleton_iff, hf, MonoidHom.comp_apply, ← map_mul, ← map_mul]
    exact congrArg π (mem_centralizer_singleton_iff.1 c.2)
  have h2 : Nat.card f.range ≤ 720 := by
    rw [← card_centralizer_hs100R_three hπy]
    exact Subgroup.card_le_of_le hrange
  have h3 : Nat.card f.ker ≤ 2 := by
    have hker : ∀ c : ↥f.ker, ((c : ↥C) : ↥N) ∈ vSub t := fun c =>
      (piHom_eq_one_iff θ _).1 (MonoidHom.mem_ker.1 c.2)
    have hinj : Function.Injective (fun c : ↥f.ker => (⟨((c : ↥C) : ↥N), hker c⟩ : ↥(vSub t))) := by
      intro a b hab
      exact Subtype.ext (Subtype.ext (Subtype.ext
        (congrArg (fun x : ↥(vSub t) => ((x : ↥N) : G)) hab)))
    have := Nat.card_le_card_of_injective _ hinj
    rwa [card_vSub ht2 ht1] at this
  rw [h1]
  calc Nat.card f.range * Nat.card f.ker ≤ 720 * 2 := Nat.mul_le_mul h2 h3
    _ = 1440 := by norm_num

omit [Finite G] in
theorem exists_conj_cent_three (ht2 : t * t = 1) (ht1 : t ≠ 1) (θ : OuterSection t ≃* ↥hs100R)
    {a b : G} (ha : a ∈ centralizer ({t} : Set G)) (hb : b ∈ centralizer ({t} : Set G))
    (ha3 : orderOf a = 3) (hb3 : orderOf b = 3) :
    ∃ n ∈ centralizer ({t} : Set G), n * a * n⁻¹ = b := by
  set aN : ↥(centralizer ({t} : Set G)) := ⟨a, ha⟩
  set bN : ↥(centralizer ({t} : Set G)) := ⟨b, hb⟩
  have haN : orderOf aN = 3 := (Subgroup.orderOf_mk a ha).trans ha3
  have hbN : orderOf bN = 3 := (Subgroup.orderOf_mk b hb).trans hb3
  obtain ⟨c, hc⟩ := exists_conj_hs100R_three (orderOf_piHom_three ht2 ht1 θ haN)
    (orderOf_piHom_three ht2 ht1 θ hbN)
  obtain ⟨n, rfl⟩ := piHom_surjective θ c
  have hmem : (n * aN * n⁻¹)⁻¹ * bN ∈ vSub t := by
    rw [← piHom_eq_one_iff θ]
    simp only [map_mul, map_inv]
    rw [← hc]
    group
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
  have hsq : vElem t * vElem t = 1 := Subtype.ext ht2
  have hbN' : bN = (n * aN * n⁻¹) * vElem t ^ k := by
    rw [hk]
    group
  rcases zpow_involution hsq k with h | h
  · rw [h, mul_one] at hbN'
    exact ⟨(n : G), n.2, congrArg Subtype.val hbN'.symm⟩
  · exfalso
    rw [h] at hbN'
    have hcomm : Commute (n * aN * n⁻¹) (vElem t) :=
      Subtype.ext (mem_centralizer_singleton_iff.1 (n * aN * n⁻¹).2)
    have ho1 : orderOf (n * aN * n⁻¹) = 3 := by
      rw [← haN]
      exact (MulAut.conj n).orderOf_eq aN
    have ho2 : orderOf (vElem t) = 2 := orderOf_vElem ht2 ht1
    have hcop : Nat.Coprime (orderOf (n * aN * n⁻¹)) (orderOf (vElem t)) := by
      rw [ho1, ho2]
      norm_num
    have := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop
    rw [← hbN', hbN, ho1, ho2] at this
    omega

end Counting

end CFSG.EvenSporadicStandard.HSStd.FiveY
