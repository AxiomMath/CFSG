module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.Step1
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.AutBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.AltData
import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltFixedCard

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped Nat

theorem card_fixedSubgroup_conjNormal {G : Type*} [Group G] {S : Subgroup G} [S.Normal] {t : G}
    (ht2 : t * t = 1) :
    Nat.card (fixedSubgroup (MulAut.conjNormal (H := S) t)) =
      Nat.card ↥(S ⊓ centralizer ({t} : Set G)) := by
  have hmap : (fixedSubgroup (MulAut.conjNormal (H := S) t)).map S.subtype =
      S ⊓ centralizer ({t} : Set G) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, mem_centralizer_singleton_iff.2 ((mem_fixedSubgroup_conjNormal ht2 x).1 hx)⟩
    · rintro ⟨hyS, hyC⟩
      exact ⟨⟨y, hyS⟩, (mem_fixedSubgroup_conjNormal ht2 ⟨y, hyS⟩).2
        (mem_centralizer_singleton_iff.1 hyC), rfl⟩
  rw [← hmap]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ S.subtype S.subtype_injective).toEquiv

theorem alt_arm_prelim {G : Type} [Group G] [Finite G] {S : Subgroup G} (hSn : S.Normal)
    (hcent : centralizer (S : Set G) = ⊥) {t : G} (ht : orderOf t = 2) {m : ℕ} (hm7 : 7 ≤ m)
    (θ : ↥S ≃* alternatingGroup (Fin m)) (hPS : centralizerDerived t ≤ S)
    (hP5 : Nonempty (↥(centralizerDerived t) ≃* alternatingGroup (Fin 5))) :
    ∃ r : ℕ, 1 ≤ r ∧ 2 * r ≤ m ∧
      Nat.card ↥(S ⊓ centralizer ({t} : Set G)) = 2 ^ (r - 1) * r ! * (m - 2 * r)! ∧
      60 ∣ Nat.card ↥(S ⊓ centralizer ({t} : Set G)) ∧
      Nat.card ↥(S ⊓ centralizer ({t} : Set G)) ∣ Nat.card ↥(centralizer ({t} : Set G)) := by
  haveI := hSn
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two ht
  set σ : MulAut ↥S := MulAut.conjNormal t with hσdef
  have hσ2 : σ * σ = 1 := by
    refine MulEquiv.ext fun y => ?_
    exact conjNormal_involutive ht2 y
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply ne_one_of_orderOf_eq_two ht
    apply conjNormal_injective_of_centralizer hcent
    rw [map_one]
    exact h1
  have hσo : orderOf σ = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact hσ2) hσ1
  obtain ⟨r, hr1, hr2, hcard⟩ :=
    CFSG.ComponentClassification.CatFC.card_fixedSubgroup_alt hm7 θ hσo
  refine ⟨r, hr1, hr2, ?_, ?_, ?_⟩
  · rw [← card_fixedSubgroup_conjNormal ht2]
    exact hcard
  · obtain ⟨e5⟩ := hP5
    have hle : centralizerDerived t ≤ S ⊓ centralizer ({t} : Set G) :=
      le_inf hPS (centralizerDerived_le t)
    have h60 : Nat.card ↥(centralizerDerived t) = 60 := by
      rw [Nat.card_congr e5.toEquiv, natCard_alternatingGroup_five]
    rw [← h60]
    exact Subgroup.card_dvd_of_le hle
  · exact Subgroup.card_dvd_of_le inf_le_right

theorem dvd_cases_240 {d : ℕ} (h60 : 60 ∣ d) (h240 : d ∣ 240) : d = 60 ∨ d = 120 ∨ d = 240 := by
  obtain ⟨j, rfl⟩ := h60
  have hj : 60 * j ≤ 240 := Nat.le_of_dvd (by norm_num) h240
  have hj4 : j ≤ 4 := by omega
  interval_cases j <;> first | omega | (exfalso; revert h240; decide)

theorem card_alt_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem card_mulAut_alt_seven : Nat.card (MulAut (alternatingGroup (Fin 7))) = 5040 := by
  have hb := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
    (by norm_num)
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin]
  rfl

theorem alt_arm_one {G : Type} [Group G] [Finite G] {S : Subgroup G} (hSn : S.Normal)
    (hcent : centralizer (S : Set G) = ⊥) {t : G} (ht : orderOf t = 2) {m : ℕ} (hm : Odd m)
    (hm7 : 7 ≤ m) (θ : ↥S ≃* alternatingGroup (Fin m)) (hPS : centralizerDerived t ≤ S)
    (hP5 : Nonempty (↥(centralizerDerived t) ≃* alternatingGroup (Fin 5)))
    (hC : Nat.card ↥(centralizer ({t} : Set G)) = 240) : Nonempty (G ≃* Equiv.Perm (Fin 7)) := by
  haveI := hSn
  obtain ⟨r, hr1, hr2, hd, h60, hdvd⟩ := alt_arm_prelim hSn hcent ht hm7 θ hPS hP5
  rw [hC] at hdvd
  obtain ⟨rfl, -, -⟩ := alt_numeric_one hm hm7 hr1 hr2 hd (dvd_cases_240 h60 hdvd)
  have hS7 : Nat.card ↥S = 2520 := by
    rw [Nat.card_congr θ.toEquiv]
    exact card_alt_seven
  have hMA : Nat.card (MulAut ↥S) = 5040 := by
    rw [Nat.card_congr (MulAut.congr θ).toEquiv]
    exact card_mulAut_alt_seven
  have hGle : Nat.card G ≤ 5040 := hMA ▸ card_le_card_mulAut hcent
  have h2S : 2520 ∣ Nat.card G := hS7 ▸ Subgroup.card_subgroup_dvd_card S
  have h240 : 240 ∣ Nat.card G := hC ▸ Subgroup.card_subgroup_dvd_card _
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have hG : Nat.card G = 5040 := by omega
  have hb := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
    (by norm_num)
  let c7 : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 7))) hb
  let ρ : G →* Equiv.Perm (Fin 7) :=
    c7.symm.toMonoidHom.comp ((MulAut.congr θ).toMonoidHom.comp MulAut.conjNormal)
  have hρ : Function.Injective ρ :=
    c7.symm.injective.comp ((MulAut.congr θ).injective.comp
      (conjNormal_injective_of_centralizer hcent))
  have hcard : Nat.card (Equiv.Perm (Fin 7)) ≤ Nat.card G := by
    rw [hG, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  exact ⟨MulEquiv.ofBijective ρ (hρ.bijective_of_nat_card_le hcard)⟩

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
