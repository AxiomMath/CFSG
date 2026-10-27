module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F7U
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F7Syl

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem card_sup_eq_mul_of_le_normalizer' {A B : Subgroup G}
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) (hinf : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left A B hBA
  let f : A × B → ↥(A ⊔ B) := fun p =>
    ⟨(p.1 : G) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨a1, ha1⟩, ⟨b1, hb1⟩⟩ ⟨⟨a2, ha2⟩, ⟨b2, hb2⟩⟩ heq
      have h1 : a1 * b1 = a2 * b2 := congrArg Subtype.val heq
      have h2 : a2⁻¹ * a1 = b2 * b1⁻¹ := by
        calc a2⁻¹ * a1 = a2⁻¹ * (a1 * b1) * b1⁻¹ := by group
          _ = a2⁻¹ * (a2 * b2) * b1⁻¹ := by rw [h1]
          _ = b2 * b1⁻¹ := by group
      have h3 : a2⁻¹ * a1 ∈ A ⊓ B :=
        ⟨A.mul_mem (A.inv_mem ha2) ha1, h2 ▸ B.mul_mem hb2 (B.inv_mem hb1)⟩
      rw [hinf, Subgroup.mem_bot] at h3
      have ha : a2 = a1 := inv_mul_eq_one.mp h3
      subst ha
      have hb : b1 = b2 := mul_left_cancel h1
      subst hb
      rfl
    · rintro ⟨x, hx⟩
      have hx' : x ∈ (A : Set G) * (B : Set G) := by rw [← hset]; exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

private theorem inf_zpowers_eq_bot_of_not_mem {E : Subgroup G} {t : G}
    (hcard : Nat.card (zpowers t) = 2) (htE : t ∉ E) : zpowers t ⊓ E = ⊥ := by
  rw [Subgroup.eq_bot_iff_card]
  have hdvd : Nat.card ↥(zpowers t ⊓ E) ∣ 2 := by
    have h := Subgroup.card_dvd_of_le (inf_le_left : zpowers t ⊓ E ≤ zpowers t)
    rwa [hcard] at h
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact h1
  · exfalso
    have heq : (zpowers t ⊓ E : Subgroup G) = zpowers t :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (by rw [h2, hcard]))
    have htmem : t ∈ (zpowers t ⊓ E : Subgroup G) := by
      rw [heq]; exact Subgroup.mem_zpowers t
    exact htE htmem.2

theorem sec8t84_conj_of_syl {t γ : G} {E E0 B B' : Subgroup G} (ht : t * t = 1)
    (hE8 : IsElemAb2 E 8) (hE08 : IsElemAb2 E0 8) (htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E)
    (htE0 : ∀ e ∈ E0, t * e * t⁻¹ ∈ E0) (hB : E ⊓ centralizer ({t} : Set G) = B)
    (hB4 : Nat.card B = 16) (hSyl : IsSylow2Of (zpowers t ⊔ E) (centralizer (B : Set G)))
    (hγ : γ ∈ centralizer ({t} : Set G)) (hB' : B' = B.map (MulAut.conj γ).toMonoidHom)
    (hB'E0 : B' ≤ E0 ⊓ centralizer ({t} : Set G))
    (hE0c : Nat.card ↥(E0 ⊓ centralizer ({t} : Set G)) ≤ 16) :
    ∃ u : G, E0 = E.map (MulAut.conj u).toMonoidHom := by
  have ht2 : t ^ 2 = 1 := by rw [pow_two]; exact ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have htE_ne : t ∉ E := by
    intro htEmem
    have hEle : E ≤ centralizer ({t} : Set G) := by
      intro e he
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hE8.1.comm he htEmem
    have hBE : B = E := by rw [← hB, inf_eq_left.mpr hEle]
    have h256 : Nat.card E = 16 := by rw [← hBE]; exact hB4
    rw [hE8.2] at h256
    exact absurd h256 (by norm_num)
  have hB'card : Nat.card B' = 16 := by
    rw [hB', Subgroup.card_map_of_injective (MulAut.conj γ).injective, hB4]
  have hBz16 : Nat.card ↥(E0 ⊓ centralizer ({t} : Set G)) = 16 := by
    apply le_antisymm hE0c
    calc 16 = Nat.card B' := hB'card.symm
      _ ≤ Nat.card ↥(E0 ⊓ centralizer ({t} : Set G)) := Subgroup.card_le_of_le hB'E0
  have htE0_ne : t ∉ E0 := by
    intro htE0mem
    have hE0le : E0 ≤ centralizer ({t} : Set G) := by
      intro e he
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hE08.1.comm he htE0mem
    have h256 : Nat.card E0 = 16 := by rw [← inf_eq_left.mpr hE0le]; exact hBz16
    rw [hE08.2] at h256
    exact absurd h256 (by norm_num)
  have ht1 : t ≠ 1 := by
    intro h
    apply htE_ne
    rw [h]
    exact E.one_mem
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard_zp : Nat.card (zpowers t) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ht2 ht1]
  have htn : t ∈ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · exact htE e
    · intro he
      have h2 := htE (t * e * t⁻¹) he
      have hconj : t * (t * e * t⁻¹) * t⁻¹ = e := by
        rw [htinv]
        calc t * (t * e * t) * t = (t * t) * e * (t * t) := by simp only [mul_assoc]
          _ = e := by rw [ht, one_mul, mul_one]
      rwa [hconj] at h2
  have hzpnorm : zpowers t ≤ Subgroup.normalizer (E : Set G) := Subgroup.zpowers_le.mpr htn
  have htn0 : t ∈ Subgroup.normalizer (E0 : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · exact htE0 e
    · intro he
      have h2 := htE0 (t * e * t⁻¹) he
      have hconj : t * (t * e * t⁻¹) * t⁻¹ = e := by
        rw [htinv]
        calc t * (t * e * t) * t = (t * t) * e * (t * t) := by simp only [mul_assoc]
          _ = e := by rw [ht, one_mul, mul_one]
      rwa [hconj] at h2
  have hzpnorm0 : zpowers t ≤ Subgroup.normalizer (E0 : Set G) := Subgroup.zpowers_le.mpr htn0
  have hdisjE : E ⊓ zpowers t = ⊥ := by
    rw [inf_comm]; exact inf_zpowers_eq_bot_of_not_mem hcard_zp htE_ne
  have hdisjE0 : E0 ⊓ zpowers t = ⊥ := by
    rw [inf_comm]; exact inf_zpowers_eq_bot_of_not_mem hcard_zp htE0_ne
  have hKcard : Nat.card (zpowers t ⊔ E : Subgroup G) = 2 ^ 9 := by
    have h := card_sup_eq_mul_of_le_normalizer' (A := E) (B := zpowers t) hzpnorm hdisjE
    calc Nat.card (zpowers t ⊔ E : Subgroup G)
        = Nat.card (E ⊔ zpowers t : Subgroup G) := by rw [sup_comm]
      _ = Nat.card E * Nat.card (zpowers t) := h
      _ = 2 ^ 9 := by rw [hE8.2, hcard_zp]; norm_num
  have hK0card : Nat.card (zpowers t ⊔ E0 : Subgroup G) = 2 ^ 9 := by
    have h := card_sup_eq_mul_of_le_normalizer' (A := E0) (B := zpowers t) hzpnorm0 hdisjE0
    calc Nat.card (zpowers t ⊔ E0 : Subgroup G)
        = Nat.card (E0 ⊔ zpowers t : Subgroup G) := by rw [sup_comm]
      _ = Nat.card E0 * Nat.card (zpowers t) := h
      _ = 2 ^ 9 := by rw [hE08.2, hcard_zp]; norm_num
  have hSylMap : IsSylow2Of ((zpowers t ⊔ E).map (MulAut.conj γ).toMonoidHom)
      (centralizer (B' : Set G)) := by
    have h := sec8t84_isSylow2Of_map hSyl γ
    rw [← sec8t84_centralizer_map B γ, ← hB'] at h
    exact h
  have hU : (zpowers t ⊔ E0 : Subgroup G) ≤ centralizer (B' : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.mp (hB'E0 hb).2
    · intro e he
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hE08.1.comm he (hB'E0 hb).1).symm
  have hU2 : IsPGroup 2 (zpowers t ⊔ E0 : Subgroup G) :=
    IsPGroup.of_card (p := 2) (n := 9) hK0card
  have hcardVU : Nat.card ((zpowers t ⊔ E).map (MulAut.conj γ).toMonoidHom) ≤
      Nat.card (zpowers t ⊔ E0 : Subgroup G) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj γ).injective, hKcard, hK0card]
  obtain ⟨h, _hh, hK0eq⟩ := sec8t84_two_syl_conj hSylMap hU hU2 hcardVU
  set A : Subgroup G := E.map (MulAut.conj (h * γ)).toMonoidHom with hA_def
  have hcomp : (MulAut.conj h).toMonoidHom.comp (MulAut.conj γ).toMonoidHom
      = (MulAut.conj (h * γ)).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hA_eq : A = (E.map (MulAut.conj γ).toMonoidHom).map (MulAut.conj h).toMonoidHom := by
    rw [hA_def, Subgroup.map_map, hcomp]
  have hA_le : A ≤ (zpowers t ⊔ E0 : Subgroup G) := by
    rw [hK0eq, hA_eq]
    exact Subgroup.map_mono (Subgroup.map_mono (le_sup_right : E ≤ zpowers t ⊔ E))
  have hA8 : IsElemAb2 A 8 := by
    rw [hA_def]
    haveI : IsMulCommutative E := hE8.1.1
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · rintro x hx
      obtain ⟨e, he, rfl⟩ := hx
      rw [← map_pow, hE8.1.2 e he, map_one]
    · rw [Subgroup.card_map_of_injective (MulAut.conj (h * γ)).injective, hE8.2]
  have hAE0 : A = E0 :=
    sec8t84_unique_E8 (E := E0) (K := zpowers t ⊔ E0)
      (B := E0 ⊓ centralizer ({t} : Set G)) (A := A)
      ht hE08 rfl htE0 rfl hBz16 hA_le hA8
  exact ⟨h * γ, by rw [← hAE0, hA_def]⟩

end CFSG.OddStandard.SmallF3.Omega
