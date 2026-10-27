module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH4Norm
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH4Sylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH4Table

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup

namespace CResH4

theorem card_inf_centralizer_alt6 (hA6 : AutA6Table) {X : Type} [Group X] (E : Subgroup X)
    [E.Normal] (e : E ≃* alternatingGroup (Fin 6)) {ζ : X} (hζ : ζ * ζ = 1) :
    Nat.card ↥(E ⊓ centralizer ({ζ} : Set X)) = 360 ∨
      Nat.card ↥(E ⊓ centralizer ({ζ} : Set X)) = 8 ∨
      Nat.card ↥(E ⊓ centralizer ({ζ} : Set X)) = 24 ∨
      Nat.card ↥(E ⊓ centralizer ({ζ} : Set X)) = 10 := by
  have hα : (MulAut.conjNormal ζ : MulAut E) * MulAut.conjNormal ζ = 1 := by
    rw [← map_mul, hζ, map_one]
  have h := hA6 e _ hα
  have hequiv : {k : E // (MulAut.conjNormal ζ : MulAut E) k = k} ≃
      ↥(E ⊓ centralizer ({ζ} : Set X)) :=
    { toFun := fun k => ⟨k.1, k.1.2, mem_centralizer_singleton_iff.2 (by
        have h1 := congrArg Subtype.val k.2
        rw [MulAut.conjNormal_apply] at h1
        exact (mul_inv_eq_iff_eq_mul.1 h1).symm)⟩
      invFun := fun y => ⟨⟨y.1, (mem_inf.1 y.2).1⟩, Subtype.ext (by
        rw [MulAut.conjNormal_apply]
        exact mul_inv_eq_iff_eq_mul.2 (mem_centralizer_singleton_iff.1 (mem_inf.1 y.2).2).symm)⟩
      left_inv := fun k => rfl
      right_inv := fun y => rfl }
  rwa [Nat.card_congr hequiv] at h

theorem arith_inf (n m : ℕ) (h1 : n = m ∨ n = 3 * m) (h2 : n = 360 ∨ n = 8 ∨ n = 24 ∨ n = 10)
    (h3 : m = 1 ∨ m = 2 ∨ m = 360 ∨ m = 720 ∨ m = 1440) : n = 360 := by
  omega

theorem arith_layer (n m : ℕ) (h1 : n = m ∨ n = 3 * m) (h2 : n = 360)
    (h3 : m = 1 ∨ m = 2 ∨ m = 360 ∨ m = 720 ∨ m = 1440) : m = 360 := by
  omega

theorem normal_comap_of_normalized {P X : Type*} [Group P] [Group X] (ρ : P →* X)
    (N : Subgroup X) (hN : ∀ ω ∈ ρ.range, ∀ n ∈ N, ω * n * ω⁻¹ ∈ N) : (N.comap ρ).Normal :=
  ⟨fun n hn g => by
    rw [mem_comap, map_mul, map_mul, map_inv]
    exact hN _ ⟨g, rfl⟩ _ hn⟩

theorem conj_mem_inf_centralizer {X : Type*} [Group X] (E : Subgroup X) [E.Normal] {ζ ω n : X}
    (hω : ω ∈ centralizer ({ζ} : Set X)) (hn : n ∈ E ⊓ centralizer ({ζ} : Set X)) :
    ω * n * ω⁻¹ ∈ E ⊓ centralizer ({ζ} : Set X) :=
  mem_inf.2 ⟨Normal.conj_mem inferInstance n (mem_inf.1 hn).1 ω,
    mul_mem (mul_mem hω (mem_inf.1 hn).2) (inv_mem hω)⟩

theorem le_centralizer_of_layer {P X : Type} [Group P] [Group X] [Finite X] (hA6 : AutA6Table)
    (ρ : P →* X) (φ : P →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6))
    (hφ : Function.Surjective φ) (hker : ρ.ker ≤ φ.ker) (hk : Nat.card φ.ker = 3)
    (E : Subgroup X) [E.Normal] (e : E ≃* alternatingGroup (Fin 6)) {ζ : X} (hζ : ζ * ζ = 1)
    (hrange : ρ.range = centralizer ({ζ} : Set X)) : E ≤ centralizer ({ζ} : Set X) := by
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup X, N = E ⊓ centralizer ({ζ} : Set X) := ⟨_, rfl⟩
  have hNr : N ≤ ρ.range := hNdef ▸ inf_le_right.trans hrange.ge
  have hNn : (N.comap ρ).Normal := normal_comap_of_normalized ρ N fun ω hω n hn =>
    hNdef ▸ conj_mem_inf_centralizer E (hrange.le hω) (hNdef ▸ hn)
  have hMn : ((N.comap ρ).map φ).Normal := hNn.map φ hφ
  have h1 := card_eq_or_card_eq_three_mul_card_map_comap ρ φ hker hk N hNr
  have h2 := hNdef ▸ card_inf_centralizer_alt6 hA6 E e hζ
  have h3 := card_normal_z2s6 _ hMn
  have h360 : Nat.card N = 360 := arith_inf _ _ h1 h2 h3
  have hE : Nat.card E = 360 := by
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_six]
  have hEN : N = E := eq_of_le_of_card_ge (hNdef ▸ inf_le_left) (by rw [h360, hE])
  exact fun x hx => (mem_inf.1 (hNdef ▸ (hEN ▸ hx : x ∈ N))).2

theorem le_two_of_pow_dvd_six (u n : ℕ) (h : u = 2 ^ n) (h6 : u ∣ 6) : u ≤ 2 := by
  rcases n with _ | _ | n
  · simp [h]
  · simp [h]
  · exfalso
    have h4 : 4 ∣ u := ⟨2 ^ n, by rw [h]; ring⟩
    have := h4.trans h6
    omega

theorem card_le_two_of_layer {P X : Type} [Group P] [Group X] [Finite X]
    (ρ : P →* X) (φ : P →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6))
    (hφ : Function.Surjective φ) (hker : ρ.ker ≤ φ.ker) (hk : Nat.card φ.ker = 3)
    (E : Subgroup X) [E.Normal] (hE : Nat.card E = 360) (hEr : E ≤ ρ.range)
    (U : Subgroup X) (hUr : U ≤ ρ.range) (hUp : IsPGroup 2 U)
    (hUE : U ≤ centralizer (E : Set X)) : Nat.card U ≤ 2 := by
  have hEn : (E.comap ρ).Normal := inferInstance
  have hMn : ((E.comap ρ).map φ).Normal := hEn.map φ hφ
  have h1 := card_eq_or_card_eq_three_mul_card_map_comap ρ φ hker hk E hEr
  have hM360 : Nat.card ((E.comap ρ).map φ) = 360 :=
    arith_layer _ _ h1 hE (card_normal_z2s6 _ hMn)
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup P, C = (centralizer (E : Set X)).comap ρ := ⟨_, rfl⟩
  have hCsnd : ∀ c ∈ C, (φ c).2 = 1 := by
    intro c hc
    refine snd_eq_one_of_commute_normal _ hMn hM360 (φ c) ?_
    rintro _ ⟨e0, he0, rfl⟩
    have hc' : ρ c ∈ centralizer (E : Set X) := by
      rw [hCdef] at hc
      exact hc
    have hcomm : ρ e0 * ρ c = ρ c * ρ e0 := mem_centralizer_iff.1 hc' (ρ e0) he0
    have hx : (e0 * c)⁻¹ * (c * e0) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, hcomm, inv_mul_cancel]
    have h2 : φ ((e0 * c)⁻¹ * (c * e0)) = 1 := hker hx
    rw [map_mul, map_inv] at h2
    have h3 : φ (e0 * c) = φ (c * e0) := inv_mul_eq_one.1 h2
    rw [← map_mul, ← map_mul]
    exact h3.symm
  have hCle : C.map φ ≤ (MonoidHom.snd (Multiplicative (ZMod 2))
      (Equiv.Perm (Fin 6))).ker := by
    rintro _ ⟨c, hc, rfl⟩
    exact hCsnd c hc
  have hd1 : Nat.card (C.map φ) ∣ 2 := by
    have := Subgroup.card_dvd_of_le hCle
    rwa [card_ker_snd] at this
  have hd2 : Nat.card ↥(C ⊓ φ.ker) ∣ 3 := by
    have := Subgroup.card_dvd_of_le (inf_le_right : C ⊓ φ.ker ≤ φ.ker)
    rwa [hk] at this
  have hC6 : Nat.card C ∣ 6 := by
    rw [← natCard_map_mul_natCard_inf_ker φ C]
    exact mul_dvd_mul hd1 hd2
  have hUC : U.comap ρ ≤ C := fun x hx => hCdef ▸ hUE hx
  have hmap : (U.comap ρ).map ρ = U := map_comap_eq_self hUr
  have hU1 : Nat.card U ∣ Nat.card (U.comap ρ) := by
    have := Subgroup.card_map_dvd (H := U.comap ρ) ρ
    rwa [hmap] at this
  have hU6 : Nat.card U ∣ 6 := hU1.trans ((Subgroup.card_dvd_of_le hUC).trans hC6)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hUp
  exact le_two_of_pow_dvd_six _ n hn hU6

theorem conj_eq_of_layer {Y X : Type} [Group Y] [Finite Y] [Group X] (hA6 : AutA6Table)
    (π : Y →* X) (hπ : Function.Surjective π) {z : Y} (hz : z * z = 1)
    (hcop : centralizer ({π z} : Set X) ≤ (centralizer ({z} : Set Y)).map π)
    (φ : centralizer ({z} : Set Y) →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6))
    (hφ : Function.Surjective φ) (hk : Nat.card φ.ker = 3)
    (hker : ∀ p : centralizer ({z} : Set Y), π p = 1 → φ p = 1)
    (hX : ∀ N : Subgroup X, N.Normal → Odd (Nat.card N) → N = ⊥)
    (E : Subgroup X) [E.Normal] (e : E ≃* alternatingGroup (Fin 6)) (x : X) :
    x * π z * x⁻¹ = π z := by
  have : Finite X := Finite.of_surjective π hπ
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : centralizer ({z} : Set Y) →* X,
      ρ = π.comp (centralizer ({z} : Set Y)).subtype := ⟨_, rfl⟩
  have hρ : ∀ p, ρ p = π (p : Y) := fun p => by rw [hρdef]; rfl
  have hζ : π z * π z = 1 := by rw [← map_mul, hz, map_one]
  have hrange : ρ.range = centralizer ({π z} : Set X) := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      rw [hρ, mem_centralizer_singleton_iff]
      have := mem_centralizer_singleton_iff.1 p.2
      rw [← map_mul, ← map_mul, this]
    · intro ω hω
      obtain ⟨p, hp, rfl⟩ := hcop hω
      exact ⟨⟨p, hp⟩, hρ ⟨p, hp⟩⟩
  have hρker : ρ.ker ≤ φ.ker := fun p hp => hker p (by rwa [← hρ])
  by_cases hζ1 : π z = 1
  · rw [hζ1]
    simp
  have hEc : E ≤ centralizer ({π z} : Set X) :=
    le_centralizer_of_layer hA6 ρ φ hφ hρker hk E e hζ hrange
  have hE360 : Nat.card E = 360 := by rw [Nat.card_congr e.toEquiv, card_alternatingGroup_six]
  have hζK : π z ∈ centralizer (E : Set X) := mem_centralizer_iff.2 fun h hh =>
    mem_centralizer_singleton_iff.1 (hEc hh)
  have hU : ∀ U : Subgroup X, IsPGroup 2 U → U ≤ centralizer (E : Set X) →
      U ≤ centralizer ({π z} : Set X) → Nat.card U ≤ 2 := fun U hUp hUK hUc =>
    card_le_two_of_layer ρ φ hφ hρker hk E hE360 (hEc.trans hrange.ge) U (hUc.trans hrange.ge)
      hUp hUK
  exact conj_eq_of_normal (centralizer (E : Set X)) hζK hζ hζ1 hU hX x

theorem map_eq_one_of_odd_ker {Y X : Type*} [Group Y] [Group X] (π : Y →* X) {z : Y}
    (hodd : Odd (Nat.card π.ker))
    (φ : centralizer ({z} : Set Y) →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6))
    (hφ : Function.Surjective φ) (p : centralizer ({z} : Set Y)) (hp : π p = 1) : φ p = 1 := by
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : centralizer ({z} : Set Y) →* X,
      ρ = π.comp (centralizer ({z} : Set Y)).subtype := ⟨_, rfl⟩
  have hρ : ∀ q, ρ q = π (q : Y) := fun q => by rw [hρdef]; rfl
  have hM : (ρ.ker.map φ).Normal := (inferInstance : ρ.ker.Normal).map φ hφ
  have hle : ρ.ker.map (centralizer ({z} : Set Y)).subtype ≤ π.ker := by
    rintro _ ⟨q, hq, rfl⟩
    have h1 := MonoidHom.mem_ker.1 hq
    rw [hρ] at h1
    exact h1
  have hd : Nat.card ρ.ker ∣ Nat.card π.ker := by
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective (centralizer ({z} : Set Y)))
      (K := ρ.ker)]
    exact Subgroup.card_dvd_of_le hle
  have hodd' : Odd (Nat.card (ρ.ker.map φ)) :=
    Odd.of_dvd_nat (Odd.of_dvd_nat hodd hd) (Subgroup.card_map_dvd ρ.ker φ)
  have hbot := normal_z2s6_eq_bot_of_odd _ hM hodd'
  have hmem : φ p ∈ ρ.ker.map φ := mem_map_of_mem φ (by rw [MonoidHom.mem_ker, hρ]; exact hp)
  rw [hbot] at hmem
  exact mem_bot.1 hmem

end CResH4

end CFSG.EvenSporadicStandard.M24Std
