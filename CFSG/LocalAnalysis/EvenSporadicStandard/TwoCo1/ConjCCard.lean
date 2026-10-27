module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.ECoreCover

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open Subgroup

variable {C G : Type*} [Group C] [Group G]

theorem commutator_mem_ker (π : C →* G) {y k : C}
    (hk : π k ∈ centralizer ({π y} : Set G)) : k * y * k⁻¹ * y⁻¹ ∈ π.ker := by
  have h := mem_centralizer_singleton_iff.1 hk
  rw [MonoidHom.mem_ker]
  simp only [map_mul, map_inv]
  rw [h]
  group

theorem commutator_eq_one_iff {a y : C} : a * y * a⁻¹ * y⁻¹ = 1 ↔ a * y = y * a := by
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

noncomputable def commHom (π : C →* G) (hz : π.ker ≤ center C) (y : C) :
    ((centralizer ({π y} : Set G)).comap π) →* π.ker where
  toFun k := ⟨k.1 * y * k.1⁻¹ * y⁻¹, commutator_mem_ker π k.2⟩
  map_one' := by
    ext
    simp
  map_mul' a b := by
    have hw := Subgroup.mem_center_iff.1 (hz (commutator_mem_ker π b.2))
    have hu := Subgroup.mem_center_iff.1 (hz (commutator_mem_ker π a.2))
    have e1 : b.1 * y * b.1⁻¹ = (b.1 * y * b.1⁻¹ * y⁻¹) * y := by group
    ext
    simp only [Subgroup.coe_mul, mul_inv_rev]
    calc a.1 * b.1 * y * (b.1⁻¹ * a.1⁻¹) * y⁻¹
        = a.1 * (b.1 * y * b.1⁻¹) * a.1⁻¹ * y⁻¹ := by group
      _ = a.1 * ((b.1 * y * b.1⁻¹ * y⁻¹) * y) * a.1⁻¹ * y⁻¹ := by rw [← e1]
      _ = (a.1 * (b.1 * y * b.1⁻¹ * y⁻¹)) * (y * a.1⁻¹ * y⁻¹) := by group
      _ = ((b.1 * y * b.1⁻¹ * y⁻¹) * a.1) * (y * a.1⁻¹ * y⁻¹) := by rw [hw a.1]
      _ = (b.1 * y * b.1⁻¹ * y⁻¹) * (a.1 * y * a.1⁻¹ * y⁻¹) := by group
      _ = (a.1 * y * a.1⁻¹ * y⁻¹) * (b.1 * y * b.1⁻¹ * y⁻¹) := hu _

theorem card_ker_commHom (π : C →* G) (hz : π.ker ≤ center C) (y : C) :
    Nat.card (commHom π hz y).ker = Nat.card (centralizer ({y} : Set C)) := by
  have hmk : ∀ k : (centralizer ({π y} : Set G)).comap π, commHom π hz y k = 1 ↔
      k.1 * y = y * k.1 := fun k => by
    rw [← commutator_eq_one_iff, ← Subtype.coe_inj]
    rfl
  refine Nat.card_congr
    { toFun := fun k => ⟨k.1.1, mem_centralizer_singleton_iff.2
        ((hmk k.1).1 (MonoidHom.mem_ker.1 k.2))⟩
      invFun := fun d => ⟨⟨d.1, by
          have h := mem_centralizer_singleton_iff.1 d.2
          rw [mem_comap, mem_centralizer_singleton_iff, ← map_mul, ← map_mul, h]⟩, by
          rw [MonoidHom.mem_ker, hmk]
          exact mem_centralizer_singleton_iff.1 d.2⟩
      left_inv := fun k => rfl
      right_inv := fun d => rfl }

theorem card_comap_eq_two_mul [Finite C] (π : C →* G) (hπ : Function.Surjective π)
    (h2 : Nat.card π.ker = 2) (K : Subgroup G) : Nat.card (K.comap π) = 2 * Nat.card K := by
  have : Finite G := Finite.of_surjective π hπ
  have h1 := Subgroup.card_mul_index (K.comap π)
  have h2' : (K.comap π).index = K.index := Subgroup.index_comap_of_surjective K hπ
  have h3 := Subgroup.card_mul_index K
  have h4 := Subgroup.card_ker_mul_card_of_surjective hπ
  have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have key : Nat.card (K.comap π) * K.index = (2 * Nat.card K) * K.index :=
    calc Nat.card (K.comap π) * K.index = Nat.card (K.comap π) * (K.comap π).index := by
          rw [h2']
      _ = Nat.card C := h1
      _ = Nat.card π.ker * Nat.card G := h4.symm
      _ = 2 * (Nat.card K * K.index) := by rw [h2, h3]
      _ = (2 * Nat.card K) * K.index := by ring
  exact Nat.eq_of_mul_eq_mul_right hpos key

theorem card_centralizer_eq_of_fused [Finite C] (π : C →* G) (hπ : Function.Surjective π)
    (ζ : C) (hker : π.ker = zpowers ζ) (hζc : ζ ∈ center C) (hζo : orderOf ζ = 2) {y c : C}
    (hc : c * y * c⁻¹ = ζ * y) :
    Nat.card (centralizer ({y} : Set C)) = Nat.card (centralizer ({π y} : Set G)) := by
  have hz : π.ker ≤ center C := hker ▸ zpowers_le.2 hζc
  have h2 : Nat.card π.ker = 2 := by rw [hker, Nat.card_zpowers, hζo]
  have hζne : ζ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hζo
    omega
  have hπζ : π ζ = 1 := MonoidHom.mem_ker.1 (hker ▸ mem_zpowers ζ)
  have hcK : π c ∈ centralizer ({π y} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h := congrArg π hc
    simp only [map_mul, map_inv, hπζ, one_mul] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  have hrdvd : Nat.card (commHom π hz y).range ∣ 2 := h2 ▸ card_subgroup_dvd_card _
  have hr2 : Nat.card (commHom π hz y).range = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hrdvd with h | h
    · exfalso
      have hbot := Subgroup.card_eq_one.1 h
      have hmem : (commHom π hz y) ⟨c, hcK⟩ ∈ (commHom π hz y).range := ⟨_, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      have := congrArg Subtype.val hmem
      have e : c * y * c⁻¹ * y⁻¹ = ζ := by rw [hc]; group
      change c * y * c⁻¹ * y⁻¹ = 1 at this
      exact hζne (e.symm.trans this)
    · exact h
  have hmain := Subgroup.card_ker_mul_card_range (commHom π hz y)
  rw [hr2, card_ker_commHom, card_comap_eq_two_mul π hπ h2] at hmain
  omega

theorem card_centralizer_eq_two_mul_of_not_fused [Finite C] (π : C →* G)
    (hπ : Function.Surjective π) (ζ : C) (hker : π.ker = zpowers ζ) (hζc : ζ ∈ center C)
    (hζo : orderOf ζ = 2) {y : C} (h : ∀ c : C, c * y * c⁻¹ ≠ ζ * y) :
    Nat.card (centralizer ({y} : Set C)) = 2 * Nat.card (centralizer ({π y} : Set G)) := by
  have hz : π.ker ≤ center C := hker ▸ zpowers_le.2 hζc
  have h2 : Nat.card π.ker = 2 := by rw [hker, Nat.card_zpowers, hζo]
  have hr1 : Nat.card (commHom π hz y).range = 1 := by
    rw [Subgroup.card_eq_one, eq_bot_iff_forall]
    rintro _ ⟨k, rfl⟩
    have hk := commutator_mem_ker π k.2
    rcases (mem_ker_iff_eq_one_or_eq π ζ hker hζo).1 hk with h1 | h1
    · exact Subtype.ext h1
    · exfalso
      exact h k.1 (mul_inv_eq_iff_eq_mul.1 h1)
  have hmain := Subgroup.card_ker_mul_card_range (commHom π hz y)
  rw [hr1, card_ker_commHom, card_comap_eq_two_mul π hπ h2] at hmain
  omega

theorem card_centralizer_eq_of_isConj {a b : G} (h : IsConj a b) :
    Nat.card (centralizer ({a} : Set G)) = Nat.card (centralizer ({b} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have hm : (centralizer ({a} : Set G)).map (MulAut.conj c).toMonoidHom =
      centralizer ({b} : Set G) := by
    rw [map_centralizer_singleton (MulAut.conj c) a, MulAut.conj_apply, hc]
  rw [← hm, Subgroup.card_map_of_injective (MulAut.conj c).injective]

end CFSG.EvenSporadicStandard.TwoCo1
