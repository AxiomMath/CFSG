module

public import CFSG.GH74.GLS.Stage2.Local.Bar
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.GH74.GLS.Stage2.Local.Concl

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12
open scoped commutatorElement

section KleinAut

variable {V : Type*} [Group V] [IsKleinFour V]

theorem klein_aut_order_three_fixed_free (σ : MulAut V) (h3 : orderOf σ = 3) {v : V}
    (hv : σ v = v) : v = 1 := by
  by_contra hv1
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at h3
    omega
  obtain ⟨w, hw⟩ : ∃ w : V, σ w ≠ w := by
    by_contra hcon
    exact hσ1 (MulEquiv.ext fun w => by by_contra h; exact hcon ⟨w, h⟩)
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact hw (map_one σ)
  have hwv : w ≠ v := by
    rintro rfl
    exact hw hv
  have hσw1 : σ w ≠ 1 := fun h => hw1 (σ.injective (by rw [h, map_one]))
  have hσwv : σ w ≠ v := fun h => hwv (σ.injective (by rw [h, hv]))
  have hσw : σ w = w * v := IsKleinFour.eq_mul_of_ne_all hw1 hv1 hwv hσw1 hw hσwv
  have hσ2w : σ (σ w) = w := by
    rw [hσw, map_mul, hσw, hv, mul_assoc, IsKleinFour.mul_self, mul_one]
  have hσ2 : ∀ u : V, σ (σ u) = u := by
    intro u
    by_cases hu1 : u = 1
    · rw [hu1, map_one, map_one]
    by_cases huv : u = v
    · rw [huv, hv, hv]
    by_cases huw : u = w
    · rw [huw]; exact hσ2w
    have : u = w * v := IsKleinFour.eq_mul_of_ne_all hw1 hv1 hwv hu1 huw huv
    rw [this, map_mul, map_mul, hσ2w, hv, hv]
  have : σ ^ 2 = 1 := by
    ext u
    simp [pow_two, hσ2 u]
  have := orderOf_dvd_of_pow_eq_one this
  rw [h3] at this
  omega

end KleinAut

section D

variable {G : Type} [Group G] [Finite G] {z : G}

theorem lemma23_d (hV : Prop21h z) : 2 ≤ pRank 2 ↥(⁅Cen z, Cen z⁆ : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨V, hVL, hV4, hAut⟩ := hV
  have hVC : V ≤ Cen z := hVL.trans (LC_le_Cen z)
  have hEA : IsElementaryAbelian 2 ↥V := hV4.1
  have hcardV : Nat.card ↥V = 4 := hV4.2
  have : IsKleinFour ↥V := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hVne : V ≠ ⊥ := by
      intro hb
      rw [hb] at hcardV
      simp at hcardV
    have : Nontrivial ↥V := (Subgroup.nontrivial_iff_ne_bot V).mpr hVne
    exact ⟨hcardV, hEA.exponent_eq_prime⟩
  let N : Subgroup G := normalizer (V : Set G) ⊓ Cen z
  have hNle : N ≤ normalizer (V : Set G) := inf_le_left
  let α : ↥N →* MulAut ↥V := V.normalizerMonoidHom.comp (Subgroup.inclusion hNle)
  have hker : α.ker = (centralizer (V : Set G) ⊓ Cen z).subgroupOf N := by
    ext ⟨g, hg⟩
    have h1 : α ⟨g, hg⟩ = 1 ↔ g ∈ centralizer (V : Set G) := by
      have := Subgroup.normalizerMonoidHom_ker V
      have h2 : (⟨g, hNle hg⟩ : ↥(normalizer (V : Set G))) ∈ V.normalizerMonoidHom.ker ↔
          g ∈ centralizer (V : Set G) := by
        rw [this]; exact Iff.rfl
      rw [← h2]; exact Iff.rfl
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, h1]
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h, hg.2⟩, fun h => h.1⟩
  have hcard : Nat.card α.range = AutOrd (Cen z) V := by
    rw [← Subgroup.index_ker, hker]; rfl
  have h3dvd : 3 ∣ Nat.card α.range := by
    rw [hcard]
    rcases hAut with h | h
    · rw [h]
    · rw [h]; decide
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  have hσ : orderOf (x : MulAut ↥V) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨g, hg⟩ := x.2
  have hfix : ∀ v : ↥V, (x : MulAut ↥V) v = v → v = 1 := fun v hv =>
    klein_aut_order_three_fixed_free (x : MulAut ↥V) hσ hv
  have hcomm : ∀ a b : ↥V, a * b = b * a := fun a b =>
    (IsKleinFour.isMulCommutative (G := ↥V)).is_comm.comm a b
  have hconj : ∀ v : ↥V, (((x : MulAut ↥V) v : ↥V) : G) = (g : G) * v * (g : G)⁻¹ := by
    intro v
    rw [← hg]
    rfl
  let _ : CommGroup ↥V := { (inferInstance : Group ↥V) with mul_comm := hcomm }
  have hinj : Function.Injective (fun v : ↥V => (x : MulAut ↥V) v / v) := by
    intro a b hab
    have h1 : (x : MulAut ↥V) a / (x : MulAut ↥V) b = a / b :=
      div_eq_div_iff_div_eq_div.mp hab
    have h2 : (x : MulAut ↥V) (a / b) = a / b := by rw [map_div]; exact h1
    exact div_eq_one.mp (hfix _ h2)
  have hsurj := Finite.injective_iff_surjective.mp hinj
  have hVle : V ≤ ⁅Cen z, Cen z⁆ := by
    intro u hu
    obtain ⟨v, hv⟩ := hsurj ⟨u, hu⟩
    have h1 : (u : G) = ⁅(g : G), (v : G)⁆ := by
      have h2 := congrArg Subtype.val hv
      simp only at h2
      rw [← h2, Subgroup.coe_div, hconj, commutatorElement_def, div_eq_mul_inv]
    rw [h1]
    exact Subgroup.commutator_mem_commutator g.2.2 (hVC v.2)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsElementaryAbelian 2 ↥V := hEA
  have hE : IsElementaryAbelian 2 ↥(V.subgroupOf ⁅Cen z, Cen z⁆) :=
    IsElementaryAbelian.subgroupOf hVle
  have hcardE : Nat.card ↥(V.subgroupOf ⁅Cen z, Cen z⁆) = 2 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVle).toEquiv, hcardV]
    norm_num
  exact CFSG.LieType.SteinbergBR.le_pRank_of_card one_lt_two _ hE hcardE

end D

end CFSG.GH74.GLS.Stage2.Local
