module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPTwoThreeLift
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoInvolutionPerm
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPTwoThreePerm

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Subgroup

namespace JankoPTwoThree

open Janko JankoInvolution

theorem odd_card_Ebar : Odd (Nat.card Ebar) := by
  rw [card_Ebar]
  decide

theorem odd_card_Pbar : Odd (Nat.card Pbar) := by
  rw [card_Pbar]
  decide

theorem ℓbar_conj_sbar₂ : ℓbar * sbar₂ * ℓbar⁻¹ = ebar₂ * ebar₃⁻¹ :=
  Subtype.ext (show (ℓbar : Perm (Fin 9)) * sbar₂ * (ℓbar : Perm (Fin 9))⁻¹ =
    ebar₂ * (ebar₃ : Perm (Fin 9))⁻¹ by decide)

theorem closure_eq_Ebar : closure {sbar₁, sbar₂, ℓbar * sbar₂ * ℓbar⁻¹} = Ebar := by
  refine le_antisymm ?_ ?_
  · rw [closure_le]
    rintro x (rfl | rfl | rfl)
    · exact sbar₁_mem_Ebar
    · exact sbar₂_mem_Ebar
    · rw [SetLike.mem_coe, ℓbar_conj_sbar₂]
      exact mul_mem ebar₂_mem_Ebar (inv_mem ebar₃_mem_Ebar)
  · set C := closure ({sbar₁, sbar₂, ℓbar * sbar₂ * ℓbar⁻¹} : Set (alternatingGroup (Fin 9)))
    have h₁ : sbar₁ ∈ C := subset_closure (by simp)
    have h₂ : sbar₂ ∈ C := subset_closure (by simp)
    have h₃ : ℓbar * sbar₂ * ℓbar⁻¹ ∈ C := subset_closure (by simp)
    have he₂ : ebar₂ ∈ C := by
      rw [show ebar₂ = (sbar₂ * (ℓbar * sbar₂ * ℓbar⁻¹)) ^ 2 from Subtype.ext (by decide +kernel)]
      exact pow_mem (mul_mem h₂ h₃) 2
    have he₃ : ebar₃ ∈ C := by
      rw [show ebar₃ = ebar₂⁻¹ * sbar₂ from Subtype.ext (by decide +kernel)]
      exact mul_mem (inv_mem he₂) h₂
    rw [Ebar, closure_le]
    rintro x (rfl | rfl | rfl)
    exacts [h₁, he₂, he₃]

variable {J : Type*} [Group J] (hJ : IsTwoANine J) (e : J ⧸ center J ≃* alternatingGroup (Fin 9))
include hJ

private theorem proj_liftOdd_of_orderOf {g : alternatingGroup (Fin 9)} (hg : orderOf g = 3) :
    proj e (liftOdd e g) = g :=
  hJ.proj_liftOdd e (by rw [hg]; exact ⟨1, rfl⟩)

theorem liftOddSubgroup_Ebar_eq_closure :
    liftOddSubgroup e Ebar = closure {liftOdd e sbar₁, liftOdd e sbar₂,
      someLift e ℓbar * liftOdd e sbar₂ * (someLift e ℓbar)⁻¹} := by
  set C := closure ({liftOdd e sbar₁, liftOdd e sbar₂,
    someLift e ℓbar * liftOdd e sbar₂ * (someLift e ℓbar)⁻¹} : Set J)
  have ho₂ : Odd (orderOf sbar₂) := by rw [orderOf_sbar₂]; exact ⟨1, rfl⟩
  have hconj : someLift e ℓbar * liftOdd e sbar₂ * (someLift e ℓbar)⁻¹ =
      liftOdd e (ℓbar * sbar₂ * ℓbar⁻¹) := by
    rw [hJ.conj_liftOdd e ho₂, proj_someLift]
  have hCE : C ≤ liftOddSubgroup e Ebar := by
    rw [closure_le]
    rintro x (rfl | rfl | rfl)
    · exact hJ.liftOdd_mem_liftOddSubgroup e odd_card_Ebar sbar₁_mem_Ebar
    · exact hJ.liftOdd_mem_liftOddSubgroup e odd_card_Ebar sbar₂_mem_Ebar
    · rw [SetLike.mem_coe, hconj]
      refine hJ.liftOdd_mem_liftOddSubgroup e odd_card_Ebar ?_
      rw [ℓbar_conj_sbar₂]
      exact mul_mem ebar₂_mem_Ebar (inv_mem ebar₃_mem_Ebar)
  have hCo : Odd (Nat.card C) :=
    (hJ.odd_card_liftOddSubgroup e odd_card_Ebar).of_dvd_nat (card_dvd_of_le hCE)
  have hmap : C.map (proj e) = Ebar := by
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
      proj_liftOdd_of_orderOf hJ e orderOf_sbar₁, proj_liftOdd_of_orderOf hJ e orderOf_sbar₂,
      hconj, hJ.proj_liftOdd e (by rw [orderOf_conj_eq]; exact ho₂), closure_eq_Ebar]
  rw [hJ.eq_liftOddSubgroup e hCo, hmap]

theorem liftOddSubgroup_Ebar_inf_centralizer {t : J} (ht : proj e t = tbar) :
    liftOddSubgroup e Ebar ⊓ centralizer {t} = zpowers (liftOdd e sbar₂) := by
  rw [liftOddSubgroup_inf_centralizer hJ e odd_card_Ebar, ht, Ebar_inf_centralizer_tbar,
    hJ.zpowers_liftOdd e (by rw [orderOf_sbar₂]; exact ⟨1, rfl⟩)]

theorem centralizer_liftOddSubgroup_Ebar :
    centralizer (liftOddSubgroup e Ebar : Set J) = liftOddSubgroup e Ebar ⊔ zpowers (zbar J) := by
  rw [hJ.centralizer_liftOddSubgroup e odd_card_Ebar, centralizer_Ebar,
    comap_eq_liftOddSubgroup_sup hJ e odd_card_Ebar]

theorem centralizer_liftOdd_sbar₂ {t : J} (ht : proj e t = tbar) :
    centralizer ({liftOdd e sbar₂} : Set J) = liftOddSubgroup e Ebar ⊔ closure {t, zbar J} := by
  have ho₂ : Odd (orderOf sbar₂) := by rw [orderOf_sbar₂]; exact ⟨1, rfl⟩
  have hz : zbar J ∈ liftOddSubgroup e Ebar ⊔ closure {t, zbar J} :=
    (le_sup_right : closure {t, zbar J} ≤ _) (subset_closure (by simp))
  rw [hJ.centralizer_eq_comap_of_odd e (hJ.odd_orderOf_liftOdd e ho₂), hJ.proj_liftOdd e ho₂,
    centralizer_sbar₂_eq, ← comap_map_proj hJ e hz, Subgroup.map_sup,
    hJ.map_liftOddSubgroup e odd_card_Ebar, MonoidHom.map_closure, Set.image_pair, ht,
    hJ.proj_zbar e, Set.pair_comm, closure_insert_one, ← zpowers_eq_closure]

theorem centralizer_liftOdd_sbar₃ :
    centralizer ({liftOdd e sbar₃} : Set J) = liftOddSubgroup e Pbar ⊔ zpowers (zbar J) := by
  have ho₃ : Odd (orderOf sbar₃) := by rw [orderOf_sbar₃]; exact ⟨1, rfl⟩
  rw [hJ.centralizer_eq_comap_of_odd e (hJ.odd_orderOf_liftOdd e ho₃), hJ.proj_liftOdd e ho₃,
    centralizer_sbar₃_eq, comap_eq_liftOddSubgroup_sup hJ e odd_card_Pbar]

omit hJ in
theorem map_subtype_inf_centralizer {G : Type*} [Group G] (H : Subgroup G) (X : Subgroup H)
    (u : H) : X.map H.subtype ⊓ centralizer {(u : G)} = (X ⊓ centralizer {u}).map H.subtype := by
  rw [map_inf _ _ _ H.subtype_injective, ← centralizer_inf_eq_map_subtype, ← inf_assoc,
    inf_eq_left.mpr (inf_le_left.trans (map_subtype_le X))]

end JankoPTwoThree

namespace Janko

open JankoPTwoThree

variable {G : Type*} [Group G] {z : G} (hH : IsTwoANine (centralizer ({z} : Set G)))
  (e : centralizer ({z} : Set G) ⧸ center (centralizer ({z} : Set G)) ≃* alternatingGroup (Fin 9))
include hH

theorem card_E : Nat.card (E e) = 27 := by
  rw [E, card_map_of_injective (centralizer ({z} : Set G)).subtype_injective,
    hH.card_liftOddSubgroup e odd_card_Ebar, card_Ebar]

theorem E_comm : ∀ a ∈ E e, ∀ b ∈ E e, a * b = b * a := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have hodd := hH.odd_card_liftOddSubgroup e odd_card_Ebar
  have hab : a * b = b * a := hH.eq_of_proj_eq_of_odd e
    (hodd.of_dvd_nat ((liftOddSubgroup e Ebar).orderOf_dvd_natCard (mul_mem ha hb)))
    (hodd.of_dvd_nat ((liftOddSubgroup e Ebar).orderOf_dvd_natCard (mul_mem hb ha))) (by
      rw [map_mul, map_mul]
      exact mem_centralizer_iff.mp (Ebar_le_centralizer_Ebar
        ((hH.mem_liftOddSubgroup_iff e odd_card_Ebar).mp hb).1) _
        ((hH.mem_liftOddSubgroup_iff e odd_card_Ebar).mp ha).1)
  exact congrArg Subtype.val hab

theorem E_pow_three : ∀ a ∈ E e, a ^ 3 = 1 := by
  rintro _ ⟨a, ha, rfl⟩
  have hodd := hH.odd_card_liftOddSubgroup e odd_card_Ebar
  have h3 : a ^ 3 = 1 := hH.eq_of_proj_eq_of_odd e
    (hodd.of_dvd_nat ((liftOddSubgroup e Ebar).orderOf_dvd_natCard (pow_mem ha 3)))
    (by rw [orderOf_one]; exact odd_one) (by
      rw [map_pow, map_one,
        pow_three_of_mem_Ebar ((hH.mem_liftOddSubgroup_iff e odd_card_Ebar).mp ha).1])
  exact congrArg Subtype.val h3

theorem E_eq_closure : E e = closure {s₁ e, s₂ e, ℓ e * s₂ e * (ℓ e)⁻¹} := by
  rw [E, liftOddSubgroup_Ebar_eq_closure hH e, MonoidHom.map_closure, Set.image_insert_eq,
    Set.image_insert_eq, Set.image_singleton]
  rfl

theorem s₃_mem_E : s₃ e ∈ E e :=
  ⟨liftOdd e sbar₃, hH.liftOdd_mem_liftOddSubgroup e odd_card_Ebar sbar₃_mem_Ebar, rfl⟩

theorem E_inf_centralizer_t : E e ⊓ centralizer ({t e} : Set G) = zpowers (s₂ e) := by
  rw [E, t, map_subtype_inf_centralizer,
    liftOddSubgroup_Ebar_inf_centralizer hH e (proj_someLift e tbar), MonoidHom.map_zpowers]
  rfl

theorem centralizer_E (hz : orderOf z = 2) :
    centralizer (E e : Set G) ⊓ centralizer ({z} : Set G) = E e ⊔ zpowers z := by
  rw [E, centralizer_map_inf_eq_map_subtype, centralizer_liftOddSubgroup_Ebar hH e,
    Subgroup.map_sup, map_subtype_zpowers_zbar hz hH]

theorem centralizer_P₂ (hz : orderOf z = 2) :
    centralizer (zpowers (s₂ e) : Set G) ⊓ centralizer ({z} : Set G) = E e ⊔ closure {t e, z} := by
  rw [zpowers_eq_closure, centralizer_closure,
    show s₂ e = ((liftOdd e sbar₂ : centralizer ({z} : Set G)) : G) from rfl,
    centralizer_inf_eq_map_subtype, centralizer_liftOdd_sbar₂ hH e (proj_someLift e tbar),
    Subgroup.map_sup, MonoidHom.map_closure, Set.image_pair, coe_subtype, coe_zbar_eq hz hH]
  rfl

theorem card_P : Nat.card (P e) = 81 := by
  rw [P, card_map_of_injective (centralizer ({z} : Set G)).subtype_injective,
    hH.card_liftOddSubgroup e odd_card_Pbar, card_Pbar]

theorem centralizer_P₃ (hz : orderOf z = 2) :
    centralizer (zpowers (s₃ e) : Set G) ⊓ centralizer ({z} : Set G) = P e ⊔ zpowers z := by
  rw [zpowers_eq_closure, centralizer_closure,
    show s₃ e = ((liftOdd e sbar₃ : centralizer ({z} : Set G)) : G) from rfl,
    centralizer_inf_eq_map_subtype, centralizer_liftOdd_sbar₃ hH e, Subgroup.map_sup,
    map_subtype_zpowers_zbar hz hH]
  rfl

end Janko

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
