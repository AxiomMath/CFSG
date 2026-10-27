module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.A5CentBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.BaseEmb

@[expose] public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

open scoped Classical

def cSideShape_a5CentCard (x : alternatingGroup (Fin 5)) : ℕ :=
  ((Finset.univ : Finset (alternatingGroup (Fin 5))).filter fun y => y * x = x * y).card

theorem cSideShape_a5CentCard_three :
    ∀ x : alternatingGroup (Fin 5), x ^ 3 = 1 → x ≠ 1 → cSideShape_a5CentCard x = 3 := by
  decide +kernel

theorem cSideShape_a5CentCard_five :
    ∀ x : alternatingGroup (Fin 5), x ^ 5 = 1 → x ≠ 1 → cSideShape_a5CentCard x = 5 := by
  decide +kernel

theorem cSideShape_natCard_A5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

theorem cSideShape_natCard_A5WrTwo : Nat.card A5WrTwo = 7200 := by
  haveI : Finite (Multiplicative (ZMod 2)) := inferInstance
  rw [RegularWreathProduct.card]
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [cSideShape_natCard_A5, h2]
  norm_num

theorem cSideShape_card_centralizer_one_a5 :
    Nat.card ↥(Subgroup.centralizer ({(1 : alternatingGroup (Fin 5))} : Set _)) = 60 := by
  have htop : Subgroup.centralizer ({(1 : alternatingGroup (Fin 5))} : Set _) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset, Set.singleton_subset_iff]
    exact Subgroup.mem_center_iff.mpr (fun g => by simp)
  rw [htop, Subgroup.card_top, cSideShape_natCard_A5]

theorem cSideShape_card_centralizer_a5 {p : ℕ} (hp : p = 3 ∨ p = 5)
    {x : alternatingGroup (Fin 5)} (hx : orderOf x = p) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) = p := by
  have hxpow : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    rcases hp with h3 | h5 <;> omega
  have hcard : cSideShape_a5CentCard x = p := by
    rcases hp with h3 | h5
    · rw [h3] at hxpow ⊢
      exact cSideShape_a5CentCard_three x hxpow hx1
    · rw [h5] at hxpow ⊢
      exact cSideShape_a5CentCard_five x hxpow hx1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfilter : (Finset.univ.filter fun y : alternatingGroup (Fin 5) =>
      y ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) =
      (Finset.univ.filter fun y : alternatingGroup (Fin 5) => y * x = x * y) := by
    apply Finset.filter_congr
    intro y _
    simp [Subgroup.mem_centralizer_singleton_iff]
  rw [hfilter]
  simpa [cSideShape_a5CentCard] using hcard

noncomputable def cSideShape_centralizerMulEquiv {p : ℕ} (hp : p = 3 ∨ p = 5)
    {x : alternatingGroup (Fin 5)}
    (hx : Nat.card ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) = p) :
    ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) ≃* Z p := by
  haveI : Fact p.Prime := ⟨hp.elim (fun h => h ▸ Nat.prime_three) (fun h => h ▸ Nat.prime_five)⟩
  have hZp : Nat.card (Z p) = p := by
    show Nat.card (Multiplicative (ZMod p)) = p
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  exact mulEquivOfPrimeCardEq hx hZp

noncomputable def cSideShape_conjCentralizerMulEquiv (b u : A5WrTwo) :
    ↥(Subgroup.centralizer ({u} : Set A5WrTwo)) ≃*
      ↥(Subgroup.centralizer ({b * u * b⁻¹} : Set A5WrTwo)) where
  toFun k := ⟨b * k * b⁻¹, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hk : (k : A5WrTwo) * u = u * k := Subgroup.mem_centralizer_singleton_iff.mp k.2
    calc (b * k * b⁻¹) * (b * u * b⁻¹) = b * (k * u) * b⁻¹ := by group
      _ = b * (u * k) * b⁻¹ := by rw [hk]
      _ = (b * u * b⁻¹) * (b * k * b⁻¹) := by group⟩
  invFun k := ⟨b⁻¹ * k * b, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hk : (k : A5WrTwo) * (b * u * b⁻¹) = (b * u * b⁻¹) * k :=
      Subgroup.mem_centralizer_singleton_iff.mp k.2
    calc (b⁻¹ * k * b) * u = b⁻¹ * (k * (b * u * b⁻¹)) * b := by group
      _ = b⁻¹ * ((b * u * b⁻¹) * k) * b := by rw [hk]
      _ = u * (b⁻¹ * k * b) := by group⟩
  left_inv k := Subtype.ext (by group)
  right_inv k := Subtype.ext (by group)
  map_mul' k l := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem cSideShape_coord_cases (q : Multiplicative (ZMod 2)) :
    q = 1 ∨ q = Multiplicative.ofAdd 1 := by
  rcases (show ∀ e : ZMod 2, e = 0 ∨ e = 1 by decide) (Multiplicative.toAdd q) with h | h
  · left
    rw [← ofAdd_toAdd q, h]
    rfl
  · right
    rw [← ofAdd_toAdd q, h]

theorem cSideShape_sigma_ne_one :
    (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) ≠ 1 := by decide

theorem cSideShape_sigma_mul_self :
    (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) *
      Multiplicative.ofAdd 1 = 1 := by decide

theorem cSideShape_sigma_inv :
    (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2))⁻¹ = Multiplicative.ofAdd 1 :=
  inv_eq_of_mul_eq_one_right cSideShape_sigma_mul_self

abbrev cSideShape_swap : A5WrTwo := ⟨1, Multiplicative.ofAdd 1⟩

theorem cSideShape_swap_mul_self : cSideShape_swap * cSideShape_swap = 1 := by
  apply RegularWreathProduct.ext
  · funext q
    simp [cSideShape_swap, RegularWreathProduct.mul_def, cSideShape_sigma_mul_self]
  · simp [cSideShape_swap, RegularWreathProduct.mul_def, cSideShape_sigma_mul_self]

noncomputable def cSideShape_t (r : Z 2) : A5WrTwo :=
  if r = 1 then 1 else cSideShape_swap

theorem cSideShape_t_mul (r r' : Z 2) :
    cSideShape_t (r * r') = cSideShape_t r * cSideShape_t r' := by
  rcases cSideShape_coord_cases r with rfl | rfl <;>
    rcases cSideShape_coord_cases r' with rfl | rfl <;>
    simp [cSideShape_t, cSideShape_swap, cSideShape_sigma_ne_one, cSideShape_sigma_mul_self,
      cSideShape_swap_mul_self]

theorem cSideShape_t_right (r : Z 2) : (cSideShape_t r).right = r := by
  rcases cSideShape_coord_cases r with rfl | rfl
  · simp [cSideShape_t]
  · rw [cSideShape_t, if_neg cSideShape_sigma_ne_one]

theorem cSideShape_t_mul_baseEmb (r : Z 2) (a b : alternatingGroup (Fin 5)) :
    cSideShape_t r * A5WrTwo.baseEmb (a, b) =
      A5WrTwo.baseEmb (if r = 1 then (a, b) else (b, a)) * cSideShape_t r := by
  rcases cSideShape_coord_cases r with rfl | rfl
  · simp [cSideShape_t]
  · rw [cSideShape_t, if_neg cSideShape_sigma_ne_one, if_neg cSideShape_sigma_ne_one]
    calc cSideShape_swap * A5WrTwo.baseEmb (a, b)
        = (cSideShape_swap * A5WrTwo.baseEmb (a, b) * cSideShape_swap⁻¹) * cSideShape_swap := by
          group
      _ = A5WrTwo.baseEmb (b, a) * cSideShape_swap := by
          rw [A5WrTwo.swap_mul_baseEmb_mul_inv]

theorem cSideShape_baseEmb_right (a b : alternatingGroup (Fin 5)) :
    (A5WrTwo.baseEmb (a, b)).right = 1 := by
  have hmem : A5WrTwo.baseEmb (a, b) ∈ A5WrTwo.baseEmb.range :=
    MonoidHom.mem_range.mpr ⟨(a, b), rfl⟩
  rw [A5WrTwo.range_baseEmb, A5WrTwo.commutator_eq_ker] at hmem
  exact hmem

theorem cSideShape_t_baseEmb_diag (x : alternatingGroup (Fin 5)) (r : Z 2) :
    cSideShape_t r * A5WrTwo.baseEmb (x, x) =
      A5WrTwo.baseEmb (x, x) * cSideShape_t r := by
  rw [cSideShape_t_mul_baseEmb]
  simp

theorem cSideShape_baseEmb_diag_comm (x c d : alternatingGroup (Fin 5))
    (hc : c ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5))))
    (hd : d ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) :
    A5WrTwo.baseEmb (c, d) * A5WrTwo.baseEmb (x, x) =
      A5WrTwo.baseEmb (x, x) * A5WrTwo.baseEmb (c, d) := by
  rw [← map_mul, ← map_mul]
  congr 1
  exact Prod.ext (Subgroup.mem_centralizer_singleton_iff.mp hc)
    (Subgroup.mem_centralizer_singleton_iff.mp hd)

end CFSG.EvenSporadicStandard.HNRecog.CSide
