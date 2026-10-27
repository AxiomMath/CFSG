module

public import CFSG.LieType.SeitzGeneration.ExcRankVacuous
public import CFSG.LieType.SeitzGeneration.ExcParabolicE67
public import CFSG.LieType.SeitzGeneration.ExcF4Two
public import CFSG.LieType.SeitzGeneration.ExcTorusCat
public import CFSG.LieType.SeitzGeneration.ExcTorusRankF4

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley TauCeti

theorem SeitzExcAnisotropicForAt.mono_on {P : LieTypeIndex → Prop}
    {Q Q' : LieTypeIndex → ℕ → Prop}
    (h : ∀ d p, p.Prime → p ≠ 2 → P d → Q' d p → Q d p)
    (hP : SeitzExcAnisotropicForAt P Q) : SeitzExcAnisotropicForAt P Q' := by
  intro d p hp hp2 hpd hex E hE hc hs
  exact hP d p hp hp2 hpd hex E hE hc ⟨hs.1, hs.2.1, h d.1 p hp hp2 hs.2.1 hs.2.2.1, hs.2.2.2⟩

@[expose] def SeitzExcAnisotropicF4Class (e : ℕ) : Prop :=
  SeitzExcAnisotropicForAt IsF4Index
    (ClassRange LieTypeIndex.F4 (fun q => ¬ (q.p = 2 ∧ q.exponent = 1)) e)

@[expose] def SeitzExcAnisotropicE6Class (e : ℕ) : Prop :=
  SeitzExcAnisotropicForAt IsE6Index (ClassRange LieTypeIndex.E6 (fun _ => True) e)

@[expose] def SeitzExcAnisotropicE8Class (e : ℕ) : Prop :=
  SeitzExcAnisotropicForAt IsE8Index (ClassRange LieTypeIndex.E8 (fun _ => True) e)

@[expose] def SeitzExcAnisotropicE6Three : Prop :=
  SeitzExcAnisotropicForAt IsE6Index PrimeRange.three

@[expose] def SeitzExcAnisotropicE7Three : Prop :=
  SeitzExcAnisotropicForAt IsE7Index PrimeRange.three

@[expose] def SeitzExcAnisotropicE8Three : Prop :=
  SeitzExcAnisotropicForAt IsE8Index PrimeRange.three

section Proved


theorem seitzExcAnisotropicF4Big_of_classes (h3 : SeitzExcAnisotropicF4Class 3)
    (h4 : SeitzExcAnisotropicF4Class 4) (h6 : SeitzExcAnisotropicF4Class 6) :
    SeitzExcAnisotropicF4Big :=
  seitzExcAnisotropicForAt_geFive_of_classes (c := LieTypeIndex.F4)
    (X := fun q => ¬ (q.p = 2 ∧ q.exponent = 1)) (F := IsF4Index) (τ := Tag.F4)
    (S := fun e => e = 3 ∨ e = 4 ∨ e = 6) LieTypeIndex.characteristic_F4 conj_injective_cat_F4
    (fun q hv p hp hpq h => rankLE1_cat_F4 q hv hp hpq h)
    (fun q hv p hp hp3 hpq h => not_rankLE2_cat_F4 q hv hp hp3 hpq h)
    (fun _ h => degCount_F4_eq_two h)
    (fun e he => by
      rcases he with rfl | rfl | rfl
      exacts [h3, h4, h6])

theorem seitzExcAnisotropicE6_geFive_of_class6 (h6 : SeitzExcAnisotropicE6Class 6) :
    SeitzExcAnisotropicForAt IsE6Index PrimeRange.geFive :=
  SeitzExcAnisotropicForAt.mono_on
    (fun d p _ _ hd hp5 => by
      obtain ⟨q, rfl⟩ := hd
      exact ⟨hp5, q, rfl, trivial⟩)
    (seitzExcAnisotropicForAt_geFive_of_classes (c := LieTypeIndex.E6) (X := fun _ => True)
      (F := IsE6Index) (τ := Tag.E6) (S := fun e => e = 4 ∨ e = 6)
      LieTypeIndex.characteristic_E6 conj_injective_cat_E6
      (fun q hv p hp hpq h => rankLE1_cat_E6 q hv hp hpq h)
      (fun q hv p hp hp3 hpq h => not_rankLE2_cat_E6 q hv hp hp3 hpq h)
      (fun _ h => degCount_E6_eq_two h)
      (fun e he => by
        rcases he with rfl | rfl
        · exact SeitzExcAnisotropicForAt.mono_on
            (fun d p hp _ _ hQ => by
              obtain ⟨-, q, hdq, -, hord⟩ := hQ
              exact ⟨q, hdq, dvd_sq_add_one_of_orderOf_eq_four hp hord⟩)
            seitzExcAnisotropicForAt_E6_phi4
        · exact h6))

theorem seitzExcAnisotropicE7_geFive : SeitzExcAnisotropicForAt IsE7Index PrimeRange.geFive :=
  SeitzExcAnisotropicForAt.mono_on
    (fun d p _ _ hd hp5 => by
      obtain ⟨q, rfl⟩ := hd
      exact ⟨hp5, q, rfl, trivial⟩)
    (seitzExcAnisotropicForAt_geFive_of_classes (c := LieTypeIndex.E7) (X := fun _ => True)
      (F := IsE7Index) (τ := Tag.E7) (S := fun e => e = 4)
      LieTypeIndex.characteristic_E7 conj_injective_cat_E7
      (fun q hv p hp hpq h => rankLE1_cat_E7 q hv hp hpq h)
      (fun q hv p hp hp3 hpq h => not_rankLE2_cat_E7 q hv hp hp3 hpq h)
      (fun _ h => degCount_E7_eq_two h)
      (fun e he => by
        rcases he with rfl
        exact SeitzExcAnisotropicForAt.mono_on
          (fun d p hp _ _ hQ => by
            obtain ⟨-, q, hdq, -, hord⟩ := hQ
            exact ⟨q, hdq, dvd_sq_add_one_of_orderOf_eq_four hp hord⟩)
          seitzExcAnisotropicForAt_E7_phi4))

theorem seitzExcAnisotropicE8_geFive_of_classes (h5 : SeitzExcAnisotropicE8Class 5)
    (h8 : SeitzExcAnisotropicE8Class 8) (h10 : SeitzExcAnisotropicE8Class 10)
    (h12 : SeitzExcAnisotropicE8Class 12) :
    SeitzExcAnisotropicForAt IsE8Index PrimeRange.geFive :=
  SeitzExcAnisotropicForAt.mono_on
    (fun d p _ _ hd hp5 => by
      obtain ⟨q, rfl⟩ := hd
      exact ⟨hp5, q, rfl, trivial⟩)
    (seitzExcAnisotropicForAt_geFive_of_classes (c := LieTypeIndex.E8) (X := fun _ => True)
      (F := IsE8Index) (τ := Tag.E8) (S := fun e => e = 5 ∨ e = 8 ∨ e = 10 ∨ e = 12)
      LieTypeIndex.characteristic_E8 conj_injective_cat_E8
      (fun q hv p hp hpq h => rankLE1_cat_E8 q hv hp hpq h)
      (fun q hv p hp hp3 hpq h => not_rankLE2_cat_E8 q hv hp hp3 hpq h)
      (fun _ h => degCount_E8_eq_two h)
      (fun e he => by
        rcases he with rfl | rfl | rfl | rfl
        exacts [h5, h8, h10, h12]))

theorem seitzExcAnisotropicE6_of_classes (h6 : SeitzExcAnisotropicE6Class 6)
    (h3 : SeitzExcAnisotropicE6Three) : SeitzExcAnisotropicE6 :=
  SeitzExcAnisotropicFor.of_three_geFive h3 (seitzExcAnisotropicE6_geFive_of_class6 h6)

theorem seitzExcAnisotropicE7_of_three (h3 : SeitzExcAnisotropicE7Three) :
    SeitzExcAnisotropicE7 :=
  SeitzExcAnisotropicFor.of_three_geFive h3 seitzExcAnisotropicE7_geFive

theorem seitzExcAnisotropicE8_of_classes (h5 : SeitzExcAnisotropicE8Class 5)
    (h8 : SeitzExcAnisotropicE8Class 8) (h10 : SeitzExcAnisotropicE8Class 10)
    (h12 : SeitzExcAnisotropicE8Class 12) (h3 : SeitzExcAnisotropicE8Three) :
    SeitzExcAnisotropicE8 :=
  SeitzExcAnisotropicFor.of_three_geFive h3 (seitzExcAnisotropicE8_geFive_of_classes h5 h8 h10 h12)

end Proved

section F4


theorem seitzExcAnisotropicF4_of_classes (h3 : SeitzExcAnisotropicF4Class 3)
    (h4 : SeitzExcAnisotropicF4Class 4) (h6 : SeitzExcAnisotropicF4Class 6)
    (hthree : SeitzExcAnisotropicF4Three) : SeitzExcAnisotropicF4 :=
  seitzExcAnisotropicFor_F4_of_residuals (seitzExcAnisotropicF4Big_of_classes h3 h4 h6) hthree

end F4

theorem seitzExcAnisotropicF4Class_of_f4Big (h : SeitzExcAnisotropicF4Big) (e : ℕ) :
    SeitzExcAnisotropicF4Class e :=
  SeitzExcAnisotropicForAt.mono (fun d p hQ => by
    obtain ⟨hp5, q, hdq, hX, -⟩ := hQ
    exact ⟨hp5, q, hdq, hX⟩) h

theorem seitzExcAnisotropicE6Class_of_e6 (h : SeitzExcAnisotropicE6) (e : ℕ) :
    SeitzExcAnisotropicE6Class e :=
  SeitzExcAnisotropicFor.toAt h _

theorem seitzExcAnisotropicE8Class_of_e8 (h : SeitzExcAnisotropicE8) (e : ℕ) :
    SeitzExcAnisotropicE8Class e :=
  SeitzExcAnisotropicFor.toAt h _

theorem seitzExcAnisotropicE6Three_of_e6 (h : SeitzExcAnisotropicE6) :
    SeitzExcAnisotropicE6Three :=
  SeitzExcAnisotropicFor.toAt h _

theorem seitzExcAnisotropicE7Three_of_e7 (h : SeitzExcAnisotropicE7) :
    SeitzExcAnisotropicE7Three :=
  SeitzExcAnisotropicFor.toAt h _

theorem seitzExcAnisotropicE8Three_of_e8 (h : SeitzExcAnisotropicE8) :
    SeitzExcAnisotropicE8Three :=
  SeitzExcAnisotropicFor.toAt h _

end CFSG.LieType.SeitzGeneration
