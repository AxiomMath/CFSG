module

public import CFSG.LargeExtraspecial.S12TriH
public import CFSG.LargeExtraspecial.S12TriG2
public import CFSG.LargeExtraspecial.S12TriInput

public section

namespace CFSG.LargeExtraspecial.S12Tri

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Subgroup CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification

theorem six_words_injective {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab1 : a * b ≠ 1) (hab3 : (a * b) ^ 3 = 1) :
    Function.Injective ![1, a, b, a * b, b * a, a * b * a] := by
  have hsq : (a * b) ^ 2 ≠ 1 := fun h => hab1 (by
    calc a * b = (a * b) ^ 3 * ((a * b) ^ 2)⁻¹ := by group
      _ = 1 := by rw [hab3, h, inv_one, one_mul])
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h1 : (1 : G) ≠ b * a := fun h => hab1 (by
    have : b = a⁻¹ := eq_inv_of_mul_eq_one_left h.symm
    rw [this, hai, ha])
  have h2 : (1 : G) ≠ a * b * a := fun h => hb1 (by
    have : a * b = a⁻¹ := eq_inv_of_mul_eq_one_left h.symm
    rw [hai] at this
    simpa using this)
  have h3 : a ≠ b := fun h => hab1 (by rw [h, hb])
  have h4 : a ≠ a * b := fun h => hb1 (by simpa using h.symm)
  have h5 : a ≠ b * a := fun h => hb1 (by simpa using h.symm)
  have h6 : a ≠ a * b * a := fun h => h1 (by
    have : b * a = 1 := by simpa [mul_assoc] using h.symm
    exact this.symm)
  have h7 : b ≠ a * b := fun h => ha1 (by simpa using h.symm)
  have h8 : b ≠ b * a := fun h => ha1 (by simpa using h.symm)
  have h9 : b ≠ a * b * a := fun h => hsq (by
    calc (a * b) ^ 2 = a * b * a * b := by rw [sq]; simp only [mul_assoc]
      _ = 1 := by rw [← h, hb])
  have h10 : a * b ≠ b * a := fun h => hsq (by
    calc (a * b) ^ 2 = a * b * (a * b) := sq _
      _ = a * b * (b * a) := by rw [h]
      _ = 1 := by
        rw [show a * b * (b * a) = a * (b * b) * a by simp only [mul_assoc], hb, mul_one, ha])
  have h11 : a * b ≠ a * b * a := fun h => ha1 (by simpa using h.symm)
  have h12 : b * a ≠ a * b * a := fun h => h7 (by simpa [mul_assoc] using h)
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hij ⊢ <;>
    first
      | rfl
      | exact absurd hij ‹_›
      | exact absurd hij.symm ‹_›

theorem six_mul_card_le {X : Type*} [Group X] [Finite X] {Q Y : Subgroup X} [Q.Normal]
    (hQY : Q ≤ Y) {d e : X} (hdY : d ∈ Y) (heY : e ∈ Y) (hd2 : d * d = 1) (he2 : e * e = 1)
    (hdQ : d ∉ Q) (heQ : e ∉ Q) (hdeQ : d * e ∉ Q) (hde3 : (d * e) ^ 3 = 1) :
    6 * Nat.card Q ≤ Nat.card Y := by
  let w : Fin 6 → X := ![1, d, e, d * e, e * d, d * e * d]
  have hwY : ∀ i, w i ∈ Y := by
    intro i
    fin_cases i
    · exact one_mem _
    · exact hdY
    · exact heY
    · exact mul_mem hdY heY
    · exact mul_mem heY hdY
    · exact mul_mem (mul_mem hdY heY) hdY
  set a : X ⧸ Q := QuotientGroup.mk d
  set b : X ⧸ Q := QuotientGroup.mk e
  have hmk : ∀ i, (QuotientGroup.mk (w i) : X ⧸ Q) = ![1, a, b, a * b, b * a, a * b * a] i := by
    intro i
    fin_cases i <;> rfl
  have hinj : Function.Injective fun i => (QuotientGroup.mk (w i) : X ⧸ Q) := by
    have h := six_words_injective (a := a) (b := b)
      (by rw [← QuotientGroup.mk_mul, hd2, QuotientGroup.mk_one])
      (by rw [← QuotientGroup.mk_mul, he2, QuotientGroup.mk_one])
      (by rwa [Ne, QuotientGroup.eq_one_iff])
      (by rwa [Ne, QuotientGroup.eq_one_iff])
      (by rwa [Ne, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff])
      (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, hde3, QuotientGroup.mk_one])
    intro i j hij
    apply h
    simp only at hij
    rw [← hmk, ← hmk, hij]
  let f : Fin 6 × Q → Y := fun p => ⟨w p.1 * p.2, mul_mem (hwY p.1) (hQY p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨i, q⟩ ⟨j, q'⟩ h
    have h' : w i * q = w j * q' := congrArg Subtype.val h
    have hij : i = j := hinj (by
      show (QuotientGroup.mk (w i) : X ⧸ Q) = QuotientGroup.mk (w j)
      rw [QuotientGroup.eq]
      have : (w i)⁻¹ * w j = q * (q' : X)⁻¹ := by
        calc (w i)⁻¹ * w j = (w i)⁻¹ * (w j * q') * (q' : X)⁻¹ := by group
          _ = (w i)⁻¹ * (w i * q) * (q' : X)⁻¹ := by rw [h']
          _ = q * (q' : X)⁻¹ := by group
      rw [this]
      exact mul_mem q.2 (inv_mem q'.2))
    subst hij
    have : (q : X) = q' := mul_left_cancel h'
    rw [Subtype.ext this]
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_fin] at this

theorem fischerTrialityInput :
    FischerTrialityInput := by
  intro X _ E hP hZ h2 h3 hcos d hd
  have := Pair.finite hP
  have hdQ := not_mem_fischerQ hP hcos hd
  have hQn := fischerQ_normal hP
  have hmap := map_commutator_inf_centralizer_X₁ hP hZ h2 h3 (d := d)
  have hC : ∀ y : X, (∀ q ∈ fischerQ E, y * q = q * y) → y = 1 := fun y hy =>
    eq_one_of_commute_fischerQ hP hZ h2 h3 hy
  obtain ⟨e, he, hdeQ⟩ := exists_mul_not_mem_fischerQ hP hcos hd
  have heQ := not_mem_fischerQ hP hcos he
  have hde : d * e ≠ e * d := fun h => hdeQ (by
    have hne : d ≠ e := fun h' => hdeQ (by rw [h', Pair.mul_self hP he]; exact one_mem _)
    exact mul_mem_fischerQ hd he hne h)
  have hde3 : (d * e) ^ 3 = 1 := by
    rw [← Pair.orderOf_mul_eq_three hP hd he hde, pow_orderOf_eq_one]
  set Y := fischerQ E ⊔ closure ({d, e} : Set X)
  have hQY : fischerQ E ≤ Y := le_sup_left
  have hdY : d ∈ Y := (le_sup_right : closure ({d, e} : Set X) ≤ Y) (subset_closure (by simp))
  have heY : e ∈ Y := (le_sup_right : closure ({d, e} : Set X) ≤ Y) (subset_closure (by simp))
  have hsix : 6 * Nat.card ((fischerQ E).subgroupOf Y) ≤ Nat.card Y := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hQY).toEquiv]
    exact six_mul_card_le hQY hdY heY (Pair.mul_self hP hd) (Pair.mul_self hP he) hdQ heQ hdeQ
      hde3
  have hCY : ∀ y : Y, (∀ q ∈ (fischerQ E).subgroupOf Y, y * q = q * y) → y = 1 := by
    intro y hy
    refine Subtype.ext (hC y fun q hq => ?_)
    exact congrArg Subtype.val (hy ⟨q, hQY hq⟩ (mem_subgroupOf.2 hq))
  have : ((fischerQ E).subgroupOf Y).Normal := hQn.subgroupOf Y
  rcases triResult_X₁ hP hd hZ h2 h3 hdQ with hG | h60 | hA
  · refine ⟨fun hsol => hG.1 ?_, hmap ▸ hG.2.map_subtype⟩
    let e' := ((commutator (fischerQ E ⊔ zpowers d : Subgroup X) ⊓
        centralizer {dOne E d}).equivMapOfInjective (fischerQ E ⊔ zpowers d).subtype
        (fischerQ E ⊔ zpowers d).subtype_injective).trans (MulEquiv.subgroupCongr hmap)
    exact Group.isSolvable_of_isSolvable_injective (f := e'.toMonoidHom) e'.injective
  · exfalso
    have h60' : Nat.card ((fischerQ E).subgroupOf Y) = 60 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hQY).toEquiv,
        ← Nat.card_congr (commutatorX₁Equiv hP hZ h2 h3 (d := d)).toEquiv]
      exact h60
    have hs : IsSimpleGroup ((fischerQ E).subgroupOf Y) := by
      have := isSimpleGroup_fischerQ hP hZ h2 h3
      exact (subgroupOfEquivOfLe hQY).isSimpleGroup
    exact false_of_card_sixty hs h60' hCY hsix
  · exfalso
    obtain ⟨eA⟩ := hA
    exact false_of_alternating_six (((subgroupOfEquivOfLe hQY).trans
      (commutatorX₁Equiv hP hZ h2 h3 (d := d)).symm).trans eA) hCY hsix

end CFSG.LargeExtraspecial.S12Tri
