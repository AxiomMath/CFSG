module

public import CFSG.LargeExtraspecial.DW2AAlphaZ
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

namespace Alpha

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

section GroupLemmas

variable {X : Type*} [Group X]

theorem braid_of_orderOf_eq_three {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (h3 : orderOf (a * b) = 3) : a * b * a = b * a * b := by
  have h := pow_orderOf_eq_one (a * b)
  rw [h3, pow_succ, pow_two] at h
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have e : a * b * a = (b * a * b)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    calc a * b * a * (b * a * b) = a * b * (a * b) * (a * b) := by group
      _ = 1 := h
  rw [e, mul_inv_rev, mul_inv_rev, ha', hb', mul_assoc]

theorem commute_of_orderOf_dvd_two {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (h : orderOf (a * b) ∣ 2) : a * b = b * a := by
  have h2 := orderOf_dvd_iff_pow_eq_one.mp h
  rw [pow_two] at h2
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have e : a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left h2
  rw [e, mul_inv_rev, ha', hb']

theorem eq_of_braid_of_commute {s t₁ t₂ : X} (hs : s * s = 1) (h2 : t₂ * t₂ = 1)
    (B1 : s * t₁ * s = t₁ * s * t₁) (B2 : s * t₂ * s = t₂ * s * t₂)
    (hc : s * (t₁ * t₂) = (t₁ * t₂) * s) : t₁ = t₂ := by
  have e1 : s * t₁ = t₁ * t₂ * s * t₂ := by
    calc s * t₁ = s * (t₁ * (t₂ * t₂)) := by rw [h2, mul_one]
      _ = s * (t₁ * t₂) * t₂ := by group
      _ = t₁ * t₂ * s * t₂ := by rw [hc]
  have e2 : s * t₁ * s = t₁ * s * t₂ := by
    calc s * t₁ * s = t₁ * t₂ * s * t₂ * s := by rw [e1]
      _ = t₁ * (t₂ * s * t₂) * s := by group
      _ = t₁ * (s * t₂ * s) * s := by rw [B2]
      _ = t₁ * s * t₂ * (s * s) := by group
      _ = t₁ * s * t₂ := by rw [hs, mul_one]
  rw [B1] at e2
  exact mul_left_cancel e2

theorem eq_of_braid_of_braid {s t₁ t₂ : X} (hs : s * s = 1) (h2 : t₂ * t₂ = 1)
    (h12 : t₁ * t₂ = t₂ * t₁) (B1 : s * t₁ * s = t₁ * s * t₁) (B2 : s * t₂ * s = t₂ * s * t₂)
    (B3 : s * (t₁ * t₂) * s = (t₁ * t₂) * s * (t₁ * t₂)) : s = t₂ := by
  have eqA : (t₁ * s * t₁) * (t₂ * s * t₂) = t₁ * t₂ * s * t₁ * t₂ := by
    calc (t₁ * s * t₁) * (t₂ * s * t₂) = (s * t₁ * s) * (s * t₂ * s) := by rw [B1, B2]
      _ = s * t₁ * (s * s) * t₂ * s := by group
      _ = s * (t₁ * t₂) * s := by rw [hs, mul_one]; group
      _ = (t₁ * t₂) * s * (t₁ * t₂) := B3
      _ = t₁ * t₂ * s * t₁ * t₂ := by group
  have eqB : s * t₁ * t₂ * s * t₂ = t₂ * s * t₁ * t₂ := by
    have : t₁ * (s * t₁ * t₂ * s * t₂) = t₁ * (t₂ * s * t₁ * t₂) := by
      calc t₁ * (s * t₁ * t₂ * s * t₂) = (t₁ * s * t₁) * (t₂ * s * t₂) := by group
        _ = t₁ * t₂ * s * t₁ * t₂ := eqA
        _ = t₁ * (t₂ * s * t₁ * t₂) := by group
    exact mul_left_cancel this
  have eqC : s * t₁ * t₂ * s * t₂ = t₁ * t₂ * s * t₁ := by
    calc s * t₁ * t₂ * s * t₂ = (s * (t₁ * t₂) * s) * t₂ := by group
      _ = (t₁ * t₂) * s * (t₁ * t₂) * t₂ := by rw [B3]
      _ = t₁ * t₂ * s * t₁ * (t₂ * t₂) := by group
      _ = t₁ * t₂ * s * t₁ := by rw [h2, mul_one]
  have eqD : t₁ * t₂ * s * t₁ = t₂ * s * t₁ * t₂ := eqC.symm.trans eqB
  have eqE : t₁ * s * t₁ = s * t₁ * t₂ := by
    have h212 : t₂ * t₁ * t₂ = t₁ := by
      calc t₂ * t₁ * t₂ = t₁ * t₂ * t₂ := by rw [← h12]
        _ = t₁ := by rw [mul_assoc, h2, mul_one]
    calc t₁ * s * t₁ = (t₂ * t₁ * t₂) * s * t₁ := by rw [h212]
      _ = t₂ * (t₁ * t₂ * s * t₁) := by group
      _ = t₂ * (t₂ * s * t₁ * t₂) := by rw [eqD]
      _ = (t₂ * t₂) * s * t₁ * t₂ := by group
      _ = s * t₁ * t₂ := by rw [h2, one_mul]
  rw [← B1] at eqE
  exact mul_left_cancel eqE

theorem orderOf_eq_four_of_four_group {s t₁ t₂ : X} (hs : s * s = 1) (h1 : t₁ * t₁ = 1)
    (h2 : t₂ * t₂ = 1) (h21 : t₂ ≠ 1) (h12 : t₁ * t₂ = t₂ * t₁) (hne : t₁ ≠ t₂)
    (hst : s * t₁ ≠ t₁ * s) (ho1 : orderOf (s * t₁) ∈ ({1, 2, 3, 4} : Finset ℕ))
    (ho2 : orderOf (s * t₂) ∈ ({1, 2, 3, 4} : Finset ℕ))
    (ho3 : orderOf (s * (t₁ * t₂)) ∈ ({1, 2, 3, 4} : Finset ℕ)) :
    orderOf (s * t₁) = 4 ∨ orderOf (s * t₂) = 4 ∨ orderOf (s * (t₁ * t₂)) = 4 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ho1 ho2 ho3
  have hu : (t₁ * t₂) * (t₁ * t₂) = 1 := by
    calc (t₁ * t₂) * (t₁ * t₂) = t₁ * (t₂ * t₁) * t₂ := by group
      _ = t₁ * (t₁ * t₂) * t₂ := by rw [h12]
      _ = (t₁ * t₁) * (t₂ * t₂) := by group
      _ = 1 := by rw [h1, h2, one_mul]
  by_contra hcon
  push Not at hcon
  obtain ⟨n1, n2, n3⟩ := hcon
  have e1 : orderOf (s * t₁) = 3 := by
    rcases ho1 with e | e | e | e
    · exact absurd (commute_of_orderOf_dvd_two hs h1 (by rw [e]; norm_num)) hst
    · exact absurd (commute_of_orderOf_dvd_two hs h1 (by rw [e])) hst
    · exact e
    · exact absurd e n1
  have B1 := braid_of_orderOf_eq_three hs h1 e1
  have h6 : s * t₂ ≠ t₂ * s := by
    intro hc
    have hcomm : Commute (s * t₁) t₂ := by
      change s * t₁ * t₂ = t₂ * (s * t₁)
      calc s * t₁ * t₂ = s * (t₁ * t₂) := by group
        _ = s * (t₂ * t₁) := by rw [h12]
        _ = (s * t₂) * t₁ := by group
        _ = (t₂ * s) * t₁ := by rw [hc]
        _ = t₂ * (s * t₁) := by group
    have ht₂ : orderOf t₂ = 2 := orderOf_eq_prime (by rw [pow_two]; exact h2) h21
    have h := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [e1, ht₂]; norm_num)
    rw [e1, ht₂, mul_assoc] at h
    rcases ho3 with e | e | e | e <;> omega
  have e2 : orderOf (s * t₂) = 3 := by
    rcases ho2 with e | e | e | e
    · exact absurd (commute_of_orderOf_dvd_two hs h2 (by rw [e]; norm_num)) h6
    · exact absurd (commute_of_orderOf_dvd_two hs h2 (by rw [e])) h6
    · exact e
    · exact absurd e n2
  have B2 := braid_of_orderOf_eq_three hs h2 e2
  rcases ho3 with e | e | e | e
  · exact hne (eq_of_braid_of_commute hs h2 B1 B2
      (commute_of_orderOf_dvd_two hs hu (by rw [e]; norm_num)))
  · exact hne (eq_of_braid_of_commute hs h2 B1 B2 (commute_of_orderOf_dvd_two hs hu (by rw [e])))
  · have B3 := braid_of_orderOf_eq_three hs hu e
    have hst' := eq_of_braid_of_braid hs h2 h12 B1 B2 B3
    subst hst'
    exact hst h12.symm
  · exact absurd e n3

end GroupLemmas

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {W : Submodule (ZMod 2) S.Qt}

variable (S W) in
@[expose] def Tset : Set S.O := {t | t ∈ Xbar S W ∧ IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2}

variable (S W) in
@[expose] def ncR (x y : S.O) : Prop := x ∈ Tset S W ∧ y ∈ Tset S W ∧ x * y ≠ y * x

variable (S W) in
@[expose] def tcomp (t : S.O) : Set S.O := {e | Relation.ReflTransGen (ncR S W) t e}

theorem Tset_ne_one {t : S.O} (ht : t ∈ Tset S W) : t ≠ 1 :=
  fun h => ht.2.2.1 (by rw [h]; rfl)

theorem Tset_mul_self {t : S.O} (ht : t ∈ Tset S W) : t * t = 1 :=
  Subtype.ext ht.2.2.2.1

theorem mem_Tset_of_mem_tcomp {t e : S.O} (ht : t ∈ Tset S W) (he : e ∈ tcomp S W t) :
    e ∈ Tset S W := by
  induction he with
  | refl => exact ht
  | tail _ hr _ => exact hr.2.1

theorem tcomp_trans {t e f : S.O} (he : e ∈ tcomp S W t) (hf : f ∈ tcomp S W e) :
    f ∈ tcomp S W t :=
  Relation.ReflTransGen.trans he hf

theorem tcomp_symm {t e : S.O} (he : e ∈ tcomp S W t) : t ∈ tcomp S W e := by
  induction he with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hr ih =>
    exact Relation.ReflTransGen.head ⟨hr.2.1, hr.1, fun h => hr.2.2 h.symm⟩ ih

theorem mem_tcomp_of_not_commute {t e : S.O} (ht : t ∈ Tset S W) (he : e ∈ Tset S W)
    (hte : t * e ≠ e * t) : e ∈ tcomp S W t :=
  Relation.ReflTransGen.single ⟨ht, he, hte⟩

theorem commute_of_not_mem_tcomp {t e f : S.O} (he : e ∈ tcomp S W t) (ht : t ∈ Tset S W)
    (hf : f ∈ Tset S W) (hf' : f ∉ tcomp S W t) : e * f = f * e := by
  by_contra h
  exact hf' (Relation.ReflTransGen.tail he ⟨mem_Tset_of_mem_tcomp ht he, hf, h⟩)

theorem commute_closure_of_not_mem {t f : S.O} (ht : t ∈ Tset S W) (hf : f ∈ Tset S W)
    (hf' : f ∉ tcomp S W t) {g : S.O} (hg : g ∈ closure (tcomp S W t)) : g * f = f * g := by
  induction hg using closure_induction with
  | mem e he => exact commute_of_not_mem_tcomp he ht hf hf'
  | one => rw [one_mul, mul_one]
  | mul x y _ _ hx hy =>
    calc x * y * f = x * (y * f) := by group
      _ = x * (f * y) := by rw [hy]
      _ = (x * f) * y := by group
      _ = (f * x) * y := by rw [hx]
      _ = f * (x * y) := by group
  | inv x _ hx =>
    calc x⁻¹ * f = x⁻¹ * (f * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * f) * x⁻¹ := by rw [hx]
      _ = f * x⁻¹ := by group

variable (hA : Hyp S W)
include hA

theorem mem_Tset_of_mem_Abar {h : G} (hx : IsDx S W h) {t : S.O}
    (ht : t ∈ Abar S (S.clPre W) h) (ht1 : t ≠ 1) : t ∈ Tset S W :=
  ⟨Abar_le_Xbar hx ht, (Abar_isTypeA hA hx ht ht1).1⟩

theorem Xbar_le_closure_Tset : Xbar S W ≤ closure (Tset S W) := by
  rw [Xbar, closure_le]
  rintro t ⟨h, hx, ht⟩
  by_cases ht1 : t = 1
  · rw [ht1]
    exact one_mem _
  · exact subset_closure (mem_Tset_of_mem_Abar hA hx ht ht1)

omit hA in
theorem closure_Tset_le_Xbar : closure (Tset S W) ≤ Xbar S W := by
  rw [closure_le]
  exact fun t ht => ht.1

theorem exists_not_commute_gen [IsSimpleGroup G] (h2 : 2 ≤ S.width) {t : S.O}
    (ht : t ∈ Tset S W) : ∃ h : G, IsDx S W h ∧ ∃ s ∈ Abar S (S.clPre W) h, s ≠ 1 ∧
      t * s ≠ s * t := by
  by_contra hcon
  push Not at hcon
  have hc : ∀ x ∈ Xbar S W, x * t = t * x := by
    intro x hx
    induction hx using closure_induction with
    | mem s hs =>
      obtain ⟨h, hx, hs⟩ := hs
      by_cases hs1 : s = 1
      · rw [hs1, one_mul, mul_one]
      · exact (hcon h hx s hs hs1).symm
    | one => rw [one_mul, mul_one]
    | mul x y _ _ hx hy =>
      calc x * y * t = x * (y * t) := by group
        _ = x * (t * y) := by rw [hy]
        _ = (x * t) * y := by group
        _ = (t * x) * y := by rw [hx]
        _ = t * (x * y) := by group
    | inv x _ hx =>
      calc x⁻¹ * t = x⁻¹ * (t * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * t) * x⁻¹ := by rw [hx]
        _ = t * x⁻¹ := by group
  exact Tset_ne_one ht (eq_one_of_mem_center hA h2 ht.1 hc)

theorem mem_tcomp_aux [IsSimpleGroup G] (h2 : 2 ≤ S.width) {a b s : S.O} (ha : a ∈ Tset S W)
    (hb : b ∈ Tset S W) (hab : a * b ∈ Tset S W) (hs : s ∈ Tset S W) (hsa : a * s ≠ s * a)
    (hsab : s * (a * b) ≠ (a * b) * s) : b ∈ tcomp S W a := by
  by_contra hb'
  have hsC : s ∈ tcomp S W a := mem_tcomp_of_not_commute ha hs hsa
  have habC : a * b ∈ tcomp S W a := tcomp_trans hsC (mem_tcomp_of_not_commute hs hab hsab)
  have hbcl : b ∈ closure (tcomp S W a) := by
    have : b = a * (a * b) := by rw [← mul_assoc, Tset_mul_self ha, one_mul]
    rw [this]
    exact mul_mem (subset_closure Relation.ReflTransGen.refl) (subset_closure habC)
  have hc' : ∀ x ∈ closure (Tset S W), x * b = b * x := by
    intro x hx
    induction hx using closure_induction with
    | mem f hf =>
      by_cases hfa : f ∈ tcomp S W a
      · exact commute_of_not_mem_tcomp hfa ha hb hb'
      · exact (commute_closure_of_not_mem ha hf hfa hbcl).symm
    | one => rw [one_mul, mul_one]
    | mul x y _ _ hx hy =>
      calc x * y * b = x * (y * b) := by group
        _ = x * (b * y) := by rw [hy]
        _ = (x * b) * y := by group
        _ = (b * x) * y := by rw [hx]
        _ = b * (x * y) := by group
    | inv x _ hx =>
      calc x⁻¹ * b = x⁻¹ * (b * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * b) * x⁻¹ := by rw [hx]
        _ = b * x⁻¹ := by group
  exact Tset_ne_one hb (eq_one_of_mem_center hA h2 hb.1
    fun x hx => hc' x (Xbar_le_closure_Tset hA hx))

theorem mem_tcomp_of_four [IsSimpleGroup G] (h2 : 2 ≤ S.width) {a b : S.O} (ha : a ∈ Tset S W)
    (hb : b ∈ Tset S W) (hcomm : a * b = b * a) (hab : a * b ∈ Tset S W) :
    b ∈ tcomp S W a := by
  obtain ⟨h, hx, s, hs, hs1, hns⟩ := exists_not_commute_gen hA h2 hab
  have hsT := mem_Tset_of_mem_Abar hA hx hs hs1
  have hns' : s * (a * b) ≠ (a * b) * s := fun e => hns e.symm
  by_cases hsa : a * s = s * a
  ·
    have hsb : b * s ≠ s * b := by
      intro hsb
      apply hns'
      calc s * (a * b) = (s * a) * b := by group
        _ = (a * s) * b := by rw [hsa]
        _ = a * (s * b) := by group
        _ = a * (b * s) := by rw [hsb]
        _ = (a * b) * s := by group
    have hba : b * a ∈ Tset S W := by rw [← hcomm]; exact hab
    have hns'' : s * (b * a) ≠ (b * a) * s := by rw [← hcomm]; exact hns'
    exact tcomp_symm (mem_tcomp_aux hA h2 hb ha hba hsT hsb hns'')
  · exact mem_tcomp_aux hA h2 ha hb hab hsT hsa hns'

theorem mem_tcomp_of_mem_Abar [IsSimpleGroup G] (h2 : 2 ≤ S.width) {h : G} (hx : IsDx S W h)
    {s u : S.O} (hs : s ∈ Abar S (S.clPre W) h) (hs1 : s ≠ 1) (hu : u ∈ Abar S (S.clPre W) h)
    (hu1 : u ≠ 1) : u ∈ tcomp S W s := by
  by_cases hsu : s = u
  · rw [hsu]
    exact Relation.ReflTransGen.refl
  have hsT := mem_Tset_of_mem_Abar hA hx hs hs1
  have huT := mem_Tset_of_mem_Abar hA hx hu hu1
  have hsu1 : s * u ≠ 1 := by
    intro e
    apply hsu
    calc s = s * (u * u) := by rw [Tset_mul_self huT, mul_one]
      _ = (s * u) * u := by group
      _ = u := by rw [e, one_mul]
  exact mem_tcomp_of_four hA h2 hsT huT (Abar_comm hA hx hs hu)
    (mem_Tset_of_mem_Abar hA hx (mul_mem hs hu) hsu1)

omit hA in

theorem polar_eq_zero_of_mem_commSpace {t : S.Qt ≃ₗ[ZMod 2] S.Qt} (ht : IsTypeA S.q t 2)
    {a b : S.Qt} (ha : a ∈ commSpace t) (hb : b ∈ commSpace t) : polar S.q a b = 0 := by
  rw [polar, ht.2.2.2.2 _ (add_mem ha hb), ht.2.2.2.2 a ha, ht.2.2.2.2 b hb]
  simp

theorem exists_not_commute [IsSimpleGroup G] (h2 : 2 ≤ S.width) {h k : G} (hx : IsDx S W h)
    (hy : IsDx S W k) (hxy : polar S.q (S.cl (h * S.z * h⁻¹)) (S.cl (k * S.z * k⁻¹)) ≠ 0) :
    ∃ s ∈ Abar S (S.clPre W) h, s ≠ 1 ∧ ∃ u ∈ Abar S (S.clPre W) k, u ≠ 1 ∧ s * u ≠ u * s := by
  obtain ⟨s, hs, -, -, hs1, -, -⟩ := exists_two_mem_Abar hA h2 hx
  obtain ⟨u₁, hu₁, u₂, hu₂, h1, h2', h12⟩ := exists_two_mem_Abar hA h2 hy
  set x := S.cl (h * S.z * h⁻¹)
  set y := S.cl (k * S.z * k⁻¹)
  obtain ⟨hsA, hxs⟩ := Abar_isTypeA hA hx hs hs1
  obtain ⟨hA₁, hy₁⟩ := Abar_isTypeA hA hy hu₁ h1
  obtain ⟨hA₂, hy₂⟩ := Abar_isTypeA hA hy hu₂ h2'
  by_contra hcon
  push Not at hcon
  have hc₁ := hcon s hs hs1 u₁ hu₁ h1
  have hc₂ := hcon s hs hs1 u₂ hu₂ h2'
  have hmeet : ∀ u : S.O, IsTypeA S.q (u : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 →
      y ∈ commSpace (u : S.Qt ≃ₗ[ZMod 2] S.Qt) → s * u = u * s →
      ∃ v ∈ commSpace (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ commSpace (u : S.Qt ≃ₗ[ZMod 2] S.Qt), v ≠ 0 := by
    intro u huA hyu hsu
    have hc : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) * (u : S.Qt ≃ₗ[ZMod 2] S.Qt) =
        (u : S.Qt ≃ₗ[ZMod 2] S.Qt) * (s : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      have := congrArg (fun w : S.O => (w : S.Qt ≃ₗ[ZMod 2] S.Qt)) hsu
      simpa using this
    rcases (commute_iff_of_isTypeA S.q_nondegenerate hsA huA).mp hc with hne | hperp
    · exact (Submodule.ne_bot_iff _).mp hne
    · exact absurd (hperp x hxs y hyu) hxy
  obtain ⟨v₁, ⟨hv₁s, hv₁u⟩, hv₁0⟩ := hmeet u₁ hA₁ hy₁ hc₁
  obtain ⟨v₂, ⟨hv₂s, hv₂u⟩, hv₂0⟩ := hmeet u₂ hA₂ hy₂ hc₂
  set K := commSpace (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓ perp S (ZMod 2 ∙ y) with hK
  have hmemK : ∀ v ∈ commSpace (s : S.Qt ≃ₗ[ZMod 2] S.Qt), polar S.q y v = 0 → v ∈ K := by
    intro v hv hyv
    refine ⟨hv, mem_perp.mpr fun w hw => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [polar_smul_left, hyv, smul_zero]
  have hK1 : finrank (ZMod 2) K ≤ 1 := by
    have hlt : K < commSpace (s : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      refine lt_of_le_of_ne inf_le_left fun e => ?_
      have : x ∈ K := e ▸ hxs
      have h0 := mem_perp.mp this.2 y (Submodule.mem_span_singleton_self y)
      rw [polar_comm] at h0
      exact hxy h0
    have := Submodule.finrank_lt_finrank_of_lt hlt
    rw [hsA.2.2.2.1] at this
    omega
  have hv₁K := hmemK v₁ hv₁s (polar_eq_zero_of_mem_commSpace hA₁ hy₁ hv₁u)
  have hv₂K := hmemK v₂ hv₂s (polar_eq_zero_of_mem_commSpace hA₂ hy₂ hv₂u)
  have hv := eq_of_finrank_le_one hK1 hv₁K hv₂K hv₁0 hv₂0
  have hvy : v₁ ∉ ZMod 2 ∙ y := by
    intro hvy
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hvy
    rcases zmod2_cases c with rfl | rfl
    · rw [zero_smul] at hc
      exact hv₁0 hc.symm
    · rw [one_smul] at hc
      have h0 := polar_eq_zero_of_mem_commSpace hsA hxs hv₁s
      rw [← hc] at h0
      exact hxy h0
  have hy0 : y ≠ 0 := hy.cl_ne_zero
  have hspan : ∀ u : S.O, IsTypeA S.q (u : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 →
      y ∈ commSpace (u : S.Qt ≃ₗ[ZMod 2] S.Qt) → v₁ ∈ commSpace (u : S.Qt ≃ₗ[ZMod 2] S.Qt) →
      commSpace (u : S.Qt ≃ₗ[ZMod 2] S.Qt) = Submodule.span (ZMod 2) {y, v₁} := by
    intro u huA hyu hvu
    refine (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm
    · rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact hyu
      · exact hvu
    · rw [huA.2.2.2.1, finrank_span_pair_of_not_mem hy0 hvy]
  have e₁ := hspan u₁ hA₁ hy₁ hv₁u
  have e₂ := hspan u₂ hA₂ hy₂ (hv ▸ hv₂u)
  exact h12 (Subtype.ext (OrthoF2.eq_of_commSpace_eq S.q_nondegenerate hA₁ hA₂ (e₁.trans e₂.symm)))

theorem mem_tcomp_of_adj [IsSimpleGroup G] (h2 : 2 ≤ S.width) {h k : G} (hx : IsDx S W h)
    (hy : IsDx S W k) (hxy : polar S.q (S.cl (h * S.z * h⁻¹)) (S.cl (k * S.z * k⁻¹)) ≠ 0)
    {s u : S.O} (hs : s ∈ Abar S (S.clPre W) h) (hs1 : s ≠ 1) (hu : u ∈ Abar S (S.clPre W) k)
    (hu1 : u ≠ 1) : u ∈ tcomp S W s := by
  obtain ⟨s', hs', hs'1, u', hu', hu'1, hsu⟩ := exists_not_commute hA h2 hx hy hxy
  have h1 := mem_tcomp_of_mem_Abar hA h2 hx hs hs1 hs' hs'1
  have h2' := mem_tcomp_of_not_commute (mem_Tset_of_mem_Abar hA hx hs' hs'1)
    (mem_Tset_of_mem_Abar hA hy hu' hu'1) hsu
  have h3 := mem_tcomp_of_mem_Abar hA h2 hy hu' hu'1 hu hu1
  exact tcomp_trans h1 (tcomp_trans h2' h3)

theorem mem_tcomp_of_cl_eq [IsSimpleGroup G] (h2 : 2 ≤ S.width) {h h' : G} (hx : IsDx S W h)
    (hx' : IsDx S W h') (hcl : S.cl (h * S.z * h⁻¹) = S.cl (h' * S.z * h'⁻¹)) {s u : S.O}
    (hs : s ∈ Abar S (S.clPre W) h) (hs1 : s ≠ 1) (hu : u ∈ Abar S (S.clPre W) h')
    (hu1 : u ≠ 1) : u ∈ tcomp S W s := by
  obtain ⟨b, ⟨k, hk, rfl⟩, hbx⟩ := exists_adj hA hx
  obtain ⟨w, hw, -, -, hw1, -, -⟩ := exists_two_mem_Abar hA h2 hk
  have h1 := mem_tcomp_of_adj hA h2 hx hk (by rw [hbx]; exact one_ne_zero) hs hs1 hw hw1
  have h3 := mem_tcomp_of_adj hA h2 hx' hk (by rw [← hcl, hbx]; exact one_ne_zero) hu hu1 hw hw1
  exact tcomp_trans h1 (tcomp_symm h3)

theorem gen_mem_tcomp [IsSimpleGroup G] (hn : 2 ≤ S.width) {h₀ : G} (hx₀ : IsDx S W h₀)
    {t₀ : S.O} (ht₀ : t₀ ∈ Abar S (S.clPre W) h₀) (ht₀1 : t₀ ≠ 1) {h : G} (hx : IsDx S W h)
    {u : S.O} (hu : u ∈ Abar S (S.clPre W) h) (hu1 : u ≠ 1) : u ∈ tcomp S W t₀ := by
  have h2 : 2 ≤ S.width := by omega
  have hD₀ : S.cl (h₀ * S.z * h₀⁻¹) ∈ Dset S W := ⟨h₀, hx₀, rfl⟩
  have hpath := mem_gcomp hA hn hD₀ ⟨h, hx, rfl⟩
  suffices key : ∀ v ∈ gcomp S W (S.cl (h₀ * S.z * h₀⁻¹)), ∀ h : G, IsDx S W h →
      S.cl (h * S.z * h⁻¹) = v → ∀ u ∈ Abar S (S.clPre W) h, u ≠ 1 → u ∈ tcomp S W t₀ from
    key _ hpath h hx rfl u hu hu1
  intro v hv
  induction hv with
  | refl =>
    intro h hx hcl u hu hu1
    exact mem_tcomp_of_cl_eq hA h2 hx₀ hx hcl.symm ht₀ ht₀1 hu hu1
  | @tail b c hb hbc ih =>
    intro h hx hcl u hu hu1
    obtain ⟨k, hk, rfl⟩ := mem_Dset_of_mem_gcomp hD₀ hb
    obtain ⟨w, hw, -, -, hw1, -, -⟩ := exists_two_mem_Abar hA h2 hk
    have h1 := ih k hk rfl w hw hw1
    have h3 := mem_tcomp_of_adj hA h2 hk hx (by rw [hcl]; exact hbc.2) hw hw1 hu hu1
    exact tcomp_trans h1 h3

theorem mem_tcomp [IsSimpleGroup G] (hn : 2 ≤ S.width) {h₀ : G} (hx₀ : IsDx S W h₀)
    {t₀ : S.O} (ht₀ : t₀ ∈ Abar S (S.clPre W) h₀) (ht₀1 : t₀ ≠ 1) {t : S.O}
    (ht : t ∈ Tset S W) : t ∈ tcomp S W t₀ := by
  obtain ⟨h, hx, s, hs, hs1, hts⟩ := exists_not_commute_gen hA (by omega) ht
  have h1 := gen_mem_tcomp hA hn hx₀ ht₀ ht₀1 hx hs hs1
  exact tcomp_trans h1 (tcomp_symm (mem_tcomp_of_not_commute ht
    (mem_Tset_of_mem_Abar hA hx hs hs1) hts))

end Alpha

end CFSG.LargeExtraspecial.DW
