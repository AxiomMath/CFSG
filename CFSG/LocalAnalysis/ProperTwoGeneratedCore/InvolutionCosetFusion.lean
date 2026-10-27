module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherEscapingRankTwo

public section

namespace CFSG.ProperTwoGeneratedCore.InvolutionCosetFusion

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {G : Type} [Group G]

theorem orderOf_eq_of_isConj {x y : G} (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨c, hc⟩ := h
  exact hc.orderOf_eq

theorem isConj_inv_conj (x g : G) : IsConj x (g⁻¹ * x * g) :=
  isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩

theorem commuting_class_product_isConj [Finite G] {u z : G} (hu : orderOf u = 2)
    (T U : Subgroup G) (hTC : T ≤ Subgroup.centralizer ({u} : Set G)) (hT : IsPGroup 2 T)
    (hTmax : ∀ Q : Subgroup G, Q ≤ Subgroup.centralizer ({u} : Set G) → IsPGroup 2 Q →
      Nat.card Q ≤ Nat.card T)
    (hclass : ∀ x ∈ T, IsConj u x → ∃ w ∈ U, x = u * w)
    (hUz : ∀ w ∈ U, w ≠ 1 → IsConj z w)
    {a b : G} (ha : IsConj u a) (hb : IsConj u b) (hab : a ≠ b) (hcomm : Commute a b) :
    IsConj z (a * b) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, rfl⟩ := isConj_iff.mp ha
  set b' := g⁻¹ * b * g with hb'
  have hb'u : b' ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hcomm.eq
    calc b' * u = g⁻¹ * (b * (g * u * g⁻¹)) * g := by rw [hb']; group
      _ = g⁻¹ * ((g * u * g⁻¹) * b) * g := by rw [← h]
      _ = u * b' := by rw [hb']; group
  have hb'conj : IsConj u b' := hb.trans (isConj_inv_conj b g)
  have hb'order : orderOf b' = 2 := (orderOf_eq_of_isConj hb'conj).symm.trans hu
  obtain ⟨c, hcC, hcT⟩ := exists_conj_mem_of_card_le hTC hT hTmax
    (Subgroup.zpowers_le.mpr hb'u) (isPGroup_zpowers_of_orderOf_eq_two hb'order)
  have hcb' : c⁻¹ * b' * c ∈ T := hcT b' (Subgroup.mem_zpowers b')
  obtain ⟨w, hwU, hw⟩ := hclass _ hcb' (hb'conj.trans (isConj_inv_conj b' c))
  have hcu : c⁻¹ * u * c = u := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp hcC
    calc c⁻¹ * u * c = c⁻¹ * (c * u) := by rw [mul_assoc, h]
      _ = u := by group
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hab
    have h1 : c⁻¹ * b' * c = c⁻¹ * u * c := by rw [hw, mul_one, hcu]
    have h2 : b' = u := by simpa using h1
    rw [hb'] at h2
    calc g * u * g⁻¹ = g * (g⁻¹ * b * g) * g⁻¹ := by rw [h2]
      _ = b := by group
  have huu : u * u = 1 := by simpa only [hu, pow_two] using pow_orderOf_eq_one u
  have hprod : (g * c)⁻¹ * (g * u * g⁻¹ * b) * (g * c) = w := by
    have : (g * c)⁻¹ * (g * u * g⁻¹ * b) * (g * c) = (c⁻¹ * u * c) * (c⁻¹ * b' * c) := by
      rw [hb']; group
    rw [this, hcu, hw, ← mul_assoc, huu, one_mul]
  have hzw := hUz w hwU hw1
  have hconj : IsConj (g * u * g⁻¹ * b) w := hprod ▸ isConj_inv_conj (g * u * g⁻¹ * b) (g * c)
  exact hzw.trans hconj.symm

theorem exists_pair_ne_one_of_isKleinFour {A : Subgroup G} (hA : IsKleinFour A) :
    ∃ a ∈ A, ∃ b ∈ A, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  have hcard : Nat.card A = 4 := hA.card_four
  have : Finite A := Nat.finite_of_card_ne_zero (by omega)
  let : Fintype A := Fintype.ofFinite A
  have hnt : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hx⟩ := exists_ne (1 : A)
  have hlt : ({1, x} : Finset A).card < (Finset.univ : Finset A).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
    exact (Finset.card_le_two).trans_lt (by norm_num)
  obtain ⟨y, -, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  refine ⟨x, x.property, y, y.property, fun h => hx (Subtype.ext h), fun h => hy.1 (Subtype.ext h),
    fun h => hy.2 (Subtype.ext h).symm⟩

theorem fourGroup_meets_class [Finite G] {u z : G} (hu : orderOf u = 2)
    (T U : Subgroup G) (hTC : T ≤ Subgroup.centralizer ({u} : Set G)) (hT : IsPGroup 2 T)
    (hTmax : ∀ Q : Subgroup G, Q ≤ Subgroup.centralizer ({u} : Set G) → IsPGroup 2 Q →
      Nat.card Q ≤ Nat.card T)
    (hclass : ∀ x ∈ T, IsConj u x → ∃ w ∈ U, x = u * w)
    (hUz : ∀ w ∈ U, w ≠ 1 → IsConj z w)
    (hinv : ∀ x : G, orderOf x = 2 → IsConj u x ∨ IsConj z x)
    (A : Subgroup G) (hA : IsKleinFour A) : ∃ x ∈ A, IsConj z x := by
  obtain ⟨a, haA, b, hbA, ha1, hb1, hab⟩ := exists_pair_ne_one_of_isKleinFour hA
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx =>
    congrArg Subtype.val (hA.mul_self ⟨x, hx⟩)
  have horder : ∀ x ∈ A, x ≠ 1 → orderOf x = 2 := fun x hx hx1 =>
    orderOf_eq_prime (by rw [pow_two]; exact hsq x hx) hx1
  have hcomm : Commute a b := by
    have := hA.isMulCommutative
    exact congrArg Subtype.val (mul_comm' (⟨a, haA⟩ : A) ⟨b, hbA⟩)
  rcases hinv a (horder a haA ha1) with hau | haz
  · rcases hinv b (horder b hbA hb1) with hbu | hbz
    · exact ⟨a * b, A.mul_mem haA hbA,
        commuting_class_product_isConj hu T U hTC hT hTmax hclass hUz hau hbu hab hcomm⟩
    · exact ⟨b, hbA, hbz⟩
  · exact ⟨a, haA, haz⟩

theorem no_fourGroup_of_disjoint_class [Finite G] {u z : G} (hu : orderOf u = 2)
    (T U : Subgroup G) (hTC : T ≤ Subgroup.centralizer ({u} : Set G)) (hT : IsPGroup 2 T)
    (hTmax : ∀ Q : Subgroup G, Q ≤ Subgroup.centralizer ({u} : Set G) → IsPGroup 2 Q →
      Nat.card Q ≤ Nat.card T)
    (hclass : ∀ x ∈ T, IsConj u x → ∃ w ∈ U, x = u * w)
    (hUz : ∀ w ∈ U, w ≠ 1 → IsConj z w)
    (hinv : ∀ x : G, orderOf x = 2 → IsConj u x ∨ IsConj z x)
    (Y : Subgroup G) (hY : ∀ y ∈ Y, ¬ IsConj z y) (A : Subgroup G) (hAY : A ≤ Y) :
    ¬ IsKleinFour A := by
  intro hA
  obtain ⟨x, hxA, hx⟩ := fourGroup_meets_class hu T U hTC hT hTmax hclass hUz hinv A hA
  exact hY x (hAY hxA) hx

theorem exists_distinct_cosets_of_three_le_relIndex {U V : Subgroup G}
    (hindex : 3 ≤ U.relIndex V) : ∃ x ∈ V, ∃ y ∈ V, x ∉ U ∧ y ∉ U ∧ x⁻¹ * y ∉ U := by
  by_contra hcon
  push Not at hcon
  have hle : U.relIndex V ≤ 2 := by
    rw [Subgroup.relIndex, Subgroup.index]
    by_cases hex : ∃ x ∈ V, x ∉ U
    · obtain ⟨x₀, hx₀V, hx₀U⟩ := hex
      let f : Bool → V ⧸ U.subgroupOf V := fun b =>
        if b then QuotientGroup.mk ⟨x₀, hx₀V⟩ else QuotientGroup.mk 1
      have hf : Function.Surjective f := by
        intro q
        induction q using QuotientGroup.induction_on with
        | H y =>
          by_cases hyU : (y : G) ∈ U
          · refine ⟨false, ?_⟩
            simp only [f, Bool.false_eq_true, ↓reduceIte]
            rw [QuotientGroup.eq]
            simpa [Subgroup.mem_subgroupOf] using hyU
          · refine ⟨true, ?_⟩
            simp only [f, ↓reduceIte]
            rw [QuotientGroup.eq]
            simpa [Subgroup.mem_subgroupOf] using hcon x₀ hx₀V y y.property hx₀U hyU
      calc Nat.card (V ⧸ U.subgroupOf V) ≤ Nat.card Bool := Nat.card_le_card_of_surjective f hf
        _ = 2 := by simp
    · push Not at hex
      have hsub : U.subgroupOf V = ⊤ := by
        rw [eq_top_iff]
        intro y _
        exact Subgroup.mem_subgroupOf.mpr (hex y y.property)
      rw [hsub]
      simp
  omega

theorem transitive_quotient_cosets_exclude_class [Finite G] {u z : G}
    (hu : orderOf u = 2) (hnconj : ¬ IsConj u z)
    (V U : Subgroup G) (hUsq : ∀ x ∈ U, x * x = 1) (hindex : 4 ≤ U.relIndex V)
    (hUz : ∀ w ∈ U, w ≠ 1 → IsConj z w)
    (A : Subgroup G) (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (htrans : ∀ x ∈ V, x ∉ U → ∀ y ∈ V, y ∉ U → ∃ a ∈ A, y⁻¹ * (a * x * a⁻¹) ∈ U)
    (hsat : ∀ x ∈ V, IsConj u x → ∀ w ∈ U, IsConj u (x * w))
    (hprod : ∀ x y : G, IsConj u x → IsConj u y → x ≠ y → Commute x y → IsConj z (x * y)) :
    ∀ x ∈ V, ¬ IsConj u x := by
  intro v hvV hvu
  have hu1 : u ≠ 1 := by
    rintro rfl
    simp at hu
  have huu : u * u = 1 := by simpa only [hu, pow_two] using pow_orderOf_eq_one u
  have hvU : v ∉ U := by
    intro hvU
    have hv1 : v ≠ 1 := by
      rintro rfl
      exact hu1 (isConj_one_right.mp hvu.symm)
    exact hnconj (hvu.trans (hUz v hvU hv1).symm)
  have hVU : ∀ y ∈ V, y ∉ U → IsConj u y := by
    intro y hyV hyU
    obtain ⟨a, haA, hw⟩ := htrans v hvV hvU y hyV hyU
    have haV : a * v * a⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hAV haA) v).mp hvV
    have hconj : IsConj u (a * v * a⁻¹) := hvu.trans (isConj_iff.mpr ⟨a, rfl⟩)
    have h := hsat _ haV hconj _ (U.inv_mem hw)
    have hy : a * v * a⁻¹ * (y⁻¹ * (a * v * a⁻¹))⁻¹ = y := by group
    rwa [hy] at h
  have hsqV : ∀ x ∈ V, x * x = 1 := by
    intro x hxV
    by_cases hxU : x ∈ U
    · exact hUsq x hxU
    · have hord := (orderOf_eq_of_isConj (hVU x hxV hxU)).symm.trans hu
      simpa only [hord, pow_two] using pow_orderOf_eq_one x
  have hcommV : ∀ x ∈ V, ∀ y ∈ V, Commute x y := by
    intro x hxV y hyV
    have hxy := hsqV (x * y) (V.mul_mem hxV hyV)
    have hx := hsqV x hxV
    have hy := hsqV y hyV
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_left hx
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_left hy
    have : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_left hxy
    rw [mul_inv_rev, hxinv, hyinv] at this
    exact this.symm
  obtain ⟨x, hxV, y, hyV, hxU, hyU, hxyU⟩ := exists_distinct_cosets_of_three_le_relIndex
    (by omega : 3 ≤ U.relIndex V)
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_left (hsqV x hxV)
  rw [hxinv] at hxyU
  have hne : x ≠ y := by
    rintro rfl
    exact hxyU (by rw [hsqV x hxV]; exact U.one_mem)
  have hz := hprod x y (hVU x hxV hxU) (hVU y hyV hyU) hne (hcommV x hxV y hyV)
  have hu' := hVU (x * y) (V.mul_mem hxV hyV) hxyU
  exact hnconj (hu'.trans hz.symm)

end CFSG.ProperTwoGeneratedCore.InvolutionCosetFusion
