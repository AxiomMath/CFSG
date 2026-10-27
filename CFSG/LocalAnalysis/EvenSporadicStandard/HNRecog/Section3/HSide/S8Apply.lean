module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Orbits
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Decomp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Dict
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Map
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.S8Core
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.S8Outer

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma orderOf_eq_of_isConj {H : Type} [Group H] {x y : H} (h : IsConj x y) :
    orderOf x = orderOf y := by
  obtain ⟨c, hc⟩ := h
  exact SemiconjBy.orderOf_eq (c : H) hc

private lemma mul_self_eq_one_of_orderOf_eq_two {H : Type} [Group H] {x : H}
    (h : orderOf x = 2) : x * x = 1 := by
  rw [← pow_two, ← h]
  exact pow_orderOf_eq_one x

private lemma mem_sSet_two {G : Type} [Group G] {a z b c : G} :
    c ∈ sSet a z b 2 ↔ c ∈ sBase a b ∧ (a * c) ^ 2 = b := by
  simp [sSet]

theorem nonempty_mulEquiv_sym_eight_of_not_isSectionOf_A8 {H : Type} [Group H] (a b c : H) (hb1 : b ≠ 1)
    (ha2 : a * a = 1) (hc2 : c * c = 1) (hac : (a * c) ^ 2 = b) (K : Subgroup H)
    (φ : alternatingGroup (Fin 8) ≃* ↥K) (hKa : ∀ k ∈ K, a * k = k * a)
    (hKb : ∀ k ∈ K, b * k = k * b) (hnorm : ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hA8 : ∀ g : H, g ^ 2 = b → ¬ CFSG.SignalizerFunctorTheorem.IsSectionOf
      (alternatingGroup (Fin 8)) ↥(Subgroup.centralizer ({g} : Set H))) :
    Nonempty (↥(K ⊔ Subgroup.zpowers c) ≃* Sym 8) := by
  have hcK : c ∉ K := by
    intro hcKin
    have hca : a * c = c * a := hKa c hcKin
    have h1 : (a * c) ^ 2 = 1 := by
      rw [pow_two]
      calc (a * c) * (a * c) = a * (c * a) * c := by group
        _ = a * (a * c) * c := by rw [hca]
        _ = (a * a) * (c * c) := by group
        _ = 1 := by rw [ha2, hc2, mul_one]
    exact hb1 (by rw [← hac]; exact h1)
  rcases inner_or_nonempty_mulEquiv_sym_eight K φ c hc2 hcK hnorm with hinner | hout
  · exact absurd hinner (not_inner_of_not_isSectionOf_A8 a b c ha2 hc2 hac K φ hKa hKb hA8)
  · exact hout

variable {G : Type} [Group G] {b z : G} {z₀ b₀ u₀ : ↥(Gx b)}

theorem not_isSectionOf_A8_Gx (L : HLab b z z₀ b₀ u₀) {g : G} (hg : g ^ 2 = b) :
    ¬ CFSG.SignalizerFunctorTheorem.IsSectionOf (alternatingGroup (Fin 8)) ↥(Gx g) := by
  have hgb : g ∈ Gx b := by
    rw [mem_Gx, ← hg, pow_two]
    group
  let g' : ↥(Gx b) := ⟨g, hgb⟩
  have hg' : g' ^ 2 = GxSelf b := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hg
  have hle : Gx g ≤ Gx b := by
    intro x hx
    rw [mem_Gx] at hx
    rw [mem_Gx, ← hg]
    calc g ^ 2 * x = g * (g * x) := by rw [pow_two]; group
      _ = g * (x * g) := by rw [hx]
      _ = (g * x) * g := by group
      _ = (x * g) * g := by rw [hx]
      _ = x * g ^ 2 := by rw [pow_two]; group
  have hEq : Gxy g b = Gx g := by
    rw [Gxy_eq_inf]
    exact inf_eq_left.mpr hle
  intro hsec
  apply L.facts.not_isSectionOf_A8 g' hg'
  obtain ⟨e1⟩ := nonempty_mulEquiv_Gxy_subtype (b := b) g'
  let e : ↥(Gx g) ≃* ↥(Gx g') := (MulEquiv.subgroupCongr hEq.symm).trans e1
  exact CFSG.SignalizerFunctorTheorem.IsSectionOf.trans hsec
    (CFSG.SignalizerFunctorTheorem.IsSectionOf.of_mulEquiv e.symm)

theorem nonempty_mulEquiv_sym_eight_of_sSet (L : HLab b z z₀ b₀ u₀) {a : G} (hb : b ∈ orb2A a a)
    (hshape : IsShapeTwoTwoTimesA8 ↥(Gxy a b)) {c : G} (hc : c ∈ sSet a z b 2) :
    Nonempty (↥(derivedOf (Gxy a b) ⊔ Subgroup.zpowers c) ≃* Sym 8) := by
  obtain ⟨hcbase, hac⟩ := (mem_sSet_two).mp hc
  have hbA : IsConj a b := hb.1
  have hcA : IsConj a c := hcbase.1
  have hbcA : IsConj a (b * c) := hcbase.2.1
  have horder_b : orderOf b = 2 := by
    rw [← Subgroup.orderOf_mk b (self_mem_Gx b)]
    exact L.facts.orderOf_a
  have horder_a : orderOf a = 2 := (orderOf_eq_of_isConj hbA).trans horder_b
  have horder_c : orderOf c = 2 := (orderOf_eq_of_isConj hcA).symm.trans horder_a
  have ha2 : a * a = 1 := mul_self_eq_one_of_orderOf_eq_two horder_a
  have hc2 : c * c = 1 := mul_self_eq_one_of_orderOf_eq_two horder_c
  have hb2 : b ^ 2 = 1 := by rw [← horder_b]; exact pow_orderOf_eq_one b
  have hbc2 : (b * c) ^ 2 = 1 := by
    have hconj : IsConj b (b * c) := hbA.symm.trans hbcA
    have horder_bc : orderOf (b * c) = 2 :=
      (orderOf_eq_of_isConj hconj).symm.trans horder_b
    rw [← horder_bc]
    exact pow_orderOf_eq_one (b * c)
  have hc2' : c ^ 2 = 1 := by rw [pow_two]; exact hc2
  have hbc_comm : b * c = c * b := comm_of_sq_mul hb2 hc2' hbc2
  have hc_inv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hbcinv : b * c⁻¹ = c⁻¹ * b := by rw [hc_inv]; exact hbc_comm
  have hcak : c * a * c⁻¹ = a * b := by
    have h1 : a * ((a * c) * (a * c)) = a * b := by rw [← pow_two, hac]
    have h2 : a * ((a * c) * (a * c)) = c * a * c := by
      calc a * ((a * c) * (a * c)) = (a * a) * (c * a * c) := by group
        _ = c * a * c := by rw [ha2, one_mul]
    have h3 : c * a * c = a * b := h2.symm.trans h1
    rw [hc_inv]
    exact h3
  have hca : c⁻¹ * a * c = a * b := by simpa [hc_inv] using hcak
  have hfh : ∀ h : G, h ∈ Gxy a b → c * h * c⁻¹ ∈ Gxy a b := by
    intro h hh
    have hah : a * h = h * a := mem_Gx.mp (mem_Gxy.mp hh).1
    have hbh : b * h = h * b := mem_Gx.mp (mem_Gxy.mp hh).2
    have hab_h : (a * b) * h = h * (a * b) := by
      calc (a * b) * h = a * (b * h) := by group
        _ = a * (h * b) := by rw [hbh]
        _ = (a * h) * b := by group
        _ = (h * a) * b := by rw [hah]
        _ = h * (a * b) := by group
    have hker : (c⁻¹ * a * c) * h = h * (c⁻¹ * a * c) := by
      rw [hca]
      exact hab_h
    have hca_h : a * (c * h * c⁻¹) = (c * h * c⁻¹) * a := by
      calc a * (c * h * c⁻¹) = c * ((c⁻¹ * a * c) * h) * c⁻¹ := by group
        _ = c * (h * (c⁻¹ * a * c)) * c⁻¹ := by rw [hker]
        _ = (c * h * c⁻¹) * a := by group
    have hcb_h : b * (c * h * c⁻¹) = (c * h * c⁻¹) * b := by
      calc b * (c * h * c⁻¹) = (b * c) * (h * c⁻¹) := by group
        _ = (c * b) * (h * c⁻¹) := by rw [hbc_comm]
        _ = c * (b * h) * c⁻¹ := by group
        _ = c * (h * b) * c⁻¹ := by rw [hbh]
        _ = (c * h) * (b * c⁻¹) := by group
        _ = (c * h) * (c⁻¹ * b) := by rw [hbcinv]
        _ = (c * h * c⁻¹) * b := by group
    exact mem_Gxy.mpr ⟨mem_Gx.mpr hca_h, mem_Gx.mpr hcb_h⟩
  have hc_norm : c ∈ Subgroup.normalizer (Gxy a b : Set G) := by
    refine Subgroup.mem_set_normalizer_iff.mpr ?_
    intro h
    constructor
    · exact hfh h
    · intro hch
      have hmem : c * (c * h * c⁻¹) * c⁻¹ ∈ Gxy a b := hfh (c * h * c⁻¹) hch
      have heq : c * (c * h * c⁻¹) * c⁻¹ = h := by
        have e1 : c * (c * h * c⁻¹) * c⁻¹ = (c * c) * h * (c⁻¹ * c⁻¹) := by group
        have e2 : c⁻¹ * c⁻¹ = 1 := by rw [hc_inv]; exact hc2
        rw [e1, hc2, e2, one_mul, mul_one]
      rw [heq] at hmem
      exact hmem
  have hnorm : ∀ k ∈ derivedOf (Gxy a b), c * k * c⁻¹ ∈ derivedOf (Gxy a b) :=
    fun k hk => conj_mem_derivedOf_of_mem_normalizer hc_norm hk
  have hKa : ∀ k ∈ derivedOf (Gxy a b), a * k = k * a := by
    intro k hk
    exact mem_Gx.mp (mem_Gxy.mp (derivedOf_le (Gxy a b) hk)).1
  have hKb : ∀ k ∈ derivedOf (Gxy a b), b * k = k * b := by
    intro k hk
    exact mem_Gx.mp (mem_Gxy.mp (derivedOf_le (Gxy a b) hk)).2
  obtain ⟨φ⟩ := nonempty_mulEquiv_derivedOf_of_isShapeTwoTwoTimesA8 hshape
  exact nonempty_mulEquiv_sym_eight_of_not_isSectionOf_A8 a b c
    (by
      rintro rfl
      rw [orderOf_one] at horder_b
      omega)
    ha2 hc2 hac (derivedOf (Gxy a b)) φ hKa hKb hnorm
    (fun g hg => not_isSectionOf_A8_Gx L hg)

end CFSG.EvenSporadicStandard.HNRecog.Section3
