module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL33Gamma
public import CFSG.GH74.E2.BlackBoxesStd
public import CFSG.LocalAnalysis.ComponentClassification.AS76bBasic
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public section

namespace CFSG.ComponentClassification.RankTwoL33

open Subgroup CFSG.GH74 CFSG.GH74.E2 CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G]

section FourGroup

variable (a b : G)

@[expose] def fourGroup (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b = b * a) : Subgroup G where
  carrier := {1, a, b, a * b}
  mul_mem' {x y} hx hy := by
    have ha' : a * a = 1 := by rw [← sq]; exact ha
    have hb' : b * b = 1 := by rw [← sq]; exact hb
    have h1 : a * (a * b) = b := by rw [← mul_assoc, ha', one_mul]
    have h2 : a * b * a = b := by rw [mul_assoc, ← hab, ← mul_assoc, ha', one_mul]
    have h3 : a * b * b = a := by rw [mul_assoc, hb', mul_one]
    have h4 : b * (a * b) = a := by rw [← mul_assoc, ← hab, mul_assoc, hb', mul_one]
    have h5 : a * b * (a * b) = 1 := by rw [← mul_assoc, h2, hb']
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp [ha', hb', h1, h2, h3, h4, h5, ← hab]
  one_mem' := by simp
  inv_mem' {x} hx := by
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hb)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · simp [ha']
    · simp [hb']
    · simp [mul_inv_rev, ha', hb', hab]

variable {a b}

theorem mem_fourGroup {ha : a ^ 2 = 1} {hb : b ^ 2 = 1} {hab : a * b = b * a} {x : G} :
    x ∈ fourGroup a b ha hb hab ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := Iff.rfl

theorem sq_of_mem_fourGroup {ha : a ^ 2 = 1} {hb : b ^ 2 = 1} {hab : a * b = b * a} {x : G}
    (hx : x ∈ fourGroup a b ha hb hab) : x ^ 2 = 1 := by
  rcases mem_fourGroup.1 hx with rfl | rfl | rfl | rfl
  · exact one_pow 2
  · exact ha
  · exact hb
  · have h1 : a * b * (a * b) = a * a * (b * b) :=
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hab]
        _ = a * a * (b * b) := by group
    rw [sq, h1, ← sq, ← sq, ha, hb, one_mul]

theorem isElemAbelian_fourGroup {ha : a ^ 2 = 1} {hb : b ^ 2 = 1} {hab : a * b = b * a} :
    IsElemAbelian 2 (fourGroup a b ha hb hab) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => sq_of_mem_fourGroup hx⟩
  have hx := x.2
  have hy := y.2
  have hxy : (x : G) * y ∈ fourGroup a b ha hb hab := mul_mem hx hy
  have h1 := sq_of_mem_fourGroup hx
  have h2 := sq_of_mem_fourGroup hy
  have h3 := sq_of_mem_fourGroup hxy
  rw [sq] at h1 h2 h3
  simp only [coe_mul]
  have hx' : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_right h1
  have hy' : (y : G)⁻¹ = y := inv_eq_of_mul_eq_one_right h2
  have hxy' : ((x : G) * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h3
  calc (x : G) * y = ((x : G) * y)⁻¹ := hxy'.symm
    _ = (y : G)⁻¹ * (x : G)⁻¹ := mul_inv_rev _ _
    _ = y * x := by rw [hx', hy']

theorem card_fourGroup {ha : a ^ 2 = 1} {hb : b ^ 2 = 1} {hab : a * b = b * a} (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hne : a ≠ b) : Nat.card (fourGroup a b ha hb hab) = 4 := by
  classical
  have hab1 : a * b ≠ 1 := fun h => hne (by
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hb)])
  have haab : a ≠ a * b := fun h => hb1 (by simpa using (congrArg (a⁻¹ * ·) h).symm)
  have hbab : b ≠ a * b := fun h => ha1 (by
    have := congrArg (· * b⁻¹) h
    simpa using this.symm)
  have hcarrier : ((fourGroup a b ha hb hab : Subgroup G) : Set G) =
      ↑({1, a, b, a * b} : Finset G) := by
    ext x
    simp [mem_fourGroup]
  rw [← SetLike.coe_sort_coe, hcarrier, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [Finset.card_insert_of_notMem (by simp [Ne.symm ha1, Ne.symm hb1, Ne.symm hab1]),
    Finset.card_insert_of_notMem (by simp [hne, haab]),
    Finset.card_insert_of_notMem (by simp [hbab]), Finset.card_singleton]

end FourGroup

theorem mem_normalizer_of_commute {C : Subgroup G} [Finite G]
    (hC : ∀ g : G, g ∉ normalizer (C : Set G) → Odd (Nat.card ↥(C ⊓ conjugate C g)))
    {t : G} (ht : t ∈ C) (ht2 : orderOf t = 2) {y : G} (hyt : y * t = t * y) :
    y ∈ normalizer (C : Set G) := by
  by_contra hy
  have hodd := hC y hy
  have htmem : t ∈ C ⊓ conjugate C y := by
    refine ⟨ht, ?_⟩
    change t ∈ rightConjugate C y
    rw [mem_rightConjugate_iff, hyt, mul_inv_cancel_right]
    exact ht
  have h2 := orderOf_dvd_natCard (⟨t, htmem⟩ : ↥(C ⊓ conjugate C y))
  rw [Subgroup.orderOf_mk, ht2] at h2
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

theorem not_mem_of_odd {S : Subgroup G} [Finite G] (hS : Odd (Nat.card S)) {t : G}
    (ht2 : orderOf t = 2) : t ∉ S := fun ht => by
  have h2 := orderOf_dvd_natCard (⟨t, ht⟩ : S)
  rw [Subgroup.orderOf_mk, ht2] at h2
  exact (Nat.not_even_iff_odd.2 hS) (even_iff_two_dvd.2 h2)

theorem conjugate_eq_rightConjugate (S : Subgroup G) (g : G) :
    conjugate S g = rightConjugate S g := rfl

theorem centralizer_conjugate (A : Subgroup G) (k : G) :
    centralizer (conjugate A k : Set G) = conjugate (centralizer (A : Set G)) k := by
  ext x
  rw [conjugate_eq_rightConjugate, conjugate_eq_rightConjugate, mem_rightConjugate_iff,
    mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h a ha
    have hmem : k⁻¹ * a * k ∈ (rightConjugate A k : Set G) := by
      rw [SetLike.mem_coe, mem_rightConjugate_iff]
      simpa [mul_assoc] using ha
    have := h _ hmem
    calc a * (k * x * k⁻¹) = k * ((k⁻¹ * a * k) * x) * k⁻¹ := by group
      _ = k * (x * (k⁻¹ * a * k)) * k⁻¹ := by rw [this]
      _ = k * x * k⁻¹ * a := by group
  · intro h y hy
    rw [SetLike.mem_coe, mem_rightConjugate_iff] at hy
    have := h _ hy
    calc y * x = k⁻¹ * ((k * y * k⁻¹) * (k * x * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * x * k⁻¹) * (k * y * k⁻¹)) * k := by rw [this]
      _ = x * y := by group

theorem false_of_conjugate [Finite G] {A : Subgroup G} (hstd : CFSG.IsStandardSubgroup A)
    (hshape : ShapeL33 ↥A) {k : G} (hk : k ∉ normalizer (A : Set G)) {u v : G}
    (hu2 : orderOf u = 2) (hv2 : orderOf v = 2) (huv : u ≠ v) (hcomm : u * v = v * u)
    (huC : u ∈ centralizer (A : Set G)) (hvC : v ∈ centralizer (A : Set G))
    (huN : u ∈ normalizer (conjugate A k : Set G))
    (hvN : v ∈ normalizer (conjugate A k : Set G)) : False := by
  obtain ⟨-, -, htight, hnorm, hcommA⟩ := hstd
  set C := centralizer (A : Set G) with hCdef
  set X := conjugate A k with hXdef
  have eX : ↥A ≃* ↥X := A.equivMapOfInjective (MulAut.conj k⁻¹).toMonoidHom
    (MulAut.conj k⁻¹).injective
  have hX : ShapeL33 ↥X := lieModel_of_mulEquiv eX hshape
  obtain ⟨hXsimple, -⟩ := shapeL33_simple hX
  have hkC : k ∉ normalizer (C : Set G) := by rwa [hnorm]
  have hodd : Odd (Nat.card ↥(C ⊓ conjugate C k)) := htight k hkC
  have hu1 : u ≠ 1 := by intro h; rw [h, orderOf_one] at hu2; omega
  have hv1 : v ≠ 1 := by intro h; rw [h, orderOf_one] at hv2; omega
  have hsq : ∀ {t : G}, orderOf t = 2 → t ^ 2 = 1 := fun h => by
    rw [← h]; exact pow_orderOf_eq_one _
  have huv1 : u * v ≠ 1 := fun h => huv (by
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq hv2)])
  have huv2 : orderOf (u * v) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ huv1
    rw [sq, show u * v * (u * v) = u * u * (v * v) by
      rw [mul_assoc, ← mul_assoc v, ← hcomm, mul_assoc, mul_assoc], ← sq, ← sq, hsq hu2, hsq hv2,
      one_mul]
  have hfaith : ∀ t : G, t ∈ C → orderOf t = 2 → t ∉ centralizer (X : Set G) := by
    intro t htC ht2 htX
    rw [hXdef, centralizer_conjugate] at htX
    exact not_mem_of_odd hodd ht2 ⟨htC, htX⟩
  have hCN : ∀ t : G, t ∈ C → orderOf t = 2 →
      X ⊓ centralizer ({t} : Set G) ≤ normalizer (C : Set G) := fun t htC ht2 y hy =>
    mem_normalizer_of_commute htight htC ht2 (mem_centralizer_singleton_iff.1 hy.2)
  have hgen := le_sup_inf_centralizer hX huN hvN (hsq hu2) (hsq hv2) hcomm
    (hfaith u huC hu2) (hfaith v hvC hv2) (hfaith (u * v) (mul_mem huC hvC) huv2)
  have hXN : X ≤ normalizer (C : Set G) := hgen.trans (sup_le (sup_le (hCN u huC hu2)
    (hCN v hvC hv2)) (hCN (u * v) (mul_mem huC hvC) huv2))
  have hnormal : ((C ⊓ X).subgroupOf X).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf, Subgroup.mem_inf] at hn ⊢
    exact ⟨(mem_normalizer_iff.1 (hXN g.2) n).1 hn.1, mul_mem (mul_mem g.2 hn.2) (inv_mem g.2)⟩⟩
  rcases hnormal.eq_bot_or_eq_top with h | h
  ·
    apply hfaith u huC hu2
    rw [mem_centralizer_iff]
    intro x hx
    have hc : x * u * x⁻¹ * u⁻¹ ∈ C ⊓ X := by
      refine Subgroup.mem_inf.2
        ⟨mul_mem ((mem_normalizer_iff.1 (hXN hx) u).1 huC) (inv_mem huC), ?_⟩
      have : x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) := by group
      rw [this]
      exact mul_mem hx ((mem_normalizer_iff.1 huN x⁻¹).1 (inv_mem hx))
    have hc' : (⟨_, (Subgroup.mem_inf.1 hc).2⟩ : X) ∈ (C ⊓ X).subgroupOf X :=
      mem_subgroupOf.2 hc
    rw [h, mem_bot] at hc'
    have h1 : x * u * x⁻¹ * u⁻¹ = 1 := congrArg Subtype.val hc'
    calc x * u = x * u * x⁻¹ * u⁻¹ * (u * x) := by group
      _ = u * x := by rw [h1, one_mul]
  ·
    apply hcommA k
    rw [eq_bot_iff, commutator_le]
    intro a ha x hx
    have hxC : x ∈ C := by
      have : (⟨x, hx⟩ : X) ∈ (C ⊓ X).subgroupOf X := h ▸ mem_top _
      exact (Subgroup.mem_inf.1 (mem_subgroupOf.1 this)).1
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (mem_centralizer_iff.1 hxC) a ha

theorem exists_conjugate_normalized [Finite G] (h33 : AS76b.Lemma33Three) {A : Subgroup G}
    (hH : AS76b.Hyp31 A) {u v : G} (hu2 : u ^ 2 = 1) (hv2 : v ^ 2 = 1) (hcomm : u * v = v * u)
    (huC : u ∈ centralizer (A : Set G)) (hvC : v ∈ centralizer (A : Set G)) :
    ∃ k : G, k ∉ normalizer (A : Set G) ∧ u ∈ normalizer (conjugate A k : Set G) ∧
      v ∈ normalizer (conjugate A k : Set G) := by
  obtain ⟨g, hg, T, hT1, hT2⟩ := h33 G A hH
  set C := centralizer (A : Set G) with hCdef
  set S := rightConjugate C g with hSdef
  have hTN : T ≤ normalizer (A : Set G) := by
    obtain ⟨Q', hQ'⟩ := hT1
    rw [← hQ']
    exact (map_subtype_le _).trans inf_le_right
  obtain ⟨Q, hQ⟩ := hT2
  have hconjS : ∀ w ∈ C, g⁻¹ * w * g ∈ S := fun w hw => by
    rw [hSdef, mem_rightConjugate_iff]
    simpa [mul_assoc] using hw
  set u' : S := ⟨g⁻¹ * u * g, hconjS u huC⟩
  set v' : S := ⟨g⁻¹ * v * g, hconjS v hvC⟩
  have hu'2 : u' ^ 2 = 1 := Subtype.ext (by
    simp only [u', SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [sq, show g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g by group, ← sq, hu2]
    group)
  have hv'2 : v' ^ 2 = 1 := Subtype.ext (by
    simp only [v', SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [sq, show g⁻¹ * v * g * (g⁻¹ * v * g) = g⁻¹ * (v * v) * g by group, ← sq, hv2]
    group)
  have hu'v' : u' * v' = v' * u' := Subtype.ext (by
    simp only [u', v', coe_mul]
    rw [show g⁻¹ * u * g * (g⁻¹ * v * g) = g⁻¹ * (u * v) * g by group, hcomm]
    group)
  have hW : IsPGroup 2 (fourGroup u' v' hu'2 hv'2 hu'v') := fun w =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using sq_of_mem_fourGroup w.2)⟩
  obtain ⟨P', hP'⟩ := hW.exists_le_sylow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq S P' Q
  have hmem : ∀ w : S, w ∈ fourGroup u' v' hu'2 hv'2 hu'v' →
      ((c * w * c⁻¹ : S) : G) ∈ T := by
    intro w hw
    have h1 : c * w * c⁻¹ ∈ (Q : Subgroup S) := by
      rw [← hc, Sylow.coe_subgroup_smul]
      have := Subgroup.smul_mem_pointwise_smul w (MulAut.conj c) (P' : Subgroup S) (hP' hw)
      simpa [MulAut.smul_def, MulAut.conj_apply] using this
    rw [← hQ]
    exact mem_map_of_mem S.subtype h1
  have hu₁ := hTN (hmem u' (mem_fourGroup.2 (Or.inr (Or.inl rfl))))
  have hv₁ := hTN (hmem v' (mem_fourGroup.2 (Or.inr (Or.inr (Or.inl rfl)))))
  have hcS : g * (c : G) * g⁻¹ ∈ C := by
    have h : (c : G) ∈ rightConjugate C g := c.2
    rw [mem_rightConjugate_iff] at h
    exact h
  have hCN : ∀ y ∈ C, y ∈ normalizer (A : Set G) := fun y hy => by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [(mem_centralizer_iff.1 hy x hx).symm, mul_inv_cancel_right]
      exact hx
    · intro hx
      have h := mem_centralizer_iff.1 hy _ hx
      have : x = y * x * y⁻¹ :=
        calc x = y⁻¹ * ((y * x * y⁻¹) * y) := by group
          _ = y⁻¹ * (y * (y * x * y⁻¹)) := by rw [h]
          _ = y * x * y⁻¹ := by group
      rw [this]
      exact hx
  have hnorm : ∀ w : S, w ∈ fourGroup u' v' hu'2 hv'2 hu'v' →
      g * (w : G) * g⁻¹ ∈ normalizer (conjugate A ((c : G) * g⁻¹) : Set G) := by
    intro w hw
    have hw₁ := hTN (hmem w hw)
    simp only [coe_mul, coe_inv] at hw₁
    rw [mem_normalizer_iff]
    intro x
    simp only [conjugate_eq_rightConjugate, mem_rightConjugate_iff]
    rw [mem_normalizer_iff.1 hw₁ ((c : G) * g⁻¹ * x * ((c : G) * g⁻¹)⁻¹)]
    have e : (c : G) * (w : G) * (c : G)⁻¹ * ((c : G) * g⁻¹ * x * ((c : G) * g⁻¹)⁻¹) *
        ((c : G) * (w : G) * (c : G)⁻¹)⁻¹ = (c : G) * g⁻¹ * (g * (w : G) * g⁻¹ * x *
          (g * (w : G) * g⁻¹)⁻¹) * ((c : G) * g⁻¹)⁻¹ := by group
    rw [e]
  refine ⟨(c : G) * g⁻¹, ?_, ?_, ?_⟩
  · intro hk
    apply hg
    rw [show g = (g * (c : G) * g⁻¹) * ((c : G) * g⁻¹)⁻¹ by group]
    exact mul_mem (hCN _ hcS) (inv_mem hk)
  · have h := hnorm u' (mem_fourGroup.2 (Or.inr (Or.inl rfl)))
    rwa [show g * ((u' : S) : G) * g⁻¹ = u by simp only [u']; group] at h
  · have h := hnorm v' (mem_fourGroup.2 (Or.inr (Or.inr (Or.inl rfl))))
    rwa [show g * ((v' : S) : G) * g⁻¹ = v by simp only [v']; group] at h

theorem aschbacherStandardL33_of (h33 : AS76b.Lemma33Three) :
    CFSG.GH74.E2.AschbacherStandardL33 := by
  intro G _ _ hG hnab _ A hstd hshape ⟨u, v, hu2, hv2, huv, hcomm, huC, hvC⟩
  obtain ⟨hAsimple, hcardA⟩ := shapeL33_simple hshape
  have hsq : ∀ {t : G}, orderOf t = 2 → t ^ 2 = 1 := fun h => by
    rw [← h]; exact pow_orderOf_eq_one _
  have hu1 : u ≠ 1 := by intro h; rw [h, orderOf_one] at hu2; omega
  have hv1 : v ≠ 1 := by intro h; rw [h, orderOf_one] at hv2; omega
  have hdvd : 5616 ∣ Nat.card G := hcardA ▸ card_subgroup_dvd_card A
  have hodd : standardComponentOddCore G = ⊥ := by
    refine sSup_eq_bot.2 fun N ⟨hN, hNodd⟩ => ?_
    rcases hN.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      rw [h, card_top] at hNodd
      obtain ⟨j, hj⟩ := hNodd
      omega
  have hrank : 1 < Open.pRank 2 (centralizer (A : Set G)) := by
    rw [← AS76b.pRank_type_eq_open]
    set uC : centralizer (A : Set G) := ⟨u, huC⟩
    set vC : centralizer (A : Set G) := ⟨v, hvC⟩
    have huC2 : uC ^ 2 = 1 := Subtype.ext (by simpa [uC] using hsq hu2)
    have hvC2 : vC ^ 2 = 1 := Subtype.ext (by simpa [vC] using hsq hv2)
    have hcommC : uC * vC = vC * uC := Subtype.ext (by simpa [uC, vC] using hcomm)
    have huC1 : uC ≠ 1 := fun h => hu1 (by simpa [uC] using congrArg Subtype.val h)
    have hvC1 : vC ≠ 1 := fun h => hv1 (by simpa [vC] using congrArg Subtype.val h)
    have huvC : uC ≠ vC := fun h => huv (by simpa [uC, vC] using congrArg Subtype.val h)
    have h := CFSG.SectionRank.le_pRank (p := 2) (by norm_num) (le_top : fourGroup uC vC huC2
      hvC2 hcommC ≤ ⊤) isElemAbelian_fourGroup (k := 2)
      (by rw [card_fourGroup huC1 hvC1 huvC]; norm_num)
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    omega
  have hnn : ¬ A.Normal := by
    intro hN
    rcases hN.eq_bot_or_eq_top with h | h
    · have := card_bot (G := G)
      rw [← h, hcardA] at this
      omega
    · have hcen : center G = ⊥ := by
        rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h1 | h1
        · exact h1
        · exfalso
          obtain ⟨a, b, hab⟩ := hnab
          exact hab ((mem_center_iff.1 (h1 ▸ mem_top b)) a)
      apply hu1
      have : u ∈ center G := by
        rw [mem_center_iff]
        intro y
        exact (mem_centralizer_iff.1 huC) y (h ▸ mem_top y)
      rw [hcen] at this
      exact this
  have hstd' : standardComponentIsStandard A := hstd.standardComponentIsStandard
  have hH : AS76b.Hyp31 A := ⟨hstd', l33_hypII _ hshape, hodd, hrank, hnn⟩
  obtain ⟨k, hk, huN, hvN⟩ :=
    exists_conjugate_normalized h33 hH (hsq hu2) (hsq hv2) hcomm huC hvC
  exact false_of_conjugate hstd hshape hk hu2 hv2 huv hcomm huC hvC huN hvN

end CFSG.ComponentClassification.RankTwoL33
