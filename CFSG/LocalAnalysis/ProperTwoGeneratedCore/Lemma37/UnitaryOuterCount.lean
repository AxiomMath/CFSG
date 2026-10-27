module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterSetting

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter

namespace OuterSetting

variable {X : Type*} [Group X] {J P : Subgroup X} [J.Normal] {zb : X} {q : ℕ}
  (hS : OuterSetting X J P zb q)

omit [J.Normal] in
theorem commute_root_torus {x t : X} (hx : x ∈ J) (ht : t ∈ torusT P J) : x * t = t * x :=
  Subgroup.mem_centralizer_iff.mp ht.2 x hx

include hS in
theorem card_inRT_sq {a b : X} (ha : a ∈ P ⊓ J) (hb : b ∈ torusT P J) :
    Nat.card {w : X // InRT P J w ∧ w ^ 2 = a * b} =
      Nat.card {x : X // x ∈ P ⊓ J ∧ x ^ 2 = a} *
        Nat.card {t : X // t ∈ torusT P J ∧ t ^ 2 = b} := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p => ⟨p.1.1 * p.2.1, ⟨p.1.1, p.1.2.1, p.2.1, p.2.2.1, rfl⟩, ?_⟩) ⟨?_, ?_⟩)
  · rw [(Commute.mul_pow (commute_root_torus p.1.2.1.2 p.2.2.1) 2), p.1.2.2, p.2.2.2]
  · rintro ⟨⟨x, hx⟩, ⟨t, ht⟩⟩ ⟨⟨x', hx'⟩, ⟨t', ht'⟩⟩ h
    obtain ⟨h1, h2⟩ := hS.eq_of_mul_eq hx.1 hx'.1 ht.1 ht'.1 (congrArg Subtype.val h)
    subst h1; subst h2; rfl
  · rintro ⟨w, ⟨y, hy, t, ht, rfl⟩, hw⟩
    rw [Commute.mul_pow (commute_root_torus hy.2 ht) 2] at hw
    obtain ⟨h1, h2⟩ := hS.eq_of_mul_eq (Subgroup.pow_mem _ hy 2) ha (Subgroup.pow_mem _ ht 2) hb hw
    exact ⟨⟨⟨y, hy, h1⟩, ⟨t, ht, h2⟩⟩, rfl⟩

theorem conj_mem_centralizer (g : X) {k : X} (hk : k ∈ Subgroup.centralizer (J : Set X)) :
    g * k * g⁻¹ ∈ Subgroup.centralizer (J : Set X) := by
  rw [Subgroup.mem_centralizer_iff] at hk ⊢
  intro j hj
  have hj' : g⁻¹ * j * g ∈ J := by
    simpa using (inferInstance : J.Normal).conj_mem j hj g⁻¹
  calc j * (g * k * g⁻¹) = g * ((g⁻¹ * j * g) * k) * g⁻¹ := by group
    _ = g * (k * (g⁻¹ * j * g)) * g⁻¹ := by rw [hk _ hj']
    _ = g * k * g⁻¹ * j := by group

theorem sq_mul_mul {y t w : X} (hy : y ∈ J) (ht : t ∈ Subgroup.centralizer (J : Set X)) :
    (y * t * w) ^ 2 = (y * (w * y * w⁻¹)) * (t * w) ^ 2 := by
  have hwy : w * y * w⁻¹ ∈ J := (inferInstance : J.Normal).conj_mem y hy w
  have hc := Subgroup.mem_centralizer_iff.mp ht _ hwy
  calc (y * t * w) ^ 2 = y * (t * (w * y * w⁻¹)) * w * t * w := by rw [pow_two]; group
    _ = y * ((w * y * w⁻¹) * t) * w * t * w := by rw [hc]
    _ = (y * (w * y * w⁻¹)) * (t * w) ^ 2 := by rw [pow_two]; group

include hS in
theorem card_outer_sq_zb {w₁ : X} (hw₁ : w₁ ∈ P) (hw₁RT : ¬ InRT P J w₁)
    (hw₁2 : w₁ ^ 2 ∈ torusT P J) :
    Nat.card {w : X // w ∈ P ∧ ¬ InRT P J w ∧ w ^ 2 = zb} =
      Nat.card {x : X // x ∈ P ⊓ J ∧ x * (w₁ * x * w₁⁻¹) = 1} *
        Nat.card {t : X // t ∈ torusT P J ∧ (t * w₁) ^ 2 = zb} := by
  have hzbT : zb ∈ torusT P J := ⟨hS.zb_mem, hS.zb_mem_centralizer⟩
  have hroot : ∀ x ∈ P ⊓ J, x * (w₁ * x * w₁⁻¹) ∈ P ⊓ J := fun x hx =>
    ⟨P.mul_mem hx.1 (P.mul_mem (P.mul_mem hw₁ hx.1) (P.inv_mem hw₁)),
      J.mul_mem hx.2 ((inferInstance : J.Normal).conj_mem x hx.2 w₁)⟩
  have htorus : ∀ t ∈ torusT P J, (t * w₁) ^ 2 ∈ torusT P J := by
    intro t ht
    have h : (t * w₁) ^ 2 = t * (w₁ * t * w₁⁻¹) * w₁ ^ 2 := by rw [pow_two, pow_two]; group
    rw [h]
    exact ⟨P.mul_mem (P.mul_mem ht.1 (P.mul_mem (P.mul_mem hw₁ ht.1) (P.inv_mem hw₁))) hw₁2.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ ht.2 (conj_mem_centralizer w₁ ht.2)) hw₁2.2⟩
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p => ⟨p.1.1 * p.2.1 * w₁, P.mul_mem (P.mul_mem p.1.2.1.1 p.2.2.1.1) hw₁, ?_, ?_⟩)
    ⟨?_, ?_⟩)
  · rintro ⟨y', hy', t', ht', h⟩
    apply hw₁RT
    refine ⟨(p.1.1)⁻¹ * y', ⟨P.mul_mem (P.inv_mem p.1.2.1.1) hy'.1,
      J.mul_mem (J.inv_mem p.1.2.1.2) hy'.2⟩, (p.2.1)⁻¹ * t',
      ⟨P.mul_mem (P.inv_mem p.2.2.1.1) ht'.1,
        Subgroup.mul_mem _ (Subgroup.inv_mem _ p.2.2.1.2) ht'.2⟩, ?_⟩
    have hc := commute_root_torus (J.mul_mem (J.inv_mem p.1.2.1.2) hy'.2)
      (Subgroup.inv_mem _ p.2.2.1)
    calc w₁ = (p.2.1)⁻¹ * ((p.1.1)⁻¹ * (p.1.1 * p.2.1 * w₁)) := by group
      _ = (p.2.1)⁻¹ * ((p.1.1)⁻¹ * y' * t') := by rw [h]; group
      _ = (p.2.1)⁻¹ * ((p.1.1)⁻¹ * y') * t' := by group
      _ = (p.1.1)⁻¹ * y' * (p.2.1)⁻¹ * t' := by rw [← hc]
      _ = (p.1.1)⁻¹ * y' * ((p.2.1)⁻¹ * t') := by group
  · rw [sq_mul_mul p.1.2.1.2 p.2.2.1.2, p.1.2.2, p.2.2.2, one_mul]
  · rintro ⟨⟨x, hx⟩, ⟨t, ht⟩⟩ ⟨⟨x', hx'⟩, ⟨t', ht'⟩⟩ h
    have h' : x * t = x' * t' := mul_right_cancel (congrArg Subtype.val h)
    obtain ⟨h1, h2⟩ := hS.eq_of_mul_eq hx.1 hx'.1 ht.1 ht'.1 h'
    subst h1; subst h2; rfl
  · rintro ⟨w, hw, hwRT, hw2⟩
    obtain ⟨y, hy, t, ht, rfl⟩ := hS.mem_coset_of_sq_eq_zb hw₁ hw₁RT hw₁2 hw hwRT hw2
    rw [sq_mul_mul hy.2 ht.2, ← one_mul zb] at hw2
    obtain ⟨h1, h2⟩ := hS.eq_of_mul_eq (hroot y hy) (Subgroup.one_mem _) (htorus t ht) hzbT hw2
    exact ⟨⟨⟨y, hy, h1⟩, ⟨t, ht, h2⟩⟩, rfl⟩

omit [J.Normal] in
theorem card_sq_split [Finite X] (y : X) :
    Nat.card {w : X // w ∈ P ∧ w ^ 2 = y} =
      Nat.card {w : X // InRT P J w ∧ w ^ 2 = y} +
        Nat.card {w : X // w ∈ P ∧ ¬ InRT P J w ∧ w ^ 2 = y} := by
  classical
  rw [← Nat.card_congr (Equiv.sumCompl fun w : {w : X // w ∈ P ∧ w ^ 2 = y} => InRT P J w.1),
    Nat.card_sum]
  congr 1
  · exact Nat.card_congr
      { toFun := fun w => ⟨w.1.1, w.2, w.1.2.2⟩
        invFun := fun w => ⟨⟨w.1, by
            obtain ⟨y', hy', t, ht, h⟩ := w.2.1
            rw [h]
            exact P.mul_mem hy'.1 ht.1, w.2.2⟩, w.2.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  · exact Nat.card_congr
      { toFun := fun w => ⟨w.1.1, w.1.2.1, w.2, w.1.2.2⟩
        invFun := fun w => ⟨⟨w.1, w.2.1, w.2.2.2⟩, w.2.2.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

include hS in
theorem card_torus_sq_one : Nat.card {t : X // t ∈ torusT P J ∧ t ^ 2 = 1} = 2 := by
  have hzbT : zb ∈ torusT P J := ⟨hS.zb_mem, hS.zb_mem_centralizer⟩
  have hzb1 : zb ≠ 1 := fun h => hS.zb_not_mem (h ▸ J.one_mem)
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, Subgroup.one_mem _, one_pow 2⟩, ⟨zb, hzbT, hS.zb_sq⟩,
    fun h => hzb1 (congrArg Subtype.val h).symm, ?_⟩
  ext t
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases hS.eq_one_or_eq_zb t.2.1 t.2.2 with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

end OuterSetting

end CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter
