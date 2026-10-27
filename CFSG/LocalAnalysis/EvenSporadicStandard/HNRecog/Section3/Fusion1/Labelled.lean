module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongr

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog Subgroup

theorem TwoHSFacts.mul_left_z {H : Type} [Group H] {a z b z₁ : H} (h : TwoHSFacts H a z b z₁) :
    TwoHSFacts H a (a * z) b z₁ := by
  have haC : a ∈ Subgroup.center H := by
    rw [h.center_eq]
    exact Subgroup.mem_zpowers a
  have hac : ∀ g : H, a * g = g * a := fun g =>
    (Subgroup.mem_center_iff.mp haC g).symm
  have ha2 : a ^ 2 = 1 := by simpa [h.orderOf_a] using pow_orderOf_eq_one a
  have haa : a * a = 1 := by rw [← pow_two]; exact ha2
  have hzz : z ^ 2 = 1 := by simpa [h.orderOf_z] using pow_orderOf_eq_one z
  have haz : a * (a * z) = z := by rw [← mul_assoc, haa, one_mul]
  have hnxz : ¬ IsConj a z := by
    have := h.not_isConj 0 1 (by decide)
    simpa using this
  have hcent : Subgroup.centralizer ({a * z} : Set H) = Subgroup.centralizer ({z} : Set H) := by
    apply le_antisymm
    · intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      apply mul_left_cancel (a := a)
      calc a * (g * z) = (a * g) * z := (mul_assoc a g z).symm
        _ = (g * a) * z := by rw [hac g]
        _ = g * (a * z) := mul_assoc g a z
        _ = (a * z) * g := hg
        _ = a * (z * g) := mul_assoc a z g
    · intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      apply mul_left_cancel (a := a)
      calc a * (g * (a * z)) = (a * g) * (a * z) := (mul_assoc a g (a * z)).symm
        _ = (g * a) * (a * z) := by rw [hac g]
        _ = g * (a * (a * z)) := mul_assoc g a (a * z)
        _ = g * z := by rw [haz]
        _ = z * g := hg
        _ = (a * (a * z)) * g := by rw [haz]
        _ = a * ((a * z) * g) := mul_assoc a (a * z) g
  have hzsup : Subgroup.zpowers a ⊔ Subgroup.zpowers (a * z) =
      Subgroup.zpowers a ⊔ Subgroup.zpowers z := by
    have hzmem : z ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers (a * z) := by
      have h : a * (a * z) ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers (a * z) :=
        Subgroup.mul_mem_sup (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers (a * z))
      rwa [haz] at h
    exact le_antisymm (sup_le le_sup_left (Subgroup.zpowers_mul_le_sup a z))
      (sup_le le_sup_left (Subgroup.zpowers_le.mpr hzmem))
  have hswap0 : Equiv.swap (1 : Fin 5) 2 (0 : Fin 5) = 0 := by decide
  have hswap1 : Equiv.swap (1 : Fin 5) 2 (1 : Fin 5) = 2 := by decide
  have hswap2 : Equiv.swap (1 : Fin 5) 2 (2 : Fin 5) = 1 := by decide
  have hswap3 : Equiv.swap (1 : Fin 5) 2 (3 : Fin 5) = 3 := by decide
  have hswap4 : Equiv.swap (1 : Fin 5) 2 (4 : Fin 5) = 4 := by decide
  have hvec : ∀ i : Fin 5, (![a, a * z, a * (a * z), b, z₁] : Fin 5 → H) i =
      (![a, z, a * z, b, z₁] : Fin 5 → H) (Equiv.swap 1 2 i) := by
    intro i
    fin_cases i <;> simp [haz, hswap0, hswap1, hswap2, hswap3, hswap4]
  have horder_z : orderOf (a * z) = 2 := by
    have hcomm : Commute a z := hac z
    have haz2 : (a * z) ^ 2 = 1 := by
      rw [hcomm.mul_pow, ha2, hzz, one_mul]
    have haz_ne : a * z ≠ 1 := by
      intro h1
      have hza : z = a := mul_left_cancel (h1.trans haa.symm)
      exact hnxz (by simpa [hza] using IsConj.refl a)
    exact orderOf_eq_prime haz2 haz_ne
  have hnot_isConj : ∀ i j : Fin 5, i ≠ j →
      ¬ IsConj (![a, a * z, a * (a * z), b, z₁] i) (![a, a * z, a * (a * z), b, z₁] j) := by
    intro i j hij hc
    exact h.not_isConj (Equiv.swap 1 2 i) (Equiv.swap 1 2 j)
      (fun heq => hij ((Equiv.swap (1 : Fin 5) 2).injective heq))
      (by rwa [hvec i, hvec j] at hc)
  have hinvolution_cover : ∀ x : H, orderOf x = 2 →
      ∃ i : Fin 5, IsConj (![a, a * z, a * (a * z), b, z₁] i) x := by
    intro x hx
    obtain ⟨j, hj⟩ := h.involution_cover x hx
    refine ⟨Equiv.swap 1 2 j, ?_⟩
    rw [hvec (Equiv.swap 1 2 j), Equiv.swap_apply_self]
    exact hj
  refine
    { center_eq := h.center_eq
      orderOf_a := h.orderOf_a
      orderOf_z := horder_z
      orderOf_b := h.orderOf_b
      orderOf_z₁ := h.orderOf_z₁
      not_isConj := hnot_isConj
      involution_cover := hinvolution_cover
      cent_z := h.cent_az
      cent_az := by rw [haz]; exact h.cent_z
      cent_b := h.cent_b
      cent_z₁ := h.cent_z₁
      mem_commutator := ⟨h.mem_commutator.1, h.mem_commutator.2.2,
        by rw [haz]; exact h.mem_commutator.2.1⟩
      not_mem_commutator := h.not_mem_commutator
      K_shape := by rw [hcent]; exact h.K_shape
      center_K := by rw [hcent, hzsup]; exact h.center_K
      exists_sq_eq := h.exists_sq_eq
      isConj_of_sq_eq := h.isConj_of_sq_eq
      not_isSectionOf_A8 := h.not_isSectionOf_A8
      card_eq := h.card_eq
      table_three := h.table_three
      table_five := h.table_five
      table_seven := h.table_seven
      table_eleven := h.table_eleven
      sl25_le_centralizer := h.sl25_le_centralizer
      sylow_two_five := h.sylow_two_five
      m11_unique_class := h.m11_unique_class
      m11_centralizer_five := h.m11_centralizer_five
      centralizer_five_of_A8 := h.centralizer_five_of_A8 }

theorem exists_labelled_facts (hI : TwoHSInterface) {G : Type} [Group G] {a z : G}
    (h : IsF5Type a z) : ∃ z' b' u' : ↥(Gx a), TwoHSFacts ↥(Gx a) (GxSelf a) z' b' u' := by
  obtain ⟨E, hE⟩ := h.cent_a
  obtain ⟨a', z', b', u', haf⟩ := hI.facts ↥(Gx a) E hE
  have hself_center : GxSelf a ∈ Subgroup.center ↥(Gx a) := by
    refine Subgroup.mem_center_iff.mpr fun x => ?_
    apply Subtype.ext
    exact (mem_Gx.mp x.2).symm
  have hself_ord : orderOf (GxSelf a) = 2 := by
    simpa [GxSelf] using h.orderOf_a
  have hself_ne_one : GxSelf a ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hself_ord
    exact (by decide : (1 : ℕ) ≠ 2) hself_ord
  have hself_zpow : GxSelf a ∈ Subgroup.zpowers a' := by
    rw [← haf.center_eq]
    exact hself_center
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hself_zpow
  have hkmod : a' ^ (k % 2) = GxSelf a := by
    have h' := zpow_mod_orderOf a' k
    rw [haf.orderOf_a] at h'
    exact h'.trans hk
  have haeq : a' = GxSelf a := by
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · exfalso
      have h1' : GxSelf a = 1 := by rw [← hkmod, h0, zpow_zero]
      exact hself_ne_one h1'
    · rw [← hkmod, h1, zpow_one]
  exact ⟨z', b', u', by rw [haeq] at haf; exact haf⟩

theorem nonempty_mulEquiv_Gxy {G : Type} [Group G] {a x : G} (hx : x ∈ Gx a) :
    Nonempty (↥(Gxy a x) ≃* ↥(Subgroup.centralizer ({(⟨x, hx⟩ : ↥(Gx a))} : Set ↥(Gx a)))) := by
  have hcentral : Subgroup.centralizer ({(⟨x, hx⟩ : ↥(Gx a))} : Set ↥(Gx a)) =
      (Gx x).subgroupOf (Gx a) := by
    ext g
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf]
    exact ⟨fun h => mem_Gx.mpr (congrArg Subtype.val h).symm,
      fun h => Subtype.ext (mem_Gx.mp h).symm⟩
  have hsub : (Gx a ⊓ Gx x).subgroupOf (Gx a) = (Gx x).subgroupOf (Gx a) := by
    ext g
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩
  let e1 : ↥(Gxy a x) ≃* ↥(Gx a ⊓ Gx x) := MulEquiv.subgroupCongr (Gxy_eq_inf a x)
  let e2 : ↥(Gx a ⊓ Gx x) ≃* ↥((Gx a ⊓ Gx x).subgroupOf (Gx a)) :=
    (Subgroup.subgroupOfEquivOfLe (inf_le_left : Gx a ⊓ Gx x ≤ Gx a)).symm
  let e3 : ↥((Gx a ⊓ Gx x).subgroupOf (Gx a)) ≃* ↥((Gx x).subgroupOf (Gx a)) :=
    MulEquiv.subgroupCongr hsub
  let e4 : ↥((Gx x).subgroupOf (Gx a)) ≃*
      ↥(Subgroup.centralizer ({(⟨x, hx⟩ : ↥(Gx a))} : Set ↥(Gx a))) :=
    (MulEquiv.subgroupCongr hcentral).symm
  exact ⟨e1.trans (e2.trans (e3.trans e4))⟩

theorem isShapeTwoTwoSixS5_Gxy {G : Type} [Group G] {a : G} {z₀ b u : ↥(Gx a)}
    (h : TwoHSFacts ↥(Gx a) (GxSelf a) z₀ b u) : IsShapeTwoTwoSixS5 ↥(Gxy a (z₀ : G)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_Gxy (G := G) (a := a) (x := (z₀ : G)) z₀.2
  exact IsShapeTwoTwoSixS5.of_mulEquiv e.symm h.cent_z

theorem mem_derivedOf_of_facts {G : Type} [Group G] {a : G} {z₀ b u : ↥(Gx a)}
    (h : TwoHSFacts ↥(Gx a) (GxSelf a) z₀ b u) : (z₀ : G) ∈ derivedOf (Gx a) := by
  rw [derivedOf]
  exact Subgroup.mem_map.mpr ⟨z₀, h.mem_commutator.2.1, rfl⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
