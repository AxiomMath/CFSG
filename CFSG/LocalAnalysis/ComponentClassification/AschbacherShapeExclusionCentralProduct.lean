module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherShapeExclusionCaseOne

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion

open Subgroup

variable {G : Type} [Group G]

theorem card_le_four_of_subset {X : Type*} [Group X] [Finite X] {E : Subgroup X} {a b c d : X}
    (hE : (E : Set X) ⊆ {a, b, c, d}) : Nat.card E ≤ 4 := by
  calc Nat.card E = Nat.card (E : Set X) := rfl
    _ ≤ Nat.card ({a, b, c, d} : Set X) := Nat.card_mono (Set.toFinite _) hE
    _ ≤ 4 := by
        rw [Nat.card_coe_set_eq]
        refine (Set.ncard_insert_le _ _).trans ?_
        refine (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1).trans ?_
        refine (Nat.add_le_add_right (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1) 1).trans ?_
        rw [Set.ncard_singleton]

namespace Config

variable {S : Subgroup G} {t x ρ : G} {k : ℕ}

theorem card_elem_le_four [Finite G] (h : Config S t x ρ k) {u : G} (huS : u ∈ S)
    (huM : u ∉ zpowers ρ ⊔ zpowers x) (hur : u * ρ * u⁻¹ = ρ⁻¹) (hux : u * x * u⁻¹ = x)
    {E : Subgroup G} (hES : E ≤ S) (hE : Assembly.IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  have hue := h.u_e_of_comm hur hux
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  by_cases hEM : ∀ g ∈ E, g ∈ zpowers ρ ⊔ zpowers x
  · refine card_le_four_of_subset (a := 1) (b := x ^ 2) (c := h.e) (d := x ^ 2 * h.e) ?_
    intro g hg
    rcases h.M_involution (hEM g hg) (hE.2 g hg) with rfl | rfl | rfl | rfl <;> simp
  · push Not at hEM
    obtain ⟨g, hgE, hgM⟩ := hEM
    have hm₁ := h.M_index_two.2.1 u huS g (hES hgE) huM hgM
    have hge : g * h.e * g⁻¹ = x ^ 2 * h.e := by
      have hcomm : (u⁻¹ * g) * h.e = h.e * (u⁻¹ * g) := h.M_comm hm₁ h.e_mem_M
      calc g * h.e * g⁻¹ = u * ((u⁻¹ * g) * h.e) * (u⁻¹ * g)⁻¹ * u⁻¹ := by group
        _ = u * h.e * u⁻¹ := by rw [hcomm]; group
        _ = x ^ 2 * h.e := hue
    have hEM' : ∀ w ∈ E, w ∈ zpowers ρ ⊔ zpowers x → w = 1 ∨ w = x ^ 2 := by
      intro w hwE hwM
      rcases h.M_involution hwM (hE.2 w hwE) with h1 | h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exfalso
        have hgw := hcommE g hgE w hwE
        rw [h1] at hgw
        have : g * h.e * g⁻¹ = h.e := by rw [hgw, mul_inv_cancel_right]
        rw [hge] at this
        apply h.x_sq_ne_one
        calc x ^ 2 = x ^ 2 * h.e * h.e⁻¹ := by group
          _ = 1 := by rw [this, mul_inv_cancel]
      · exfalso
        have hgw := hcommE g hgE w hwE
        rw [h1] at hgw
        have h2 : g * (x ^ 2 * h.e) * g⁻¹ = x ^ 2 * h.e := by rw [hgw, mul_inv_cancel_right]
        have hgx : g * x ^ 2 * g⁻¹ = x ^ 2 := by
          rw [← conj_pow]
          rcases h.conj_x (hES hgE) with hx | hx <;> rw [hx]
          rw [inv_pow, inv_eq_iff_mul_eq_one, ← pow_add]
          exact h.x_pow_four
        have h3 : g * (x ^ 2 * h.e) * g⁻¹ = (g * x ^ 2 * g⁻¹) * (g * h.e * g⁻¹) := by group
        rw [h3, hgx, hge] at h2
        apply h.x_sq_ne_one
        calc x ^ 2 = x ^ 2 * (x ^ 2 * h.e) * (x ^ 2 * h.e)⁻¹ := by group
          _ = 1 := by rw [h2, mul_inv_cancel]
    refine card_le_four_of_subset (a := 1) (b := x ^ 2) (c := g) (d := g * x ^ 2) ?_
    intro w hw
    by_cases hwM : w ∈ zpowers ρ ⊔ zpowers x
    · rcases hEM' w hw hwM with rfl | rfl <;> simp
    · have hm := h.M_index_two.2.1 g (hES hgE) w (hES hw) hgM hwM
      have hw' : w = g * (g⁻¹ * w) := by group
      rcases hEM' _ (mul_mem (inv_mem hgE) hw) hm with h1 | h1 <;> rw [hw', h1] <;> simp

end Config

namespace Setting

variable {A : Subgroup G} {S₀ : Sylow 2 A} {t x ρ : G} {k : ℕ}

theorem exists_elem_preimage [Finite G] (hs : Setting A S₀ t x ρ k)
    (htriv : ∀ w ∈ (S₀ : Subgroup A).map A.subtype, w ∈ centralizer (A : Set G) → w = 1)
    {E : Subgroup (A ⧸ center A)} (hET : E ≤ (sylowBar S₀ : Subgroup (A ⧸ center A)))
    (hE : Assembly.IsElemAbelian 2 E) :
    ∃ E' : Subgroup G, E' ≤ (S₀ : Subgroup A).map A.subtype ∧ Assembly.IsElemAbelian 2 E' ∧
      Nat.card E' = Nat.card E := by
  have hSA := hs.S_le_A
  set E' : Subgroup G :=
    (E.comap (QuotientGroup.mk' (center A))).map A.subtype ⊓ (S₀ : Subgroup A).map A.subtype
    with hE'
  have hmem : ∀ g : G, g ∈ E' ↔ g ∈ (S₀ : Subgroup A).map A.subtype ∧ bar A g ∈ E := by
    intro g
    constructor
    · intro hg
      obtain ⟨⟨a, ha, rfl⟩, hgS⟩ := mem_inf.1 hg
      refine ⟨hgS, ?_⟩
      change bar A (a : G) ∈ E
      rw [bar_of_mem a.2]
      exact ha
    · rintro ⟨hgS, hgE⟩
      refine mem_inf.2 ⟨⟨⟨g, hSA hgS⟩, ?_, rfl⟩, hgS⟩
      change QuotientGroup.mk' (center A) ⟨g, hSA hgS⟩ ∈ E
      rw [QuotientGroup.mk'_apply, ← bar_of_mem (hSA hgS)]
      exact hgE
  have hinj : ∀ {g g' : G}, g ∈ (S₀ : Subgroup A).map A.subtype →
      g' ∈ (S₀ : Subgroup A).map A.subtype → bar A g = bar A g' → g = g' :=
    fun hg hg' hgg' => bar_injective_of_trivial S₀ htriv hg hg' hgg'
  refine ⟨E', inf_le_right, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun g hg => ?_⟩, ?_⟩
  · obtain ⟨haS, haE⟩ := (hmem a).1 a.2
    obtain ⟨hbS, hbE⟩ := (hmem b).1 b.2
    apply hinj (mul_mem haS hbS) (mul_mem hbS haS)
    rw [bar_mul (hSA haS) (hSA hbS), bar_mul (hSA hbS) (hSA haS)]
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨_, haE⟩ ⟨_, hbE⟩)
  · obtain ⟨hgS, hgE⟩ := (hmem g).1 hg
    exact hinj (pow_mem hgS 2) (one_mem _) (by rw [bar_pow (hSA hgS), hE.2 _ hgE, bar_one])
  · refine Nat.card_eq_of_bijective (fun g => ⟨bar A g, ((hmem g).1 g.2).2⟩) ⟨?_, ?_⟩
    · intro g g' hgg'
      exact Subtype.ext (hinj ((hmem g).1 g.2).1 ((hmem g').1 g'.2).1
        (congrArg Subtype.val hgg'))
    · rintro ⟨q, hq⟩
      obtain ⟨g, hgS, rfl⟩ := (mem_sylowBar_iff S₀).1 (hET hq)
      exact ⟨⟨g, (hmem g).2 ⟨hgS, hq⟩⟩, rfl⟩

theorem false_of_caseIIb [Finite G] (hs : Setting A S₀ t x ρ k) {u : G}
    (huS : u ∈ (S₀ : Subgroup A).map A.subtype) (huM : u ∉ zpowers ρ ⊔ zpowers x)
    (hu2 : u ^ 2 = 1) (hux : u * x * u⁻¹ = x) : False := by
  have h := hs.config
  have : IsSimpleGroup (A ⧸ center A) := hs.quasi.2
  have hSA := hs.S_le_A
  obtain ⟨hur, -⟩ := h.involution_outside huS huM hu2
  have hxu : x * u = u * x := by
    calc x * u = u * x * u⁻¹ * u := by rw [hux]
      _ = u * x := by group
  have hxuS : x * u ∈ (S₀ : Subgroup A).map A.subtype := mul_mem h.x_mem huS
  have hxuM : x * u ∉ zpowers ρ ⊔ zpowers x := fun hm => huM (by
    have : u = x⁻¹ * (x * u) := by group
    rw [this]
    exact mul_mem (inv_mem (mem_sup_right (mem_zpowers x))) hm)
  have huρ : ∀ i : ℤ, (u * ρ ^ i) ^ 2 = 1 := fun i => by
    have hc : u * ρ ^ i * u⁻¹ = ρ ^ (-i) := by
      rw [← _root_.conj_zpow, hur, inv_zpow']
    calc (u * ρ ^ i) ^ 2 = (u * ρ ^ i * u⁻¹) * (u * u) * ρ ^ i := by rw [pow_two]; group
      _ = 1 := by rw [hc, ← pow_two, hu2, mul_one, ← zpow_add, neg_add_cancel, zpow_zero]
  have hcx : ∀ i : ℤ, Commute x (u * ρ ^ i) := fun i =>
    (Commute.mul_right hxu (Commute.zpow_right h.rho_x.symm i))
  have hxu2 : (x * u) ^ 2 = x ^ 2 := by
    have := huρ 0
    rw [zpow_zero, mul_one] at this
    rw [Commute.mul_pow hxu, this, mul_one]
  have hz : x ^ 2 ∉ centralizer (A : Set G) := by
    refine hs.x_sq_not_central_of_outside hxuS hxuM (hxu2 ▸ h.x_sq_mem) (fun i h1 => ?_)
    rw [mul_assoc, (hcx i).mul_pow, huρ i, mul_one] at h1
    exact h.x_sq_ne_one h1
  have htriv := (hs.central_trivial_or).resolve_left hz
  have hinj : ∀ {g g' : G}, g ∈ (S₀ : Subgroup A).map A.subtype →
      g' ∈ (S₀ : Subgroup A).map A.subtype → bar A g = bar A g' → g = g' :=
    fun hg hg' hgg' => bar_injective_of_trivial S₀ htriv hg hg' hgg'
  have hx2S : x ^ 2 ∈ (S₀ : Subgroup A).map A.subtype := pow_mem h.x_mem 2
  have heS := h.e_mem
  have hz2 : bar A (x ^ 2) ^ 2 = 1 := by rw [← bar_pow (hSA hx2S), hs.x_sq_sq, bar_one]
  have he2 : bar A h.e ^ 2 = 1 := by rw [← bar_pow (hSA heS), h.e_sq, bar_one]
  have hz1 : bar A (x ^ 2) ≠ 1 := fun h1 =>
    h.x_sq_ne_one (hinj hx2S (one_mem _) (h1.trans bar_one.symm))
  have he1 : bar A h.e ≠ 1 := fun h1 =>
    h.e_not_mem (hinj heS (one_mem _) (h1.trans bar_one.symm) ▸ one_mem _)
  have hez : bar A h.e ≠ bar A (x ^ 2) := fun h1 =>
    h.e_not_mem (hinj heS hx2S h1 ▸ h.x_sq_mem)
  have hzecomm : bar A (x ^ 2) * bar A h.e = bar A h.e * bar A (x ^ 2) := by
    rw [← bar_mul (hSA hx2S) (hSA heS), ← bar_mul (hSA heS) (hSA hx2S),
      h.M_comm (mem_sup_left h.x_sq_mem) h.e_mem_M]
  obtain ⟨hV, hV4, -⟩ := four_group hz2 he2 hz1 he1 hez hzecomm
  have hrank : Assembly.twoRank (A ⧸ center A) = 2 := by
    refine twoRank_eq_two (sylowBar S₀) hV hV4 fun E hET hE => ?_
    obtain ⟨E', hE'S, hE'el, hcard⟩ := hs.exists_elem_preimage htriv hET hE
    rw [← hcard]
    exact h.card_elem_le_four huS huM hur hux hE'S hE'el
  have hshape : IsRankTwoSylowShape (sylowBar S₀ : Subgroup (A ⧸ center A)) :=
    CFSG.RankTwoShapes.rank_two_sylow_shapes (nonabelian_bar hs.quasi) hrank (sylowBar S₀)
  have hxZ : ∀ g ∈ (S₀ : Subgroup A).map A.subtype, g * x = x * g := by
    intro g hg
    by_cases hgM : g ∈ zpowers ρ ⊔ zpowers x
    · exact h.M_comm hgM (mem_sup_right (mem_zpowers x))
    · have hm := h.M_index_two.2.1 u huS g hg huM hgM
      have hmx : (u⁻¹ * g) * x = x * (u⁻¹ * g) := h.M_comm hm (mem_sup_right (mem_zpowers x))
      calc g * x = u * ((u⁻¹ * g) * x) := by group
        _ = u * x * (u⁻¹ * g) := by rw [hmx]; group
        _ = x * g := by rw [← hxu]; group
  refine false_of_shape_central_four hshape
    (c := ⟨bar A x, bar_mem_sylowBar S₀ h.x_mem⟩)
    (a := ⟨bar A ρ, bar_mem_sylowBar S₀ h.rho_mem⟩)
    (b := ⟨bar A h.e, bar_mem_sylowBar S₀ heS⟩) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [mem_center_iff]
    rintro ⟨q, hq⟩
    obtain ⟨g, hgS, rfl⟩ := (mem_sylowBar_iff S₀).1 hq
    apply Subtype.ext
    change bar A g * bar A x = bar A x * bar A g
    rw [← bar_mul (hSA hgS) (hSA h.x_mem), ← bar_mul (hSA h.x_mem) (hSA hgS), hxZ g hgS]
  · intro h1
    apply hz1
    have := congrArg Subtype.val h1
    rw [bar_pow (hSA h.x_mem)]
    simpa using this
  · apply Subtype.ext
    change bar A ρ * bar A h.e = bar A h.e * bar A ρ
    rw [← bar_mul (hSA h.rho_mem) (hSA heS), ← bar_mul (hSA heS) (hSA h.rho_mem)]
    have := h.e_comm_zpow 1
    rw [zpow_one] at this
    rw [this]
  · exact Subtype.ext (by simpa using he2)
  · intro hmem
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hmem
    have hj' : bar A (ρ ^ j) = bar A h.e := by
      rw [bar_zpow (hSA h.rho_mem)]
      exact congrArg Subtype.val hj
    exact h.e_not_mem (hinj (zpow_mem h.rho_mem j) heS hj' ▸ zpow_mem (mem_zpowers ρ) j)
  · rw [hs.card_sylowBar_of_trivial htriv, Subgroup.orderOf_mk,
      orderOf_bar_of_trivial S₀ htriv h.rho_mem, h.rho_order, pow_add]
    ring

end Setting

end CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion
