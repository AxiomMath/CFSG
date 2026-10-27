module

public import CFSG.LieType.Chevalley.GraphFixedF4Canonical
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot

public noncomputable section

namespace CFSG.LieType.Chevalley.E6SecondGraphFixed

open CFSG.Blueprint CFSG.Blueprint.Chevalley

section General

variable {G : Type*} [Group G] {C J : Subgroup G} {P t : G}

@[expose] def SecondGraphFixedSubgroup (C J : Subgroup G) (P t : G) {H : Type*} [Group H]
    (e : J ≃* H) : Prop :=
  ∃ (htJ : t ∈ J) (hJC : J ≤ C) (η : MulAut C), (∀ g : C, (η g : G) = P * g * P⁻¹) ∧
    (∀ η' : MulAut C, (∀ g : C, (η' g : G) = P * g * P⁻¹) → η' = η) ∧
    (∀ g : C, ((MulAut.conj (⟨t, hJC htJ⟩ : C) * η) g : G) = t * (P * g * P⁻¹) * t⁻¹) ∧
    orderOf (MulAut.conj (⟨t, hJC htJ⟩ : C) * η) = 2 ∧
    (∀ g : C, (MulAut.conj (⟨t, hJC htJ⟩ : C) * η) g = g ↔ (g : G) ∈ J ∧ t * g = g * t) ∧
    (∀ φ : MulAut C, φ * η * φ⁻¹ ≠ MulAut.conj (⟨t, hJC htJ⟩ : C) * η) ∧
    orderOf (e ⟨t, htJ⟩) = 2 ∧
    (∀ x : J, (∃ hx : (x : G) ∈ C,
      (MulAut.conj (⟨t, hJC htJ⟩ : C) * η) ⟨x, hx⟩ = ⟨x, hx⟩) ↔
        e x * e ⟨t, htJ⟩ = e ⟨t, htJ⟩ * e x) ∧
    ∀ y : H, y * e ⟨t, htJ⟩ = e ⟨t, htJ⟩ * y ↔ ∃ x : J, (∃ hx : (x : G) ∈ C,
      (MulAut.conj (⟨t, hJC htJ⟩ : C) * η) ⟨x, hx⟩ = ⟨x, hx⟩) ∧ e x = y

theorem center_eq_bot_of_mulEquiv {H : Type*} [Group H] {M : Type*} [Group M] (e : M ≃* H)
    (hZ : Subgroup.center H = ⊥) : Subgroup.center M = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e z ∈ Subgroup.center H := Subgroup.mem_center_iff.2 fun y => by
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz x)]
  rw [hZ, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  exact e.injective (hz'.trans (map_one e).symm)

theorem mulAut_mul_conj {M : Type*} [Group M] (φ : MulAut M) (x : M) :
    φ * MulAut.conj x = MulAut.conj (φ x) * φ := by
  rw [← mulAut_mul_conj_mul_inv, inv_mul_cancel_right]

theorem secondGraphFixedSubgroup_of (hcan : CanonicalGraphFixedSubgroup C J P) (htJ : t ∈ J)
    (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (hint : ∀ g ∈ C, t * (P * g * P⁻¹) * t⁻¹ = g → P * g * P⁻¹ = g)
    {H : Type*} [Group H] (e : J ≃* H) (hZ : Subgroup.center H = ⊥) :
    SecondGraphFixedSubgroup C J P t e := by
  obtain ⟨η, hη, hη2, hJC, hfix, -⟩ := hcan
  set tC : C := ⟨t, hJC htJ⟩ with htC
  set ξ := MulAut.conj tC * η with hξ
  have htinv : t⁻¹ = t := (eq_inv_of_mul_eq_one_left ht2).symm
  have hξg : ∀ g : C, (ξ g : G) = t * (P * g * P⁻¹) * t⁻¹ := fun g => by
    change (tC * η g * tC⁻¹ : G) = _
    rw [Subgroup.coe_inv, hη]
  have hηt : η tC = tC := (hfix tC).2 htJ
  have ht2C : tC * tC = 1 := Subtype.ext ht2
  have hη2' : η * η = 1 := by rw [← pow_two, ← hη2, pow_orderOf_eq_one]
  have hfixξ : ∀ g : C, ξ g = g ↔ (g : G) ∈ J ∧ t * g = g * t := by
    intro g
    constructor
    · intro h
      have h' : t * (P * g * P⁻¹) * t⁻¹ = g := by rw [← hξg, h]
      have hPg := hint g g.2 h'
      rw [hPg] at h'
      refine ⟨(hfix g).1 (Subtype.ext ((hη g).trans hPg)), ?_⟩
      calc t * g = t * (t * g * t⁻¹) := by rw [h']
        _ = g * t := by rw [htinv, ← mul_assoc, ← mul_assoc, ht2, one_mul]
    · rintro ⟨hgJ, hgt⟩
      apply Subtype.ext
      have hPg : P * g * P⁻¹ = g := by rw [← hη, (hfix g).2 hgJ]
      rw [hξg, hPg, hgt, mul_inv_cancel_right]
  have hξ1 : ξ ≠ 1 := by
    intro h
    have hη1 : η ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hη2; exact absurd hη2 (by norm_num)
    obtain ⟨x, hx⟩ : ∃ x : C, η x ≠ x := by
      by_contra hcon
      exact hη1 (MulEquiv.ext fun x => not_not.1 fun h => hcon ⟨x, h⟩)
    have hxJ : (x : G) ∈ J := ((hfixξ x).1 (by rw [h]; rfl)).1
    exact hx ((hfix x).2 hxJ)
  have hξ2 : ξ ^ 2 = 1 := by
    rw [pow_two, hξ, mul_assoc, ← mul_assoc η, mulAut_mul_conj, hηt, mul_assoc, hη2',
      mul_one, ← map_mul, ht2C, map_one]
  have hZJ := center_eq_bot_of_mulEquiv e hZ
  have hnc : ∀ φ : MulAut C, φ * η * φ⁻¹ ≠ ξ := by
    intro φ hφ
    have hηφ : ∀ x : C, η (φ⁻¹ x) = φ⁻¹ (ξ x) := fun x => by
      rw [← hφ]
      simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    set τ := φ⁻¹ tC with hτ
    have hτfix : η τ = τ := by
      rw [hτ, hηφ, (hfixξ tC).2 ⟨htJ, rfl⟩]
    have hτJ : (τ : G) ∈ J := (hfix τ).1 hτfix
    have hτc : ∀ y : C, (y : G) ∈ J → τ * y = y * τ := by
      intro y hy
      have hξy : ξ (φ y) = φ y := by
        rw [← hφ]
        simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, (hfix y).2 hy]
      obtain ⟨-, hcomm⟩ := (hfixξ (φ y)).1 hξy
      have hcommC : tC * φ y = φ y * tC := Subtype.ext hcomm
      have := congrArg (fun z => φ⁻¹ z) hcommC
      simp only [map_mul, MulAut.inv_apply_self] at this
      exact this
    have hτZ : (⟨τ, hτJ⟩ : J) ∈ Subgroup.center J := Subgroup.mem_center_iff.2 fun x => by
      apply Subtype.ext
      have := hτc ⟨x, hJC x.2⟩ x.2
      exact (congrArg Subtype.val this).symm
    rw [hZJ, Subgroup.mem_bot] at hτZ
    have hτ1 : τ = 1 := Subtype.ext (congrArg (fun z : J => (z : G)) hτZ)
    have htC1 : tC = 1 := by
      have := congrArg φ hτ1
      rwa [hτ, MulAut.inv_apply, MulEquiv.apply_symm_apply, map_one] at this
    exact ht1 (congrArg Subtype.val htC1)
  have horder : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  have hident : ∀ x : J, (∃ hx : (x : G) ∈ C, ξ ⟨x, hx⟩ = ⟨x, hx⟩) ↔
      e x * e ⟨t, htJ⟩ = e ⟨t, htJ⟩ * e x := by
    intro x
    constructor
    · rintro ⟨hx, hξx⟩
      obtain ⟨-, hcomm⟩ := (hfixξ ⟨x, hx⟩).1 hξx
      have hJ : (⟨t, htJ⟩ : J) * x = x * ⟨t, htJ⟩ := Subtype.ext hcomm
      rw [← map_mul, ← map_mul, hJ]
    · intro h
      rw [← map_mul, ← map_mul] at h
      have hJ := e.injective h
      exact ⟨hJC x.2, (hfixξ ⟨x, hJC x.2⟩).2 ⟨x.2, (congrArg Subtype.val hJ).symm⟩⟩
  refine ⟨htJ, hJC, η, hη, fun η' hη' => MulEquiv.ext fun g => Subtype.ext ((hη' g).trans
    (hη g).symm), hξg, orderOf_eq_prime hξ2 hξ1, hfixξ, hnc, ?_, hident, fun y => ?_⟩
  · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, horder]
  · constructor
    · intro hy
      refine ⟨e.symm y, (hident _).2 ?_, e.apply_symm_apply y⟩
      rw [e.apply_symm_apply]
      exact hy
    · rintro ⟨x, hx, rfl⟩
      exact (hident x).1 hx

end General


section Cases

variable {E : Type} [Field E]

theorem pinnedX_e6HighestRoot_one_ne_one
    :
    pinnedX TwistTag.E6.tag E e6HighestRoot 1 ≠ 1 := fun h => by
  rw [← pinnedX_zero TwistTag.E6.tag E e6HighestRoot] at h
  exact one_ne_zero (pinnedX_injective (τ := TwistTag.E6.tag) (R := E) e6HighestRoot h)

theorem pinnedX_e6HighestRoot_mem_twistedFixedGroup
    (hE : ringChar E = 2) :
    pinnedX TwistTag.E6.tag E e6HighestRoot 1 ∈ twistedFixedGroup TwistTag.E6 E (RingHom.id E) := by
  obtain ⟨hC, hP, -⟩ := even_E6_highest_root_graph_fixed_centralizer_intersection E hE one_ne_zero
  exact mem_twistedFixedGroup_id_iff.2 ⟨hC, mul_inv_eq_iff_eq_mul.1 hP⟩

theorem pinnedX_e6HighestRoot_mul_self
    (hE : ringChar E = 2) :
    pinnedX TwistTag.E6.tag E e6HighestRoot 1 * pinnedX TwistTag.E6.tag E e6HighestRoot 1 = 1 := by
  obtain ⟨-, -, h, -⟩ := even_E6_highest_root_graph_fixed_centralizer_intersection E hE one_ne_zero
  rwa [pow_two] at h

theorem diagramMap_conj_eq_of_conj
    (hE : ringChar E = 2) {g : ModGL TwistTag.E6.tag E}
    (hg : g ∈ adjointGroup TwistTag.E6.tag E)
    (h : pinnedX TwistTag.E6.tag E e6HighestRoot 1 *
      (diagramMap TwistTag.E6 E * g * (diagramMap TwistTag.E6 E)⁻¹) *
        (pinnedX TwistTag.E6.tag E e6HighestRoot 1)⁻¹ = g) :
    diagramMap TwistTag.E6 E * g * (diagramMap TwistTag.E6 E)⁻¹ = g := by
  obtain ⟨-, -, -, hset⟩ :=
    even_E6_highest_root_graph_fixed_centralizer_intersection E hE one_ne_zero
  have hmem : g ∈ {g ∈ (adjointGroup TwistTag.E6.tag E : Set (ModGL TwistTag.E6.tag E)) |
      pinnedX TwistTag.E6.tag E e6HighestRoot 1 *
        (diagramMap TwistTag.E6 E * g * (diagramMap TwistTag.E6 E)⁻¹) *
          (pinnedX TwistTag.E6.tag E e6HighestRoot 1)⁻¹ = g} := ⟨hg, h⟩
  rw [hset] at hmem
  exact hmem.1.2

end Cases

theorem ringChar_eq_two_of_card {F : Type} [Field F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) : ringChar F = 2 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have : Fintype F := Fintype.ofFinite F
  exact FiniteField.even_card_iff_char_two.2 (by
    rw [← Nat.card_eq_fintype_card, hF, ← Nat.sub_add_cancel hn, pow_succ, Nat.mul_mod_left])

theorem _root_.CFSG.LieType.Chevalley.even_E6_twisted_E6_second_graph_fixed_subgroup
    (f : ℕ)
    (hf : 1 ≤ f) (k K : Type) [Field k] [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∃ ht : pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∈
        twistedFixedGroup TwistTag.E6 k (RingHom.id k),
      e6FixedToF4 k ⟨_, ht⟩ ∈ adjointGroup Tag.F4 k ∧ e6FixedToF4 k ⟨_, ht⟩ ≠ 1 ∧
      e6FixedToF4 k ⟨_, ht⟩ * e6FixedToF4 k ⟨_, ht⟩ = 1 ∧
      (∃ e : (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (RingHom.id k)) ≃*
          adjointGroup Tag.F4 k,
        (∀ (g : twistedFixedGroup TwistTag.E6 k (RingHom.id k))
          (x : (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (RingHom.id k))),
          (x : ModGL TwistTag.E6.tag k) = baseChangeGL (RingHom.id k) g →
            (e x : ModGL Tag.F4 k) = e6FixedToF4 k g) ∧
        (∀ htJ : pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∈
            (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (RingHom.id k)),
          (e ⟨_, htJ⟩ : ModGL Tag.F4 k) = e6FixedToF4 k ⟨_, ht⟩) ∧
        SecondGraphFixedSubgroup (adjointGroup TwistTag.E6.tag k)
          ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (RingHom.id k)))
          (diagramMap TwistTag.E6 k) (pinnedX TwistTag.E6.tag k e6HighestRoot 1) e) ∧
      (∃ e : (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
          (baseChangeGL (algebraMap k K)) ≃* adjointGroup Tag.F4 k,
        (∀ (g : twistedFixedGroup TwistTag.E6 k (RingHom.id k))
          (x : (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
            (baseChangeGL (algebraMap k K))),
          (x : ModGL TwistTag.E6.tag K) = baseChangeGL (algebraMap k K) g →
            (e x : ModGL Tag.F4 k) = e6FixedToF4 k g) ∧
        (∀ htJ : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈
            (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)),
          (e ⟨_, htJ⟩ : ModGL Tag.F4 k) = e6FixedToF4 k ⟨_, ht⟩) ∧
        SecondGraphFixedSubgroup (graphFixedRootGroup TwistTag.E6 K σ)
          ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)))
          (diagramMap TwistTag.E6 K) (pinnedX TwistTag.E6.tag K e6HighestRoot 1) e) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hk2 : ringChar k = 2 := ringChar_eq_two_of_card hf hk
  have hK2 : ringChar K = 2 := ringChar_eq_two_of_card (n := 2 * f) (by omega)
    (by rw [hK, ← pow_mul, mul_comm])
  have h2 : (2 : k) = 0 := two_eq_zero_of_ringChar hk2
  have hcan := even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf k K hk hK σ hσ
  obtain ⟨⟨hcan₁, e₁, he₁⟩, ⟨hcan₂, e₂, he₂⟩⟩ := hcan
  have ht := pinnedX_e6HighestRoot_mem_twistedFixedGroup hk2
  have hZ := center_adjointGroup_eq_bot (τ := Tag.F4) (K := k)
  have hs : e6FixedToF4 k ⟨_, ht⟩ = (e6FixedF4Equiv k h2 ⟨_, ht⟩ : ModGL Tag.F4 k) := rfl
  have hsne : e6FixedToF4 k ⟨_, ht⟩ ≠ 1 := by
    intro h1
    rw [hs] at h1
    have h1' : e6FixedF4Equiv k h2 ⟨_, ht⟩ = e6FixedF4Equiv k h2 1 := by
      rw [map_one]
      exact Subtype.ext h1
    have h3 := (e6FixedF4Equiv k h2).injective h1'
    have h4 : pinnedX TwistTag.E6.tag k e6HighestRoot 1 = 1 := by
      have := congrArg (fun z : twistedFixedGroup TwistTag.E6 k (RingHom.id k) =>
        (z : ModGL TwistTag.E6.tag k)) h3
      exact this
    exact pinnedX_e6HighestRoot_one_ne_one h4
  have hss : e6FixedToF4 k ⟨_, ht⟩ * e6FixedToF4 k ⟨_, ht⟩ = 1 := by
    rw [← map_mul]
    have : (⟨_, ht⟩ : twistedFixedGroup TwistTag.E6 k (RingHom.id k)) * ⟨_, ht⟩ = 1 :=
      Subtype.ext (pinnedX_e6HighestRoot_mul_self hk2)
    rw [this, map_one]
  refine ⟨ht, by rw [hs]; exact (e6FixedF4Equiv k h2 ⟨_, ht⟩).2, hsne, hss,
    ⟨e₁, he₁, fun htJ => he₁ _ _ ?_, ?_⟩, ⟨e₂, he₂, fun htJ => he₂ _ _ ?_, ?_⟩⟩
  · exact (baseChangeGL_id k _).symm
  · refine secondGraphFixedSubgroup_of hcan₁ ⟨_, ht, baseChangeGL_id k _⟩
      pinnedX_e6HighestRoot_one_ne_one (pinnedX_e6HighestRoot_mul_self hk2)
      (fun g hg h => diagramMap_conj_eq_of_conj hk2 hg h) e₁ hZ
  · rw [baseChangeGL_pinnedX, map_one]
  · refine secondGraphFixedSubgroup_of hcan₂ ⟨_, ht, by rw [baseChangeGL_pinnedX, map_one]⟩
      pinnedX_e6HighestRoot_one_ne_one (pinnedX_e6HighestRoot_mul_self hK2)
      (fun g hg h => diagramMap_conj_eq_of_conj hK2 (graphFixedRootGroup_le _ _ _ hg).1 h) e₂ hZ


end CFSG.LieType.Chevalley.E6SecondGraphFixed
