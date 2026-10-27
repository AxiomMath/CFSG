module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.ModelStar
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.Recognition
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion

public section

namespace CFSG.EvenSporadicStandard.TwoFi22

open Subgroup CFSG.Sporadic.Fi23 CFSG.Blueprint.Fischer CFSG.Fischer

structure SquareFacts : Prop where
  d_ne_sq : ∀ w : J, w * w ≠ d
  sq_of_involution : ∀ x : J, x * d = d * x → x * x = 1 → x ≠ 1 → x ≠ d → x ∉ D23 →
    d * x ∉ D23 → ∃ w : J, w * d = d * w ∧ w * w = x

structure Model (G : Type) [Group G] (t : G) where
  ψ : centralizer ({t} : Set G) →* J
  inj : Function.Injective ψ
  range : ∀ c : J, c * d = d * c ↔ ∃ x, ψ x = c
  map_t : ψ ⟨t, mem_centralizer_singleton_iff.2 rfl⟩ = d

@[expose] def Dt {G : Type} [Group G] (t : G) : Set (centralizer ({t} : Set G)) :=
  {x | IsConj t (x : G) ∧ (x : G) ≠ t}

section

variable {G : Type} [Group G] {t : G}

theorem mul_self_of_orderOf_two {x : G} (hx : orderOf x = 2) : x * x = 1 := by
  rw [← sq, ← hx, pow_orderOf_eq_one]

theorem Dt_conj {x y : centralizer ({t} : Set G)} (hx : x ∈ Dt t) : y * x * y⁻¹ ∈ Dt t := by
  refine ⟨hx.1.trans (isConj_iff.2 ⟨(y : G), by simp⟩), fun h => hx.2 ?_⟩
  have hyt : (y : G) * t = t * (y : G) := mem_centralizer_singleton_iff.1 y.2
  have h' : (y : G) * (x : G) * (y : G)⁻¹ = t := h
  calc (x : G) = (y : G)⁻¹ * ((y : G) * (x : G) * (y : G)⁻¹) * (y : G) := by group
    _ = (y : G)⁻¹ * t * (y : G) := by rw [h']
    _ = (y : G)⁻¹ * (t * (y : G)) := by group
    _ = (y : G)⁻¹ * ((y : G) * t) := by rw [hyt]
    _ = t := by group

theorem Dt_mul_self (ht : orderOf t = 2) {x : centralizer ({t} : Set G)} (hx : x ∈ Dt t) :
    x * x = 1 :=
  Subtype.ext (mul_self_of_orderOf_two (orderOf_eq_two_of_isConj ht hx.1))

theorem Dt_ne_one (ht : orderOf t = 2) {x : centralizer ({t} : Set G)} (hx : x ∈ Dt t) :
    x ≠ 1 := by
  intro h
  have := orderOf_eq_two_of_isConj ht hx.1
  rw [show (x : G) = 1 from congrArg Subtype.val h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem not_sq (M : Model G t) (hF : SquareFacts)
    {x : centralizer ({t} : Set G)} (hx : IsConj t (x : G)) :
    ¬ ∃ w : centralizer ({t} : Set G), w * w = x := by
  rintro ⟨w, hw⟩
  obtain ⟨g, hg⟩ := isConj_iff.1 hx
  have hww : (w : G) * w = x := congrArg Subtype.val hw
  obtain ⟨u, hu_def⟩ : ∃ u : G, u = g⁻¹ * (w : G) * g := ⟨_, rfl⟩
  have hu : u * u = t := by
    calc u * u = g⁻¹ * ((w : G) * w) * g := by rw [hu_def]; group
      _ = g⁻¹ * (g * t * g⁻¹) * g := by rw [hww, hg]
      _ = t := by group
  have hut : u * t = t * u := by
    calc u * t = u * (u * u) := by rw [hu]
      _ = (u * u) * u := by group
      _ = t * u := by rw [hu]
  have hmem : u ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hut
  refine hF.d_ne_sq (M.ψ ⟨u, hmem⟩) ?_
  rw [← map_mul]
  have : (⟨u, hmem⟩ * ⟨u, hmem⟩ : centralizer ({t} : Set G)) =
      ⟨t, mem_centralizer_singleton_iff.2 rfl⟩ := Subtype.ext hu
  rw [this, M.map_t]

theorem psi_comm_d (M : Model G t) (x : centralizer ({t} : Set G)) :
    M.ψ x * d = d * M.ψ x :=
  (M.range _).2 ⟨x, rfl⟩

theorem psi_mem_star_or (M : Model G t) (hF : SquareFacts)
    (ht : orderOf t = 2) {x : centralizer ({t} : Set G)}
    (hx : x ∈ Dt t) : M.ψ x ∈ LocalClass D23 d ∨ InStar2 (M.ψ x) := by
  have hxd := psi_comm_d M x
  have hsq : M.ψ x * M.ψ x = 1 := by rw [← map_mul, Dt_mul_self ht hx, map_one]
  have hne1 : M.ψ x ≠ 1 := fun h => Dt_ne_one ht hx (M.inj (by rw [h, map_one]))
  have hned : M.ψ x ≠ d := fun h => hx.2 (by
    have := M.inj (h.trans M.map_t.symm)
    exact congrArg Subtype.val this)
  by_cases h1 : M.ψ x ∈ D23
  · exact Or.inl ⟨h1, hned, hxd⟩
  by_cases h2 : d * M.ψ x ∈ D23
  · refine Or.inr ⟨d * M.ψ x, ⟨h2, fun h => hne1 (mul_left_cancel (a := d) (by simpa using h)),
      ?_⟩, ?_⟩
    · calc d * M.ψ x * d = d * (M.ψ x * d) := by group
        _ = d * (d * M.ψ x) := by rw [hxd]
    · rw [← mul_assoc, d_sq, one_mul]
  exfalso
  obtain ⟨w, hwd, hww⟩ := hF.sq_of_involution _ hxd hsq hne1 hned h1 h2
  obtain ⟨v, rfl⟩ := (M.range w).1 hwd
  exact not_sq M hF hx.1 ⟨v, M.inj (by rw [map_mul, hww])⟩

theorem Dt_nonempty [IsSimpleGroup G] [Finite G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (ht : orderOf t = 2) : ∃ x, x ∈ Dt t := by
  obtain ⟨g, hne, hc⟩ := exists_fused_commuting_involution hnonab ht
  exact ⟨⟨g * t * g⁻¹, mem_centralizer_singleton_iff.2 hc⟩,
    isConj_iff.2 ⟨g, rfl⟩, hne⟩

theorem psi_image_conj (M : Model G t)
    {x : centralizer ({t} : Set G)} (hx : x ∈ Dt t) {c : J}
    (hc : c * d = d * c) : ∃ x' ∈ Dt t, M.ψ x' = c * M.ψ x * c⁻¹ := by
  obtain ⟨v, rfl⟩ := (M.range c).1 hc
  exact ⟨v * x * v⁻¹, Dt_conj hx, by simp [map_mul, map_inv]⟩


theorem star_subset_psi
    (M : Model G t) {x : centralizer ({t} : Set G)}
    (hx : x ∈ Dt t) (hA : M.ψ x ∈ LocalClass D23 d) :
    ∀ y ∈ LocalClass D23 d, ∃ x' ∈ Dt t, M.ψ x' = y := by
  intro y hy
  obtain ⟨c, hc, hcxy⟩ := star_conj_exists hA hy
  obtain ⟨x', hx', e⟩ := psi_image_conj M hx hc
  exact ⟨x', hx', e.trans hcxy⟩

theorem star2_subset_psi
    (M : Model G t) {x : centralizer ({t} : Set G)}
    (hx : x ∈ Dt t) (hA : InStar2 (M.ψ x)) :
    ∀ y, InStar2 y → ∃ x' ∈ Dt t, M.ψ x' = y := by
  intro y hy
  obtain ⟨c, hc, hcxy⟩ := star_conj_exists (d_mul_star2_mem_star hA) (d_mul_star2_mem_star hy)
  obtain ⟨x', hx', e⟩ := psi_image_conj M hx hc
  refine ⟨x', hx', e.trans ?_⟩
  apply mul_left_cancel (a := d)
  calc d * (c * M.ψ x * c⁻¹) = (d * c) * M.ψ x * c⁻¹ := by group
    _ = (c * d) * M.ψ x * c⁻¹ := by rw [hc]
    _ = c * (d * M.ψ x) * c⁻¹ := by group
    _ = d * y := hcxy

theorem mul_three_self {Γ : Type*} [Group Γ] {a b c : Γ} (ha : a * a = 1) (hb : b * b = 1)
    (hc : c * c = 1) (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    a * b * c * (a * b * c) = 1 := by
  calc a * b * c * (a * b * c) = a * b * (c * a) * b * c := by group
    _ = a * b * (a * c) * b * c := by rw [hac]
    _ = a * (b * a) * c * b * c := by group
    _ = a * (a * b) * c * b * c := by rw [hab]
    _ = (a * a) * b * (c * b) * c := by group
    _ = (a * a) * b * (b * c) * c := by rw [hbc]
    _ = (a * a) * (b * b) * (c * c) := by group
    _ = 1 := by rw [ha, hb, hc, one_mul, one_mul]

theorem exists_sq_triple
    (hF : SquareFacts) {x1 x2 : J} (hx1 : x1 ∈ LocalClass D23 d) (hx2 : x2 ∈ LocalClass D23 d)
    (hx21 : x2 ∈ LocalClass D23 x1) : ∃ w : J, w * d = d * w ∧ w * w = d * x1 * x2 := by
  have hxd1 : x1 * d = d * x1 := hx1.2.2
  have hxd2 : x2 * d = d * x2 := hx2.2.2
  have hsq : d * x1 * x2 * (d * x1 * x2) = 1 :=
    mul_three_self (Γ := J) d_sq (mul_self_of_mem_star hx1) (mul_self_of_mem_star hx2)
      hxd1.symm hxd2.symm hx21.2.2.symm
  refine hF.sq_of_involution (d * x1 * x2) ?_ hsq ?_ ?_ (not_mem_D23_mul_triple hx1 hx2 hx21) ?_
  · calc d * x1 * x2 * d = d * x1 * (x2 * d) := by group
      _ = d * x1 * (d * x2) := by rw [hxd2]
      _ = d * (x1 * d) * x2 := by group
      _ = d * (d * x1) * x2 := by rw [hxd1]
      _ = d * (d * x1 * x2) := by group
  · intro h
    have h' : x1 * x2 = d := by
      calc x1 * x2 = (d * d) * x1 * x2 := by rw [d_sq, one_mul]
        _ = d * (d * x1 * x2) := by group
        _ = d * 1 := by rw [h]
        _ = d := mul_one d
    exact not_mem_D23_mul_pair hx1 hx21 (by show IsConj d (x1 * x2); rw [h'])
  · intro h
    have h' : x1 * x2 = x1 * x1 := by
      apply mul_left_cancel (a := d)
      calc d * (x1 * x2) = d * x1 * x2 := by group
        _ = d := h
        _ = d * (x1 * x1) := by rw [mul_self_of_mem_star hx1, mul_one]
    exact hx21.2.1 (mul_left_cancel h')
  · have : d * (d * x1 * x2) = x1 * x2 := by
      calc d * (d * x1 * x2) = (d * d) * x1 * x2 := by group
        _ = x1 * x2 := by rw [d_sq, one_mul]
    rw [this]
    exact not_mem_D23_mul_pair hx1 hx21

theorem not_both
    (M : Model G t) (hF : SquareFacts) (ht : orderOf t = 2)
    (h1 : ∀ y ∈ LocalClass D23 d, ∃ x ∈ Dt t, M.ψ x = y)
    (h2 : ∀ y, InStar2 y → ∃ x ∈ Dt t, M.ψ x = y) : False := by
  obtain ⟨x1, x2, hx1, hx2, hx21⟩ := exists_star_pair
  obtain ⟨X1, hX1, e1⟩ := h1 x1 hx1
  obtain ⟨X2, hX2, e2⟩ := h1 x2 hx2
  obtain ⟨Z, hZ, eZ⟩ := h2 (d * x1) (star_mul_mem_star2 hx1)
  let tL : centralizer ({t} : Set G) := ⟨t, mem_centralizer_singleton_iff.2 rfl⟩
  have htL : ∀ y : centralizer ({t} : Set G), y * tL = tL * y := fun y =>
    Subtype.ext (mem_centralizer_singleton_iff.1 y.2)
  have hZe : Z = tL * X1 := M.inj (by rw [eZ, map_mul, M.map_t, e1])
  have hc21 : X2 * X1 = X1 * X2 := M.inj (by rw [map_mul, map_mul, e1, e2]; exact hx21.2.2)
  have hc2Z : X2 * Z = Z * X2 := by
    rw [hZe]
    calc X2 * (tL * X1) = (X2 * tL) * X1 := by rw [mul_assoc]
      _ = (tL * X2) * X1 := by rw [htL X2]
      _ = tL * (X2 * X1) := by rw [mul_assoc]
      _ = tL * (X1 * X2) := by rw [hc21]
      _ = (tL * X1) * X2 := by rw [mul_assoc]
  have hc2Z' : (X2 : G) * Z = Z * X2 := congrArg Subtype.val hc2Z
  obtain ⟨g, hg⟩ := isConj_iff.1 hZ.1
  obtain ⟨y', hy'_def⟩ : ∃ y' : G, y' = g⁻¹ * (X2 : G) * g := ⟨_, rfl⟩
  have hy'comm : y' * t = t * y' := by
    have ht' : g⁻¹ * (Z : G) * g = t := by rw [← hg]; group
    calc y' * t = y' * (g⁻¹ * (Z : G) * g) := by rw [ht']
      _ = g⁻¹ * ((X2 : G) * Z) * g := by rw [hy'_def]; group
      _ = g⁻¹ * (Z * (X2 : G)) * g := by rw [hc2Z']
      _ = (g⁻¹ * (Z : G) * g) * y' := by rw [hy'_def]; group
      _ = t * y' := by rw [ht']
  have hy'mem : y' ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hy'comm
  have hconj_y' : IsConj t y' := by
    rw [hy'_def]
    exact hX2.1.trans (isConj_iff.2 ⟨g⁻¹, by simp⟩)
  have hy'ne : y' ≠ t := by
    intro h
    have hXZ : X2 = Z := Subtype.ext (by
      calc (X2 : G) = g * y' * g⁻¹ := by rw [hy'_def]; group
        _ = g * t * g⁻¹ := by rw [h]
        _ = Z := hg)
    exact star_ne_d_mul_star hx1 hx21 (by rw [← e2, hXZ, eZ])
  have hy'D : (⟨y', hy'mem⟩ : centralizer ({t} : Set G)) ∈ Dt t := ⟨hconj_y', hy'ne⟩
  obtain ⟨w, hwD, hw⟩ : ∃ w ∈ Dt t, M.ψ w = d * M.ψ ⟨y', hy'mem⟩ := by
    rcases psi_mem_star_or M hF ht hy'D with h | h
    · exact h2 _ (star_mul_mem_star2 h)
    · exact h1 _ (d_mul_star2_mem_star h)
  have hwe : w = tL * ⟨y', hy'mem⟩ := M.inj (by rw [hw, map_mul, M.map_t])
  have hty : IsConj t (t * y') := by
    have := hwD.1
    rwa [hwe] at this
  have hD : IsConj t (((tL * X1 * X2 : centralizer ({t} : Set G)) : G)) := by
    have e : (((tL * X1 * X2 : centralizer ({t} : Set G)) : G)) = g * (t * y') * g⁻¹ := by
      have hZ' : (Z : G) = t * (X1 : G) := by rw [hZe]; rfl
      calc (((tL * X1 * X2 : centralizer ({t} : Set G)) : G)) = (Z : G) * X2 := by rw [← hZe]; rfl
        _ = (g * t * g⁻¹) * (g * y' * g⁻¹) := by rw [hg, hy'_def]; group
        _ = g * (t * y') * g⁻¹ := by group
    rw [e]
    exact hty.trans (isConj_iff.2 ⟨g, rfl⟩)
  obtain ⟨w', hw'd, hw'w⟩ := exists_sq_triple hF hx1 hx2 hx21
  obtain ⟨v, rfl⟩ := (M.range w').1 hw'd
  exact not_sq M hF hD ⟨v, M.inj (by rw [map_mul, hw'w, map_mul, map_mul, M.map_t, e1, e2])⟩

theorem Dt_eq
    [IsSimpleGroup G] [Finite G] (M : Model G t) (hF : SquareFacts)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (ht : orderOf t = 2) :
    (∀ x : centralizer ({t} : Set G), x ∈ Dt t ↔ M.ψ x ∈ LocalClass D23 d) ∨
      (∀ x : centralizer ({t} : Set G), x ∈ Dt t ↔ InStar2 (M.ψ x)) := by
  obtain ⟨x0, hx0⟩ := Dt_nonempty hnonab ht
  rcases psi_mem_star_or M hF ht hx0 with h | h
  · left
    have h1 := star_subset_psi M hx0 h
    intro x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · rcases psi_mem_star_or M hF ht hx with h' | h'
      · exact h'
      · exact (not_both M hF ht h1 (star2_subset_psi M hx h')).elim
    · obtain ⟨x', hx', e⟩ := h1 _ hx
      rwa [← M.inj e]
  · right
    have h2 := star2_subset_psi M hx0 h
    intro x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · rcases psi_mem_star_or M hF ht hx with h' | h'
      · exact (not_both M hF ht (star_subset_psi M hx h') h2).elim
      · exact h'
    · obtain ⟨x', hx', e⟩ := h2 _ hx
      rwa [← M.inj e]

theorem Dt_eq_starSet
    [IsSimpleGroup G] [Finite G] (M : Model G t) (hF : SquareFacts)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (ht : orderOf t = 2) :
    ∃ ε : Bool, ∀ x : centralizer ({t} : Set G), x ∈ Dt t ↔ M.ψ x ∈ starSet ε := by
  rcases Dt_eq M hF hnonab ht with h | h
  · exact ⟨false, fun x => (h x).trans mem_starSet_false.symm⟩
  · exact ⟨true, fun x => (h x).trans mem_starSet_true.symm⟩

end

end CFSG.EvenSporadicStandard.TwoFi22
