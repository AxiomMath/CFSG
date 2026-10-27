module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SteinbergBQRankOneConjugateSpanHead

public section

namespace CFSG.QuasithinUnique

open Module

namespace SteinbergBQ.RankOneSplit

open SteinbergBQ.RankOne SteinbergBQ.RankOneHead

variable {F W : Type*} [Field F] [AddCommGroup W] [Module F W]

theorem apply_mem_of_range_le {g : LinearMap.GeneralLinearGroup F W} {U : Submodule F W}
    (h : LinearMap.range ((g : W →ₗ[F] W) - 1) ≤ U) {u : W} (hu : u ∈ U) :
    (g : W →ₗ[F] W) u ∈ U := by
  have h1 : (g : W →ₗ[F] W) u = u + ((g : W →ₗ[F] W) - 1) u := by
    rw [LinearMap.sub_apply, Module.End.one_apply]
    abel
  rw [h1]
  exact U.add_mem hu (h (LinearMap.mem_range_self _ u))

theorem inv_apply_mem_of_range_le {g : LinearMap.GeneralLinearGroup F W} {U : Submodule F W}
    (h : LinearMap.range ((g : W →ₗ[F] W) - 1) ≤ U) {u : W} (hu : u ∈ U) :
    ((g⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) u ∈ U := by
  set y := ((g⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) u
  have h1 : y = u - ((g : W →ₗ[F] W) - 1) y := by
    rw [LinearMap.sub_apply, Module.End.one_apply, apply_inv_apply]
    abel
  rw [h1]
  exact U.sub_mem hu (h (LinearMap.mem_range_self _ y))

theorem apply_eq_of_mem_ker {g : LinearMap.GeneralLinearGroup F W} {u : W}
    (hu : u ∈ LinearMap.ker ((g : W →ₗ[F] W) - 1)) : (g : W →ₗ[F] W) u = u := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hu
  exact hu

theorem inv_apply_eq_of_mem_ker {g : LinearMap.GeneralLinearGroup F W} {u : W}
    (hu : u ∈ LinearMap.ker ((g : W →ₗ[F] W) - 1)) :
    ((g⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) u = u := by
  conv_lhs => rw [← apply_eq_of_mem_ker hu]
  exact inv_apply_apply g u

theorem closure_preserves' {S : Set (LinearMap.GeneralLinearGroup F W)} {U : Submodule F W}
    (hS : ∀ g ∈ S, LinearMap.range ((g : W →ₗ[F] W) - 1) ≤ U ∨
      U ≤ LinearMap.ker ((g : W →ₗ[F] W) - 1))
    {n : LinearMap.GeneralLinearGroup F W} (hn : n ∈ Subgroup.closure S) :
    ∀ u ∈ U, (n : W →ₗ[F] W) u ∈ U := by
  induction hn using Subgroup.closure_induction'' with
  | mem g hg =>
    intro u hu
    rcases hS g hg with h1 | h1
    · exact apply_mem_of_range_le h1 hu
    · rw [apply_eq_of_mem_ker (h1 hu)]
      exact hu
  | inv_mem g hg =>
    intro u hu
    rcases hS g hg with h1 | h1
    · exact inv_apply_mem_of_range_le h1 hu
    · rw [inv_apply_eq_of_mem_ker (h1 hu)]
      exact hu
  | one =>
    intro u hu
    exact hu
  | mul x y _ _ hx hy =>
    intro u hu
    rw [mul_apply']
    exact hx _ (hy u hu)

theorem closure_fixes {S : Set (LinearMap.GeneralLinearGroup F W)} {U : Submodule F W}
    (hS : ∀ g ∈ S, U ≤ LinearMap.ker ((g : W →ₗ[F] W) - 1))
    {n : LinearMap.GeneralLinearGroup F W} (hn : n ∈ Subgroup.closure S) :
    ∀ u ∈ U, (n : W →ₗ[F] W) u = u := by
  induction hn using Subgroup.closure_induction'' with
  | mem g hg =>
    intro u hu
    exact apply_eq_of_mem_ker (hS g hg hu)
  | inv_mem g hg =>
    intro u hu
    exact inv_apply_eq_of_mem_ker (hS g hg hu)
  | one =>
    intro u _
    rfl
  | mul x y _ _ hx hy =>
    intro u hu
    rw [mul_apply', hy u hu, hx u hu]

theorem eq_one_of_fixes {ι : Type*} {U : ι → Submodule F W} (hU : ⨆ i, U i = ⊤)
    {n : LinearMap.GeneralLinearGroup F W} (hn : ∀ i, ∀ u ∈ U i, (n : W →ₗ[F] W) u = u) :
    n = 1 := by
  have h1 : (⨆ i, U i) ≤ LinearMap.ker ((n : W →ₗ[F] W) - 1) :=
    iSup_le fun i u hu => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hn i u hu, sub_self]
  rw [hU, top_le_iff, LinearMap.ker_eq_top, sub_eq_zero] at h1
  exact Units.ext h1

theorem eq_of_agree {ι : Type*} {U : ι → Submodule F W} (hU : ⨆ i, U i = ⊤)
    {x y : LinearMap.GeneralLinearGroup F W}
    (h : ∀ i, ∀ u ∈ U i, (x : W →ₗ[F] W) u = (y : W →ₗ[F] W) u) : x = y := by
  have h1 : (⨆ i, U i) ≤ LinearMap.ker ((x : W →ₗ[F] W) - (y : W →ₗ[F] W)) :=
    iSup_le fun i u hu => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, h i u hu, sub_self]
  rw [hU, top_le_iff, LinearMap.ker_eq_top, sub_eq_zero] at h1
  exact Units.ext h1

theorem conj_sub_one (h g : LinearMap.GeneralLinearGroup F W) :
    ((h * g * h⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) - 1 =
      (h : W →ₗ[F] W) * ((g : W →ₗ[F] W) - 1) *
        ((h⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) := by
  have hh : (h : W →ₗ[F] W) * ((h⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Units.val_mul]
  rw [mul_sub, sub_mul, mul_one, hh]

theorem range_conj (h g : LinearMap.GeneralLinearGroup F W) :
    LinearMap.range (((h * g * h⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) - 1) =
      (LinearMap.range ((g : W →ₗ[F] W) - 1)).map (h : W →ₗ[F] W) := by
  rw [conj_sub_one, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
    LinearMap.range_comp_of_range_eq_top, LinearMap.range_comp]
  exact LinearMap.range_eq_top.2 fun v => ⟨(h : W →ₗ[F] W) v, inv_apply_apply h v⟩

theorem mem_ker_conj (h g : LinearMap.GeneralLinearGroup F W) (u : W) :
    u ∈ LinearMap.ker (((h * g * h⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) - 1) ↔
      ((h⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) u ∈
        LinearMap.ker ((g : W →ₗ[F] W) - 1) := by
  rw [LinearMap.mem_ker, LinearMap.mem_ker, conj_sub_one, Module.End.mul_apply,
    Module.End.mul_apply]
  constructor
  · intro h1
    rw [← map_zero (h : W →ₗ[F] W)] at h1
    exact injective_apply h h1
  · intro h1
    rw [h1, map_zero]

theorem finrank_range_conj (h g : LinearMap.GeneralLinearGroup F W) :
    finrank F (LinearMap.range (((h * g * h⁻¹ : LinearMap.GeneralLinearGroup F W) :
      W →ₗ[F] W) - 1)) = finrank F (LinearMap.range ((g : W →ₗ[F] W) - 1)) := by
  rw [range_conj, finrank_map_of_disjoint]
  rw [Submodule.disjoint_def]
  intro e _ he
  exact injective_apply h (by rw [LinearMap.mem_ker.1 he, map_zero])

@[expose] def conjSet (H : Subgroup (LinearMap.GeneralLinearGroup F W))
    (t : LinearMap.GeneralLinearGroup F W) : Set (LinearMap.GeneralLinearGroup F W) :=
  {x | ∃ h ∈ H, x = h * t * h⁻¹}

@[expose] def edgeRel (D : Set (LinearMap.GeneralLinearGroup F W))
    (x y : LinearMap.GeneralLinearGroup F W) : Prop :=
  x ∈ D ∧ y ∈ D ∧ ((x : W →ₗ[F] W) - 1) * ((y : W →ₗ[F] W) - 1) ≠ 0

@[expose] def compSet (D : Set (LinearMap.GeneralLinearGroup F W))
    (x : LinearMap.GeneralLinearGroup F W) : Set (LinearMap.GeneralLinearGroup F W) :=
  {y | y ∈ D ∧ Relation.ReflTransGen (edgeRel D) x y}

@[expose] def comp (D : Set (LinearMap.GeneralLinearGroup F W))
    (x : LinearMap.GeneralLinearGroup F W) : Submodule F W :=
  ⨆ y ∈ compSet D x, LinearMap.range ((y : W →ₗ[F] W) - 1)

theorem conj_mem_conjSet {H : Subgroup (LinearMap.GeneralLinearGroup F W)}
    {t g : LinearMap.GeneralLinearGroup F W} (hg : g ∈ H) {x : LinearMap.GeneralLinearGroup F W}
    (hx : x ∈ conjSet H t) : g * x * g⁻¹ ∈ conjSet H t := by
  obtain ⟨h, hh, rfl⟩ := hx
  exact ⟨g * h, H.mul_mem hg hh, by group⟩

theorem mem_conjSet_self {H : Subgroup (LinearMap.GeneralLinearGroup F W)}
    {t : LinearMap.GeneralLinearGroup F W} : t ∈ conjSet H t :=
  ⟨1, H.one_mem, by group⟩

theorem reach_conj {D : Set (LinearMap.GeneralLinearGroup F W)}
    {g : LinearMap.GeneralLinearGroup F W} (hgD : ∀ x ∈ D, g * x * g⁻¹ ∈ D)
    {x y : LinearMap.GeneralLinearGroup F W} (h : Relation.ReflTransGen (edgeRel D) x y) :
    Relation.ReflTransGen (edgeRel D) (g * x * g⁻¹) (g * y * g⁻¹) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    refine ih.tail ⟨hgD b hbc.1, hgD c hbc.2.1, ?_⟩
    rw [conj_sub_one, conj_sub_one]
    intro h0
    apply hbc.2.2
    have h1 : ((g⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) *
        ((g : W →ₗ[F] W) * ((b : W →ₗ[F] W) - 1) *
          ((g⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) *
        ((g : W →ₗ[F] W) * ((c : W →ₗ[F] W) - 1) *
          ((g⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W))) *
        (g : W →ₗ[F] W) = ((b : W →ₗ[F] W) - 1) * ((c : W →ₗ[F] W) - 1) := by
      have hgi : ((g⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) *
          (g : W →ₗ[F] W) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      calc _ = (((g⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) * (g : W →ₗ[F] W)) *
            ((b : W →ₗ[F] W) - 1) *
            (((g⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) * (g : W →ₗ[F] W)) *
            ((c : W →ₗ[F] W) - 1) *
            (((g⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) * (g : W →ₗ[F] W)) := by
            simp only [mul_assoc]
        _ = _ := by rw [hgi, one_mul, mul_one, mul_one]
    rw [← h1, h0, mul_zero, zero_mul]

theorem reach_symm {H : Subgroup (LinearMap.GeneralLinearGroup F W)} [Finite H]
    {t : LinearMap.GeneralLinearGroup F W} {x y : LinearMap.GeneralLinearGroup F W}
    (hx : x ∈ conjSet H t) (hy : y ∈ conjSet H t)
    (hxy : Relation.ReflTransGen (edgeRel (conjSet H t)) x y) :
    Relation.ReflTransGen (edgeRel (conjSet H t)) y x := by
  obtain ⟨h₁, hh₁, rfl⟩ := hx
  obtain ⟨h₂, hh₂, rfl⟩ := hy
  set g := h₂ * h₁⁻¹ with hg
  have hgH : g ∈ H := H.mul_mem hh₂ (H.inv_mem hh₁)
  set x := h₁ * t * h₁⁻¹ with hx
  have hyx : h₂ * t * h₂⁻¹ = g * x * g⁻¹ := by rw [hg, hx]; group
  rw [hyx] at hxy ⊢
  have hpow : ∀ k : ℕ, g ^ k ∈ H := fun k => H.pow_mem hgH k
  have hstep : ∀ k : ℕ, Relation.ReflTransGen (edgeRel (conjSet H t)) x
      (g ^ k * x * (g ^ k)⁻¹) := by
    intro k
    induction k with
    | zero => simpa using Relation.ReflTransGen.refl
    | succ k ih =>
      refine ih.trans ?_
      have h1 := reach_conj (fun z hz => conj_mem_conjSet (hpow k) hz) hxy
      have h2 : g ^ k * (g * x * g⁻¹) * (g ^ k)⁻¹ = g ^ (k + 1) * x * (g ^ (k + 1))⁻¹ := by
        rw [pow_succ]
        group
      rwa [h2] at h1
  set m := orderOf (⟨g, hgH⟩ : H) with hm
  have hm0 : 0 < m := orderOf_pos _
  have hgm : g ^ m = 1 := by
    have h1 := pow_orderOf_eq_one (⟨g, hgH⟩ : H)
    rw [← hm] at h1
    have h2 := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
  have hginv : g ^ (m - 1) = g⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hm0, hgm]
  have h1 := hstep (m - 1)
  rw [hginv, inv_inv] at h1
  have h2 := reach_conj (fun z hz => conj_mem_conjSet hgH hz) h1
  have h3 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rwa [h3] at h2

section Summands

variable {H : Subgroup (LinearMap.GeneralLinearGroup F W)} {t : LinearMap.GeneralLinearGroup F W}

theorem finrank_range_of_mem_conjSet
    (hrank : finrank F (LinearMap.range ((t : W →ₗ[F] W) - 1)) = 1)
    {x : LinearMap.GeneralLinearGroup F W} (hx : x ∈ conjSet H t) :
    finrank F (LinearMap.range ((x : W →ₗ[F] W) - 1)) = 1 := by
  obtain ⟨h, _, rfl⟩ := hx
  rw [finrank_range_conj, hrank]

theorem range_le_of_apply_ne [FiniteDimensional F W] {a : LinearMap.GeneralLinearGroup F W}
    (ha : finrank F (LinearMap.range ((a : W →ₗ[F] W) - 1)) = 1) {U : Submodule F W}
    (hinv : ∀ u ∈ U, (a : W →ₗ[F] W) u ∈ U) {e : W} (he : e ∈ U)
    (hae : ((a : W →ₗ[F] W) - 1) e ≠ 0) : LinearMap.range ((a : W →ₗ[F] W) - 1) ≤ U := by
  have h1 : ((a : W →ₗ[F] W) - 1) e ∈ U := by
    rw [LinearMap.sub_apply, Module.End.one_apply]
    exact U.sub_mem (hinv e he) he
  rw [eq_span_of_finrank_eq_one ha (LinearMap.mem_range_self _ e) hae]
  exact (Submodule.span_singleton_le_iff_mem _ U).2 h1

theorem iSup_range_eq_top
    (hirr : ∀ U : Submodule F W, (∀ h ∈ H, ∀ u ∈ U, (h : W →ₗ[F] W) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hrank : finrank F (LinearMap.range ((t : W →ₗ[F] W) - 1)) = 1) :
    ⨆ x ∈ conjSet H t, LinearMap.range ((x : W →ₗ[F] W) - 1) = ⊤ := by
  have hinv : ∀ h ∈ H, ∀ u ∈ ⨆ x ∈ conjSet H t, LinearMap.range ((x : W →ₗ[F] W) - 1),
      (h : W →ₗ[F] W) u ∈ ⨆ x ∈ conjSet H t, LinearMap.range ((x : W →ₗ[F] W) - 1) := by
    intro h hh u hu
    have h1 : (⨆ x ∈ conjSet H t, LinearMap.range ((x : W →ₗ[F] W) - 1)).map
        (h : W →ₗ[F] W) ≤ ⨆ x ∈ conjSet H t, LinearMap.range ((x : W →ₗ[F] W) - 1) := by
      simp only [Submodule.map_iSup]
      refine iSup₂_le fun x hx => ?_
      rw [← range_conj]
      exact le_iSup₂_of_le (h * x * h⁻¹) (conj_mem_conjSet hh hx) le_rfl
    exact h1 ⟨u, hu, rfl⟩
  rcases hirr _ hinv with h1 | h1
  · exfalso
    have h2 : LinearMap.range ((t : W →ₗ[F] W) - 1) ≤
        ⨆ x ∈ conjSet H t, LinearMap.range ((x : W →ₗ[F] W) - 1) :=
      le_iSup₂_of_le t mem_conjSet_self le_rfl
    rw [h1, le_bot_iff] at h2
    rw [h2, finrank_bot] at hrank
    exact absurd hrank (by norm_num)
  · exact h1

theorem iInf_ker_eq_bot
    (hirr : ∀ U : Submodule F W, (∀ h ∈ H, ∀ u ∈ U, (h : W →ₗ[F] W) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hrank : finrank F (LinearMap.range ((t : W →ₗ[F] W) - 1)) = 1) :
    ⨅ x ∈ conjSet H t, LinearMap.ker ((x : W →ₗ[F] W) - 1) = ⊥ := by
  have hinv : ∀ h ∈ H, ∀ u ∈ ⨅ x ∈ conjSet H t, LinearMap.ker ((x : W →ₗ[F] W) - 1),
      (h : W →ₗ[F] W) u ∈ ⨅ x ∈ conjSet H t, LinearMap.ker ((x : W →ₗ[F] W) - 1) := by
    intro h hh u hu
    simp only [Submodule.mem_iInf] at hu ⊢
    intro x hx
    have hx' : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
    rw [hx', mem_ker_conj, inv_apply_apply]
    have h1 := conj_mem_conjSet (H.inv_mem hh) hx
    rw [inv_inv] at h1
    exact hu _ h1
  rcases hirr _ hinv with h1 | h1
  · exact h1
  · exfalso
    have h2 : (⨅ x ∈ conjSet H t, LinearMap.ker ((x : W →ₗ[F] W) - 1)) ≤
        LinearMap.ker ((t : W →ₗ[F] W) - 1) := iInf₂_le t mem_conjSet_self
    rw [h1, top_le_iff, LinearMap.ker_eq_top] at h2
    rw [h2, LinearMap.range_zero, finrank_bot] at hrank
    exact absurd hrank (by norm_num)

theorem exists_apply_ne
    (hirr : ∀ U : Submodule F W, (∀ h ∈ H, ∀ u ∈ U, (h : W →ₗ[F] W) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hrank : finrank F (LinearMap.range ((t : W →ₗ[F] W) - 1)) = 1) {u : W} (hu : u ≠ 0) :
    ∃ z ∈ conjSet H t, ((z : W →ₗ[F] W) - 1) u ≠ 0 := by
  by_contra h1
  push Not at h1
  have h2 : u ∈ ⨅ x ∈ conjSet H t, LinearMap.ker ((x : W →ₗ[F] W) - 1) := by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    exact h1
  rw [iInf_ker_eq_bot hirr hrank] at h2
  exact hu ((Submodule.mem_bot F).1 h2)

theorem self_mem_compSet {D : Set (LinearMap.GeneralLinearGroup F W)}
    {x : LinearMap.GeneralLinearGroup F W} (hx : x ∈ D) : x ∈ compSet D x :=
  ⟨hx, Relation.ReflTransGen.refl⟩

theorem range_le_comp {D : Set (LinearMap.GeneralLinearGroup F W)}
    {x y : LinearMap.GeneralLinearGroup F W} (hy : y ∈ compSet D x) :
    LinearMap.range ((y : W →ₗ[F] W) - 1) ≤ comp D x :=
  le_iSup₂_of_le y hy le_rfl

theorem comp_le_ker [Finite H] {x y : LinearMap.GeneralLinearGroup F W} (hy : y ∈ conjSet H t)
    (hxy : ¬ Relation.ReflTransGen (edgeRel (conjSet H t)) x y) :
    comp (conjSet H t) x ≤ LinearMap.ker ((y : W →ₗ[F] W) - 1) := by
  refine iSup₂_le fun a ha => ?_
  obtain ⟨ha, hxa⟩ := ha
  by_contra h1
  have h2 : ((y : W →ₗ[F] W) - 1) * ((a : W →ₗ[F] W) - 1) ≠ 0 := by
    intro h3
    apply h1
    rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_ker, ← Module.End.mul_apply, h3, LinearMap.zero_apply]
  exact hxy (hxa.trans (reach_symm hy ha (Relation.ReflTransGen.single ⟨hy, ha, h2⟩)))

theorem range_le_or_le_ker [Finite H] {x y : LinearMap.GeneralLinearGroup F W}
    (hy : y ∈ conjSet H t) :
    LinearMap.range ((y : W →ₗ[F] W) - 1) ≤ comp (conjSet H t) x ∨
      comp (conjSet H t) x ≤ LinearMap.ker ((y : W →ₗ[F] W) - 1) := by
  by_cases hxy : Relation.ReflTransGen (edgeRel (conjSet H t)) x y
  · exact Or.inl (range_le_comp ⟨hy, hxy⟩)
  · exact Or.inr (comp_le_ker hy hxy)

theorem closure_preserves_comp [Finite H] (x : LinearMap.GeneralLinearGroup F W)
    {n : LinearMap.GeneralLinearGroup F W} (hn : n ∈ Subgroup.closure (conjSet H t)) :
    ∀ w ∈ comp (conjSet H t) x, (n : W →ₗ[F] W) w ∈ comp (conjSet H t) x :=
  closure_preserves' (fun _ hy => range_le_or_le_ker hy) hn

theorem compSet_eq [Finite H] {x y : LinearMap.GeneralLinearGroup F W} (hx : x ∈ conjSet H t)
    (hy : y ∈ conjSet H t) (hxy : Relation.ReflTransGen (edgeRel (conjSet H t)) x y) :
    compSet (conjSet H t) x = compSet (conjSet H t) y := by
  ext z
  constructor
  · rintro ⟨hz, hxz⟩
    exact ⟨hz, (reach_symm hx hy hxy).trans hxz⟩
  · rintro ⟨hz, hyz⟩
    exact ⟨hz, hxy.trans hyz⟩

theorem comp_eq_of_reach [Finite H] {x y : LinearMap.GeneralLinearGroup F W}
    (hx : x ∈ conjSet H t) (hy : y ∈ conjSet H t)
    (hxy : Relation.ReflTransGen (edgeRel (conjSet H t)) x y) :
    comp (conjSet H t) x = comp (conjSet H t) y := by
  rw [comp, comp, compSet_eq hx hy hxy]

theorem disjoint_comp [Finite H]
    (hirr : ∀ U : Submodule F W, (∀ h ∈ H, ∀ u ∈ U, (h : W →ₗ[F] W) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hrank : finrank F (LinearMap.range ((t : W →ₗ[F] W) - 1)) = 1)
    {x : LinearMap.GeneralLinearGroup F W} {U : Submodule F W}
    (hU : ∀ z ∈ compSet (conjSet H t) x, U ≤ LinearMap.ker ((z : W →ₗ[F] W) - 1)) :
    Disjoint (comp (conjSet H t) x) U := by
  rw [Submodule.disjoint_def]
  intro w hw hwU
  have h1 : w ∈ ⨅ z ∈ conjSet H t, LinearMap.ker ((z : W →ₗ[F] W) - 1) := by
    simp only [Submodule.mem_iInf]
    intro z hz
    by_cases hxz : Relation.ReflTransGen (edgeRel (conjSet H t)) x z
    · exact hU z ⟨hz, hxz⟩ hwU
    · exact comp_le_ker hz hxz hw
  rwa [iInf_ker_eq_bot hirr hrank, Submodule.mem_bot] at h1

theorem disjoint_comp_comp [Finite H]
    (hirr : ∀ U : Submodule F W, (∀ h ∈ H, ∀ u ∈ U, (h : W →ₗ[F] W) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hrank : finrank F (LinearMap.range ((t : W →ₗ[F] W) - 1)) = 1)
    {x y : LinearMap.GeneralLinearGroup F W} (hy : y ∈ conjSet H t)
    (hxy : ¬ Relation.ReflTransGen (edgeRel (conjSet H t)) x y) :
    Disjoint (comp (conjSet H t) x) (comp (conjSet H t) y) := by
  refine disjoint_comp hirr hrank fun z hz => comp_le_ker hz.1 fun hyz => ?_
  exact hxy (hz.2.trans (reach_symm hy hz.1 hyz))

theorem comp_ne_bot (hrank : finrank F (LinearMap.range ((t : W →ₗ[F] W) - 1)) = 1)
    {x : LinearMap.GeneralLinearGroup F W} (hx : x ∈ conjSet H t) :
    comp (conjSet H t) x ≠ ⊥ := by
  intro h1
  have h2 := range_le_comp (self_mem_compSet hx)
  rw [h1, le_bot_iff] at h2
  have h3 := finrank_range_of_mem_conjSet hrank hx
  rw [h2, finrank_bot] at h3
  exact absurd h3 (by norm_num)

theorem range_le_comp_iff [Finite H]
    (hirr : ∀ U : Submodule F W, (∀ h ∈ H, ∀ u ∈ U, (h : W →ₗ[F] W) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hrank : finrank F (LinearMap.range ((t : W →ₗ[F] W) - 1)) = 1)
    {x y : LinearMap.GeneralLinearGroup F W} (hy : y ∈ conjSet H t) :
    LinearMap.range ((y : W →ₗ[F] W) - 1) ≤ comp (conjSet H t) x ↔
      Relation.ReflTransGen (edgeRel (conjSet H t)) x y := by
  refine ⟨fun h1 => ?_, fun h => range_le_comp ⟨hy, h⟩⟩
  by_contra hxy
  have h2 := disjoint_comp_comp hirr hrank hy hxy
  have h3 : LinearMap.range ((y : W →ₗ[F] W) - 1) = ⊥ :=
    le_bot_iff.1 ((le_inf h1 (range_le_comp (self_mem_compSet hy))).trans h2.le_bot)
  have h4 := finrank_range_of_mem_conjSet hrank hy
  rw [h3, finrank_bot] at h4
  exact absurd h4 (by norm_num)

theorem comp_le_of_range_le [FiniteDimensional F W] [Finite H]
    (hrank : finrank F (LinearMap.range ((t : W →ₗ[F] W) - 1)) = 1)
    {x : LinearMap.GeneralLinearGroup F W} (hx : x ∈ conjSet H t) {U : Submodule F W}
    (hinv : ∀ y ∈ compSet (conjSet H t) x, ∀ u ∈ U, (y : W →ₗ[F] W) u ∈ U)
    {z : LinearMap.GeneralLinearGroup F W} (hz : z ∈ compSet (conjSet H t) x)
    (hzU : LinearMap.range ((z : W →ₗ[F] W) - 1) ≤ U) : comp (conjSet H t) x ≤ U := by
  have hall : ∀ a, Relation.ReflTransGen (edgeRel (conjSet H t)) a z →
      a ∈ compSet (conjSet H t) x → LinearMap.range ((a : W →ₗ[F] W) - 1) ≤ U := by
    intro a haz
    induction haz using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun _ => hzU
    | @head a b hab _ ih =>
      intro ha
      have hbU := ih ⟨hab.2.1, ha.2.tail hab⟩
      obtain ⟨e, he⟩ : ∃ e, ((a : W →ₗ[F] W) - 1) (((b : W →ₗ[F] W) - 1) e) ≠ 0 := by
        by_contra h
        push Not at h
        exact hab.2.2 (LinearMap.ext fun e => by rw [Module.End.mul_apply, h e]; rfl)
      exact range_le_of_apply_ne (finrank_range_of_mem_conjSet hrank ha.1) (hinv a ha)
        (hbU (LinearMap.mem_range_self _ e)) he
  refine iSup₂_le fun a ha => hall a ?_ ha
  exact (reach_symm hx ha.1 ha.2).trans hz.2

theorem comp_irreducible [FiniteDimensional F W] [Finite H]
    (hirr : ∀ U : Submodule F W, (∀ h ∈ H, ∀ u ∈ U, (h : W →ₗ[F] W) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hrank : finrank F (LinearMap.range ((t : W →ₗ[F] W) - 1)) = 1)
    {x : LinearMap.GeneralLinearGroup F W} (hx : x ∈ conjSet H t) {U : Submodule F W}
    (hUle : U ≤ comp (conjSet H t) x)
    (hinv : ∀ y ∈ compSet (conjSet H t) x, ∀ u ∈ U, (y : W →ₗ[F] W) u ∈ U) :
    U = ⊥ ∨ U = comp (conjSet H t) x := by
  by_cases hU : U = ⊥
  · exact Or.inl hU
  right
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  obtain ⟨z, hz, hzu⟩ := exists_apply_ne hirr hrank hu0
  have hxz : Relation.ReflTransGen (edgeRel (conjSet H t)) x z := by
    by_contra hxz
    exact hzu (comp_le_ker hz hxz (hUle huU))
  refine le_antisymm hUle (comp_le_of_range_le hrank hx hinv ⟨hz, hxz⟩ ?_)
  exact range_le_of_apply_ne (finrank_range_of_mem_conjSet hrank hz)
    (hinv z ⟨hz, hxz⟩) huU hzu

theorem eq_comp_of_irreducible [FiniteDimensional F W] [Finite H]
    (hirr : ∀ U : Submodule F W, (∀ h ∈ H, ∀ u ∈ U, (h : W →ₗ[F] W) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hrank : finrank F (LinearMap.range ((t : W →ₗ[F] W) - 1)) = 1) {U : Submodule F W}
    (hU0 : U ≠ ⊥)
    (hUinv : ∀ n ∈ Subgroup.closure (conjSet H t), ∀ u ∈ U, (n : W →ₗ[F] W) u ∈ U)
    (hUirr : ∀ U' : Submodule F W, U' ≤ U →
      (∀ n ∈ Subgroup.closure (conjSet H t), ∀ u ∈ U', (n : W →ₗ[F] W) u ∈ U') →
        U' = ⊥ ∨ U' = U) :
    ∃ z ∈ conjSet H t, U = comp (conjSet H t) z := by
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  obtain ⟨z, hz, hzu⟩ := exists_apply_ne hirr hrank hu0
  have hinv : ∀ y ∈ compSet (conjSet H t) z, ∀ w ∈ U, (y : W →ₗ[F] W) w ∈ U :=
    fun y hy => hUinv y (Subgroup.subset_closure hy.1)
  have hle : comp (conjSet H t) z ≤ U :=
    comp_le_of_range_le hrank hz hinv (self_mem_compSet hz)
      (range_le_of_apply_ne (finrank_range_of_mem_conjSet hrank hz)
        (hUinv z (Subgroup.subset_closure hz)) huU hzu)
  rcases hUirr _ hle fun n hn => closure_preserves_comp z hn with h1 | h1
  · exact absurd h1 (comp_ne_bot hrank hz)
  · exact ⟨z, hz, h1.symm⟩

theorem map_comp {h : LinearMap.GeneralLinearGroup F W} (hh : h ∈ H)
    (x : LinearMap.GeneralLinearGroup F W) :
    (comp (conjSet H t) x).map (h : W →ₗ[F] W) = comp (conjSet H t) (h * x * h⁻¹) := by
  rw [comp, comp]
  simp only [Submodule.map_iSup]
  apply le_antisymm
  · refine iSup₂_le fun y hy => ?_
    rw [← range_conj]
    exact le_iSup₂_of_le (h * y * h⁻¹) ⟨conj_mem_conjSet hh hy.1,
      reach_conj (fun z hz => conj_mem_conjSet hh hz) hy.2⟩ le_rfl
  · refine iSup₂_le fun y hy => ?_
    have hy' : h⁻¹ * y * h ∈ compSet (conjSet H t) x := by
      refine ⟨by simpa using conj_mem_conjSet (H.inv_mem hh) hy.1, ?_⟩
      have h1 := reach_conj (fun z hz => conj_mem_conjSet (H.inv_mem hh) hz) hy.2
      have h2 : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
      rwa [h2, inv_inv] at h1
    have h3 : y = h * (h⁻¹ * y * h) * h⁻¹ := by group
    rw [h3, range_conj]
    exact le_iSup₂_of_le (h⁻¹ * y * h) hy' le_rfl

end Summands

@[expose] def fixer (U : Submodule F W) : Subgroup (LinearMap.GeneralLinearGroup F W) where
  carrier := {g | ∀ u ∈ U, (g : W →ₗ[F] W) u = u}
  one_mem' _ _ := rfl
  mul_mem' {a b} ha hb u hu := by
    change ((a * b : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) u = u
    rw [mul_apply', hb u hu, ha u hu]
  inv_mem' {a} ha u hu := by
    change ((a⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) u = u
    conv_lhs => rw [← ha u hu]
    exact inv_apply_apply a u

theorem mem_fixer {U : Submodule F W} {g : LinearMap.GeneralLinearGroup F W} :
    g ∈ fixer U ↔ ∀ u ∈ U, (g : W →ₗ[F] W) u = u :=
  Iff.rfl

theorem commute_closure {G : Type*} [Group G] {S T : Set G}
    (h : ∀ a ∈ S, ∀ b ∈ T, a * b = b * a) {a b : G} (ha : a ∈ Subgroup.closure S)
    (hb : b ∈ Subgroup.closure T) : a * b = b * a := by
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure T : Set G) := by
    rw [Subgroup.closure_le]
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro b hb
    have h2 : Subgroup.closure T ≤ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.closure_le]
      intro b hb
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (h a ha b hb).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (h2 hb)
  exact (Subgroup.mem_centralizer_iff.1 (h1 ha) b hb).symm

theorem exists_mul_of_mem_sup {G : Type*} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : G} (hg : g ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
  let P : Subgroup G :=
    { carrier := {g | ∃ a ∈ A, ∃ b ∈ B, g = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by group⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [h a' ha' b hb]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        rw [mul_inv_rev]
        exact (h _ (A.inv_mem ha) _ (B.inv_mem hb)).symm }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by group⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by group⟩)
  exact hle hg

theorem exists_enumeration {H : Subgroup (LinearMap.GeneralLinearGroup F W)} [Finite H]
    (t : LinearMap.GeneralLinearGroup F W) :
    ∃ (s : ℕ) (hs : 1 ≤ s) (Wi : Fin s → Submodule F W), Function.Injective Wi ∧
      (∀ i, ∃ x ∈ conjSet H t, Wi i = comp (conjSet H t) x) ∧
      (∀ x ∈ conjSet H t, ∃ i, Wi i = comp (conjSet H t) x) ∧
      Wi ⟨0, hs⟩ = comp (conjSet H t) t := by
  classical
  have hfin : (conjSet H t).Finite :=
    (Set.finite_range fun h : H => (h : LinearMap.GeneralLinearGroup F W) * t *
      (h : LinearMap.GeneralLinearGroup F W)⁻¹).subset (by
        rintro _ ⟨h, hh, rfl⟩
        exact ⟨⟨h, hh⟩, rfl⟩)
  set S : Finset (Submodule F W) := hfin.toFinset.image (comp (conjSet H t)) with hS
  have hmem : ∀ x ∈ conjSet H t, comp (conjSet H t) x ∈ S := fun x hx =>
    Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 hx)
  have hs : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hmem t mem_conjSet_self⟩
  set e := S.equivFin with he
  set i₀ := e ⟨_, hmem t mem_conjSet_self⟩ with hi₀
  set σ := Equiv.swap (⟨0, hs⟩ : Fin S.card) i₀ with hσ
  refine ⟨S.card, hs, fun i => (e.symm (σ i) : Submodule F W), ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact σ.injective (e.symm.injective (Subtype.ext hij))
  · intro i
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.1 (e.symm (σ i)).2
    exact ⟨x, hfin.mem_toFinset.1 hx, hxe.symm⟩
  · intro x hx
    refine ⟨σ.symm (e ⟨_, hmem x hx⟩), ?_⟩
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  · simp only [hσ, Equiv.swap_apply_left, hi₀, Equiv.symm_apply_apply]

end SteinbergBQ.RankOneSplit

open SteinbergBQ.RankOne SteinbergBQ.RankOneHead SteinbergBQ.RankOneSplit

theorem rank_one_normal_closure_splits_irreducible_summands {F W : Type*} [Field F]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] [Nontrivial W]
    (H : Subgroup (LinearMap.GeneralLinearGroup F W)) [Finite H]
    (hirr : ∀ U : Submodule F W, (∀ h ∈ H, ∀ u ∈ U, (h : W →ₗ[F] W) u ∈ U) → U = ⊥ ∨ U = ⊤)
    {t : LinearMap.GeneralLinearGroup F W} (_ht : t ∈ H)
    (hrank : finrank F (LinearMap.range ((t : W →ₗ[F] W) - 1)) = 1)
    {N : Subgroup (LinearMap.GeneralLinearGroup F W)}
    (hN : N = Subgroup.closure {x | ∃ h ∈ H, x = h * t * h⁻¹}) :
    ∃ (s : ℕ) (hs : 1 ≤ s) (Wi : Fin s → Submodule F W),
      DirectSum.IsInternal Wi ∧ (∀ i, Wi i ≠ ⊥) ∧
      (∀ i, ∀ n ∈ N, ∀ w ∈ Wi i, (n : W →ₗ[F] W) w ∈ Wi i) ∧
      (∀ i, ∀ U : Submodule F W, U ≤ Wi i → (∀ n ∈ N, ∀ u ∈ U, (n : W →ₗ[F] W) u ∈ U) →
        U = ⊥ ∨ U = Wi i) ∧
      (∀ i j, i ≠ j → ∀ e : Wi i ≃ₗ[F] Wi j, ¬ ∀ n ∈ N, ∀ w w' : Wi i,
        (w' : W) = (n : W →ₗ[F] W) w → ((e w' : Wi j) : W) = (n : W →ₗ[F] W) (e w)) ∧
      (∀ (r : ℕ) (W' : Fin r → Submodule F W), DirectSum.IsInternal W' → (∀ k, W' k ≠ ⊥) →
        (∀ k, ∀ n ∈ N, ∀ w ∈ W' k, (n : W →ₗ[F] W) w ∈ W' k) →
        (∀ k, ∀ U : Submodule F W, U ≤ W' k → (∀ n ∈ N, ∀ u ∈ U, (n : W →ₗ[F] W) u ∈ U) →
          U = ⊥ ∨ U = W' k) →
        Set.range W' = Set.range Wi) ∧
      (∀ h ∈ H, ∀ i, ∃ j, (Wi i).map (h : W →ₗ[F] W) = Wi j) ∧
      (∀ i j, ∃ h ∈ H, (Wi i).map (h : W →ₗ[F] W) = Wi j) ∧
      ∀ Ni : Fin s → Subgroup (LinearMap.GeneralLinearGroup F W),
        (∀ i n, n ∈ Ni i ↔ n ∈ N ∧ ∀ j, j ≠ i → ∀ w ∈ Wi j, (n : W →ₗ[F] W) w = w) →
        (∀ i j, i ≠ j → ∀ x ∈ Ni i, ∀ y ∈ Ni j, x * y = y * x) ∧
        (⨆ i, Ni i) = N ∧ iSupIndep Ni ∧
        (∀ i, ∀ n ∈ Ni i, (∀ w ∈ Wi i, (n : W →ₗ[F] W) w = w) → n = 1) ∧
        (∀ i, ∀ U : Submodule F W, U ≤ Wi i →
          (∀ n ∈ Ni i, ∀ u ∈ U, (n : W →ₗ[F] W) u ∈ U) → U = ⊥ ∨ U = Wi i) ∧
        (∀ i, Ni i = Subgroup.closure {x | (∃ h ∈ H, x = h * t * h⁻¹) ∧
          ∃ w ∈ Wi i, (x : W →ₗ[F] W) w ≠ w}) ∧
        (∀ i x, (∃ h ∈ H, x = h * t * h⁻¹) → (∃ w ∈ Wi i, (x : W →ₗ[F] W) w ≠ w) →
          finrank F ((Wi i).map ((x : W →ₗ[F] W) - 1)) = 1) ∧
        t ∈ Ni ⟨0, hs⟩ ∧
        (∀ h ∈ H, ∀ i j, (Wi i).map (h : W →ₗ[F] W) = Wi j →
          (Ni i).map (MulAut.conj h).toMonoidHom = Ni j) ∧
        (∀ i j, ∃ h ∈ H, (Wi i).map (h : W →ₗ[F] W) = Wi j ∧
          (Ni i).map (MulAut.conj h).toMonoidHom = Ni j) := by
  classical
  subst hN
  have hDdef : {x | ∃ h ∈ H, x = h * t * h⁻¹} = conjSet H t := rfl
  rw [hDdef]
  set D := conjSet H t with hD
  obtain ⟨s, hs, Wi, hinj, hex, hof, h0⟩ := exists_enumeration (H := H) t
  have htD : t ∈ D := mem_conjSet_self
  have hdiff : ∀ i j x y, Wi i = comp D x → Wi j = comp D y → x ∈ D → y ∈ D → i ≠ j →
      ¬ Relation.ReflTransGen (edgeRel D) x y := by
    intro i j x y hxi hyj hx hy hij hxy
    exact hij (hinj (by rw [hxi, hyj, comp_eq_of_reach hx hy hxy]))
  have hnontriv : ∀ x ∈ D, ∃ w ∈ comp D x, ((x : W →ₗ[F] W) - 1) w ≠ 0 := by
    intro x hx
    by_contra h1
    push Not at h1
    have h2 : (⊤ : Submodule F W) ≤ LinearMap.ker ((x : W →ₗ[F] W) - 1) := by
      rw [← iSup_range_eq_top hirr hrank]
      refine iSup₂_le fun z hz => (range_le_comp (self_mem_compSet hz)).trans ?_
      by_cases hzx : Relation.ReflTransGen (edgeRel D) z x
      · rw [comp_eq_of_reach hz hx hzx]
        exact fun w hw => h1 w hw
      · exact comp_le_ker hx hzx
    rw [top_le_iff, LinearMap.ker_eq_top] at h2
    have h3 := finrank_range_of_mem_conjSet hrank hx
    rw [h2, LinearMap.range_zero, finrank_bot] at h3
    exact absurd h3 (by norm_num)
  have htop : ⨆ i, Wi i = ⊤ := by
    rw [eq_top_iff, ← iSup_range_eq_top hirr hrank]
    refine iSup₂_le fun y hy => ?_
    obtain ⟨i, hi⟩ := hof y hy
    exact (range_le_comp (self_mem_compSet hy)).trans ((le_of_eq hi.symm).trans (le_iSup Wi i))
  have hind : iSupIndep Wi := by
    rw [iSupIndep_def]
    intro i
    obtain ⟨x, hx, hxi⟩ := hex i
    rw [hxi]
    refine disjoint_comp hirr hrank fun z hz => iSup₂_le fun j hj => ?_
    obtain ⟨y, hy, hyj⟩ := hex j
    rw [hyj]
    refine comp_le_ker hz.1 fun hyz => ?_
    exact hdiff j i y x hyj hxi hy hx hj (hyz.trans (reach_symm hx hz.1 hz.2))
  have hpres : ∀ i, ∀ n ∈ Subgroup.closure D, ∀ w ∈ Wi i, (n : W →ₗ[F] W) w ∈ Wi i := by
    intro i n hn
    obtain ⟨x, _, hxi⟩ := hex i
    rw [hxi]
    exact closure_preserves_comp x hn
  have hne : ∀ i, Wi i ≠ ⊥ := by
    intro i
    obtain ⟨x, hx, hxi⟩ := hex i
    rw [hxi]
    exact comp_ne_bot hrank hx
  have hΓfix : ∀ i, ∀ y ∈ D, LinearMap.range ((y : W →ₗ[F] W) - 1) ≤ Wi i →
      ∀ j, j ≠ i → ∀ w ∈ Wi j, (y : W →ₗ[F] W) w = w := by
    intro i y hy hyi j hji w hw
    obtain ⟨x, hx, hxi⟩ := hex i
    obtain ⟨z, hz, hzj⟩ := hex j
    rw [hxi, range_le_comp_iff hirr hrank hy] at hyi
    rw [hzj] at hw
    refine apply_eq_of_mem_ker (comp_le_ker hy (fun hzy => ?_) hw)
    exact hdiff j i z x hzj hxi hz hx hji (hzy.trans (reach_symm hx hy hyi))
  have hΓkill : ∀ i, ∀ y ∈ D, ¬ LinearMap.range ((y : W →ₗ[F] W) - 1) ≤ Wi i →
      Wi i ≤ LinearMap.ker ((y : W →ₗ[F] W) - 1) := by
    intro i y hy hyi
    obtain ⟨x, _, hxi⟩ := hex i
    rw [hxi] at hyi ⊢
    rw [range_le_comp_iff hirr hrank hy] at hyi
    exact comp_le_ker hy hyi
  have hΓnontriv : ∀ i, ∀ y ∈ D, (∃ w ∈ Wi i, (y : W →ₗ[F] W) w ≠ w) ↔
      LinearMap.range ((y : W →ₗ[F] W) - 1) ≤ Wi i := by
    intro i y hy
    constructor
    · rintro ⟨w, hw, hyw⟩
      by_contra h1
      exact hyw (apply_eq_of_mem_ker (hΓkill i y hy h1 hw))
    · intro h1
      obtain ⟨x, hx, hxi⟩ := hex i
      have h2 := h1
      rw [hxi, range_le_comp_iff hirr hrank hy] at h2
      obtain ⟨w, hw, hyw⟩ := hnontriv y hy
      refine ⟨w, ?_, ?_⟩
      · rw [hxi, comp_eq_of_reach hx hy h2]
        exact hw
      · intro h3
        apply hyw
        rw [LinearMap.sub_apply, Module.End.one_apply, h3, sub_self]
  refine ⟨s, hs, Wi, DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop, hne,
    hpres, ?_, ?_, ?_, ?_, ?_, fun Ni hNi => ?_⟩
  ·
    intro i U hUle hU
    obtain ⟨x, hx, hxi⟩ := hex i
    rw [hxi] at hUle ⊢
    exact comp_irreducible hirr hrank hx hUle fun y hy => hU y (Subgroup.subset_closure hy.1)
  ·
    intro i j hij e he
    obtain ⟨x, hx, hxi⟩ := hex i
    obtain ⟨y, hy, hyj⟩ := hex j
    obtain ⟨w, hw, hxw⟩ := hnontriv x hx
    rw [← hxi] at hw
    have hxW : (x : W →ₗ[F] W) w ∈ Wi i := hpres i x (Subgroup.subset_closure hx) w hw
    have h1 := he x (Subgroup.subset_closure hx) ⟨w, hw⟩ ⟨(x : W →ₗ[F] W) w, hxW⟩ rfl
    have h2 : (x : W →ₗ[F] W) (e ⟨w, hw⟩ : W) = (e ⟨w, hw⟩ : W) := by
      have h3 : (e ⟨w, hw⟩ : W) ∈ comp D y := by
        rw [← hyj]
        exact (e ⟨w, hw⟩).2
      exact apply_eq_of_mem_ker (comp_le_ker hx (hdiff j i y x hyj hxi hy hx (Ne.symm hij)) h3)
    rw [h2] at h1
    have h4 : (⟨(x : W →ₗ[F] W) w, hxW⟩ : Wi i) = ⟨w, hw⟩ := e.injective (Subtype.ext h1)
    apply hxw
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    exact congrArg Subtype.val h4
  ·
    intro r W' hW'int hW'ne hW'inv hW'irr
    have hsub : ∀ k, ∃ i, W' k = Wi i := by
      intro k
      obtain ⟨z, hz, hzk⟩ :=
        eq_comp_of_irreducible hirr hrank (hW'ne k) (hW'inv k) (hW'irr k)
      obtain ⟨i, hi⟩ := hof z hz
      exact ⟨i, hzk.trans hi.symm⟩
    ext U
    constructor
    · rintro ⟨k, rfl⟩
      obtain ⟨i, hi⟩ := hsub k
      exact ⟨i, hi.symm⟩
    · rintro ⟨i, rfl⟩
      by_contra hni
      have h1 : ⨆ k, W' k ≤ ⨆ (j) (_ : j ≠ i), Wi j := by
        refine iSup_le fun k => ?_
        obtain ⟨j, hj⟩ := hsub k
        have hji : j ≠ i := by
          rintro rfl
          exact hni ⟨k, hj⟩
        rw [hj]
        exact le_iSup₂_of_le j hji le_rfl
      rw [hW'int.submodule_iSup_eq_top] at h1
      exact hne i (le_bot_iff.1 ((le_inf le_rfl (le_top.trans h1)).trans
        ((iSupIndep_def.1 hind i).le_bot)))
  ·
    intro h hh i
    obtain ⟨x, hx, hxi⟩ := hex i
    obtain ⟨j, hj⟩ := hof _ (conj_mem_conjSet hh hx)
    exact ⟨j, by rw [hxi, map_comp hh, hj]⟩
  ·
    intro i j
    obtain ⟨x, hx, hxi⟩ := hex i
    obtain ⟨y, hy, hyj⟩ := hex j
    obtain ⟨h₁, hh₁, rfl⟩ := hx
    obtain ⟨h₂, hh₂, rfl⟩ := hy
    refine ⟨h₂ * h₁⁻¹, H.mul_mem hh₂ (H.inv_mem hh₁), ?_⟩
    rw [hxi, map_comp (H.mul_mem hh₂ (H.inv_mem hh₁)), hyj]
    congr 1
    group
  have hΓmem : ∀ i, ∀ y ∈ D, LinearMap.range ((y : W →ₗ[F] W) - 1) ≤ Wi i → y ∈ Ni i :=
    fun i y hy hyi => (hNi i y).2 ⟨Subgroup.subset_closure hy, hΓfix i y hy hyi⟩
  have hNiN : ∀ i, Ni i ≤ Subgroup.closure D := fun i n hn => ((hNi i n).1 hn).1
  have hNifix : ∀ i j, j ≠ i → Ni j ≤ fixer (Wi i) := fun i j hji n hn =>
    mem_fixer.2 (((hNi j n).1 hn).2 i (Ne.symm hji))
  have hfixall : ∀ i, ∀ n ∈ Ni i, (∀ w ∈ Wi i, (n : W →ₗ[F] W) w = w) → n = 1 := by
    intro i n hn hni
    refine eq_one_of_fixes htop fun k w hw => ?_
    by_cases hki : k = i
    · subst hki
      exact hni w hw
    · exact ((hNi i n).1 hn).2 k hki w hw
  have hNi_eq : ∀ i, Ni i = Subgroup.closure
      {y | y ∈ D ∧ LinearMap.range ((y : W →ₗ[F] W) - 1) ≤ Wi i} := by
    intro i
    apply le_antisymm
    · intro n hn
      obtain ⟨hnN, hnfix⟩ := (hNi i n).1 hn
      have hsplit : Subgroup.closure D = Subgroup.closure
          {y | y ∈ D ∧ LinearMap.range ((y : W →ₗ[F] W) - 1) ≤ Wi i} ⊔ Subgroup.closure
          {y | y ∈ D ∧ ¬ LinearMap.range ((y : W →ₗ[F] W) - 1) ≤ Wi i} := by
        rw [← Subgroup.closure_union]
        congr 1
        ext y
        simp only [Set.mem_union, Set.mem_ofPred_eq]
        tauto
      rw [hsplit] at hnN
      have hgen : ∀ y ∈ {y | y ∈ D ∧ LinearMap.range ((y : W →ₗ[F] W) - 1) ≤ Wi i},
          ∀ z ∈ {y | y ∈ D ∧ ¬ LinearMap.range ((y : W →ₗ[F] W) - 1) ≤ Wi i},
          y * z = z * y := by
        rintro y ⟨hy, hyi⟩ z ⟨hz, hzi⟩
        refine eq_of_agree htop fun k w hw => ?_
        rw [mul_apply', mul_apply']
        by_cases hki : k = i
        · subst hki
          have hzw := apply_eq_of_mem_ker (hΓkill k z hz hzi hw)
          rw [hzw, apply_eq_of_mem_ker (hΓkill k z hz hzi
            (hpres k y (Subgroup.subset_closure hy) w hw))]
        · have hyw := hΓfix i y hy hyi k hki w hw
          rw [hyw, hΓfix i y hy hyi k hki _ (hpres k z (Subgroup.subset_closure hz) w hw)]
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup
        (fun a ha b hb => commute_closure hgen ha hb) hnN
      have hb1 : b = 1 := by
        refine eq_one_of_fixes htop fun k w hw => ?_
        by_cases hki : k = i
        · subst hki
          exact closure_fixes (fun z hz => hΓkill k z hz.1 hz.2) hb w hw
        · have h1 := hnfix k hki w hw
          have h2 : (a : W →ₗ[F] W) w = w := closure_fixes (fun y hy u hu => by
            rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
              hΓfix i y hy.1 hy.2 k hki u hu, sub_self]) ha w hw
          rw [mul_apply'] at h1
          exact injective_apply a (h1.trans h2.symm)
      rw [hb1, mul_one]
      exact ha
    · rw [Subgroup.closure_le]
      intro y hy
      exact hΓmem i y hy.1 hy.2
  refine ⟨?_, ?_, ?_, hfixall, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro i j hij x hx y hy
    refine eq_of_agree htop fun k w hw => ?_
    rw [mul_apply', mul_apply']
    obtain ⟨hxN, hxfix⟩ := (hNi i x).1 hx
    obtain ⟨hyN, hyfix⟩ := (hNi j y).1 hy
    by_cases hki : k = i
    · subst hki
      rw [hyfix k hij w hw, hyfix k hij _ (hpres k x hxN w hw)]
    · rw [hxfix k hki w hw, hxfix k hki _ (hpres k y hyN w hw)]
  ·
    apply le_antisymm (iSup_le hNiN)
    rw [Subgroup.closure_le]
    intro y hy
    obtain ⟨i, hi⟩ := hof y hy
    exact (le_iSup Ni i) (hΓmem i y hy (hi ▸ range_le_comp (self_mem_compSet hy)))
  ·
    rw [iSupIndep_def]
    intro i
    rw [Subgroup.disjoint_def]
    intro n hn hn'
    have h1 : (⨆ (j) (_ : j ≠ i), Ni j) ≤ fixer (Wi i) := iSup₂_le fun j hj => hNifix i j hj
    exact hfixall i n hn (mem_fixer.1 (h1 hn'))
  ·
    intro i U hUle hU
    obtain ⟨x, hx, hxi⟩ := hex i
    rw [hxi] at hUle ⊢
    refine comp_irreducible hirr hrank hx hUle fun y hy => hU y (hΓmem i y hy.1 ?_)
    rw [hxi]
    exact range_le_comp hy
  ·
    intro i
    rw [hNi_eq i]
    congr 1
    ext y
    constructor
    · rintro ⟨hy, hyi⟩
      exact ⟨hy, (hΓnontriv i y hy).2 hyi⟩
    · rintro ⟨hy, hyw⟩
      exact ⟨hy, (hΓnontriv i y hy).1 hyw⟩
  ·
    intro i x hx hxw
    obtain ⟨w, hw, hxw⟩ := hxw
    have h1 : (Wi i).map ((x : W →ₗ[F] W) - 1) ≤ LinearMap.range ((x : W →ₗ[F] W) - 1) :=
      LinearMap.map_le_range
    have h2 := Submodule.finrank_mono h1
    rw [finrank_range_of_mem_conjSet hrank hx] at h2
    have h3 : (Wi i).map ((x : W →ₗ[F] W) - 1) ≠ ⊥ := by
      intro h4
      apply hxw
      have h5 : ((x : W →ₗ[F] W) - 1) w ∈ (Wi i).map ((x : W →ₗ[F] W) - 1) := ⟨w, hw, rfl⟩
      rw [h4, Submodule.mem_bot, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h5
      exact h5
    have h6 : finrank F ((Wi i).map ((x : W →ₗ[F] W) - 1)) ≠ 0 :=
      fun h7 => h3 (Submodule.finrank_eq_zero.1 h7)
    omega
  ·
    exact hΓmem ⟨0, hs⟩ t htD (h0 ▸ range_le_comp (self_mem_compSet htD))
  ·
    intro h hh i j hij
    rw [hNi_eq i, hNi_eq j, MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨z, ⟨hz, hzi⟩, rfl⟩
      refine ⟨conj_mem_conjSet hh hz, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, range_conj, ← hij]
      exact Submodule.map_mono hzi
    · rintro ⟨hy, hyj⟩
      refine ⟨h⁻¹ * y * h, ⟨by simpa using conj_mem_conjSet (H.inv_mem hh) hy, ?_⟩, ?_⟩
      · have h1 : h⁻¹ * y * h = h⁻¹ * y * h⁻¹⁻¹ := by rw [inv_inv]
        rw [h1, range_conj]
        have h3 : ((h⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) ∘ₗ
            (h : W →ₗ[F] W) = LinearMap.id := by
          rw [← Module.End.mul_eq_comp, ← Units.val_mul, inv_mul_cancel, Units.val_one]
          rfl
        have h2 : (Wi j).map ((h⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) = Wi i := by
          rw [← hij, ← Submodule.map_comp, h3, Submodule.map_id]
        rw [← h2]
        exact Submodule.map_mono hyj
      · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
  ·
    intro i j
    obtain ⟨x, hx, hxi⟩ := hex i
    obtain ⟨y, hy, hyj⟩ := hex j
    obtain ⟨h₁, hh₁, rfl⟩ := hx
    obtain ⟨h₂, hh₂, rfl⟩ := hy
    have hg : h₂ * h₁⁻¹ ∈ H := H.mul_mem hh₂ (H.inv_mem hh₁)
    have hWij : (Wi i).map ((h₂ * h₁⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) =
        Wi j := by
      rw [hxi, map_comp hg, hyj]
      congr 1
      group
    refine ⟨h₂ * h₁⁻¹, hg, hWij, ?_⟩
    rw [hNi_eq i, hNi_eq j, MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨z, ⟨hz, hzi⟩, rfl⟩
      refine ⟨conj_mem_conjSet hg hz, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, range_conj, ← hWij]
      exact Submodule.map_mono hzi
    · rintro ⟨hy, hyj'⟩
      set g := h₂ * h₁⁻¹ with hgdef
      refine ⟨g⁻¹ * y * g, ⟨by simpa using conj_mem_conjSet (H.inv_mem hg) hy, ?_⟩, ?_⟩
      · have h1 : g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹ := by rw [inv_inv]
        rw [h1, range_conj]
        have h3 : ((g⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) ∘ₗ
            (g : W →ₗ[F] W) = LinearMap.id := by
          rw [← Module.End.mul_eq_comp, ← Units.val_mul, inv_mul_cancel, Units.val_one]
          rfl
        have h2 : (Wi j).map ((g⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) = Wi i := by
          rw [← hWij, ← Submodule.map_comp, h3, Submodule.map_id]
        rw [← h2]
        exact Submodule.map_mono hyj'
      · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group

end CFSG.QuasithinUnique
