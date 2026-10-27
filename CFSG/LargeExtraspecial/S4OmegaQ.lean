module

public import CFSG.LargeExtraspecial.S4SpFour
public import CFSG.LargeExtraspecial.OrthoF2Radical

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Module Subgroup QuadraticMap CFSG.LargeExtraspecial.OrthoF2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {β : LinearMap.BilinForm (ZMod 2) V}

@[expose] def orbitOf (X : Subgroup (V ≃ₗ[ZMod 2] V)) (a : V) : Set V := {v | ∃ x ∈ X, x a = v}

omit [FiniteDimensional (ZMod 2) V] in
theorem apply_mem_orbitOf {X : Subgroup (V ≃ₗ[ZMod 2] V)} {a : V} {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ X) {v : V} (hv : v ∈ orbitOf X a) : g v ∈ orbitOf X a := by
  obtain ⟨x, hx, rfl⟩ := hv
  exact ⟨g * x, mul_mem hg hx, rfl⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem apply_mem_orbitOf_iff {X : Subgroup (V ≃ₗ[ZMod 2] V)} {a : V} {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ X) {v : V} : g v ∈ orbitOf X a ↔ v ∈ orbitOf X a := by
  refine ⟨fun h => ?_, apply_mem_orbitOf hg⟩
  have := apply_mem_orbitOf (inv_mem hg) h
  rwa [show g⁻¹ (g v) = v from g.symm_apply_apply v] at this

structure RadConfig (β : LinearMap.BilinForm (ZMod 2) V) (X : Subgroup (V ≃ₗ[ZMod 2] V)) (a : V)
    (E : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop where
  alt : β.IsAlt
  nondeg : β.Nondegenerate
  le_sp : X ≤ TauCeti.BilinForm.isometryGroup β
  ne_zero : a ≠ 0
  span_eq : Submodule.span (ZMod 2) (orbitOf X a) = ⊤
  le_X : E ≤ X
  le_U : E ≤ spPointRadical β a
  card_le : Nat.card (spPointRadical β a) ≤ 2 * Nat.card E
  tau_not_mem : spTransvection β alt a ∉ E

namespace RadConfig

variable {X E : Subgroup (V ≃ₗ[ZMod 2] V)} {a : V} (C : RadConfig β X a E)
include C

omit [FiniteDimensional (ZMod 2) V] in
theorem exists_spRho_apply_eq {x : V} (hx : β x a = 1) {w : V} (hw : β a w = 0) :
    spRho C.alt hw (β x w) x = x + w := by
  rw [spRho_apply, hx, one_smul, mul_one, zmod2_add_self, zero_smul, add_zero]

theorem mem_or_mul_mem {u : V ≃ₗ[ZMod 2] V} (hu : u ∈ spPointRadical β a) :
    u ∈ E ∨ u * spTransvection β C.alt a ∈ E := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv_of_finite
  exact mem_or_mul_mem_of_card C.le_U C.card_le (spTransvection_mem_U C.alt a) C.tau_not_mem hu

theorem exists_mem_E_apply_eq {x : V} (hx : β x a = 1) {w : V} (hw : β a w = 0) :
    ∃ e ∈ E, e x = x + w ∨ e (x + a) = x + w := by
  set u := spRho C.alt hw (β x w) with hu
  have huU : u ∈ spPointRadical β a := spRho_mem_spPointRadical C.alt hw _
  rcases C.mem_or_mul_mem huU with h | h
  · exact ⟨u, h, Or.inl (C.exists_spRho_apply_eq hx hw)⟩
  · refine ⟨_, h, Or.inr ?_⟩
    have h1 : spTransvection β C.alt a (x + a) = x := by
      rw [spTransvection_apply, map_add, LinearMap.add_apply, hx, C.alt.self_eq_zero, add_zero,
        one_smul, add_assoc, vec_add_self, add_zero]
    rw [LinearEquiv.mul_apply, h1]
    exact C.exists_spRho_apply_eq hx hw

omit [FiniteDimensional (ZMod 2) V] in
theorem zero_not_mem_orbitOf : (0 : V) ∉ orbitOf X a := by
  rintro ⟨x, -, hx⟩
  exact C.ne_zero (x.map_eq_zero_iff.mp hx)

omit [FiniteDimensional (ZMod 2) V] C in
theorem mem_orbitOf_self : a ∈ orbitOf X a := ⟨1, one_mem _, rfl⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem symm (x y : V) : β x y = β y x := isAlt_symm C.alt x y

omit [FiniteDimensional (ZMod 2) V] in
theorem eq_zero_of_forall_orbit {v : V} (h : ∀ y ∈ orbitOf X a, β y v = 0) : v = 0 := by
  refine C.nondeg.2 v fun y => ?_
  have hy : y ∈ Submodule.span (ZMod 2) (orbitOf X a) := by rw [C.span_eq]; trivial
  induction hy using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => simp
  | add u w _ _ hu hw => rw [map_add, LinearMap.add_apply, hu, hw, add_zero]
  | smul c u _ hu => rw [map_smul, LinearMap.smul_apply, hu, smul_zero]

omit [FiniteDimensional (ZMod 2) V] in
theorem exists_orbit_pair_eq_one {v : V} (hv : v ≠ 0) : ∃ y ∈ orbitOf X a, β y v = 1 := by
  by_contra h
  push Not at h
  exact hv (C.eq_zero_of_forall_orbit fun y hy => (zmod2_eq_zero_or_eq_one _).resolve_right
    (h y hy))

theorem mem_iff_add_not_mem_self (hntr : ∃ v : V, v ≠ 0 ∧ v ∉ orbitOf X a) {x : V}
    (hx : β x a = 1) : x ∈ orbitOf X a ↔ x + a ∉ orbitOf X a := by
  constructor
  · intro hxT hxaT
    obtain ⟨v, hv0, hvT⟩ := hntr
    apply hvT
    have hall : ∀ y, β y a = 1 → y ∈ orbitOf X a := by
      intro y hy
      have hw : β a (y - x) = 0 := by
        rw [map_sub, C.symm a y, C.symm a x, hy, hx, sub_self]
      obtain ⟨e, he, h1 | h1⟩ := C.exists_mem_E_apply_eq hx hw
      · rw [add_sub_cancel] at h1
        rw [← h1]
        exact apply_mem_orbitOf (C.le_X he) hxT
      · rw [add_sub_cancel] at h1
        rw [← h1]
        exact apply_mem_orbitOf (C.le_X he) hxaT
    obtain ⟨b, hbT, hbv⟩ := C.exists_orbit_pair_eq_one hv0
    obtain ⟨g, hgX, rfl⟩ := hbT
    have hgI := C.le_sp hgX
    have h1 : β (g⁻¹ v) a = 1 := by
      rw [← TauCeti.BilinForm.mem_isometryGroup_iff.mp hgI, show g (g⁻¹ v) = v from
        g.apply_symm_apply v, C.symm, hbv]
    have := apply_mem_orbitOf hgX (hall _ h1)
    rwa [show g (g⁻¹ v) = v from g.apply_symm_apply v] at this
  · intro hxa
    obtain ⟨y, hyT, hy⟩ := C.exists_orbit_pair_eq_one C.ne_zero
    have hy' : β y a = 1 := hy
    have hw : β a (y - x) = 0 := by
      rw [map_sub, C.symm a y, C.symm a x, hy', hx, sub_self]
    obtain ⟨e, he, h1 | h1⟩ := C.exists_mem_E_apply_eq hx hw
    · rw [add_sub_cancel] at h1
      rw [← apply_mem_orbitOf_iff (C.le_X he), h1]
      exact hyT
    · exfalso
      rw [add_sub_cancel] at h1
      apply hxa
      rw [← apply_mem_orbitOf_iff (C.le_X he), h1]
      exact hyT

theorem mem_iff_add_not_mem (hntr : ∃ v : V, v ≠ 0 ∧ v ∉ orbitOf X a) {b : V}
    (hb : b ∈ orbitOf X a) {x : V} (hx : β x b = 1) :
    x ∈ orbitOf X a ↔ x + b ∉ orbitOf X a := by
  obtain ⟨g, hgX, rfl⟩ := hb
  have hgI := C.le_sp hgX
  have h1 : β (g⁻¹ x) a = 1 := by
    rw [← TauCeti.BilinForm.mem_isometryGroup_iff.mp hgI, show g (g⁻¹ x) = x from
      g.apply_symm_apply x, hx]
  have key := C.mem_iff_add_not_mem_self hntr h1
  rw [← apply_mem_orbitOf_iff (inv_mem hgX), ← apply_mem_orbitOf_iff (inv_mem hgX) (v := x + g a),
    map_add, show g⁻¹ (g a) = a from g.symm_apply_apply a]
  exact key

theorem mem_iff_add_mem_self {v : V} (hva : β v a = 0)
    (hv : v ∉ Submodule.span (ZMod 2) {a}) : v ∈ orbitOf X a ↔ v + a ∈ orbitOf X a := by
  obtain ⟨w, haw, hvw⟩ : ∃ w, β a w = 0 ∧ β v w = 1 := by
    have hPP := LinearMap.BilinForm.orthogonal_orthogonal C.nondeg C.alt.isRefl
      (Submodule.span (ZMod 2) {a})
    rw [← hPP, LinearMap.BilinForm.mem_orthogonal_iff] at hv
    push Not at hv
    obtain ⟨w, hw, hwv⟩ := hv
    refine ⟨w, ?_, ?_⟩
    · exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hw) a (Submodule.mem_span_singleton_self a)
    · rw [C.symm]
      exact zmod2_eq_one_of_ne_zero hwv
  obtain ⟨l, hlE⟩ : ∃ l, spRho C.alt haw l ∈ E := by
    rcases C.mem_or_mul_mem (spRho_mem_spPointRadical C.alt haw 0) with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, by rwa [← spRho_one_eq] at h⟩
  have hev : spRho C.alt haw l v = v + a := by
    rw [spRho_apply, hva, zero_smul, add_zero, hvw, mul_zero, add_zero, one_smul]
  have hea : spRho C.alt haw l a = a := (spRho_mem_spPointRadical C.alt haw l).2.1
  have hX := C.le_X hlE
  constructor
  · intro h
    rw [← hev]
    exact apply_mem_orbitOf hX h
  · intro h
    have := apply_mem_orbitOf hX h
    rwa [map_add, hev, hea, add_assoc, vec_add_self, add_zero] at this

theorem mem_iff_add_mem {b : V} (hb : b ∈ orbitOf X a) {v : V} (hvb : β v b = 0)
    (hv : v ∉ Submodule.span (ZMod 2) {b}) : v ∈ orbitOf X a ↔ v + b ∈ orbitOf X a := by
  obtain ⟨g, hgX, rfl⟩ := hb
  have hgI := C.le_sp hgX
  have h1 : β (g⁻¹ v) a = 0 := by
    rw [← TauCeti.BilinForm.mem_isometryGroup_iff.mp hgI, show g (g⁻¹ v) = v from
      g.apply_symm_apply v, hvb]
  have h2 : g⁻¹ v ∉ Submodule.span (ZMod 2) {a} := by
    intro hmem
    apply hv
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
    rw [Submodule.mem_span_singleton]
    refine ⟨k, ?_⟩
    have := congrArg g hk
    rwa [map_smul, show g (g⁻¹ v) = v from g.apply_symm_apply v] at this
  have key := C.mem_iff_add_mem_self h1 h2
  rw [← apply_mem_orbitOf_iff (inv_mem hgX), ← apply_mem_orbitOf_iff (inv_mem hgX) (v := v + g a),
    map_add, show g⁻¹ (g a) = a from g.symm_apply_apply a]
  exact key

theorem add_mem_iff_of_mem (hntr : ∃ v : V, v ≠ 0 ∧ v ∉ orbitOf X a) {x y : V}
    (hx : x ∈ orbitOf X a) (hy : y ∈ orbitOf X a) (hxy : x ≠ y) :
    x + y ∈ orbitOf X a ↔ β x y = 0 := by
  rcases zmod2_eq_zero_or_eq_one (β x y) with h | h
  · simp only [h, iff_true]
    have hyx : β y x = 0 := by rw [C.symm, h]
    have hyP : y ∉ Submodule.span (ZMod 2) {x} := by
      intro hmem
      rcases mem_span_singleton_iff.mp hmem with h0 | h1
      · exact C.zero_not_mem_orbitOf (h0 ▸ hy)
      · exact hxy h1.symm
    rw [add_comm]
    exact (C.mem_iff_add_mem hx hyx hyP).mp hy
  · rw [h]
    simp only [one_ne_zero, iff_false]
    have hyx : β y x = 1 := by rw [C.symm, h]
    have := (C.mem_iff_add_not_mem hntr hx hyx).mp hy
    rwa [add_comm] at this

theorem add_mem_iff_of_not_mem (hntr : ∃ v : V, v ≠ 0 ∧ v ∉ orbitOf X a) {x y : V}
    (hx : x ∈ orbitOf X a) (hy : y ∉ orbitOf X a) (hy0 : y ≠ 0) :
    x + y ∈ orbitOf X a ↔ β x y = 1 := by
  rcases zmod2_eq_zero_or_eq_one (β x y) with h | h
  · rw [h]
    simp only [zero_ne_one, iff_false]
    intro hxyT
    have hne : x ≠ x + y := fun h' => hy0 (by
      have := congrArg (· + x) h'
      simpa [add_comm x y, add_assoc, vec_add_self] using this.symm)
    have h2 := (C.add_mem_iff_of_mem hntr hx hxyT hne).mpr (by
      rw [map_add, C.alt.self_eq_zero, zero_add, h])
    rw [← add_assoc, vec_add_self, zero_add] at h2
    exact hy h2
  · simp only [h, iff_true]
    have hyx : β y x = 1 := by rw [C.symm, h]
    by_contra h'
    have := (C.mem_iff_add_not_mem hntr hx hyx).mpr (by rwa [add_comm])
    exact hy this

theorem add_mem_iff_of_not_mem_not_mem (hntr : ∃ v : V, v ≠ 0 ∧ v ∉ orbitOf X a) {x y : V}
    (hx : x ∉ orbitOf X a) (hx0 : x ≠ 0) (hy : y ∉ orbitOf X a) (hy0 : y ≠ 0) (hxy : x ≠ y) :
    x + y ∈ orbitOf X a ↔ β x y = 0 := by
  constructor
  · intro hT
    by_contra h
    have h1 : β x (x + y) = 1 := by
      rw [map_add, C.alt.self_eq_zero, zero_add]
      exact zmod2_eq_one_of_ne_zero h
    have := (C.mem_iff_add_not_mem hntr hT h1).mpr (by
      rw [← add_assoc, vec_add_self, zero_add]; exact hy)
    exact hx this
  · intro h
    by_contra hT
    obtain ⟨b, hbT, hby⟩ := C.exists_orbit_pair_eq_one hy0
    have hyb : y + b ∈ orbitOf X a := by
      rw [add_comm]
      exact (C.add_mem_iff_of_not_mem hntr hbT hy hy0).mpr hby
    have hxy0 : x + y ≠ 0 := fun h' => hxy (by
      have := congrArg (· + y) h'
      simpa [add_assoc, vec_add_self] using this)
    rcases zmod2_eq_zero_or_eq_one (β b x) with hbx | hbx
    ·
      have hxyb : x + y + b ∈ orbitOf X a := by
        rw [add_comm]
        refine (C.add_mem_iff_of_not_mem hntr hbT hT hxy0).mpr ?_
        rw [map_add, hbx, hby, zero_add]
      have hne : x + y + b ≠ y + b := fun h' => hx0 (by
        have := congrArg (· + (y + b)) h'
        simpa [add_assoc, vec_add_self, add_comm, add_left_comm] using this)
      have key := C.add_mem_iff_of_mem hntr hxyb hyb hne
      have hsum : x + y + b + (y + b) = x := by
        calc x + y + b + (y + b) = x + (y + y) + (b + b) := by abel
          _ = x := by rw [vec_add_self, vec_add_self, add_zero, add_zero]
      rw [hsum] at key
      have hval : β (x + y + b) (y + b) = 0 := by
        have e1 : β x b = 0 := by rw [C.symm]; exact hbx
        have e2 : β b y = β y b := C.symm b y
        simp only [map_add, LinearMap.add_apply, h, e1, e2, C.alt.self_eq_zero, add_zero,
          zero_add, zmod2_add_self]
      exact absurd (key.mpr hval) hx
    ·
      have hxb : x + b ∈ orbitOf X a := by
        rw [add_comm]
        exact (C.add_mem_iff_of_not_mem hntr hbT hx hx0).mpr hbx
      have hne : x + b ≠ y + b := fun h' => hxy (add_right_cancel h')
      have key := (C.add_mem_iff_of_mem hntr hxb hyb hne).mpr (by
        have e1 : β x b = 1 := by rw [C.symm]; exact hbx
        simp only [map_add, LinearMap.add_apply, h, e1, hby, C.alt.self_eq_zero, add_zero,
          zero_add, zmod2_add_self])
      have hsum : x + b + (y + b) = x + y := by
        calc x + b + (y + b) = x + y + (b + b) := by abel
          _ = x + y := by rw [vec_add_self, add_zero]
      rw [hsum] at key
      exact hT key

open Classical in
@[expose] noncomputable def qOrbit (X : Subgroup (V ≃ₗ[ZMod 2] V)) (a : V) (v : V) : ZMod 2 :=
  if v = 0 ∨ v ∈ orbitOf X a then 0 else 1

omit [FiniteDimensional (ZMod 2) V] C in
theorem qOrbit_eq_zero_iff {v : V} : qOrbit X a v = 0 ↔ v = 0 ∨ v ∈ orbitOf X a := by
  unfold qOrbit
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' one_ne_zero, fun h' => absurd h' h⟩

omit [FiniteDimensional (ZMod 2) V] C in
theorem qOrbit_eq_one_iff {v : V} : qOrbit X a v = 1 ↔ ¬ (v = 0 ∨ v ∈ orbitOf X a) := by
  rw [← qOrbit_eq_zero_iff]
  rcases zmod2_eq_zero_or_eq_one (qOrbit X a v) with h | h <;> rw [h] <;> decide

theorem qOrbit_add (hntr : ∃ v : V, v ≠ 0 ∧ v ∉ orbitOf X a) (x y : V) :
    qOrbit X a (x + y) = qOrbit X a x + qOrbit X a y + β x y := by
  have hT0 := C.zero_not_mem_orbitOf
  by_cases hx0 : x = 0
  · subst hx0
    rw [zero_add, map_zero, LinearMap.zero_apply, add_zero,
      (qOrbit_eq_zero_iff (X := X) (a := a)).mpr (Or.inl rfl), zero_add]
  by_cases hy0 : y = 0
  · subst hy0
    rw [add_zero, map_zero, add_zero, (qOrbit_eq_zero_iff (X := X) (a := a)).mpr (Or.inl rfl),
      add_zero]
  by_cases hxy : x = y
  · subst hxy
    rw [vec_add_self, C.alt.self_eq_zero, add_zero, zmod2_add_self,
      (qOrbit_eq_zero_iff (X := X) (a := a)).mpr (Or.inl rfl)]
  have hxy0 : x + y ≠ 0 := fun h' => hxy (by
    have := congrArg (· + y) h'
    simpa [add_assoc, vec_add_self] using this)
  have hq0 : ∀ v : V, v ∈ orbitOf X a → qOrbit X a v = 0 := fun v hv =>
    (qOrbit_eq_zero_iff (X := X) (a := a)).mpr (Or.inr hv)
  have hq1 : ∀ v : V, v ≠ 0 → v ∉ orbitOf X a → qOrbit X a v = 1 := fun v hv h =>
    (qOrbit_eq_one_iff (X := X) (a := a)).mpr (by tauto)
  by_cases hxT : x ∈ orbitOf X a <;> by_cases hyT : y ∈ orbitOf X a
  · have key := C.add_mem_iff_of_mem hntr hxT hyT hxy
    rw [hq0 x hxT, hq0 y hyT, zero_add, zero_add]
    rcases zmod2_eq_zero_or_eq_one (β x y) with h | h
    · rw [h, hq0 _ (key.mpr h)]
    · rw [h, hq1 _ hxy0 (fun h' => by rw [key.mp h'] at h; exact absurd h (by decide))]
  · have key := C.add_mem_iff_of_not_mem hntr hxT hyT hy0
    rw [hq0 x hxT, hq1 y hy0 hyT, zero_add]
    rcases zmod2_eq_zero_or_eq_one (β x y) with h | h
    · rw [h, hq1 _ hxy0 (fun h' => by rw [key.mp h'] at h; exact absurd h (by decide))]
      rfl
    · rw [h, hq0 _ (key.mpr h)]
      rfl
  · have key := C.add_mem_iff_of_not_mem hntr hyT hxT hx0
    rw [hq1 x hx0 hxT, hq0 y hyT, add_zero, add_comm x y, C.symm x y]
    rcases zmod2_eq_zero_or_eq_one (β y x) with h | h
    · rw [h, hq1 _ (by rwa [add_comm])
        (fun h' => by rw [key.mp h'] at h; exact absurd h (by decide))]
      rfl
    · rw [h, hq0 _ (key.mpr h)]
      rfl
  · have key := C.add_mem_iff_of_not_mem_not_mem hntr hxT hx0 hyT hy0 hxy
    rw [hq1 x hx0 hxT, hq1 y hy0 hyT]
    rcases zmod2_eq_zero_or_eq_one (β x y) with h | h
    · rw [h, hq0 _ (key.mpr h)]
      rfl
    · rw [h, hq1 _ hxy0 (fun h' => by rw [key.mp h'] at h; exact absurd h (by decide))]
      rfl

@[expose] noncomputable def qOrbitForm (hntr : ∃ v : V, v ≠ 0 ∧ v ∉ orbitOf X a) :
    QuadraticForm (ZMod 2) V :=
  QuadraticMap.ofPolar (qOrbit X a)
    (fun c x => by
      rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
      · rw [zero_smul, mul_zero, zero_smul, (qOrbit_eq_zero_iff (X := X) (a := a)).mpr
          (Or.inl rfl)]
      · rw [one_smul, mul_one, one_smul])
    (fun x x' y => by
      simp only [QuadraticMap.polar, C.qOrbit_add hntr, map_add, LinearMap.add_apply]
      ring_nf
      try reduce_mod_char)
    (fun c x y => by
      simp only [QuadraticMap.polar, C.qOrbit_add hntr, map_smul, LinearMap.smul_apply,
        smul_eq_mul]
      rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
      · rw [zero_smul, (qOrbit_eq_zero_iff (X := X) (a := a)).mpr (Or.inl rfl)]
        ring
      · rw [one_smul]
        ring)

theorem qOrbitForm_apply (hntr : ∃ v : V, v ≠ 0 ∧ v ∉ orbitOf X a) (v : V) :
    C.qOrbitForm hntr v = qOrbit X a v :=
  rfl

theorem polar_qOrbitForm (hntr : ∃ v : V, v ≠ 0 ∧ v ∉ orbitOf X a) (x y : V) :
    QuadraticMap.polar (C.qOrbitForm hntr) x y = β x y := by
  rw [QuadraticMap.polar, qOrbitForm_apply, qOrbitForm_apply, qOrbitForm_apply,
    C.qOrbit_add hntr]
  ring

theorem polarBilin_qOrbitForm (hntr : ∃ v : V, v ≠ 0 ∧ v ∉ orbitOf X a) :
    (C.qOrbitForm hntr).polarBilin = β := by
  ext x y
  rw [polarBilin_apply_apply, C.polar_qOrbitForm hntr]

theorem qOrbitForm_nondegenerate (hntr : ∃ v : V, v ≠ 0 ∧ v ∉ orbitOf X a) :
    (C.qOrbitForm hntr).polarBilin.Nondegenerate := by
  rw [C.polarBilin_qOrbitForm hntr]
  exact C.nondeg

theorem mem_orthogonalGroup_of_mem (hntr : ∃ v : V, v ≠ 0 ∧ v ∉ orbitOf X a)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ X) :
    g ∈ TauCeti.QuadraticMap.orthogonalGroup (C.qOrbitForm hntr) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [qOrbitForm_apply, qOrbitForm_apply]
  unfold qOrbit
  rw [apply_mem_orbitOf_iff hg, g.map_eq_zero_iff]

omit [FiniteDimensional (ZMod 2) V] C in
theorem le_pointRadical_of_polar {Q : QuadraticForm (ZMod 2) V}
    (hQ : ∀ x y, QuadraticMap.polar Q x y = β x y) {c : V} {u : V ≃ₗ[ZMod 2] V}
    (hu : u ∈ spPointRadical β c) (huQ : u ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    u ∈ pointRadical Q c := by
  obtain ⟨-, hu2, hu3, hu4⟩ := hu
  refine ⟨huQ, hu2, fun x hx => hu3 x (by rw [← hQ]; exact hx), fun v => ?_⟩
  rw [hQ]
  exact hu4 v

theorem E_eq_pointRadical (hntr : ∃ v : V, v ≠ 0 ∧ v ∉ orbitOf X a) :
    E = pointRadical (C.qOrbitForm hntr) a := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv_of_finite
  have hle : E ≤ pointRadical (C.qOrbitForm hntr) a := fun u hu =>
    le_pointRadical_of_polar (C.polar_qOrbitForm hntr) (C.le_U hu)
      (C.mem_orthogonalGroup_of_mem hntr (C.le_X hu))
  have ha : C.qOrbitForm hntr a = 0 := by
    rw [qOrbitForm_apply, qOrbit_eq_zero_iff]
    exact Or.inr (mem_orbitOf_self)
  refine eq_of_le_of_card_ge hle ?_
  have h1 := card_pointRadical (C.qOrbitForm_nondegenerate hntr) C.ne_zero ha
  have h2 := C.card_le
  rw [card_spPointRadical C.alt C.nondeg C.ne_zero] at h2
  rw [h1]
  have hpos : 2 ≤ finrank (ZMod 2) V := by
    by_contra h
    push Not at h
    have h3 := C.nondeg
    obtain ⟨b, hb⟩ : ∃ b, β a b ≠ 0 := by
      by_contra! h'
      exact C.ne_zero (C.nondeg.1 a h')
    have hb' : b ∉ Submodule.span (ZMod 2) {a} := by
      intro hmem
      obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hmem
      rw [map_smul, C.alt.self_eq_zero, smul_zero] at hb
      exact hb rfl
    have := finrank_span_singleton (K := ZMod 2) C.ne_zero
    have h4 := Submodule.finrank_le (Submodule.span (ZMod 2) ({a} : Set V))
    have h5 : Submodule.span (ZMod 2) ({a} : Set V) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      omega
    exact hb' (h5 ▸ Submodule.mem_top)
  have : 2 ^ (finrank (ZMod 2) V - 1) = 2 * 2 ^ (finrank (ZMod 2) V - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

end RadConfig

theorem card_spPointRadical_inf_le_two (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    {Q : QuadraticForm (ZMod 2) V} (hQ : ∀ x y, QuadraticMap.polar Q x y = β x y) {c : V}
    (hc : Q c = 1) :
    Nat.card (spPointRadical β c ⊓ TauCeti.QuadraticMap.orthogonalGroup Q :
      Subgroup (V ≃ₗ[ZMod 2] V)) ≤ 2 := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv_of_finite
  have hc0 : c ≠ 0 := fun h => by rw [h, map_zero] at hc; exact zero_ne_one hc
  have key : ∀ u ∈ (spPointRadical β c ⊓ TauCeti.QuadraticMap.orthogonalGroup Q :
      Subgroup (V ≃ₗ[ZMod 2] V)), u = 1 ∨ u = spTransvection β hβ c := by
    intro u ⟨huU, huQ⟩
    obtain ⟨d, hcd, l, rfl⟩ := exists_eq_spRho hβ hnd hc0 huU
    have hd : d ∈ Submodule.span (ZMod 2) {c} := by
      have hPP := LinearMap.BilinForm.orthogonal_orthogonal hnd hβ.isRefl
        (Submodule.span (ZMod 2) {c})
      rw [← hPP, LinearMap.BilinForm.mem_orthogonal_iff]
      intro x hx
      have hxc : β c x = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) c
        (Submodule.mem_span_singleton_self c)
      have hxc' : β x c = 0 := by rw [isAlt_symm hβ, hxc]
      have h1 := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp huQ) x
      rw [spRho_apply, hxc', zero_smul, add_zero, mul_zero, add_zero,
        CFSG.RankThree.OrthogonalInvolutions.map_add_eq, QuadraticMap.map_smul, hc, hQ,
        map_smul] at h1
      simp only [hxc', smul_eq_mul, mul_one, mul_zero, add_zero, zmod2_mul_self] at h1
      change β x d = 0
      exact add_eq_left.mp h1
    have h0 : β c 0 = 0 := map_zero _
    have hρ : spRho hβ hcd l = spRho hβ h0 l := by
      rcases mem_span_singleton_iff.mp hd with hd0 | hdc
      · exact spRho_congr hβ hcd h0 rfl hd0 rfl
      · have h' : β c (0 + c) = 0 := by rw [zero_add]; exact hβ.self_eq_zero c
        rw [← spRho_add_self hβ h0 l h']
        exact spRho_congr hβ hcd h' rfl (by rw [hdc, zero_add]) rfl
    rw [hρ]
    rcases zmod2_eq_zero_or_eq_one l with rfl | rfl
    · exact Or.inl (spRho_zero_zero hβ c h0)
    · exact Or.inr (spRho_zero_one hβ c h0)
  have hsub : ((spPointRadical β c ⊓ TauCeti.QuadraticMap.orthogonalGroup Q :
      Subgroup (V ≃ₗ[ZMod 2] V)) : Set (V ≃ₗ[ZMod 2] V)) ⊆ {1, spTransvection β hβ c} :=
    fun u hu => by
      rcases key u hu with h | h
      · exact Or.inl h
      · exact Or.inr h
  have h1 := Nat.card_mono (Set.toFinite _) hsub
  refine h1.trans ?_
  rw [Nat.card_coe_set_eq]
  calc ({1, spTransvection β hβ c} : Set (V ≃ₗ[ZMod 2] V)).ncard ≤
        ({spTransvection β hβ c} : Set (V ≃ₗ[ZMod 2] V)).ncard + 1 := Set.ncard_insert_le _ _
    _ = 2 := by rw [Set.ncard_singleton]

end CFSG.LargeExtraspecial.S4
