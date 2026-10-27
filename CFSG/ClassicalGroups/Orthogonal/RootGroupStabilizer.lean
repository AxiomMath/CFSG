module

public import CFSG.ClassicalGroups.Orthogonal.RootGroupExt
public import CFSG.ClassicalGroups.PCoreSection
public import CFSG.ClassicalGroups.Orthogonal.RootGroupChar

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap CFSG.Open CFSG.ClassicalGroups.PCoreSection

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem Gom.app_zero (g : Gom Q) : g.app 0 = 0 := map_zero (g : V ≃ₗ[K] V)

@[expose] def pointStabilizer (Q : QuadraticForm K V) (u : V) : Subgroup (Gom Q) where
  carrier := {g | ∃ c : K, g.app u = c • u}
  one_mem' := ⟨1, by rw [Gom.app_one, one_smul]⟩
  mul_mem' := by
    rintro g h ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨d * c, by rw [Gom.app_mul, hd, Gom.map_smul, hc, smul_smul]⟩
  inv_mem' := by
    rintro g ⟨c, hc⟩
    by_cases hc0 : c = 0
    · have hu : u = 0 := by
        rw [← Gom.app_inv_app g u, hc, hc0, zero_smul, Gom.app_zero]
      exact ⟨1, by rw [hu, Gom.app_zero, smul_zero]⟩
    · refine ⟨c⁻¹, ?_⟩
      conv_lhs => rw [← inv_smul_smul₀ hc0 u]
      rw [← hc, Gom.map_smul, Gom.app_inv_app]

theorem mem_pointStabilizer {u : V} {g : Gom Q} :
    g ∈ pointStabilizer Q u ↔ ∃ c : K, g.app u = c • u := Iff.rfl

theorem isLinearAction_Gom (Q : QuadraticForm K V) :
    IsLinearAction K (fun (g : Gom Q) (x : V) => g.app x) :=
  ⟨Gom.app_one, Gom.app_mul, Gom.map_add, Gom.map_smul⟩

theorem Gom.ne_zero_of_app_eq_smul {u : V} (hu : u ≠ 0) {g : Gom Q} {c : K}
    (hc : g.app u = c • u) : c ≠ 0 := by
  rintro rfl
  apply hu
  rw [← Gom.app_inv_app g u, hc, zero_smul, Gom.app_zero]

theorem polar_app_eq_zero_of_mem_pointStabilizer {u : V} (hu : u ≠ 0) {s : Gom Q}
    (hs : s ∈ pointStabilizer Q u) {x : V} (hx : polar Q x u = 0) : polar Q (s.app x) u = 0 := by
  obtain ⟨c, hc⟩ := hs
  have hc0 := Gom.ne_zero_of_app_eq_smul hu hc
  have h1 : polar Q (s.app x) (s.app u) = 0 := by rw [Gom.polar_app, hx]
  rw [hc, polar_smul_right_eq] at h1
  exact (mul_eq_zero.mp h1).resolve_left hc0

theorem Eom_mem_pointStabilizer {u a w : V} (ha : Q a = 0) (haw : polar Q a w = 0)
    (hua : polar Q u a = 0) (huw : polar Q u w = 0) : Eom Q a w ∈ pointStabilizer Q u :=
  ⟨1, by rw [Eom_app ha haw, hua, huw]; simp⟩

theorem app_eq_self_of_mem_Lom {u : V} {g : Gom Q} (hg : g ∈ Lom Q u) : g.app u = u := by
  obtain ⟨w, -, hgw⟩ := mem_rootGroup.mp (mem_Lom.mp hg)
  show (g : V ≃ₗ[K] V) u = u
  rw [← hgw]
  exact eichler_apply_self u w

theorem Lom_le_pointStabilizer (u : V) : Lom Q u ≤ pointStabilizer Q u :=
  fun _ hg => ⟨1, by rw [app_eq_self_of_mem_Lom hg, one_smul]⟩

theorem conj_mem_Lom_of_mem_pointStabilizer {u : V} {s : Gom Q} (hs : s ∈ pointStabilizer Q u)
    {n : Gom Q} (hn : n ∈ Lom Q u) : s * n * s⁻¹ ∈ Lom Q u := by
  obtain ⟨c, hc⟩ := hs
  exact conj_mem_rootGroup_of_apply_eq_smul (elementaryGroup_le_orthogonalGroup Q s.2) hc
    (mem_Lom.mp hn)

theorem isPGroup_Lom [CharP K 2] (u : V) : IsPGroup 2 (Lom Q u) := by
  intro x
  have h := sq_eq_one_of_mem_rootGroup (u := u) CharTwo.two_eq_zero (mem_Lom.mp x.2)
  have hsq : x.1 * x.1 = 1 := Subtype.ext h
  exact ⟨1, Subtype.ext (by simpa [pow_two] using hsq)⟩

theorem Lom_le_pCoreOf_pointStabilizer [CharP K 2] (u : V) :
    Lom Q u ≤ pCoreOf 2 (pointStabilizer Q u) :=
  le_pCoreOf (Lom_le_pointStabilizer u) (fun _ hs _ hn => conj_mem_Lom_of_mem_pointStabilizer hs hn)
    (isPGroup_Lom u)

section Orth

private theorem polarBilin_isRefl : (polarBilin Q).IsRefl := fun x y h => by
  rw [polarBilin_apply_apply] at h ⊢
  rwa [polar_comm]

theorem mem_orth_iff {W : Submodule K V} {z : V} :
    z ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) W ↔ ∀ x ∈ W, polar Q x z = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  exact Iff.rfl

theorem mem_orth_span_single_iff {u z : V} :
    z ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}) ↔ polar Q u z = 0 := by
  rw [mem_orth_iff]
  constructor
  · intro h
    exact h u (Submodule.mem_span_singleton_self u)
  · intro h x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [polar_smul_left_eq, h, mul_zero]

theorem mem_orth_span_pair_iff {a b z : V} :
    z ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {a, b}) ↔
      polar Q a z = 0 ∧ polar Q b z = 0 := by
  rw [mem_orth_iff]
  constructor
  · intro h
    exact ⟨h a (Submodule.subset_span (by simp)), h b (Submodule.subset_span (by simp))⟩
  · rintro ⟨h1, h2⟩ x hx
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hx
    rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, h1, h2]
    ring

theorem finrank_span_pair_le (a b : V) : Module.finrank K (Submodule.span K {a, b}) ≤ 2 := by
  classical
  have h := finrank_span_finset_le_card (R := K) ({a, b} : Finset V)
  have h2 : (({a, b} : Finset V) : Set V) = {a, b} := by simp
  rw [Set.finrank, h2] at h
  exact h.trans Finset.card_le_two

variable [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)

include hQ

theorem exists_polar_ne_zero_of_not_mem {N : Submodule K V} {y : V} (hy : y ∉ N) :
    ∃ z ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) N, polar Q y z ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hy
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hQ polarBilin_isRefl N, mem_orth_iff]
  intro x hx
  rw [polar_comm]
  exact hcon x hx

theorem exists_polar_ne_zero_of_finrank {N : Submodule K V} (hN : Module.finrank K N ≤ 2)
    (h5 : 5 ≤ Module.finrank K V) :
    ∃ m₁ ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) N,
      ∃ m₂ ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) N, polar Q m₁ m₂ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hle : LinearMap.BilinForm.orthogonal (polarBilin Q) N ≤
      LinearMap.BilinForm.orthogonal (polarBilin Q)
        (LinearMap.BilinForm.orthogonal (polarBilin Q) N) := by
    intro m₁ hm₁
    rw [mem_orth_iff]
    intro x hx
    rw [polar_comm]
    exact hcon m₁ hm₁ x hx
  rw [LinearMap.BilinForm.orthogonal_orthogonal hQ polarBilin_isRefl N] at hle
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.BilinForm.finrank_orthogonal hQ N
  have h3 := Submodule.finrank_le N
  omega

theorem exists_nonsingular_of_finrank {N : Submodule K V} (hN : Module.finrank K N ≤ 2)
    (h5 : 5 ≤ Module.finrank K V) :
    ∃ m ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) N, Q m ≠ 0 ∧
      ∃ m' ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) N, polar Q m m' ≠ 0 := by
  obtain ⟨m₁, hm₁, m₂, hm₂, h12⟩ := exists_polar_ne_zero_of_finrank hQ hN h5
  by_cases h1 : Q m₁ = 0
  · by_cases h2 : Q m₂ = 0
    · refine ⟨m₁ + m₂, Submodule.add_mem _ hm₁ hm₂, ?_, m₂, hm₂, ?_⟩
      · rw [QuadraticMap.map_add Q, h1, h2, zero_add, zero_add]
        exact h12
      · rw [polar_add_left, polar_self_eq_zero h2, add_zero]
        exact h12
    · exact ⟨m₂, hm₂, h2, m₁, hm₁, by rw [polar_comm]; exact h12⟩
  · exact ⟨m₁, hm₁, h1, m₂, hm₂, h12⟩

omit hQ in
theorem eichler_diff_mem {u : V} {X : Submodule K V}
    (hXinv : ∀ s ∈ pointStabilizer Q u, ∀ x ∈ X, s.app x ∈ X) {x : V} (hx : x ∈ X) {a w : V}
    (ha : Q a = 0) (haw : polar Q a w = 0) (hua : polar Q u a = 0) (huw : polar Q u w = 0) :
    polar Q x a • w - (polar Q x w + Q w * polar Q x a) • a ∈ X := by
  have h := X.sub_mem (hXinv _ (Eom_mem_pointStabilizer ha haw hua huw) x hx) hx
  rw [Eom_app ha haw] at h
  convert h using 1
  abel

theorem orth_le_of_singular_mem (h5 : 5 ≤ Module.finrank K V) {u : V} {X : Submodule K V}
    (hXinv : ∀ s ∈ pointStabilizer Q u, ∀ x ∈ X, s.app x ∈ X) {s : V} (hsX : s ∈ X)
    (hs : Q s = 0) (hus : polar Q u s = 0) (hsL : s ∉ Submodule.span K {u}) :
    LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}) ≤ X := by
  obtain ⟨z', hz'P, hsz'⟩ : ∃ z' ∈ LinearMap.BilinForm.orthogonal (polarBilin Q)
      (Submodule.span K {u}), polar Q s z' = 1 := by
    obtain ⟨z, hzP, hsz⟩ := exists_polar_ne_zero_of_not_mem hQ hsL
    exact ⟨(polar Q s z)⁻¹ • z, Submodule.smul_mem _ _ hzP, by
      rw [polar_smul_right_eq, inv_mul_cancel₀ hsz]⟩
  have huz' := mem_orth_span_single_iff.mp hz'P
  let P' := HypPair.ofPolarEqOne hs hsz'
  have hQu' : Q P'.f = 0 := P'.Q_f
  have hsu' : polar Q s P'.f = 1 := P'.polar_ef
  have hu'def : P'.f = z' - Q z' • s := rfl
  have hua : polar Q u P'.f = 0 := by
    rw [hu'def, polar_sub_right, polar_smul_right_eq, huz', hus]
    ring
  have hd : ∀ w ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u, P'.f}),
      w - (polar Q s w + Q w) • P'.f ∈ X := by
    intro w hw
    obtain ⟨huw, hu'w⟩ := mem_orth_span_pair_iff.mp hw
    have := eichler_diff_mem hXinv hsX hQu' hu'w hua huw
    rwa [hsu', one_smul, mul_one] at this
  obtain ⟨w₁, hw₁, w₂, hw₂, h12⟩ :=
    exists_polar_ne_zero_of_finrank hQ (finrank_span_pair_le u P'.f) h5
  have hu'X : P'.f ∈ X := by
    have h3 := hd (w₁ + w₂) (Submodule.add_mem _ hw₁ hw₂)
    have h4 := X.sub_mem (X.sub_mem h3 (hd w₁ hw₁)) (hd w₂ hw₂)
    have h5' : polar Q w₁ w₂ • P'.f ∈ X := by
      have := X.neg_mem h4
      convert this using 1
      rw [polar_add_right, QuadraticMap.map_add Q w₁ w₂]
      module
    have h6 := X.smul_mem (polar Q w₁ w₂)⁻¹ h5'
    rwa [smul_smul, inv_mul_cancel₀ h12, one_smul] at h6
  have hRX : ∀ w ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u, P'.f}),
      w ∈ X := by
    intro w hw
    have := X.add_mem (hd w hw) (X.smul_mem (polar Q s w + Q w) hu'X)
    simpa using this
  intro p hp
  have hpu : polar Q u p = 0 := mem_orth_span_single_iff.mp hp
  have hpR : p - polar Q p P'.f • s ∈
      LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u, P'.f}) := by
    rw [mem_orth_span_pair_iff]
    constructor
    · rw [polar_sub_right, polar_smul_right_eq, hus, hpu]
      ring
    · rw [polar_sub_right, polar_smul_right_eq, polar_comm Q P'.f s, hsu', polar_comm Q P'.f p]
      ring
  have := X.add_mem (hRX _ hpR) (X.smul_mem (polar Q p P'.f) hsX)
  simpa using this

theorem exists_singular_mem [Finite K] [CharP K 2] (h5 : 5 ≤ Module.finrank K V) {u : V}
    (hQu : Q u = 0) {X : Submodule K V}
    (hXP : X ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}))
    (hXinv : ∀ s ∈ pointStabilizer Q u, ∀ x ∈ X, s.app x ∈ X) {y : V} (hyX : y ∈ X)
    (hyL : y ∉ Submodule.span K {u}) :
    ∃ s ∈ X, Q s = 0 ∧ polar Q u s = 0 ∧ s ∉ Submodule.span K {u} := by
  have hyu : polar Q u y = 0 := mem_orth_span_single_iff.mp (hXP hyX)
  by_cases hy0 : Q y = 0
  · exact ⟨y, hyX, hy0, hyu, hyL⟩
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨m, hm, hQm, m', hm', hmm'⟩ :=
    exists_nonsingular_of_finrank hQ (finrank_span_pair_le u y) h5
  obtain ⟨hum, hym⟩ := mem_orth_span_pair_iff.mp hm
  obtain ⟨hum', hym'⟩ := mem_orth_span_pair_iff.mp hm'
  obtain ⟨a, ha⟩ : IsSquare (Q m / Q y) := FiniteField.isSquare_of_char_two (ringChar.eq K 2) _
  have hay : a ^ 2 * Q y = Q m := by
    have h1 : a * a * Q y = Q m / Q y * Q y := by rw [← ha]
    rw [div_mul_cancel₀ _ hy0] at h1
    rw [pow_two]
    exact h1
  obtain ⟨v, hv⟩ : ∃ v : V, v = a • y + m := ⟨_, rfl⟩
  have hQv : Q v = 0 := by
    rw [hv, QuadraticMap.map_add Q, map_smul_eq_sq, polar_smul_left_eq, hym, hay]
    linear_combination (Q m) * h2
  have hvu : polar Q u v = 0 := by
    rw [hv, polar_add_right, polar_smul_right_eq, hyu, hum]
    ring
  have hyv : polar Q y v = 0 := by
    rw [hv, polar_add_right, polar_smul_right_eq, hym, polar_self_eq_two_mul]
    linear_combination (a * Q y) * h2
  have hyspan : y ∉ Submodule.span K {u, v} := by
    intro hy'
    obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hy'
    apply hy0
    rw [← hcd, QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hQu, hQv,
      polar_smul_left_eq, polar_smul_right_eq, hvu]
    ring
  obtain ⟨w, hw, hyw⟩ := exists_polar_ne_zero_of_not_mem hQ hyspan
  obtain ⟨huw, hvw⟩ := mem_orth_span_pair_iff.mp hw
  have hvX : v ∈ X := by
    have h := eichler_diff_mem hXinv hyX hQv hvw hvu huw
    rw [hyv, zero_smul, mul_zero, add_zero, zero_sub] at h
    have h1 : polar Q y w • v ∈ X := by simpa using X.neg_mem h
    have h3 := X.smul_mem (polar Q y w)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hyw, one_smul] at h3
  refine ⟨v, hvX, hQv, hvu, fun hvL => ?_⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hvL
  apply hmm'
  have hmeq : m = c • u - a • y := by
    rw [hc, hv]
    abel
  rw [hmeq, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, hum', hym']
  ring

theorem eq_span_or_eq_orth [Finite K] [CharP K 2] (h5 : 5 ≤ Module.finrank K V) {u : V}
    (hQu : Q u = 0) (X : Submodule K V) (hLX : Submodule.span K {u} ≤ X)
    (hXP : X ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}))
    (hXinv : ∀ s ∈ pointStabilizer Q u, ∀ x ∈ X, s.app x ∈ X) :
    X = Submodule.span K {u} ∨
      X = LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}) := by
  by_cases hXL : X = Submodule.span K {u}
  · exact Or.inl hXL
  refine Or.inr (le_antisymm hXP ?_)
  obtain ⟨y, hyX, hyL⟩ : ∃ y ∈ X, y ∉ Submodule.span K {u} := by
    by_contra hcon
    push Not at hcon
    exact hXL (le_antisymm hcon hLX)
  obtain ⟨s, hsX, hs, hus, hsL⟩ :=
    exists_singular_mem hQ h5 hQu hXP hXinv hyX hyL
  exact orth_le_of_singular_mem hQ h5 hXinv hsX hs hus hsL

end Orth

theorem Lom_eq_pCoreOf_pointStabilizer [FiniteDimensional K V] [Finite K] [CharP K 2]
    (hQ : (polarBilin Q).Nondegenerate) (h5 : 5 ≤ Module.finrank K V) {u : V} (hu : u ≠ 0)
    (hQu : Q u = 0) : Lom Q u = pCoreOf 2 (pointStabilizer Q u) := by
  haveI : Finite V := Module.finite_of_finite K
  refine eq_pCoreOf_of_section (isLinearAction_Gom Q) (L := Submodule.span K {u})
    (P := LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u})) hu
    (fun s hs => hs) (Lom_le_pointStabilizer u)
    (fun s hs n hn => conj_mem_Lom_of_mem_pointStabilizer hs hn) (isPGroup_Lom u) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [mem_orth_span_single_iff, polar_smul_right_eq, polar_self_eq_zero hQu, mul_zero]
  · intro s hs x hx
    refine mem_orth_span_single_iff.mpr ?_
    rw [polar_comm]
    exact polar_app_eq_zero_of_mem_pointStabilizer hu hs
      (by rw [polar_comm]; exact mem_orth_span_single_iff.mp hx)
  · intro s hs x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨c, hc⟩ := hs
    rw [Gom.map_smul, hc, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  · exact fun X hLX hXP hXinv => eq_span_or_eq_orth hQ h5 hQu X hLX hXP hXinv
  · intro g _ hgu hgx
    rw [mem_Lom, mem_rootGroup_iff hQ hQu hu]
    refine ⟨elementaryGroup_le_orthogonalGroup Q g.2, hgu, fun x hx => ?_⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      (hgx x (mem_orth_span_single_iff.mpr (by rw [polar_comm]; exact hx)))
    exact ⟨c, hc.symm⟩

end CFSG.ClassicalGroups.Orthogonal
