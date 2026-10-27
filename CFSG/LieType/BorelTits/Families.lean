module

public import CFSG.LieType.BorelTits.OrthogonalModels

public section

namespace CFSG.LieType.BorelTits

open Module Matrix CFSG.Assembly.LowTwoRank

universe u v w

section General

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

namespace ReflForm

variable {F : ReflForm K V}

theorem IsTotallyIsotropic.finrank_add_finrank_inf_le [FiniteDimensional K V]
    {Y : Submodule K V} (hY : F.IsTotallyIsotropic Y) (X : Submodule K V) :
    finrank K Y + finrank K ↥(X ⊓ Y) ≤ finrank K X + finrank K ↥(Y ⊓ F.perp X) := by
  have hle : Y ⊔ F.perp X ≤ F.perp (X ⊓ Y) :=
    sup_le (hY.trans (F.perp_antitone inf_le_right)) (F.perp_antitone inf_le_left)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq Y (F.perp X)
  have h2 := Submodule.finrank_mono hle
  have h3 := F.finrank_perp X
  have h4 := F.finrank_perp (X ⊓ Y)
  omega

variable (F) in
theorem finrank_le_finrank_inf_perp_span_singleton_add_one [FiniteDimensional K V]
    (A : Submodule K V) (v : V) : finrank K A ≤ finrank K ↥(A ⊓ F.perp (K ∙ v)) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq A (F.perp (K ∙ v))
  have h2 := Submodule.finrank_le (A ⊔ F.perp (K ∙ v))
  have h3 := F.finrank_perp (K ∙ v)
  have h4 : finrank K (K ∙ v) ≤ 1 := (finrank_span_le_card ({v} : Set V)).trans (by simp)
  omega

end ReflForm

namespace QuadForm

variable (Φ : QuadForm K V)

private theorem polar_smul_left' (c : K) (u v : V) :
    Φ.polar.β (c • u) v = c * Φ.polar.β u v := by
  rw [Φ.polar.smul_left, Φ.polar_σ, RingEquiv.refl_apply]

@[expose] def IsTotallySingular (W : Submodule K V) : Prop :=
  ∀ w ∈ W, Φ.Q w = 0

variable {Φ}

theorem IsTotallySingular.mono {W W' : Submodule K V} (hW : Φ.IsTotallySingular W)
    (h : W' ≤ W) : Φ.IsTotallySingular W' :=
  fun w hw => hW w (h hw)

theorem isTotallySingular_bot : Φ.IsTotallySingular ⊥ := by
  intro w hw
  rw [Submodule.mem_bot] at hw
  rw [hw, Φ.Q_zero]

theorem isTotallySingular_span_singleton {v : V} (hv : Φ.Q v = 0) :
    Φ.IsTotallySingular (K ∙ v) := by
  intro w hw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [Φ.Q_smul, hv, mul_zero]

theorem IsTotallySingular.isTotallyIsotropic {W : Submodule K V}
    (hW : Φ.IsTotallySingular W) : Φ.polar.IsTotallyIsotropic W := by
  intro v hv w hw
  have h := Φ.Q_add w v
  rw [hW _ (add_mem hw hv), hW w hw, hW v hv] at h
  linear_combination -h

theorem IsTotallySingular.sup {A B : Submodule K V} (hA : Φ.IsTotallySingular A)
    (hB : Φ.IsTotallySingular B) (hAB : A ≤ Φ.polar.perp B) : Φ.IsTotallySingular (A ⊔ B) := by
  intro w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
  rw [Φ.Q_add, hA a ha, hB b hb, Φ.polar_symm, hAB ha b hb, add_zero, add_zero]

theorem IsTotallySingular.sup_span {W : Submodule K V} (hW : Φ.IsTotallySingular W) {v : V}
    (hv : v ∈ Φ.polar.perp W) (hQv : Φ.Q v = 0) : Φ.IsTotallySingular (W ⊔ K ∙ v) :=
  hW.sup (isTotallySingular_span_singleton hQv) fun w hw =>
    Φ.polar.mem_perp_span_singleton.mpr ((Φ.polar_symm v w).trans (hv w hw))

theorem IsTotallySingular.two_mul_finrank_le [FiniteDimensional K V] {W : Submodule K V}
    (hW : Φ.IsTotallySingular W) : 2 * finrank K W ≤ finrank K V := by
  have h1 := Φ.polar.finrank_perp W
  have h2 := Submodule.finrank_mono hW.isTotallyIsotropic
  omega

variable (Φ) in
@[expose] def IsLagrangian (W : Submodule K V) : Prop :=
  Φ.IsTotallySingular W ∧ 2 * finrank K W = finrank K V

theorem IsLagrangian.perp_eq [FiniteDimensional K V] {X : Submodule K V}
    (hX : Φ.IsLagrangian X) : Φ.polar.perp X = X := by
  have h1 := Φ.polar.finrank_perp X
  have h2 := hX.2
  exact (Submodule.eq_of_le_of_finrank_eq hX.1.isTotallyIsotropic (by omega)).symm

theorem IsLagrangian.eq_of_le [FiniteDimensional K V] {X Y : Submodule K V}
    (hX : Φ.IsLagrangian X) (hY : Φ.IsTotallySingular Y) (hXY : X ≤ Y) : X = Y := by
  have h1 := hY.two_mul_finrank_le
  have h2 := Submodule.finrank_mono hXY
  exact Submodule.eq_of_le_of_finrank_eq hXY (by have := hX.2; omega)

theorem isLagrangian_iff_maximal [FiniteDimensional K V] {X₀ : Submodule K V}
    (hX₀ : Φ.IsLagrangian X₀) {X : Submodule K V} :
    Φ.IsLagrangian X ↔ Maximal Φ.IsTotallySingular X := by
  refine ⟨fun hX => ⟨hX.1, fun Y hY hXY => (hX.eq_of_le hY hXY).ge⟩, fun hX => ?_⟩
  refine ⟨hX.1, le_antisymm hX.1.two_mul_finrank_le ?_⟩
  have hsub : X₀ ⊓ Φ.polar.perp X ≤ X ⊓ X₀ := fun y hy => by
    obtain ⟨hy₀, hyX⟩ := Submodule.mem_inf.mp hy
    have hle := hX.2 (hX.1.sup_span hyX (hX₀.1 y hy₀)) le_sup_left
    exact Submodule.mem_inf.mpr
      ⟨hle (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)), hy₀⟩
  have h1 := hX₀.1.isTotallyIsotropic.finrank_add_finrank_inf_le X
  have h2 := Submodule.finrank_mono hsub
  have h3 := hX₀.2
  omega

theorem finrank_eq_of_maximal [FiniteDimensional K V] {n : ℕ} (hn : finrank K V = 2 * n)
    {X₀ : Submodule K V} (hX₀ : Φ.IsLagrangian X₀) {X : Submodule K V}
    (hX : Maximal Φ.IsTotallySingular X) : finrank K X = n := by
  have := ((isLagrangian_iff_maximal hX₀).mpr hX).2
  omega

theorem exists_isLagrangian_le [FiniteDimensional K V] {X₀ : Submodule K V}
    (hX₀ : Φ.IsLagrangian X₀) {W : Submodule K V} (hW : Φ.IsTotallySingular W) :
    ∃ X, Φ.IsLagrangian X ∧ W ≤ X := by
  obtain ⟨M, ⟨hWM, hM⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian K V) {M | W ≤ M ∧ Φ.IsTotallySingular M} ⟨W, le_rfl, hW⟩
  refine ⟨M, (isLagrangian_iff_maximal hX₀).mpr ⟨hM, fun Y hY hMY => ?_⟩, hWM⟩
  by_contra h
  exact hmax Y ⟨hWM.trans hMY, hY⟩ (lt_of_le_of_ne hMY fun e => h (e ▸ le_rfl))

private theorem finrank_inf_le_finrank_inf_add_one [FiniteDimensional K V]
    {I Y : Submodule K V} (hIY : I ≤ Y) (hI : finrank K I + 1 = finrank K Y)
    (X : Submodule K V) : finrank K ↥(X ⊓ Y) ≤ finrank K ↥(X ⊓ I) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (X ⊓ Y) I
  have h2 : X ⊓ Y ⊓ I = X ⊓ I := by rw [inf_assoc, inf_eq_right.mpr hIY]
  have h3 := Submodule.finrank_mono (sup_le inf_le_right hIY : X ⊓ Y ⊔ I ≤ Y)
  rw [h2] at h1
  omega

theorem IsLagrangian.mem_of_mem_perp [FiniteDimensional K V] {I Y : Submodule K V}
    (hY : Φ.IsLagrangian Y) (hIY : I ≤ Y) (hI : finrank K I + 1 = finrank K Y) {y u : V}
    (hy : y ∈ Y) (hyI : y ∉ I) (hu : u ∈ Φ.polar.perp I) (hyu : Φ.polar.β y u = 0) : u ∈ Y := by
  have hle : I ⊔ K ∙ y ≤ Y := sup_le hIY ((Submodule.span_singleton_le_iff_mem _ _).mpr hy)
  have hY' : I ⊔ K ∙ y = Y := by
    have h1 := Submodule.finrank_lt_finrank_of_lt (Submodule.lt_sup_iff_notMem.mpr hyI)
    have h2 := Submodule.finrank_mono hle
    exact Submodule.eq_of_le_of_finrank_eq hle (by omega)
  rw [← hY.perp_eq, ← hY', Φ.polar.perp_sup]
  exact Submodule.mem_inf.mpr ⟨hu, Φ.polar.mem_perp_span_singleton.mpr hyu⟩

theorem IsLagrangian.mem_or_mem_of_mem_sup [FiniteDimensional K V] {Y Y' : Submodule K V}
    (hY : Φ.IsLagrangian Y) (hY' : Φ.IsLagrangian Y')
    (hYY' : finrank K ↥(Y ⊓ Y') + 1 = finrank K Y) {w : V} (hw : w ∈ Y ⊔ Y')
    (hQw : Φ.Q w = 0) : w ∈ Y ∨ w ∈ Y' := by
  obtain ⟨y, hy, y', hy', rfl⟩ := Submodule.mem_sup.mp hw
  have hyy' : Φ.polar.β y' y = 0 := by
    rw [Φ.Q_add, hY.1 y hy, hY'.1 y' hy', zero_add, zero_add] at hQw
    rw [Φ.polar_symm]
    exact hQw
  by_cases hy'Y : y' ∈ Y
  · exact Or.inl (add_mem hy hy'Y)
  · have hfin : finrank K ↥(Y ⊓ Y') + 1 = finrank K Y' := by
      have := hY.2
      have := hY'.2
      omega
    refine Or.inr (add_mem ?_ hy')
    exact hY'.mem_of_mem_perp inf_le_right hfin hy' (fun h => hy'Y (Submodule.mem_inf.mp h).1)
      (Φ.polar.perp_antitone inf_le_left (hY.1.isTotallyIsotropic hy)) hyy'

theorem IsLagrangian.finrank_inf_flip [FiniteDimensional K V] {n : ℕ}
    (hn : finrank K V = 2 * n) {X Y Y' : Submodule K V} (hX : Φ.IsLagrangian X)
    (hY : Φ.IsLagrangian Y) (hY' : Φ.IsLagrangian Y') (hI : finrank K ↥(Y ⊓ Y') + 1 = n) :
    finrank K ↥(X ⊓ Y) = finrank K ↥(X ⊓ (Y ⊓ Y')) ∧
        finrank K ↥(X ⊓ Y') = finrank K ↥(X ⊓ (Y ⊓ Y')) + 1 ∨
      finrank K ↥(X ⊓ Y) = finrank K ↥(X ⊓ (Y ⊓ Y')) + 1 ∧
        finrank K ↥(X ⊓ Y') = finrank K ↥(X ⊓ (Y ⊓ Y')) := by
  have hXn := hX.2
  have hYn := hY.2
  have hY'n := hY'.2
  have hle1 := finrank_inf_le_finrank_inf_add_one (inf_le_left : Y ⊓ Y' ≤ Y) (by omega) X
  have hle2 := finrank_inf_le_finrank_inf_add_one (inf_le_right : Y ⊓ Y' ≤ Y') (by omega) X
  have hsub1 : X ⊓ (Y ⊓ Y') ≤ X ⊓ Y := inf_le_inf_left X inf_le_left
  have hsub2 : X ⊓ (Y ⊓ Y') ≤ X ⊓ Y' := inf_le_inf_left X inf_le_right
  have hge1 := Submodule.finrank_mono hsub1
  have hge2 := Submodule.finrank_mono hsub2
  have hnb : ¬(finrank K ↥(X ⊓ (Y ⊓ Y')) < finrank K ↥(X ⊓ Y) ∧
      finrank K ↥(X ⊓ (Y ⊓ Y')) < finrank K ↥(X ⊓ Y')) := by
    rintro ⟨h1, h2⟩
    obtain ⟨y, hy, hyI⟩ :=
      IsConcreteLE.exists_of_lt (Submodule.lt_of_le_of_finrank_lt_finrank hsub1 h1)
    obtain ⟨y', hy', hy'I⟩ :=
      IsConcreteLE.exists_of_lt (Submodule.lt_of_le_of_finrank_lt_finrank hsub2 h2)
    rw [Submodule.mem_inf] at hy hy'
    have hyY' : y ∈ Y' := hY'.mem_of_mem_perp inf_le_right (by omega) hy'.2
      (fun h => hy'I (Submodule.mem_inf.mpr ⟨hy'.1, h⟩))
      (Φ.polar.perp_antitone inf_le_left (hY.1.isTotallyIsotropic hy.2))
      (hX.1.isTotallyIsotropic hy.1 y' hy'.1)
    exact hyI (Submodule.mem_inf.mpr ⟨hy.1, Submodule.mem_inf.mpr ⟨hy.2, hyY'⟩⟩)
  have hne : ¬(finrank K ↥(X ⊓ Y) = finrank K ↥(X ⊓ (Y ⊓ Y')) ∧
      finrank K ↥(X ⊓ Y') = finrank K ↥(X ⊓ (Y ⊓ Y'))) := by
    rintro ⟨h1, h2⟩
    have e1 := Submodule.eq_of_le_of_finrank_eq hsub1 h1.symm
    have e2 := Submodule.eq_of_le_of_finrank_eq hsub2 h2.symm
    have hIiso : Φ.polar.IsTotallyIsotropic (Y ⊓ Y') := hY.1.isTotallyIsotropic.mono inf_le_left
    have hA := hX.1.isTotallyIsotropic.finrank_add_finrank_inf_le (Y ⊓ Y')
    rw [inf_comm (Y ⊓ Y') X] at hA
    have hlt : X ⊓ (Y ⊓ Y') < X ⊓ Φ.polar.perp (Y ⊓ Y') :=
      Submodule.lt_of_le_of_finrank_lt_finrank (inf_le_inf_left X hIiso) (by omega)
    obtain ⟨w, hw, hwI⟩ := IsConcreteLE.exists_of_lt hlt
    rw [Submodule.mem_inf] at hw
    have hperp : Y ⊔ Y' = Φ.polar.perp (Y ⊓ Y') := by
      refine Submodule.eq_of_le_of_finrank_eq
        (sup_le (hY.1.isTotallyIsotropic.trans (Φ.polar.perp_antitone inf_le_left))
          (hY'.1.isTotallyIsotropic.trans (Φ.polar.perp_antitone inf_le_right))) ?_
      have := Submodule.finrank_sup_add_finrank_inf_eq Y Y'
      have := Φ.polar.finrank_perp (Y ⊓ Y')
      omega
    rcases hY.mem_or_mem_of_mem_sup hY' (by omega) (by rw [hperp]; exact hw.2) (hX.1 w hw.1)
      with h | h
    · exact hwI (by rw [e1]; exact Submodule.mem_inf.mpr ⟨hw.1, h⟩)
    · exact hwI (by rw [e2]; exact Submodule.mem_inf.mpr ⟨hw.1, h⟩)
  omega

theorem IsLagrangian.exists_finrank_inf_eq_succ [FiniteDimensional K V] {n : ℕ}
    (hn : finrank K V = 2 * n) {Y Z : Submodule K V} (hY : Φ.IsLagrangian Y)
    (hZ : Φ.IsLagrangian Z) (hYZ : finrank K ↥(Y ⊓ Z) < n) :
    ∃ Y', Φ.IsLagrangian Y' ∧ finrank K ↥(Y ⊓ Y') + 1 = n ∧
      finrank K ↥(Y' ⊓ Z) = finrank K ↥(Y ⊓ Z) + 1 := by
  have hYn := hY.2
  have hZn := hZ.2
  obtain ⟨z, hz, hzY⟩ : ∃ z ∈ Z, z ∉ Y := by
    by_contra! h
    have := Submodule.finrank_mono (le_inf h le_rfl : Z ≤ Y ⊓ Z)
    omega
  set A := Y ⊓ Φ.polar.perp (K ∙ z)
  have hAY : finrank K Y ≤ finrank K A + 1 :=
    Φ.polar.finrank_le_finrank_inf_perp_span_singleton_add_one Y z
  have hzA : z ∉ A := fun h => hzY (Submodule.mem_inf.mp h).1
  have hY's : Φ.IsTotallySingular (A ⊔ K ∙ z) :=
    (hY.1.mono inf_le_left).sup (isTotallySingular_span_singleton (hZ.1 z hz)) inf_le_right
  have h1 := Submodule.finrank_lt_finrank_of_lt (Submodule.lt_sup_iff_notMem.mpr hzA)
  have h2 := hY's.two_mul_finrank_le
  have hY' : Φ.IsLagrangian (A ⊔ K ∙ z) := ⟨hY's, by omega⟩
  have hzY' : z ∈ A ⊔ K ∙ z := Submodule.mem_sup_right (Submodule.mem_span_singleton_self z)
  have hYY' : finrank K ↥(Y ⊓ (A ⊔ K ∙ z)) + 1 = n := by
    have h3 := Submodule.finrank_mono (le_inf inf_le_left le_sup_left : A ≤ Y ⊓ (A ⊔ K ∙ z))
    have h4 : finrank K ↥(Y ⊓ (A ⊔ K ∙ z)) < finrank K Y := by
      refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left fun h => hzY ?_)
      rw [hY.eq_of_le hY's (h.symm.le.trans inf_le_right)]
      exact hzY'
    omega
  refine ⟨A ⊔ K ∙ z, hY', hYY', ?_⟩
  have hZY' : Y ⊓ Z ≤ (A ⊔ K ∙ z) ⊓ Z := fun u hu => by
    rw [Submodule.mem_inf] at hu ⊢
    refine ⟨Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨hu.1, ?_⟩), hu.2⟩
    exact Φ.polar.mem_perp_span_singleton.mpr (hZ.1.isTotallyIsotropic hu.2 z hz)
  have hlt : Y ⊓ Z < (A ⊔ K ∙ z) ⊓ Z := lt_of_le_of_ne hZY' fun h => hzY <| by
    have : z ∈ (A ⊔ K ∙ z) ⊓ Z := Submodule.mem_inf.mpr ⟨hzY', hz⟩
    rw [← h] at this
    exact (Submodule.mem_inf.mp this).1
  have h5 := Submodule.finrank_lt_finrank_of_lt hlt
  have h6 := finrank_inf_le_finrank_inf_add_one (inf_le_right : Y ⊓ (A ⊔ K ∙ z) ≤ A ⊔ K ∙ z)
    (by omega) Z
  have h7 := Submodule.finrank_mono
    (inf_le_inf_left Z inf_le_left : Z ⊓ (Y ⊓ (A ⊔ K ∙ z)) ≤ Z ⊓ Y)
  rw [inf_comm Z (A ⊔ K ∙ z), inf_comm Z Y] at *
  omega

theorem IsLagrangian.even_add_add [FiniteDimensional K V] {n : ℕ} (hn : finrank K V = 2 * n)
    {X Y Z : Submodule K V} (hX : Φ.IsLagrangian X) (hY : Φ.IsLagrangian Y)
    (hZ : Φ.IsLagrangian Z) :
    Even ((n - finrank K ↥(X ⊓ Y)) + (n - finrank K ↥(Y ⊓ Z)) + (n - finrank K ↥(X ⊓ Z))) := by
  suffices h : ∀ k, ∀ Y, Φ.IsLagrangian Y → n - finrank K ↥(Y ⊓ Z) = k →
      Even ((n - finrank K ↥(X ⊓ Y)) + (n - finrank K ↥(Y ⊓ Z)) + (n - finrank K ↥(X ⊓ Z))) from
    h _ Y hY rfl
  intro k
  induction k with
  | zero =>
    intro Y hY hk
    have hYn := hY.2
    have hle := Submodule.finrank_mono (inf_le_left : Y ⊓ Z ≤ Y)
    have hYZ : Y ⊓ Z = Y := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
    have hYeq : Y = Z := hY.eq_of_le hZ.1 (hYZ.symm.le.trans inf_le_right)
    subst hYeq
    rw [inf_idem, Nat.even_iff]
    omega
  | succ k ih =>
    intro Y hY hk
    have hYn := hY.2
    obtain ⟨Y', hY', hYY', hY'Z⟩ := hY.exists_finrank_inf_eq_succ hn hZ (by omega)
    have hih := ih Y' hY' (by omega)
    have hflip := hX.finrank_inf_flip hn hY hY' hYY'
    have hXn := hX.2
    have h1 := Submodule.finrank_mono (inf_le_left : X ⊓ Y ≤ X)
    have h2 := Submodule.finrank_mono (inf_le_left : X ⊓ Y' ≤ X)
    have h3 := Submodule.finrank_mono (inf_le_left : X ⊓ Z ≤ X)
    have h4 := Submodule.finrank_mono (inf_le_left : Y' ⊓ Z ≤ Y')
    have hY'n := hY'.2
    rw [Nat.even_iff] at hih ⊢
    omega

theorem exists_isLagrangian_pair [FiniteDimensional K V] {n : ℕ} (hn : finrank K V = 2 * n)
    {X₀ : Submodule K V} (hX₀ : Φ.IsLagrangian X₀) {I : Submodule K V}
    (hI : Φ.IsTotallySingular I) (hIn : finrank K I + 1 = n) :
    ∃ Y Y' : Submodule K V, Y ≠ Y' ∧ Φ.IsLagrangian Y ∧ Φ.IsLagrangian Y' ∧ I ≤ Y ∧ I ≤ Y' ∧
      ∀ X, Φ.IsLagrangian X → I ≤ X → X = Y ∨ X = Y' := by
  obtain ⟨Y, hY, hIY⟩ := exists_isLagrangian_le hX₀ hI
  have hYn := hY.2
  have hYperp : Y ≤ Φ.polar.perp I :=
    hY.1.isTotallyIsotropic.trans (Φ.polar.perp_antitone hIY)
  obtain ⟨w, hw, hwY⟩ : ∃ w ∈ Φ.polar.perp I, w ∉ Y := by
    refine IsConcreteLE.exists_of_lt (Submodule.lt_of_le_of_finrank_lt_finrank hYperp ?_)
    have := Φ.polar.finrank_perp I
    omega
  obtain ⟨y, hy, hyw⟩ : ∃ y ∈ Y, Φ.polar.β y w ≠ 0 := by
    by_contra! h
    have hwY' : w ∈ Φ.polar.perp Y := h
    rw [hY.perp_eq] at hwY'
    exact hwY hwY'
  set z := w + (-(Φ.Q w / Φ.polar.β y w)) • y with hz
  have hzI : z ∈ Φ.polar.perp I := add_mem hw (Submodule.smul_mem _ _ (hYperp hy))
  have hQz : Φ.Q z = 0 := by
    rw [hz, Φ.Q_add, Φ.Q_smul, hY.1 y hy, mul_zero, add_zero, Φ.polar.smul_right,
      Φ.polar_symm w y, neg_mul, div_mul_cancel₀ _ hyw, add_neg_cancel]
  have hzY : z ∉ Y := fun h => hwY <| by
    have := sub_mem h (Submodule.smul_mem Y (-(Φ.Q w / Φ.polar.β y w)) hy)
    rwa [hz, add_sub_cancel_right] at this
  have hY's : Φ.IsTotallySingular (I ⊔ K ∙ z) := hI.sup_span hzI hQz
  have h1 := Submodule.finrank_lt_finrank_of_lt
    (Submodule.lt_sup_iff_notMem.mpr fun h => hzY (hIY h))
  have h2 := hY's.two_mul_finrank_le
  have hY' : Φ.IsLagrangian (I ⊔ K ∙ z) := ⟨hY's, by omega⟩
  have hzY' : z ∈ I ⊔ K ∙ z := Submodule.mem_sup_right (Submodule.mem_span_singleton_self z)
  have hne : Y ≠ I ⊔ K ∙ z := fun h => hzY (h ▸ hzY')
  have hII : finrank K ↥(Y ⊓ (I ⊔ K ∙ z)) + 1 = n := by
    have h3 := Submodule.finrank_mono (le_inf hIY le_sup_left : I ≤ Y ⊓ (I ⊔ K ∙ z))
    have h4 : finrank K ↥(Y ⊓ (I ⊔ K ∙ z)) < finrank K Y :=
      Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left fun h =>
        hne (hY.eq_of_le hY'.1 (h.symm.le.trans inf_le_right)))
    omega
  have hIeq : I = Y ⊓ (I ⊔ K ∙ z) :=
    Submodule.eq_of_le_of_finrank_eq (le_inf hIY le_sup_left) (by omega)
  refine ⟨Y, I ⊔ K ∙ z, hne, hY, hY', hIY, le_sup_left, fun X hX hIX => ?_⟩
  have hflip := hX.finrank_inf_flip hn hY hY' hII
  rw [← hIeq, inf_eq_right.mpr hIX] at hflip
  have hXn := hX.2
  rcases hflip with ⟨-, h⟩ | ⟨h, -⟩
  · have : X ⊓ (I ⊔ K ∙ z) = X := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
    exact Or.inr (hX.eq_of_le hY'.1 (this.symm.le.trans inf_le_right))
  · have : X ⊓ Y = X := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
    exact Or.inl (hX.eq_of_le hY.1 (this.symm.le.trans inf_le_right))

theorem injective_of_Q {g : V →ₗ[K] V} (hg : ∀ v, Φ.Q (g v) = Φ.Q v) :
    Function.Injective g := by
  refine (injective_iff_map_eq_zero g).mpr fun v hv => Φ.polar.nondeg v fun u => ?_
  rw [← Φ.polar_map_of_Q hg, hv, Φ.polar.β_zero_left]

theorem finrank_map_of_Q {g : V →ₗ[K] V} (hg : ∀ v, Φ.Q (g v) = Φ.Q v) (W : Submodule K V) :
    finrank K ↥(W.map g) = finrank K W :=
  (Submodule.equivMapOfInjective g (injective_of_Q hg) W).finrank_eq.symm

theorem IsLagrangian.map {X : Submodule K V} (hX : Φ.IsLagrangian X) {g : V →ₗ[K] V}
    (hg : ∀ v, Φ.Q (g v) = Φ.Q v) : Φ.IsLagrangian (X.map g) := by
  refine ⟨?_, by rw [finrank_map_of_Q hg]; exact hX.2⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [hg]
  exact hX.1 x hx

end QuadForm

@[expose] noncomputable def dicksonInvariant (X₀ : Submodule K V) (g : Module.End K V) : ZMod 2 :=
  (finrank K X₀ - finrank K ↥(X₀ ⊓ X₀.map g) : ℕ)

namespace QuadForm

variable {Φ : QuadForm K V}

theorem dicksonInvariant_mul [FiniteDimensional K V] {X₀ : Submodule K V}
    (hX₀ : Φ.IsLagrangian X₀) {g h : Module.End K V} (hg : ∀ v, Φ.Q (g v) = Φ.Q v)
    (hh : ∀ v, Φ.Q (h v) = Φ.Q v) :
    dicksonInvariant X₀ (g * h) = dicksonInvariant X₀ g + dicksonInvariant X₀ h := by
  have hgh : ∀ v, Φ.Q ((g * h) v) = Φ.Q v := fun v => by rw [Module.End.mul_apply, hg, hh]
  have hpar := hX₀.even_add_add hX₀.2.symm (hX₀.map hg) (hX₀.map hgh)
  have hmap : X₀.map g ⊓ X₀.map (g * h) = (X₀ ⊓ X₀.map h).map g := by
    rw [Module.End.mul_eq_comp, Submodule.map_comp, Submodule.map_inf g (injective_of_Q hg)]
  rw [hmap, finrank_map_of_Q hg, Nat.even_iff] at hpar
  have h1 := Submodule.finrank_mono (inf_le_left : X₀ ⊓ X₀.map g ≤ X₀)
  have h2 := Submodule.finrank_mono (inf_le_left : X₀ ⊓ X₀.map h ≤ X₀)
  have h3 := Submodule.finrank_mono (inf_le_left : X₀ ⊓ X₀.map (g * h) ≤ X₀)
  rw [dicksonInvariant, dicksonInvariant, dicksonInvariant, ← Nat.cast_add,
    ZMod.natCast_eq_natCast_iff']
  omega

theorem dicksonInvariant_eq [FiniteDimensional K V] {X₀ X : Submodule K V}
    (hX₀ : Φ.IsLagrangian X₀) (hX : Φ.IsLagrangian X) {g : Module.End K V}
    (hg : ∀ v, Φ.Q (g v) = Φ.Q v) : dicksonInvariant X₀ g = dicksonInvariant X g := by
  have hn := hX₀.2.symm
  have hXn := hX.2
  have p1 := hX₀.even_add_add hn hX (hX₀.map hg)
  have p2 := hX.even_add_add hn (hX.map hg) (hX₀.map hg)
  rw [← Submodule.map_inf g (injective_of_Q hg), finrank_map_of_Q hg, inf_comm X X₀] at p2
  rw [Nat.even_iff] at p1 p2
  have h1 := Submodule.finrank_mono (inf_le_left : X₀ ⊓ X ≤ X₀)
  have h2 := Submodule.finrank_mono (inf_le_left : X ⊓ X₀.map g ≤ X)
  have h3 := Submodule.finrank_mono (inf_le_left : X₀ ⊓ X₀.map g ≤ X₀)
  have h4 := Submodule.finrank_mono (inf_le_left : X ⊓ X.map g ≤ X)
  rw [dicksonInvariant, dicksonInvariant, ZMod.natCast_eq_natCast_iff']
  omega

theorem dicksonInvariant_eq_one_of_reflection [FiniteDimensional K V] {X₀ : Submodule K V}
    (hX₀ : Φ.IsLagrangian X₀) {g : Module.End K V} (hg : ∀ v, Φ.Q (g v) = Φ.Q v)
    {Z : Submodule K V} (hZ : Φ.IsTotallySingular Z) {a : V} (ha : a ∈ Φ.polar.perp Z)
    (hQa : Φ.Q a ≠ 0)
    (hrefl : ∀ v ∈ Φ.polar.perp Z, g v - (v - (Φ.polar.β v a / Φ.Q a) • a) ∈ Z) :
    dicksonInvariant X₀ g = 1 := by
  obtain ⟨X, hX, hZX⟩ := exists_isLagrangian_le hX₀ hZ
  rw [dicksonInvariant_eq hX₀ hX hg]
  have hgZ : Z.map g ≤ Z := by
    rintro _ ⟨z, hz, rfl⟩
    have h := hrefl z (hZ.isTotallyIsotropic hz)
    rw [ha z hz, zero_div, zero_smul, sub_zero] at h
    simpa using add_mem h hz
  have hZg : Z ≤ Z.map g := (Submodule.eq_of_le_of_finrank_eq hgZ (finrank_map_of_Q hg Z)).ge
  have hXZ : X ≤ Φ.polar.perp Z := hX.1.isTotallyIsotropic.trans (Φ.polar.perp_antitone hZX)
  have hsub : X ⊓ Φ.polar.perp (K ∙ a) ≤ X ⊓ X.map g := by
    intro x hx
    rw [Submodule.mem_inf] at hx ⊢
    have h := hrefl x (hXZ hx.1)
    rw [Φ.polar_symm x a, Φ.polar.mem_perp_span_singleton.mp hx.2, zero_div, zero_smul,
      sub_zero] at h
    refine ⟨hx.1, ?_⟩
    have e : x = g x - (g x - x) := by abel
    rw [e]
    exact sub_mem (Submodule.mem_map_of_mem hx.1) (Submodule.map_mono hZX (hZg h))
  have hne : ¬X ≤ X.map g := by
    intro hle
    have heq : X = X.map g := Submodule.eq_of_le_of_finrank_eq hle (finrank_map_of_Q hg X).symm
    obtain ⟨x, hx, hxa⟩ : ∃ x ∈ X, Φ.polar.β x a ≠ 0 := by
      by_contra! h
      have haX : a ∈ Φ.polar.perp X := h
      rw [hX.perp_eq] at haX
      exact hQa (hX.1 a haX)
    have h := hrefl x (hXZ hx)
    have hgx : g x ∈ X := by
      rw [heq]
      exact Submodule.mem_map_of_mem hx
    have hca : (Φ.polar.β x a / Φ.Q a) • a ∈ X := by
      have e : (Φ.polar.β x a / Φ.Q a) • a =
          (g x - (x - (Φ.polar.β x a / Φ.Q a) • a)) - g x + x := by abel
      rw [e]
      exact add_mem (sub_mem (hZX h) hgx) hx
    exact hQa (hX.1 a ((Submodule.smul_mem_iff X (div_ne_zero hxa hQa)).mp hca))
  have h1 := Φ.polar.finrank_le_finrank_inf_perp_span_singleton_add_one X a
  have h2 := Submodule.finrank_mono hsub
  have h3 : finrank K ↥(X ⊓ X.map g) < finrank K X :=
    Submodule.finrank_lt_finrank_of_lt
      (lt_of_le_of_ne inf_le_left fun h => hne (h.symm.le.trans inf_le_right))
  rw [dicksonInvariant, show finrank K X - finrank K ↥(X ⊓ X.map g) = 1 by omega, Nat.cast_one]

theorem apply_mem_of_dicksonInvariant_eq_zero [FiniteDimensional K V] {X A : Submodule K V}
    (hAX : A ≤ X) (hrank : finrank K X = finrank K A + 1) {g : Module.End K V}
    (hg : ∀ v, Φ.Q (g v) = Φ.Q v) (hgA : ∀ v ∈ A, g v ∈ A) (hε : dicksonInvariant X g = 0) :
    ∀ v ∈ X, g v ∈ X := by
  have hgA' : A.map g ≤ A := Submodule.map_le_iff_le_comap.mpr hgA
  have hAgX : A ≤ X ⊓ X.map g := le_inf hAX
    ((Submodule.eq_of_le_of_finrank_eq hgA' (finrank_map_of_Q hg A)).ge.trans
      (Submodule.map_mono hAX))
  have h1 := Submodule.finrank_mono hAgX
  have h2 := Submodule.finrank_mono (inf_le_left : X ⊓ X.map g ≤ X)
  have hXX : X ⊓ X.map g = X := by
    refine Submodule.eq_of_le_of_finrank_eq inf_le_left ?_
    rw [dicksonInvariant, ← Nat.cast_zero, ZMod.natCast_eq_natCast_iff'] at hε
    omega
  have hle : X ≤ X.map g := hXX.symm.le.trans inf_le_right
  have heq : X.map g = X := (Submodule.eq_of_le_of_finrank_eq hle (finrank_map_of_Q hg X).symm).symm
  exact fun v hv => heq ▸ Submodule.mem_map_of_mem hv

@[expose] noncomputable def dicksonHom [FiniteDimensional K V] {H : Type w} [Group H]
    (ρ : H →* Module.End K V) (hρ : ∀ h v, Φ.Q (ρ h v) = Φ.Q v) {X₀ : Submodule K V}
    (hX₀ : Φ.IsLagrangian X₀) : H →* Multiplicative (ZMod 2) where
  toFun h := Multiplicative.ofAdd (dicksonInvariant X₀ (ρ h))
  map_one' := by
    rw [map_one, dicksonInvariant, Module.End.one_eq_id, Submodule.map_id, inf_idem, Nat.sub_self,
      Nat.cast_zero, ofAdd_zero]
  map_mul' g h := by
    rw [map_mul, dicksonInvariant_mul hX₀ (hρ g) (hρ h), ofAdd_add]

@[simp] theorem dicksonHom_apply [FiniteDimensional K V] {H : Type w} [Group H]
    (ρ : H →* Module.End K V) (hρ : ∀ h v, Φ.Q (ρ h v) = Φ.Q v) {X₀ : Submodule K V}
    (hX₀ : Φ.IsLagrangian X₀) (h : H) :
    dicksonHom ρ hρ hX₀ h = Multiplicative.ofAdd (dicksonInvariant X₀ (ρ h)) :=
  rfl

variable (Φ) in
@[expose] def prodNeg : QuadForm K (V × V) where
  Q p := Φ.Q p.1 - Φ.Q p.2
  polar :=
    { σ := RingEquiv.refl K
      β := fun p q => Φ.polar.β p.1 q.1 - Φ.polar.β p.2 q.2
      add_left := fun p p' q => by
        simp only [Prod.fst_add, Prod.snd_add, Φ.polar.add_left]
        ring
      smul_left := fun c p q => by
        simp only [Prod.smul_fst, Prod.smul_snd, polar_smul_left', RingEquiv.refl_apply]
        ring
      add_right := fun p q q' => by
        simp only [Prod.fst_add, Prod.snd_add, Φ.polar.add_right]
        ring
      smul_right := fun c p q => by
        simp only [Prod.smul_fst, Prod.smul_snd, Φ.polar.smul_right]
        ring
      refl := fun p q h => by
        have h' : Φ.polar.β p.1 q.1 - Φ.polar.β p.2 q.2 = 0 := h
        show Φ.polar.β q.1 p.1 - Φ.polar.β q.2 p.2 = 0
        rw [Φ.polar_symm q.1, Φ.polar_symm q.2]
        exact h'
      nondeg := fun p h => by
        have h1 : p.1 = 0 := Φ.polar.nondeg _ fun u => by
          simpa [Φ.polar.β_zero_right] using h (u, 0)
        have h2 : p.2 = 0 := Φ.polar.nondeg _ fun u => by
          simpa [Φ.polar.β_zero_right] using h (0, u)
        exact Prod.ext h1 h2 }
  polar_σ := rfl
  Q_smul := fun c p => by
    simp only [Prod.smul_fst, Prod.smul_snd, Φ.Q_smul]
    ring
  Q_add := fun p q => by
    simp only [Prod.fst_add, Prod.snd_add, Φ.Q_add]
    ring

variable (Φ) in
@[simp] theorem prodNeg_Q (p : V × V) : Φ.prodNeg.Q p = Φ.Q p.1 - Φ.Q p.2 :=
  rfl

variable (Φ) in
@[simp] theorem prodNeg_polar_β (p q : V × V) :
    Φ.prodNeg.polar.β p q = Φ.polar.β p.1 q.1 - Φ.polar.β p.2 q.2 :=
  rfl

variable (Φ) in
theorem isLagrangian_prodNeg_diagonal [FiniteDimensional K V] :
    Φ.prodNeg.IsLagrangian (LinearMap.range (LinearMap.id.prod LinearMap.id : V →ₗ[K] V × V)) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨v, rfl⟩
    simp
  · rw [LinearMap.finrank_range_of_inj fun v w h => congrArg Prod.fst h, Module.finrank_prod]
    ring

theorem prodNeg_Q_prodMap {g : Module.End K V} (hg : ∀ v, Φ.Q (g v) = Φ.Q v) (p : V × V) :
    Φ.prodNeg.Q (g.prodMap LinearMap.id p) = Φ.prodNeg.Q p := by
  simp [hg]

theorem dicksonInvariant_prodMap_eq_one [FiniteDimensional K V] {g : Module.End K V}
    (hg : ∀ v, Φ.Q (g v) = Φ.Q v) {Z : Submodule K V} (hZ : Φ.IsTotallySingular Z) {a : V}
    (ha : a ∈ Φ.polar.perp Z) (hQa : Φ.Q a ≠ 0)
    (hrefl : ∀ v ∈ Φ.polar.perp Z, g v - (v - (Φ.polar.β v a / Φ.Q a) • a) ∈ Z) :
    dicksonInvariant (LinearMap.range (LinearMap.id.prod LinearMap.id : V →ₗ[K] V × V))
      (g.prodMap LinearMap.id) = 1 := by
  refine dicksonInvariant_eq_one_of_reflection Φ.isLagrangian_prodNeg_diagonal
    (prodNeg_Q_prodMap hg) (Z := Z.prod ⊥) (a := (a, 0)) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Submodule.mem_prod, Submodule.mem_bot] at hp
    simp [hZ _ hp.1, hp.2, Φ.Q_zero]
  · intro p hp
    rw [Submodule.mem_prod, Submodule.mem_bot] at hp
    simp [ha _ hp.1, Φ.polar.β_zero_right]
  · simpa [Φ.Q_zero] using hQa
  · intro p hp
    have hp1 : p.1 ∈ Φ.polar.perp Z := fun z hz => by
      simpa [Φ.polar.β_zero_left] using
        hp (z, 0) (Submodule.mem_prod.mpr ⟨hz, Submodule.zero_mem _⟩)
    have e : Φ.prodNeg.polar.β p (a, 0) / Φ.prodNeg.Q (a, 0) = Φ.polar.β p.1 a / Φ.Q a := by
      simp [Φ.polar.β_zero_right, Φ.Q_zero]
    rw [e, Submodule.mem_prod, Submodule.mem_bot]
    exact ⟨by simpa using hrefl p.1 hp1, by simp⟩

end QuadForm

@[expose] def prodIdRep {H : Type w} [Group H] (ρ : H →* Module.End K V) :
    H →* Module.End K (V × V) where
  toFun h := (ρ h).prodMap LinearMap.id
  map_one' := LinearMap.ext fun p => by simp
  map_mul' g h := LinearMap.ext fun p => by simp

@[simp] theorem prodIdRep_apply {H : Type w} [Group H] (ρ : H →* Module.End K V) (h : H) :
    prodIdRep ρ h = (ρ h).prodMap LinearMap.id :=
  rfl

end General

section Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem QuadForm.Q_natRep_orthGroup (Φ : QuadForm K (ι → K)) (h : orthGroup Φ.Q)
    (v : ι → K) : Φ.Q (natRep (orthGroup Φ.Q) h v) = Φ.Q v := by
  rw [natRep_apply]
  exact orthGroup_preserves Φ.Q h.2 v

theorem map_eq_one_of_mem_statedOmega {A : Type*} [CommGroup A] {Q : (ι → K) → K}
    (f : orthGroup Q →* A) {g : GL ι K} (hg : g ∈ StatedOmega Q) :
    f ⟨g, statedOmega_le_orthGroup Q hg⟩ = 1 := by
  have hg' : g ∈ (commutator (orthGroup Q)).map (orthGroup Q).subtype := by
    rw [Subgroup.map_subtype_commutator]
    exact hg
  obtain ⟨x, hx, rfl⟩ := hg'
  exact Abelianization.commutator_subset_ker f hx

namespace QuadForm

@[expose] noncomputable def orthDicksonHom (Φ : QuadForm K (ι → K)) {X₀ : Submodule K (ι → K)}
    (hX₀ : Φ.IsLagrangian X₀) : orthGroup Φ.Q →* Multiplicative (ZMod 2) :=
  dicksonHom (natRep (orthGroup Φ.Q)) Φ.Q_natRep_orthGroup hX₀

@[expose] noncomputable def prodNegDicksonHom (Φ : QuadForm K (ι → K)) :
    orthGroup Φ.Q →* Multiplicative (ZMod 2) :=
  dicksonHom (prodIdRep (natRep (orthGroup Φ.Q)))
    (fun h p => by rw [prodIdRep_apply]; exact prodNeg_Q_prodMap (Φ.Q_natRep_orthGroup h) p)
    Φ.isLagrangian_prodNeg_diagonal

end QuadForm

theorem not_reflection_on_quotient_of_mem_statedOmega (Φ : QuadForm K (ι → K)) {g : GL ι K}
    (hg : g ∈ StatedOmega Φ.Q) {Z : Submodule K (ι → K)} (hZ : Φ.IsTotallySingular Z)
    {a : ι → K} (ha : a ∈ Φ.polar.perp Z) (hQa : Φ.Q a ≠ 0) :
    ¬∀ v ∈ Φ.polar.perp Z, (g : Matrix ι ι K) *ᵥ v - (v - (Φ.polar.β v a / Φ.Q a) • a) ∈ Z := by
  intro hrefl
  have h1 : Multiplicative.ofAdd (dicksonInvariant
      (LinearMap.range (LinearMap.id.prod LinearMap.id : (ι → K) →ₗ[K] (ι → K) × (ι → K)))
      ((natRep (orthGroup Φ.Q) ⟨g, statedOmega_le_orthGroup Φ.Q hg⟩).prodMap LinearMap.id)) = 1 :=
    map_eq_one_of_mem_statedOmega Φ.prodNegDicksonHom hg
  have h2 := QuadForm.dicksonInvariant_prodMap_eq_one
    (Φ.Q_natRep_orthGroup ⟨g, statedOmega_le_orthGroup Φ.Q hg⟩) hZ ha hQa fun v hv => by
      rw [natRep_apply]
      exact hrefl v hv
  rw [ofAdd_eq_one, h2] at h1
  exact one_ne_zero h1

theorem even_finrank_sub_finrank_inf_of_mem_statedOmega (Φ : QuadForm K (ι → K))
    {X : Submodule K (ι → K)} (hX : Φ.IsLagrangian X) {g : GL ι K} (hg : g ∈ StatedOmega Φ.Q) :
    Even (finrank K X - finrank K ↥(X ⊓ X.map (Matrix.toLin' (g : Matrix ι ι K)))) := by
  have h : Multiplicative.ofAdd
      (dicksonInvariant X (natRep (orthGroup Φ.Q) ⟨g, statedOmega_le_orthGroup Φ.Q hg⟩)) = 1 :=
    map_eq_one_of_mem_statedOmega (Φ.orthDicksonHom hX) hg
  have he : natRep (orthGroup Φ.Q) ⟨g, statedOmega_le_orthGroup Φ.Q hg⟩ =
      Matrix.toLin' (g : Matrix ι ι K) :=
    LinearMap.ext fun v => by rw [natRep_apply, Matrix.toLin'_apply]
  rw [ofAdd_eq_one, he, dicksonInvariant, ZMod.natCast_eq_zero_iff_even] at h
  exact h

theorem mulVec_mem_of_mem_statedOmega (Φ : QuadForm K (ι → K)) {X A : Submodule K (ι → K)}
    (hX : Φ.IsLagrangian X) (hAX : A ≤ X) (hrank : finrank K X = finrank K A + 1) {g : GL ι K}
    (hg : g ∈ StatedOmega Φ.Q) (hgA : ∀ v ∈ A, (g : Matrix ι ι K) *ᵥ v ∈ A) :
    ∀ v ∈ X, (g : Matrix ι ι K) *ᵥ v ∈ X := by
  have h : Multiplicative.ofAdd
      (dicksonInvariant X (natRep (orthGroup Φ.Q) ⟨g, statedOmega_le_orthGroup Φ.Q hg⟩)) = 1 :=
    map_eq_one_of_mem_statedOmega (Φ.orthDicksonHom hX) hg
  rw [ofAdd_eq_one] at h
  intro v hv
  have := QuadForm.apply_mem_of_dicksonInvariant_eq_zero hAX hrank
    (Φ.Q_natRep_orthGroup ⟨g, statedOmega_le_orthGroup Φ.Q hg⟩)
    (fun v hv => by rw [natRep_apply]; exact hgA v hv) h v hv
  rwa [natRep_apply] at this

theorem reflection_notMem_statedOmega (Φ : QuadForm K (ι → K)) {g : GL ι K} {a : ι → K}
    (hQa : Φ.Q a ≠ 0) (hga : ∀ v, (g : Matrix ι ι K) *ᵥ v = v - (Φ.polar.β v a / Φ.Q a) • a) :
    g ∉ StatedOmega Φ.Q := fun hg =>
  not_reflection_on_quotient_of_mem_statedOmega Φ hg QuadForm.isTotallySingular_bot
    (by rw [Φ.polar.perp_bot]; exact Submodule.mem_top) hQa fun v _ => by
      rw [hga, sub_self]
      exact Submodule.zero_mem _

theorem isLagrangian_quadPlusForm (n : ℕ) (K : Type) [Field K] :
    (quadPlusForm n K).IsLagrangian
      (LinearMap.ker (LinearMap.funLeft K K (Sum.inr : Fin n → Fin n ⊕ Fin n))) := by
  refine ⟨fun v hv => ?_, ?_⟩
  · have h : ∀ i, v (Sum.inr i) = 0 := fun i => congrFun (LinearMap.mem_ker.mp hv) i
    show ∑ i, v (Sum.inl i) * v (Sum.inr i) = 0
    simp [h]
  · have h1 := LinearMap.finrank_range_add_finrank_ker
      (LinearMap.funLeft K K (Sum.inr : Fin n → Fin n ⊕ Fin n))
    rw [LinearMap.range_eq_top.mpr
        (LinearMap.funLeft_surjective_of_injective _ _ _ Sum.inr_injective), finrank_top,
      Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
      Fintype.card_fin] at h1
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega

@[expose] noncomputable def quadPlusDicksonHom (n : ℕ) (K : Type) [Field K] :
    orthGroup (StatedQuadPlus n K) →* Multiplicative (ZMod 2) :=
  (quadPlusForm n K).orthDicksonHom (isLagrangian_quadPlusForm n K)

theorem not_reflection_on_quotient_of_mem_statedOmega_quadPlus (n : ℕ) {K : Type} [Field K]
    {g : GL (Fin n ⊕ Fin n) K} (hg : g ∈ StatedOmega (StatedQuadPlus n K))
    {Z : Submodule K (Fin n ⊕ Fin n → K)} (hZ : ∀ z ∈ Z, StatedQuadPlus n K z = 0)
    {a : Fin n ⊕ Fin n → K} (ha : ∀ z ∈ Z, quadPlusPolar n K z a = 0)
    (hQa : StatedQuadPlus n K a ≠ 0) :
    ¬∀ v, (∀ z ∈ Z, quadPlusPolar n K z v = 0) →
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v -
        (v - (quadPlusPolar n K v a / StatedQuadPlus n K a) • a) ∈ Z :=
  not_reflection_on_quotient_of_mem_statedOmega (quadPlusForm n K) hg hZ ha hQa

theorem not_reflection_on_quotient_of_mem_statedOmega_quadMinus (n : ℕ) {K : Type} [Field K]
    [Finite K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {g : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K} (hg : g ∈ StatedOmega (StatedQuadMinus n K b c))
    {Z : Submodule K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)}
    (hZ : ∀ z ∈ Z, StatedQuadMinus n K b c z = 0) {a : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K}
    (ha : ∀ z ∈ Z, quadMinusPolar n K b c z a = 0) (hQa : StatedQuadMinus n K b c a ≠ 0) :
    ¬∀ v, (∀ z ∈ Z, quadMinusPolar n K b c z v = 0) →
      (g : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) *ᵥ
          v - (v - (quadMinusPolar n K b c v a / StatedQuadMinus n K b c a) • a) ∈ Z :=
  not_reflection_on_quotient_of_mem_statedOmega (quadMinusForm n K b c hirr) hg hZ ha hQa

end Matrix

end CFSG.LieType.BorelTits
