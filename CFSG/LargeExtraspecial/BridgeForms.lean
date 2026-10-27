module

public import CFSG.LargeExtraspecial.BridgeConclusion

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.Bridge

open Module CFSG.Open

variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def conjLinearEquiv (f : V ≃ₗ[ZMod 2] W) :
    (V ≃ₗ[ZMod 2] V) ≃* (W ≃ₗ[ZMod 2] W) where
  toFun g := f.symm.trans (g.trans f)
  invFun g := f.trans (g.trans f.symm)
  left_inv g := by ext v; simp
  right_inv g := by ext w; simp
  map_mul' g h := by ext w; simp

@[simp] theorem conjLinearEquiv_apply (f : V ≃ₗ[ZMod 2] W) (g : V ≃ₗ[ZMod 2] V) (w : W) :
    conjLinearEquiv f g w = f (g (f.symm w)) := rfl

theorem map_closure_of_iff {A B : Type*} [Group A] [Group B] (e : A ≃* B) {s : Set A}
    {t : Set B} (h : ∀ g, e g ∈ t ↔ g ∈ s) :
    (Subgroup.closure s).map e.toMonoidHom = Subgroup.closure t := by
  rw [MonoidHom.map_closure]
  congr 1
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (h a).mpr ha
  · intro hb
    exact ⟨e.symm b, (h _).mp (by simpa using hb), by simp⟩

variable (f : V ≃ₗ[ZMod 2] W) {q : V → ZMod 2} {q' : W → ZMod 2}

theorem conj_mem_isometries_iff (hq : ∀ v, q' (f v) = q v) (g : V ≃ₗ[ZMod 2] V) :
    conjLinearEquiv f g ∈ timmesfeldIsometries q' ↔ g ∈ timmesfeldIsometries q := by
  change (∀ w, q' (conjLinearEquiv f g w) = q' w) ↔ ∀ v, q (g v) = q v
  constructor
  · intro h v
    simpa [hq] using h (f v)
  · intro h w
    obtain ⟨v, rfl⟩ := f.surjective w
    simp [hq, h]

theorem isometries_map (hq : ∀ v, q' (f v) = q v) :
    (timmesfeldIsometries q).map (conjLinearEquiv f).toMonoidHom = timmesfeldIsometries q' := by
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (conj_mem_isometries_iff f hq g).mpr hg
  · intro hh
    refine ⟨(conjLinearEquiv f).symm h, ?_, by simp⟩
    rw [SetLike.mem_coe, ← conj_mem_isometries_iff f hq]
    simpa using hh

theorem finrank_range_conj_sub (g : V ≃ₗ[ZMod 2] V) :
    finrank (ZMod 2) (LinearMap.range
        (((conjLinearEquiv f g : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) - LinearMap.id)) =
      finrank (ZMod 2) (LinearMap.range ((g : V →ₗ[ZMod 2] V) - LinearMap.id)) := by
  have h : ((conjLinearEquiv f g : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) - LinearMap.id =
      (f : V →ₗ[ZMod 2] W) ∘ₗ ((g : V →ₗ[ZMod 2] V) - LinearMap.id) ∘ₗ
        (f.symm : W →ₗ[ZMod 2] V) := by
    ext w
    simp
  rw [h, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    LinearEquiv.finrank_map_eq]

theorem omega_map (hq : ∀ v, q' (f v) = q v) :
    (timmesfeldOmega q).map (conjLinearEquiv f).toMonoidHom = timmesfeldOmega q' := by
  unfold timmesfeldOmega
  refine map_closure_of_iff _ fun g => ?_
  simp only [Set.mem_ofPred_eq]
  rw [conj_mem_isometries_iff f hq, finrank_range_conj_sub]

@[expose] noncomputable def isometriesEquiv (hq : ∀ v, q' (f v) = q v) :
    timmesfeldIsometries q ≃* timmesfeldIsometries q' :=
  equivOfMapEq (conjLinearEquiv f) (isometries_map f hq)

@[expose] noncomputable def omegaEquiv (hq : ∀ v, q' (f v) = q v) :
    timmesfeldOmega q ≃* timmesfeldOmega q' :=
  equivOfMapEq (conjLinearEquiv f) (omega_map f hq)

theorem polar_map (hq : ∀ v, q' (f v) = q v) (u v : V) :
    QuadraticMap.polar q' (f u) (f v) = QuadraticMap.polar q u v := by
  simp only [QuadraticMap.polar]
  rw [← map_add, hq, hq, hq]

theorem nondegenerate_of_map (hq : ∀ v, q' (f v) = q v)
    (hnd : ∀ u, (∀ v, QuadraticMap.polar q u v = 0) → u = 0) :
    ∀ u, (∀ v, QuadraticMap.polar q' u v = 0) → u = 0 := by
  intro u hu
  obtain ⟨u, rfl⟩ := f.surjective u
  rw [hnd u fun v => by rw [← polar_map f hq]; exact hu _, map_zero]

theorem totallySingular_map (hq : ∀ v, q' (f v) = q v) {U : Submodule (ZMod 2) V}
    (hU : ∀ v ∈ U, q v = 0) : ∀ w ∈ U.map (f : V →ₗ[ZMod 2] W), q' w = 0 := by
  rintro _ ⟨v, hv, rfl⟩
  rw [LinearEquiv.coe_coe, hq]
  exact hU v hv

theorem polarBilin_nondegenerate_iff (q : QuadraticForm (ZMod 2) V) :
    q.polarBilin.Nondegenerate ↔ ∀ u, (∀ v, QuadraticMap.polar q u v = 0) → u = 0 := by
  have hrefl : q.polarBilin.IsRefl := fun x y h => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] at h
    rwa [QuadraticMap.polarBilin_apply_apply]
  rw [hrefl.nondegenerate_iff_separatingLeft]
  exact Iff.rfl

theorem exists_fin_form [Module.Finite (ZMod 2) V] (q : QuadraticForm (ZMod 2) V) {d : ℕ}
    (hV : finrank (ZMod 2) V = d) :
    ∃ q' : QuadraticForm (ZMod 2) (Fin d → ZMod 2),
      ((∀ u, (∀ v, QuadraticMap.polar q u v = 0) → u = 0) → timmesfeldNondegenerate q') ∧
      ((∃ U : Submodule (ZMod 2) V, 2 * finrank (ZMod 2) U = d ∧ ∀ v ∈ U, q v = 0) →
        timmesfeldPlusType q') ∧
      Nonempty (timmesfeldOmega q ≃* timmesfeldOmega q') ∧
      Nonempty (timmesfeldIsometries q ≃* timmesfeldIsometries q') := by
  let f : V ≃ₗ[ZMod 2] (Fin d → ZMod 2) := (Module.finBasisOfFinrankEq (ZMod 2) V hV).equivFun
  let q' : QuadraticForm (ZMod 2) (Fin d → ZMod 2) :=
    q.comp (f.symm : (Fin d → ZMod 2) →ₗ[ZMod 2] V)
  have hq : ∀ v, q' (f v) = q v := fun v => by simp [q']
  refine ⟨q', fun hnd => nondegenerate_of_map f hq hnd, ?_, ⟨omegaEquiv f hq⟩,
    ⟨isometriesEquiv f hq⟩⟩
  rintro ⟨U, hU, hq0⟩
  refine ⟨U.map (f : V →ₗ[ZMod 2] (Fin d → ZMod 2)), ?_, totallySingular_map f hq hq0⟩
  rw [LinearEquiv.finrank_map_eq, hU]

theorem exists_fin_quotientIso_omega [Module.Finite (ZMod 2) V] {A : Type*} [Group A]
    {N : Subgroup A} (q : QuadraticForm (ZMod 2) V) {d : ℕ} (hV : finrank (ZMod 2) V = d)
    (hnd : ∀ u, (∀ v, QuadraticMap.polar q u v = 0) → u = 0)
    (h : timmesfeldQuotientIso N (timmesfeldOmega q)) :
    ∃ q' : QuadraticForm (ZMod 2) (Fin d → ZMod 2), timmesfeldNondegenerate q' ∧
      ((∃ U : Submodule (ZMod 2) V, 2 * finrank (ZMod 2) U = d ∧ ∀ v ∈ U, q v = 0) →
        timmesfeldPlusType q') ∧
      timmesfeldQuotientIso N (timmesfeldOmega q') := by
  obtain ⟨q', hnd', hplus, ⟨eΩ⟩, -⟩ := exists_fin_form q hV
  exact ⟨q', hnd' hnd, hplus, quotientIso_congr_right h eΩ⟩

theorem TimmesfeldAlt3.of_space [Module.Finite (ZMod 2) V] {Mbar : Type*} [Group Mbar] {w : ℕ}
    (h6 : 6 ≤ w) (he : Even w) (q : QuadraticForm (ZMod 2) V) (hV : finrank (ZMod 2) V = w)
    (hnd : ∀ u, (∀ v, QuadraticMap.polar q u v = 0) → u = 0)
    (h : Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldOmega q) ∨
      Nonempty (Mbar ≃* Equiv.Perm (Fin 3) × timmesfeldIsometries q)) :
    TimmesfeldAlt3 w Mbar := by
  obtain ⟨q', hnd', -, ⟨eΩ⟩, ⟨eO⟩⟩ := exists_fin_form q hV
  exact ⟨h6, he, q', hnd' hnd,
    h.imp (fun ⟨g⟩ => ⟨g.trans (MulEquiv.prodCongr (MulEquiv.refl _) eΩ)⟩)
      (fun ⟨g⟩ => ⟨g.trans (MulEquiv.prodCongr (MulEquiv.refl _) eO)⟩)⟩

end CFSG.LargeExtraspecial.Bridge
