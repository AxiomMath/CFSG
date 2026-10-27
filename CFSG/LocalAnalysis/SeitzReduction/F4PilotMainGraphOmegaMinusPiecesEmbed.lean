module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactMatrix

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega)
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono le_perfectCore_of_perfect
  perfectCore_perfect)
open CFSG.SeitzReduction.SymplecticPilot (suppGL mem_suppGL IsSuppMat)

section Embed

variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] {F : Type}
  [Field F] {e : ι' → ι}

open Classical in
variable (e) in
@[expose] noncomputable def coordEmbedMat (g : Matrix ι' ι' F) : Matrix ι ι F :=
  Matrix.of fun a b => if h : a ∈ Set.range e ∧ b ∈ Set.range e then g h.1.choose h.2.choose
    else (1 : Matrix ι ι F) a b

omit [Fintype ι] [DecidableEq ι'] in
theorem coordEmbedMat_apply_image (he : Function.Injective e) (g : Matrix ι' ι' F) (x y : ι') :
    coordEmbedMat e g (e x) (e y) = g x y := by
  have h : e x ∈ Set.range e ∧ e y ∈ Set.range e := ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  rw [coordEmbedMat, Matrix.of_apply, dite_eq_left h, he h.1.choose_spec, he h.2.choose_spec]

omit [Fintype ι] [DecidableEq ι'] in
theorem coordEmbedMat_apply_of_not_mem (g : Matrix ι' ι' F) {a b : ι}
    (h : ¬(a ∈ Set.range e ∧ b ∈ Set.range e)) :
    coordEmbedMat e g a b = (1 : Matrix ι ι F) a b := by
  rw [coordEmbedMat, Matrix.of_apply, dite_eq_right h]

omit [DecidableEq ι] [DecidableEq ι'] in
theorem sum_eq_sum_comp_of_vanish (he : Function.Injective e) (f : ι → F)
    (hf : ∀ c, c ∉ Set.range e → f c = 0) : ∑ c, f c = ∑ z, f (e z) :=
  (Fintype.sum_of_injective e he (f ∘ e) f hf (fun _ => rfl)).symm

omit [Fintype ι] in
theorem coordEmbedMat_one (he : Function.Injective e) :
    coordEmbedMat e (1 : Matrix ι' ι' F) = 1 := by
  ext a b
  by_cases h : a ∈ Set.range e ∧ b ∈ Set.range e
  · obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := h
    rw [coordEmbedMat_apply_image he, Matrix.one_apply, Matrix.one_apply]
    exact if_congr he.eq_iff.symm rfl rfl
  · exact coordEmbedMat_apply_of_not_mem _ h

omit [DecidableEq ι'] in
theorem coordEmbedMat_mul (he : Function.Injective e) (g h : Matrix ι' ι' F) :
    coordEmbedMat e (g * h) = coordEmbedMat e g * coordEmbedMat e h := by
  ext a b
  rw [Matrix.mul_apply]
  by_cases hab : a ∈ Set.range e ∧ b ∈ Set.range e
  · obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := hab
    rw [coordEmbedMat_apply_image he, Matrix.mul_apply,
      sum_eq_sum_comp_of_vanish he _ (fun c hc => by
        rw [coordEmbedMat_apply_of_not_mem g (fun h' => hc h'.2),
          Matrix.one_apply_ne (fun h' => hc ⟨x, h'⟩), zero_mul])]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [coordEmbedMat_apply_image he, coordEmbedMat_apply_image he]
  · rcases not_and_or.1 hab with ha | hb
    · have hr : ∀ c, coordEmbedMat e g a c = (1 : Matrix ι ι F) a c :=
        fun c => coordEmbedMat_apply_of_not_mem g (fun h' => ha h'.1)
      rw [Finset.sum_congr rfl (fun c _ => by rw [hr c]), ← Matrix.mul_apply, Matrix.one_mul,
        coordEmbedMat_apply_of_not_mem _ (fun h' => ha h'.1),
        coordEmbedMat_apply_of_not_mem _ (fun h' => ha h'.1)]
    · have hc : ∀ c, coordEmbedMat e h c b = (1 : Matrix ι ι F) c b :=
        fun c => coordEmbedMat_apply_of_not_mem h (fun h' => hb h'.2)
      rw [Finset.sum_congr rfl (fun c _ => by rw [hc c]), ← Matrix.mul_apply, Matrix.mul_one,
        coordEmbedMat_apply_of_not_mem _ (fun h' => hb h'.2),
        coordEmbedMat_apply_of_not_mem _ (fun h' => hb h'.2)]

omit [Fintype ι] [DecidableEq ι'] in
theorem coordEmbedMat_injective (he : Function.Injective e) :
    Function.Injective (coordEmbedMat (F := F) e) := by
  intro g h hgh
  ext x y
  have := congrFun (congrFun hgh (e x)) (e y)
  rwa [coordEmbedMat_apply_image he, coordEmbedMat_apply_image he] at this

omit [DecidableEq ι'] in
theorem coordEmbedMat_mulVec_comp (he : Function.Injective e) (g : Matrix ι' ι' F)
    (v : ι → F) : (coordEmbedMat e g *ᵥ v) ∘ e = g *ᵥ (v ∘ e) := by
  funext x
  simp only [Function.comp_apply, mulVec, dotProduct]
  rw [sum_eq_sum_comp_of_vanish he _ (fun c hc => by
    rw [coordEmbedMat_apply_of_not_mem g (fun h' => hc h'.2),
      Matrix.one_apply_ne (fun h' => hc ⟨x, h'⟩), zero_mul])]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [coordEmbedMat_apply_image he]

omit [DecidableEq ι'] in
theorem coordEmbedMat_mulVec_of_not_mem (g : Matrix ι' ι' F) (v : ι → F) {a : ι}
    (ha : a ∉ Set.range e) : (coordEmbedMat e g *ᵥ v) a = v a := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single a (fun c _ hca => by
      rw [coordEmbedMat_apply_of_not_mem g (fun h => ha h.1), Matrix.one_apply_ne (Ne.symm hca),
        zero_mul])
    (fun h => absurd (Finset.mem_univ a) h),
    coordEmbedMat_apply_of_not_mem g (fun h => ha h.1), Matrix.one_apply_eq, one_mul]

variable (e) in
@[expose] noncomputable def coordEmbedGL (he : Function.Injective e) : GL ι' F →* GL ι F where
  toFun g :=
    { val := coordEmbedMat e (g : Matrix ι' ι' F)
      inv := coordEmbedMat e ((g⁻¹ : GL ι' F) : Matrix ι' ι' F)
      val_inv := by rw [← coordEmbedMat_mul he, Units.mul_inv, coordEmbedMat_one he]
      inv_val := by rw [← coordEmbedMat_mul he, Units.inv_mul, coordEmbedMat_one he] }
  map_one' := Units.ext (coordEmbedMat_one he)
  map_mul' g h := Units.ext (coordEmbedMat_mul he (g : Matrix ι' ι' F) h)

theorem coe_coordEmbedGL (he : Function.Injective e) (g : GL ι' F) :
    (coordEmbedGL e he g : Matrix ι ι F) = coordEmbedMat e (g : Matrix ι' ι' F) :=
  rfl

theorem coordEmbedGL_injective (he : Function.Injective e) :
    Function.Injective (coordEmbedGL (F := F) e he) := fun _ _ hgh =>
  Units.ext (coordEmbedMat_injective he (congrArg Units.val hgh))

theorem coordEmbedGL_mem_suppGL (he : Function.Injective e) (g : GL ι' F) :
    coordEmbedGL e he g ∈ suppGL F (Set.range e) :=
  fun _ _ h => coordEmbedMat_apply_of_not_mem _ h

theorem exists_coordEmbedGL_eq_of_mem_suppGL (he : Function.Injective e) {x : GL ι F}
    (hx : x ∈ suppGL F (Set.range e)) : ∃ y : GL ι' F, coordEmbedGL e he y = x := by
  set X : Matrix ι ι F := (x : Matrix ι ι F)
  set X' : Matrix ι ι F := ((x⁻¹ : GL ι F) : Matrix ι ι F)
  have hX : IsSuppMat (Set.range e) X := hx
  have hX' : IsSuppMat (Set.range e) X' :=
    SymplecticPilot.IsSuppMat.of_mul_eq_one hX (by rw [← Units.val_mul, inv_mul_cancel,
      Units.val_one]) (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
  have hemb : ∀ M : Matrix ι ι F, IsSuppMat (Set.range e) M →
      coordEmbedMat e (M.submatrix e e) = M := by
    intro M hM
    ext a b
    by_cases h : a ∈ Set.range e ∧ b ∈ Set.range e
    · obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := h
      rw [coordEmbedMat_apply_image he, submatrix_apply]
    · rw [coordEmbedMat_apply_of_not_mem _ h, hM a b h]
  have h1 : X.submatrix e e * X'.submatrix e e = 1 := coordEmbedMat_injective he (by
    rw [coordEmbedMat_mul he, hemb X hX, hemb X' hX', coordEmbedMat_one he, ← Units.val_mul,
      mul_inv_cancel, Units.val_one])
  have h2 : X'.submatrix e e * X.submatrix e e = 1 := coordEmbedMat_injective he (by
    rw [coordEmbedMat_mul he, hemb X hX, hemb X' hX', coordEmbedMat_one he, ← Units.val_mul,
      inv_mul_cancel, Units.val_one])
  exact ⟨⟨X.submatrix e e, X'.submatrix e e, h1, h2⟩, Units.ext (hemb X hX)⟩

end Embed

section Split

variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] {F : Type}
  [Field F] {e : ι' → ι}

@[expose] def IsCoordSplit (Q : (ι → F) → F) (Q' : (ι' → F) → F) (e : ι' → ι) : Prop :=
  ∃ R : (ι → F) → F, (∀ v, Q v = Q' (v ∘ e) + R v) ∧
    ∀ v w : ι → F, (∀ a, a ∉ Set.range e → v a = w a) → R v = R w

abbrev isoClosure (Q : (ι → F) → F) : Subgroup (GL ι F) :=
  Subgroup.closure {A : GL ι F | ∀ v, Q ((A : Matrix ι ι F) *ᵥ v) = Q v}

theorem statedOmega_eq_commutator_isoClosure (Q : (ι → F) → F) :
    StatedOmega Q = ⁅isoClosure Q, isoClosure Q⁆ :=
  rfl

theorem isometry_of_mem_isoClosure {Q : (ι → F) → F} {A : GL ι F} (hA : A ∈ isoClosure Q)
    (v : ι → F) : Q ((A : Matrix ι ι F) *ᵥ v) = Q v := by
  induction hA using Subgroup.closure_induction generalizing v with
  | mem x hx => exact hx v
  | one => rw [Units.val_one, one_mulVec]
  | mul x y _ _ hx hy => rw [Units.val_mul, ← mulVec_mulVec, hx, hy]
  | inv x _ hx =>
    calc Q (((x⁻¹ : GL ι F) : Matrix ι ι F) *ᵥ v) =
        Q ((x : Matrix ι ι F) *ᵥ (((x⁻¹ : GL ι F) : Matrix ι ι F) *ᵥ v)) := (hx _).symm
      _ = Q v := by rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem isometry_of_mem_statedOmega {Q : (ι → F) → F} {A : GL ι F} (hA : A ∈ StatedOmega Q)
    (v : ι → F) : Q ((A : Matrix ι ι F) *ᵥ v) = Q v :=
  isometry_of_mem_isoClosure (Subgroup.commutator_le_self (isoClosure Q) hA) v

omit [DecidableEq ι'] in
theorem IsCoordSplit.isometry_iff {Q : (ι → F) → F} {Q' : (ι' → F) → F}
    (hs : IsCoordSplit Q Q' e) (he : Function.Injective e) (g : Matrix ι' ι' F) :
    (∀ v, Q (coordEmbedMat e g *ᵥ v) = Q v) ↔ ∀ w, Q' (g *ᵥ w) = Q' w := by
  obtain ⟨R, hQ, hR⟩ := hs
  have hrest : ∀ v, R (coordEmbedMat e g *ᵥ v) = R v :=
    fun v => hR _ _ (fun a ha => coordEmbedMat_mulVec_of_not_mem g v ha)
  constructor
  · intro h w
    have hvw : (Function.extend e w 0) ∘ e = w := funext fun y => he.extend_apply w 0 y
    have h1 := h (Function.extend e w 0)
    rw [hQ, hQ (Function.extend e w 0), coordEmbedMat_mulVec_comp he, hvw, hrest] at h1
    exact add_right_cancel h1
  · intro h v
    rw [hQ, hQ v, coordEmbedMat_mulVec_comp he, h, hrest]

theorem IsCoordSplit.map_isoClosure_le {Q : (ι → F) → F} {Q' : (ι' → F) → F}
    (hs : IsCoordSplit Q Q' e) (he : Function.Injective e) :
    (isoClosure Q').map (coordEmbedGL e he) ≤ isoClosure Q := by
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_le _ |>.2 ?_
  rintro _ ⟨g, hg, rfl⟩
  exact Subgroup.subset_closure ((hs.isometry_iff he _).2 hg)

theorem IsCoordSplit.map_statedOmega_le {Q : (ι → F) → F} {Q' : (ι' → F) → F}
    (hs : IsCoordSplit Q Q' e) (he : Function.Injective e) :
    (StatedOmega Q').map (coordEmbedGL e he) ≤ StatedOmega Q := by
  rw [statedOmega_eq_commutator_isoClosure, statedOmega_eq_commutator_isoClosure,
    Subgroup.map_commutator]
  exact Subgroup.commutator_mono (hs.map_isoClosure_le he) (hs.map_isoClosure_le he)

theorem IsCoordSplit.map_statedOmega_le_inf_suppGL {Q : (ι → F) → F} {Q' : (ι' → F) → F}
    (hs : IsCoordSplit Q Q' e) (he : Function.Injective e) :
    (StatedOmega Q').map (coordEmbedGL e he) ≤ StatedOmega Q ⊓ suppGL F (Set.range e) := by
  refine le_inf (hs.map_statedOmega_le he) ?_
  rintro _ ⟨g, -, rfl⟩
  exact coordEmbedGL_mem_suppGL he g

theorem IsCoordSplit.statedOmega_inf_suppGL_le_map {Q : (ι → F) → F} {Q' : (ι' → F) → F}
    (hs : IsCoordSplit Q Q' e) (he : Function.Injective e) :
    StatedOmega Q ⊓ suppGL F (Set.range e) ≤ (isoClosure Q').map (coordEmbedGL e he) := by
  intro x hx
  obtain ⟨hxO, hxS⟩ := mem_inf.1 hx
  obtain ⟨y, rfl⟩ := exists_coordEmbedGL_eq_of_mem_suppGL he hxS
  exact ⟨y, Subgroup.subset_closure ((hs.isometry_iff he _).1
    (isometry_of_mem_statedOmega hxO)), rfl⟩

theorem IsCoordSplit.perfectCore_statedOmega_inf_suppGL [Finite F] {Q : (ι → F) → F}
    {Q' : (ι' → F) → F} (hs : IsCoordSplit Q Q' e) (he : Function.Injective e)
    (hperf : ⁅StatedOmega Q', StatedOmega Q'⁆ = StatedOmega Q') :
    perfectCore (StatedOmega Q ⊓ suppGL F (Set.range e)) =
      (StatedOmega Q').map (coordEmbedGL e he) := by
  refine le_antisymm ?_ (le_perfectCore_of_perfect (hs.map_statedOmega_le_inf_suppGL he)
    (by rw [← Subgroup.map_commutator, hperf]))
  calc perfectCore (StatedOmega Q ⊓ suppGL F (Set.range e)) ≤
        perfectCore ((isoClosure Q').map (coordEmbedGL e he)) :=
        perfectCore_mono (hs.statedOmega_inf_suppGL_le_map he)
    _ = (perfectCore (isoClosure Q')).map (coordEmbedGL e he) :=
        (CFSG.Quasithin.map_perfectCore _ _).symm
    _ ≤ (StatedOmega Q').map (coordEmbedGL e he) := by
        refine map_mono ?_
        rw [statedOmega_eq_commutator_isoClosure]
        calc perfectCore (isoClosure Q') =
              ⁅perfectCore (isoClosure Q'), perfectCore (isoClosure Q')⁆ :=
              (perfectCore_perfect _).symm
          _ ≤ ⁅isoClosure Q', isoClosure Q'⁆ :=
              Subgroup.commutator_mono (perfectCore_le _) (perfectCore_le _)

end Split

end CFSG.SeitzReduction.F4Pilot
