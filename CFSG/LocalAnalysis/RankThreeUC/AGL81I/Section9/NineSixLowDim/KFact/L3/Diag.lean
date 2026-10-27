module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Matrix Module

variable {F : Type} [Field F]

private def IsInv (A : Subgroup (GL (Fin 3) F)) (W : Submodule F (Fin 3 → F)) : Prop :=
  ∀ g ∈ A, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W

private lemma not_isCyclic_quot {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {p : ℕ}
    (hp : p.Prime) (hpow : ∀ g : G, g ^ p ∈ N) (hcard : Nat.card (G ⧸ N) = p ^ 2) :
    ¬ IsCyclic (G ⧸ N) := by
  intro hcyc
  have hexp : Monoid.exponent (G ⧸ N) ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
    induction x using QuotientGroup.induction_on with
    | H g => rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hpow g
  rw [IsCyclic.exponent_eq_card, hcard] at hexp
  have := Nat.le_of_dvd hp.pos hexp
  nlinarith [hp.two_le]

private lemma isCyclic_quot_of_hom {G D : Type*} [Group G] [Finite G] [CommRing D] [IsDomain D]
    (φ : G →* D) {N : Subgroup G} [N.Normal] (hN : ∀ g, φ g = 1 → g ∈ N) :
    IsCyclic (G ⧸ N) := by
  set φ' := φ.toHomUnits
  have hinj : Function.Injective ((Units.coeHom D).comp (QuotientGroup.kerLift φ')) :=
    Units.val_injective.comp (QuotientGroup.kerLift_injective φ')
  have := isCyclic_of_injective_ringHom _ hinj
  refine isCyclic_of_surjective (QuotientGroup.map φ'.ker N (MonoidHom.id G) fun g hg => hN g ?_) ?_
  · simpa [φ'] using congrArg Units.val (φ'.mem_ker.mp hg)
  · intro y
    induction y using QuotientGroup.induction_on with
    | H g => exact ⟨QuotientGroup.mk g, rfl⟩

private lemma mem_center_of_smul {g : GL (Fin 3) F} {c : F}
    (h : ∀ v, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = c • v) :
    g ∈ Subgroup.center (GL (Fin 3) F) := by
  have hg : (g : Matrix (Fin 3) (Fin 3) F) = c • 1 := by
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this
  refine Subgroup.mem_center_iff.mpr fun x => Units.ext ?_
  simp [hg]

private lemma eq_diagonal_of_mem_center {g : GL (Fin 3) F}
    (hg : g ∈ Subgroup.center (GL (Fin 3) F)) :
    ∃ c : Fˣ, (g : Matrix (Fin 3) (Fin 3) F) = diagonal fun _ => (c : F) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
  obtain ⟨c, rfl⟩ := hg
  exact ⟨c, by simp [Matrix.scalar_apply]⟩

section Irred

variable {G V : Type*} [Group G] [AddCommGroup V] [Module F V] (r : G →* Module.End F V)

private lemma ker_eq_bot_of_commute
    (hirr : ∀ Y : Submodule F V, (∀ g, ∀ y ∈ Y, r g y ∈ Y) → Y = ⊥ ∨ Y = ⊤)
    {a : Module.End F V} (ha : a ≠ 0) (hc : ∀ g, Commute (r g) a) : LinearMap.ker a = ⊥ := by
  refine (hirr _ fun g y hy => ?_).resolve_right fun h => ha (LinearMap.ker_eq_top.mp h)
  rw [LinearMap.mem_ker] at hy ⊢
  have := congrArg (· y) (hc g).eq
  simp only [Module.End.mul_apply, hy, map_zero] at this
  exact this.symm

private lemma isDomain_adjoin [Nontrivial V]
    (hirr : ∀ Y : Submodule F V, (∀ g, ∀ y ∈ Y, r g y ∈ Y) → Y = ⊥ ∨ Y = ⊤)
    (hcomm : ∀ g h, Commute (r g) (r h)) : IsDomain (Algebra.adjoin F (Set.range r)) := by
  have : NoZeroDivisors (Algebra.adjoin F (Set.range r)) := by
    refine ⟨fun {a b} hab => or_iff_not_imp_left.mpr fun ha => ?_⟩
    have ha' : (a : Module.End F V) ≠ 0 := fun h => ha (Subtype.ext h)
    have hk := ker_eq_bot_of_commute r hirr ha' fun g =>
      Algebra.commute_of_mem_adjoin_of_forall_mem_commute a.2
        (by rintro _ ⟨h, rfl⟩; exact hcomm g h)
    refine Subtype.ext (LinearMap.ext fun x => ?_)
    have hx : (b : Module.End F V) x ∈ LinearMap.ker (a : Module.End F V) := by
      simpa using congrArg (fun m : Algebra.adjoin F (Set.range r) => (m : Module.End F V) x) hab
    rw [hk] at hx
    simpa using hx
  exact NoZeroDivisors.to_isDomain (Algebra.adjoin F (Set.range r))

private lemma isCyclic_quot_of_irred [Finite G] [Nontrivial V]
    (hirr : ∀ Y : Submodule F V, (∀ g, ∀ y ∈ Y, r g y ∈ Y) → Y = ⊥ ∨ Y = ⊤)
    (hcomm : ∀ g h, Commute (r g) (r h)) (ψ : G →* Fˣ) {N : Subgroup G} [N.Normal]
    (hN : ∀ g, r g = ((ψ g : Fˣ) : F) • 1 → g ∈ N) : IsCyclic (G ⧸ N) := by
  let _ : CommRing (Algebra.adjoin F (Set.range r)) := Algebra.adjoinCommRingOfComm F
    (by rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩ -; exact hcomm g h)
  have := isDomain_adjoin r hirr hcomm
  let φ : G →* Algebra.adjoin F (Set.range r) :=
    { toFun g := ⟨(((ψ g)⁻¹ : Fˣ) : F) • r g,
        Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self g)) _⟩
      map_one' := by ext1; simp
      map_mul' g h := by
        ext1
        simp only [map_mul, MulMemClass.mk_mul_mk]
        rw [smul_mul_smul_comm, _root_.mul_inv_rev, Units.val_mul, mul_comm] }
  refine isCyclic_quot_of_hom φ fun g hg => hN g ?_
  have h1 := congrArg Subtype.val hg
  simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one] at h1
  rw [← h1, smul_smul, Units.mul_inv, one_smul]

end Irred

private def resHom (A : Subgroup (GL (Fin 3) F)) {X : Submodule F (Fin 3 → F)} (hX : IsInv A X) :
    A →* Module.End F X where
  toFun g := (Matrix.mulVecLin ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).restrict (hX g g.2)
  map_one' := by ext x; simp
  map_mul' g h := by
    ext x i
    change _ = (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (((h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (x : Fin 3 → F))) i
    simp [Matrix.mulVec_mulVec]

private lemma resHom_coe (A : Subgroup (GL (Fin 3) F)) {X : Submodule F (Fin 3 → F)}
    (hX : IsInv A X) (g : A) (x : X) :
    ((resHom A hX g x : X) : Fin 3 → F) = ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x :=
  rfl

private lemma resHom_irred {A : Subgroup (GL (Fin 3) F)} {X : Submodule F (Fin 3 → F)}
    (hX : IsInv A X) (hirr : ∀ Y ≤ X, IsInv A Y → Y = ⊥ ∨ Y = X) (Y : Submodule F X)
    (hY : ∀ g, ∀ y ∈ Y, resHom A hX g y ∈ Y) : Y = ⊥ ∨ Y = ⊤ := by
  have hinv : IsInv A (Y.map X.subtype) := by
    rintro g hg _ ⟨y, hy, rfl⟩
    exact ⟨_, hY ⟨g, hg⟩ y hy, rfl⟩
  rcases hirr _ (Submodule.map_subtype_le _ _) hinv with h | h
  · exact .inl (Submodule.map_injective_of_injective X.injective_subtype
      (h.trans (Submodule.map_bot _).symm))
  · exact .inr (Submodule.map_injective_of_injective X.injective_subtype
      (h.trans (Submodule.map_subtype_top X).symm))

private lemma false_of_irred [Finite F] {p : ℕ} (hp : p.Prime) {A : Subgroup (GL (Fin 3) F)}
    (hA : IsElemModScalars p A) (hc : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g)
    {X : Submodule F (Fin 3 → F)} (hX0 : X ≠ ⊥) (hX : IsInv A X)
    (hirr : ∀ Y ≤ X, IsInv A Y → Y = ⊥ ∨ Y = X) (ψ : A →* Fˣ)
    (hψ : ∀ g : A, (∀ x ∈ X, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = (ψ g : F) • x) →
      (g : GL (Fin 3) F) ∈ Subgroup.center (GL (Fin 3) F)) : False := by
  have : Nontrivial X := Submodule.nontrivial_iff_ne_bot.mpr hX0
  have hcomm : ∀ g h : A, Commute (resHom A hX g) (resHom A hX h) := fun g h => by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (hc _ g.2 _ h.2))
  refine not_isCyclic_quot hp (fun g => Subgroup.mem_subgroupOf.mpr ?_) hA.card_eq
    (isCyclic_quot_of_irred (resHom A hX) (resHom_irred hX hirr) hcomm ψ fun g hg =>
      Subgroup.mem_subgroupOf.mpr (hψ g fun x hx => ?_))
  · simpa using hA.pow_mem g g.2
  · have := congrArg (fun f : Module.End F X => (f ⟨x, hx⟩ : Fin 3 → F)) hg
    simpa [resHom_coe] using this

private def eigChar (A : Subgroup (GL (Fin 3) F)) {w : Fin 3 → F} {i : Fin 3} (hi : w i ≠ 0)
    (heig : ∀ g : A, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w =
      ((((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) i / w i) • w) : A →* F where
  toFun g := (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) i / w i
  map_one' := by simp [hi]
  map_mul' g h := by
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [← Matrix.mulVec_mulVec, heig h, Matrix.mulVec_smul, heig g]
    simp [hi]
    ring

private lemma exists_char {A : Subgroup (GL (Fin 3) F)} {L : Submodule F (Fin 3 → F)}
    (hL : IsInv A L) (h1 : finrank F L ≤ 1) :
    ∃ ψ : A →* Fˣ, ∀ g : A, ∀ y ∈ L,
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y = (ψ g : F) • y := by
  obtain ⟨w, hw⟩ := finrank_le_one_iff.mp h1
  by_cases hw0 : (w : Fin 3 → F) = 0
  · refine ⟨1, fun g y hy => ?_⟩
    obtain ⟨c, hc⟩ := hw ⟨y, hy⟩
    have : y = 0 := by simpa [hw0] using (congrArg Subtype.val hc).symm
    simp [this]
  obtain ⟨i, hi⟩ : ∃ i, (w : Fin 3 → F) i ≠ 0 := by
    by_contra h; push Not at h; exact hw0 (funext h)
  have hmul : ∀ g : A, ∃ c : F,
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = c • (w : Fin 3 → F) := fun g => by
    obtain ⟨c, hc⟩ := hw ⟨_, hL g g.2 w w.2⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  have heig : ∀ g : A, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w =
      ((((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) i / (w : Fin 3 → F) i) •
        (w : Fin 3 → F) := fun g => by
    obtain ⟨c, hc⟩ := hmul g
    rw [hc]; simp [hi]
  refine ⟨(eigChar A hi heig).toHomUnits, fun g y hy => ?_⟩
  obtain ⟨c, hc⟩ := hw ⟨y, hy⟩
  have hy' : y = c • (w : Fin 3 → F) := by simpa using (congrArg Subtype.val hc).symm
  rw [hy']
  simp only [Matrix.mulVec_smul, MonoidHom.coe_toHomUnits]
  rw [heig g, smul_comm]
  rfl

private lemma false_of_split [Finite F] {p : ℕ} (hp : p.Prime) {A : Subgroup (GL (Fin 3) F)}
    (hA : IsElemModScalars p A) (hc : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g)
    {X : Submodule F (Fin 3 → F)} (hX0 : X ≠ ⊥) (hX : IsInv A X)
    (hirr : ∀ Y ≤ X, IsInv A Y → Y = ⊥ ∨ Y = X) {Y : Submodule F (Fin 3 → F)} (hY : IsInv A Y)
    (hY1 : finrank F Y ≤ 1) (hXY : X ⊔ Y = ⊤) : False := by
  obtain ⟨ψ, hψ⟩ := exists_char hY hY1
  refine false_of_irred hp hA hc hX0 hX hirr ψ fun g hg =>
    mem_center_of_smul (c := (ψ g : F)) fun v => ?_
  have hv : v ∈ X ⊔ Y := hXY ▸ Submodule.mem_top
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  rw [Matrix.mulVec_add, hg x hx, hψ g y hy, smul_add]

private lemma IsInv.sup {A : Subgroup (GL (Fin 3) F)} {X Y : Submodule F (Fin 3 → F)}
    (hX : IsInv A X) (hY : IsInv A Y) : IsInv A (X ⊔ Y) := by
  intro g hg v hv
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  rw [Matrix.mulVec_add]
  exact Submodule.add_mem_sup (hX g hg x hx) (hY g hg y hy)

private def matRep (A : Subgroup (GL (Fin 3) F)) : Representation F A (Fin 3 → F) where
  toFun g := Matrix.mulVecLin ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

private lemma exists_inv_compl [Finite F] {A : Subgroup (GL (Fin 3) F)} [NeZero (Nat.card A : F)]
    {X : Submodule F (Fin 3 → F)} (hX : IsInv A X) : ∃ Y, IsInv A Y ∧ IsCompl X Y := by
  have : Finite A := inferInstance
  obtain ⟨τ, hτ⟩ := exists_isCompl
    (⟨X, fun g v hv => hX g g.2 v hv⟩ : Subrepresentation (matRep A))
  refine ⟨τ.toSubmodule, fun g hg w hw => τ.apply_mem_toSubmodule ⟨g, hg⟩ hw, ?_⟩
  exact IsCompl.of_eq (congrArg Subrepresentation.toSubmodule hτ.inf_eq_bot)
    (congrArg Subrepresentation.toSubmodule hτ.sup_eq_top)

private lemma exists_irred {A : Subgroup (GL (Fin 3) F)} {W : Submodule F (Fin 3 → F)}
    (hW0 : W ≠ ⊥) (hW : IsInv A W) :
    ∃ X ≤ W, X ≠ ⊥ ∧ IsInv A X ∧ ∀ Y ≤ X, IsInv A Y → Y = ⊥ ∨ Y = X := by
  obtain ⟨X, ⟨hXW, hX0, hX⟩, hmin⟩ :=
    (measure fun X : Submodule F (Fin 3 → F) => finrank F X).wf.has_min
    {X | X ≤ W ∧ X ≠ ⊥ ∧ IsInv A X} ⟨W, le_rfl, hW0, hW⟩
  refine ⟨X, hXW, hX0, hX, fun Y hYX hY => or_iff_not_imp_left.mpr fun hY0 => ?_⟩
  by_contra hne
  exact hmin Y ⟨hYX.trans hXW, hY0, hY⟩
    (Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hYX hne))

private lemma one_le_finrank {X : Submodule F (Fin 3 → F)} (h : X ≠ ⊥) : 1 ≤ finrank F X :=
  Nat.one_le_iff_ne_zero.mpr fun h0 => h (Submodule.finrank_eq_zero.mp h0)

private lemma exists_line_compl [Finite F] {p : ℕ} (hp : p.Prime) {A : Subgroup (GL (Fin 3) F)}
    (hA : IsElemModScalars p A) (hc : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g) [NeZero (Nat.card A : F)] :
    ∃ X Y : Submodule F (Fin 3 → F), IsInv A X ∧ IsInv A Y ∧ IsCompl X Y ∧
      finrank F X = 1 ∧ finrank F Y = 2 := by
  obtain ⟨X, -, hX0, hX, hirr⟩ :=
    exists_irred (A := A) (W := ⊤) top_ne_bot fun _ _ _ _ => Submodule.mem_top
  obtain ⟨Y, hY, hXY⟩ := exists_inv_compl hX
  have hsum := Submodule.finrank_add_eq_of_isCompl hXY
  rw [Module.finrank_fin_fun] at hsum
  have h1 := one_le_finrank hX0
  have h2 : 2 ≤ finrank F Y := by
    by_contra h
    exact false_of_split hp hA hc hX0 hX hirr hY (by omega) hXY.sup_eq_top
  exact ⟨X, Y, hX, hY, hXY, by omega, by omega⟩

private lemma exists_line_le [Finite F] {p : ℕ} (hp : p.Prime) {A : Subgroup (GL (Fin 3) F)}
    (hA : IsElemModScalars p A) (hc : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g)
    {X Y : Submodule F (Fin 3 → F)} (hX : IsInv A X) (hY : IsInv A Y) (hXY : IsCompl X Y)
    (hX1 : finrank F X = 1) (hY2 : finrank F Y = 2) :
    ∃ X' ≤ Y, IsInv A X' ∧ finrank F X' = 1 := by
  have hY0 : Y ≠ ⊥ := fun h => by rw [h, finrank_bot] at hY2; omega
  obtain ⟨X', hX'Y, hX'0, hX', hirr⟩ := exists_irred hY0 hY
  have hne : X' ≠ Y := by
    rintro rfl
    exact false_of_split hp hA hc hX'0 hX' hirr hX hX1.le (by rw [sup_comm]; exact hXY.sup_eq_top)
  have := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hX'Y hne)
  have := one_le_finrank hX'0
  exact ⟨X', hX'Y, hX', by omega⟩

private lemma exists_three_lines [Finite F] {p : ℕ} (hp : p.Prime) {A : Subgroup (GL (Fin 3) F)}
    (hA : IsElemModScalars p A) (hc : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g) [NeZero (Nat.card A : F)] :
    ∃ L : Fin 3 → Submodule F (Fin 3 → F), (∀ i, IsInv A (L i)) ∧ (∀ i, finrank F (L i) = 1) ∧
      L 0 ⊔ L 1 ⊔ L 2 = ⊤ := by
  obtain ⟨X, Y, hX, hY, hXY, hX1, hY2⟩ := exists_line_compl hp hA hc
  obtain ⟨X', hX'Y, hX', hX'1⟩ := exists_line_le hp hA hc hX hY hXY hX1 hY2
  obtain ⟨Z, hZ, hWZ⟩ := exists_inv_compl (hX.sup hX')
  have hinf : X ⊓ X' = ⊥ := eq_bot_iff.mpr ((inf_le_inf_left X hX'Y).trans hXY.inf_eq_bot.le)
  have hW := Submodule.finrank_sup_add_finrank_inf_eq X X'
  rw [hinf, finrank_bot, hX1, hX'1] at hW
  have hsum := Submodule.finrank_add_eq_of_isCompl hWZ
  rw [Module.finrank_fin_fun] at hsum
  refine ⟨![X, X', Z], fun i => ?_, fun i => ?_, hWZ.sup_eq_top⟩
  · fin_cases i <;> assumption
  · fin_cases i
    exacts [hX1, hX'1, show finrank F Z = 1 by omega]

private lemma exists_span_vec {L : Submodule F (Fin 3 → F)} (h1 : finrank F L = 1) :
    ∃ v ∈ L, ∀ y ∈ L, ∃ c : F, c • v = y := by
  obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.mp h1
  refine ⟨v, v.2, fun y hy => ?_⟩
  obtain ⟨c, hc⟩ := hv ⟨y, hy⟩
  exact ⟨c, by simpa using congrArg Subtype.val hc⟩

private lemma exists_coords {L : Fin 3 → Submodule F (Fin 3 → F)} (htop : L 0 ⊔ L 1 ⊔ L 2 = ⊤)
    {v : Fin 3 → Fin 3 → F} (hv : ∀ i, ∀ y ∈ L i, ∃ c : F, c • v i = y) (x : Fin 3 → F) :
    ∃ c : Fin 3 → F, ∑ j, c j • v j = x := by
  have hx : x ∈ L 0 ⊔ L 1 ⊔ L 2 := htop ▸ Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨y0, hy0, y1, hy1, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨c0, rfl⟩ := hv 0 y0 hy0
  obtain ⟨c1, rfl⟩ := hv 1 y1 hy1
  obtain ⟨c2, rfl⟩ := hv 2 z hz
  exact ⟨![c0, c1, c2], by simp [Fin.sum_univ_three]⟩

private lemma exists_conj_eq_diag {A : Subgroup (GL (Fin 3) F)} (v : Fin 3 → Fin 3 → F)
    (ψ : Fin 3 → A →* Fˣ) (hspan : ∀ x : Fin 3 → F, ∃ c : Fin 3 → F, ∑ j, c j • v j = x)
    (hψ : ∀ j (g : A), ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v j = (ψ j g : F) • v j) :
    ∃ P : GL (Fin 3) F, ∀ g : A, P * g * P⁻¹ = diagThree fun j => ψ j g := by
  set Q : Matrix (Fin 3) (Fin 3) F := Matrix.of fun a j => v j a
  have hQ : IsUnit Q := Matrix.mulVec_surjective_iff_isUnit.mp fun x => by
    obtain ⟨c, hc⟩ := hspan x
    refine ⟨c, ?_⟩
    rw [← hc]
    ext a
    simp [Q, Matrix.mulVec, dotProduct, Fin.sum_univ_three, mul_comm]
  refine ⟨hQ.unit⁻¹, fun g => Units.ext ?_⟩
  have hgQ : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * hQ.unit =
      hQ.unit * diagonal fun j => (ψ j g : F) := by
    rw [IsUnit.unit_spec]
    ext a j
    have := congrFun (hψ j g) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Q, Matrix.of_apply]
    rw [this, mul_comm]
  rw [inv_inv, Units.val_mul, Units.val_mul, mul_assoc, hgQ, ← mul_assoc, Units.inv_mul, one_mul]
  rfl

private lemma psi_eq_of_diagonal {A : Subgroup (GL (Fin 3) F)} {P : GL (Fin 3) F}
    {ψ : Fin 3 → A →* Fˣ} (hP : ∀ g : A, P * g * P⁻¹ = diagThree fun j => ψ j g) {g : A}
    {c : Fˣ} (hg : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal fun _ => (c : F))
    (j : Fin 3) : ψ j g = c := by
  have hcen : (g : GL (Fin 3) F) ∈ Subgroup.center (GL (Fin 3) F) :=
    mem_center_of_smul (c := (c : F)) fun v => by ext i; simp [hg, Matrix.mulVec_diagonal]
  have h1 : P * g * P⁻¹ = g := by
    rw [Subgroup.mem_center_iff.mp hcen P, mul_inv_cancel_right]
  have := congrArg (fun M : GL (Fin 3) F => (M : Matrix (Fin 3) (Fin 3) F) j j)
    ((hP g).symm.trans h1)
  simp only [diagThree, diagonal_apply_eq, hg] at this
  exact Units.ext this

private lemma mem_center_of_psi_eq {A : Subgroup (GL (Fin 3) F)} {P : GL (Fin 3) F}
    {ψ : Fin 3 → A →* Fˣ} (hP : ∀ g : A, P * g * P⁻¹ = diagThree fun j => ψ j g) {g : A}
    (h0 : ψ 0 g = ψ 2 g) (h1 : ψ 1 g = ψ 2 g) :
    (g : GL (Fin 3) F) ∈ Subgroup.center (GL (Fin 3) F) := by
  have hz : P * g * P⁻¹ ∈ Subgroup.center (GL (Fin 3) F) := by
    rw [hP g]
    refine mem_center_of_smul (c := (ψ 2 g : F)) fun v => ?_
    ext i
    fin_cases i <;> simp [diagThree, Matrix.mulVec_diagonal, h0, h1]
  have := (inferInstance : (Subgroup.center (GL (Fin 3) F)).Normal).conj_mem _ hz P⁻¹
  simpa [mul_assoc] using this

private def thetaHom {A : Subgroup (GL (Fin 3) F)} (ψ : Fin 3 → A →* Fˣ) : A →* Fˣ × Fˣ :=
  (ψ 0 / ψ 2).prod (ψ 1 / ψ 2)

private lemma thetaHom_apply {A : Subgroup (GL (Fin 3) F)} (ψ : Fin 3 → A →* Fˣ) (g : A) :
    thetaHom ψ g = (ψ 0 g / ψ 2 g, ψ 1 g / ψ 2 g) :=
  rfl

private lemma range_thetaHom [Finite F] {p : ℕ} (hp : p.Prime) {A : Subgroup (GL (Fin 3) F)}
    (hA : IsElemModScalars p A) {P : GL (Fin 3) F} {ψ : Fin 3 → A →* Fˣ}
    (hP : ∀ g : A, P * g * P⁻¹ = diagThree fun j => ψ j g) :
    (thetaHom ψ).range = (rootsOfUnity p F).prod (rootsOfUnity p F) ∧
      p ≤ Nat.card (rootsOfUnity p F) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hle : (thetaHom ψ).range ≤ (rootsOfUnity p F).prod (rootsOfUnity p F) := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨c, hc⟩ := eq_diagonal_of_mem_center (hA.pow_mem g g.2)
    have h := psi_eq_of_diagonal hP (g := g ^ p) (c := c) (by simpa using hc)
    simp only [thetaHom_apply, Subgroup.mem_prod, mem_rootsOfUnity, div_pow, ← map_pow, h,
      div_self', and_self]
  have hker : (thetaHom ψ).ker ≤ (Subgroup.center (GL (Fin 3) F)).subgroupOf A := fun g hg => by
    rw [MonoidHom.mem_ker, thetaHom_apply, Prod.mk_eq_one, div_eq_one, div_eq_one] at hg
    exact Subgroup.mem_subgroupOf.mpr (mem_center_of_psi_eq hP hg.1 hg.2)
  have hcard : p ^ 2 ≤ Nat.card (thetaHom ψ).range := by
    rw [← hA.card_eq, ← Subgroup.index_eq_card, ← Subgroup.index_ker]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hker)
  have hprod : Nat.card ((rootsOfUnity p F).prod (rootsOfUnity p F)) =
      Nat.card (rootsOfUnity p F) * Nat.card (rootsOfUnity p F) := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
  have hμ := card_rootsOfUnity F p
  have h2 := Subgroup.card_le_of_le hle
  refine ⟨Subgroup.eq_of_le_of_card_ge hle (by nlinarith), by nlinarith⟩

private lemma exists_psi_eq [Finite F] {p : ℕ} (hp : p.Prime) {A : Subgroup (GL (Fin 3) F)}
    (hA : IsElemModScalars p A) {P : GL (Fin 3) F} {ψ : Fin 3 → A →* Fˣ}
    (hP : ∀ g : A, P * g * P⁻¹ = diagThree fun j => ψ j g) {a b : Fˣ}
    (ha : a ∈ rootsOfUnity p F) (hb : b ∈ rootsOfUnity p F) :
    ∃ g : A, ψ 0 g = a ∧ ψ 1 g = b ∧ ψ 2 g = 1 := by
  obtain ⟨g, hg⟩ : (a, b) ∈ (thetaHom ψ).range :=
    (range_thetaHom hp hA hP).1 ▸ Subgroup.mem_prod.mpr ⟨ha, hb⟩
  rw [thetaHom_apply, Prod.mk.injEq] at hg
  obtain ⟨c, hc⟩ : ∃ c, c = (ψ 2 g)⁻¹ := ⟨_, rfl⟩
  have hs : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ A := hA.center_le (by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨_, rfl⟩)
  have hψs := psi_eq_of_diagonal hP (g := ⟨_, hs⟩) (c := c) (by simp [Matrix.scalar_apply])
  refine ⟨⟨_, hs⟩ * g, ?_, ?_, ?_⟩ <;> rw [map_mul, hψs, hc]
  · rw [← hg.1, inv_mul_eq_div]
  · rw [← hg.2, inv_mul_eq_div]
  · rw [inv_mul_cancel]

private lemma neZero_card {q : ℕ} [Fact q.Prime] {p : ℕ} (hp : p.Prime) (hpq : p ≠ q)
    {A : Subgroup (GL (Fin 3) (ZMod q))} (hA : IsElemModScalars p A) :
    NeZero (Nat.card A : ZMod q) := by
  have hq : q.Prime := Fact.out
  refine ⟨fun h => ?_⟩
  rw [ZMod.natCast_eq_zero_iff] at h
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := A) q h
  obtain ⟨c, hc⟩ := eq_diagonal_of_mem_center (hA.pow_mem g g.2)
  have h1 : g ^ (p * (q - 1)) = 1 := by
    refine Subtype.ext (Units.ext ?_)
    rw [pow_mul]
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hc, Matrix.diagonal_pow,
      OneMemClass.coe_one, Units.val_one]
    rw [show (fun _ : Fin 3 => (c : ZMod q)) ^ (q - 1) = fun _ => 1 from
      funext fun _ => ZMod.pow_card_sub_one_eq_one c.ne_zero, Matrix.diagonal_one]
  have hdvd := orderOf_dvd_of_pow_eq_one h1
  rw [hg] at hdvd
  have := hq.two_le
  rcases hq.dvd_mul.mp hdvd with h | h
  · exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
  · have := Nat.le_of_dvd (by omega) h
    omega

theorem exists_conj_diag_of_commute {q : ℕ} [Fact q.Prime] {p : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2)
    (hpq : p ≠ q) {A : Subgroup (GL (Fin 3) (ZMod q))} (hA : IsElemModScalars p A)
    (hc : ∀ g ∈ A, ∀ h ∈ A, g * h = h * g) :
    ∃ (ζ : (ZMod q)ˣ) (P : GL (Fin 3) (ZMod q)), ζ ≠ 1 ∧
      diagThree ![ζ, 1, 1] ∈ A.map (MulAut.conj P).toMonoidHom ∧
      diagThree ![1, ζ, 1] ∈ A.map (MulAut.conj P).toMonoidHom := by
  have := neZero_card hp hpq hA
  obtain ⟨L, hLinv, hL1, htop⟩ := exists_three_lines hp hA hc
  choose v hvL hv using fun i => exists_span_vec (hL1 i)
  choose ψ hψ using fun i => exists_char (hLinv i) (hL1 i).le
  obtain ⟨P, hP⟩ := exists_conj_eq_diag v ψ (exists_coords htop hv) fun j g => hψ j g _ (hvL j)
  obtain ⟨-, hμ⟩ := range_thetaHom hp hA hP
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨⟨ζ, hζμ⟩, hζ⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    ((Subgroup.one_lt_card_iff_ne_bot _).mp (by have := hp.two_le; omega) :
      rootsOfUnity p (ZMod q) ≠ ⊥)
  have hζ1 : ζ ≠ 1 := fun h => hζ (Subtype.ext h)
  obtain ⟨g, hg0, hg1, hg2⟩ := exists_psi_eq hp hA hP hζμ (Subgroup.one_mem _)
  obtain ⟨h, hh0, hh1, hh2⟩ := exists_psi_eq hp hA hP (Subgroup.one_mem _) hζμ
  refine ⟨ζ, P, hζ1, ⟨g, g.2, ?_⟩, ⟨h, h.2, ?_⟩⟩
  · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hP g]
    congr 1; funext j; fin_cases j <;> simp [hg0, hg1, hg2]
  · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hP h]
    congr 1; funext j; fin_cases j <;> simp [hh0, hh1, hh2]

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
