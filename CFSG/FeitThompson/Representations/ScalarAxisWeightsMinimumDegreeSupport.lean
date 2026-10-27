module

public import CFSG.FeitThompson.Representations.RegularRepresentationContainsIrreducibles
public import CFSG.FeitThompson.Representations.FrobeniusAbelianKernelInducedCharacters
public import CFSG.FeitThompson.Representations.InvariantDetectingCharsQuotientDegree
public import CFSG.FeitThompson.Representations.TwoCoordinateWeightKernelIntersections

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module SemidirectProduct

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open NormalInduction (conjClassFun conjClassFun_apply)

theorem finite_monoidHom_units (A : Type*) [CommGroup A] [Finite A] : Finite (A →* ℂˣ) := by
  have h : Set.range (linearCharFun (A := A)) ⊆ Irr A := by rw [Irr_eq_range_linearCharFun]
  have hfin : (Set.range (linearCharFun (A := A))).Finite := Set.Finite.subset finite_Irr h
  have := hfin.to_subtype
  exact Finite.of_injective (fun χ => (⟨linearCharFun χ, Set.mem_range_self χ⟩ :
    (Set.range (linearCharFun (A := A)) : Set (A → ℂ)))) fun _ _ h =>
    linearCharFun_injective (congrArg Subtype.val h)

theorem natCard_monoidHom_units {A : Type*} [CommGroup A] [Finite A] :
    Nat.card (A →* ℂˣ) = Nat.card A := by
  have h1 : Nat.card (Set.range (linearCharFun (A := A))) = Nat.card (A →* ℂˣ) :=
    Nat.card_range_of_injective linearCharFun_injective
  rw [← h1, ← Irr_eq_range_linearCharFun, card_Irr_eq_card]

theorem natCard_monoidHom_units_trivialOn {A : Type*} [CommGroup A] [Finite A] (W : Subgroup A) :
    Nat.card {χ : A →* ℂˣ // ∀ w ∈ W, χ w = 1} = W.index := by
  have h1 : {χ : A →* ℂˣ // ∀ w ∈ W, χ w = 1} ≃ (MonoidHom.domRestrictHom W ℂˣ).ker := by
    refine Equiv.subtypeEquivRight fun χ => ?_
    rw [MonoidHom.mem_ker]
    refine ⟨fun h => ?_, fun h w hw => ?_⟩
    · ext w; simpa [MonoidHom.domRestrictHom] using h w w.2
    · simpa [MonoidHom.domRestrictHom] using DFunLike.congr_fun h (⟨w, hw⟩ : W)
  rw [Nat.card_congr h1, Nat.card_congr (MonoidHom.domRestrictHomKerEquiv ℂˣ W).toEquiv,
    natCard_monoidHom_units, ← Subgroup.index_eq_card]

theorem natCard_subtype_ne {α : Type*} [Finite α] (a : α) :
    Nat.card {x : α // x ≠ a} = Nat.card α - 1 := by
  classical
  have := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (p := fun x => x = a)]
  have h : Fintype.card {x : α // x = a} = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨a, rfl⟩, fun y => Subtype.ext y.2⟩
  rw [h]

theorem bijOn_comp_of_surjective {G G' : Type*} [Group G] [Group G'] [Finite G]
    {ρ : G →* G'} (hρ : Function.Surjective ρ) :
    Set.BijOn (fun θ : G' → ℂ => θ ∘ ρ) (Irr G') (irrTrivialOn ρ.ker) := by
  have : Finite G' := Finite.of_surjective _ hρ
  set e := QuotientGroup.liftEquiv (φ := ρ) ρ.ker hρ rfl with he
  have hemk : ∀ x : G, e (QuotientGroup.mk x) = ρ x := fun x => QuotientGroup.liftEquiv_mk _ _ _ _
  refine ⟨fun θ hθ => ?_, fun θ _ θ' _ h => ?_, fun χ hχ => ?_⟩
  · have h1 : θ ∘ e ∈ Irr (G ⧸ ρ.ker) := FrobeniusInduction.mem_Irr_comp_mulEquiv hθ e
    have h2 := mem_irrTrivialOn_comp_mk h1
    have h3 : (θ ∘ e) ∘ (QuotientGroup.mk : G → G ⧸ ρ.ker) = θ ∘ ρ := by
      funext x; simp only [Function.comp_apply, hemk]
    rwa [h3] at h2
  · funext y
    obtain ⟨x, rfl⟩ := hρ y
    exact congrFun h x
  · obtain ⟨ψ, hψ, hψ'⟩ := exists_comp_mk_eq_of_mem_irrTrivialOn hχ
    refine ⟨ψ ∘ e.symm, FrobeniusInduction.mem_Irr_comp_mulEquiv hψ e.symm, ?_⟩
    funext x
    have h4 : e.symm (ρ x) = QuotientGroup.mk x := by rw [← hemk x, MulEquiv.symm_apply_apply]
    simp only [Function.comp_apply, h4]
    exact congrFun hψ' x

variable {p q : ℕ} [Fact p.Prime] {V U : Type*} [AddCommGroup V] [Module (ZMod p) V] [Group U]

namespace ScalarCoordinateSystem

variable (S : ScalarCoordinateSystem p q V U)

def offLine (i : Fin q) : Submodule (ZMod p) V := ⨆ j, ⨆ (_ : j ≠ i), S.line j

theorem line_le_offLine {i j : Fin q} (h : j ≠ i) : S.line j ≤ S.offLine i :=
  le_trans (le_iSup (fun (_ : j ≠ i) => S.line j) h)
    (le_iSup (fun j => ⨆ (_ : j ≠ i), S.line j) j)

theorem isCompl_line_offLine (i : Fin q) : IsCompl (S.line i) (S.offLine i) := by
  refine ⟨S.indep_line i, ?_⟩
  rw [codisjoint_iff, eq_top_iff, ← S.iSup_line]
  refine iSup_le fun j => ?_
  by_cases h : j = i
  · exact h ▸ le_sup_left
  · exact le_trans (S.line_le_offLine h) le_sup_right

theorem offLine_induction {i : Fin q} {motive : V → Prop}
    (hline : ∀ j, j ≠ i → ∀ v ∈ S.line j, motive v) (h0 : motive 0)
    (hadd : ∀ v w, motive v → motive w → motive (v + w)) {v : V} (hv : v ∈ S.offLine i) :
    motive v :=
  Submodule.iSup_induction _ (motive := motive) hv
    (fun j x hx => Submodule.iSup_induction _ (motive := motive) hx
      (fun hj y hy => hline j hj y hy) h0 hadd) h0 hadd

noncomputable def lineProj (i : Fin q) : V →ₗ[ZMod p] S.line i :=
  (S.line i).projectionOnto (S.offLine i) (S.isCompl_line_offLine i)

theorem lineProj_eq_zero_iff (i : Fin q) {v : V} : S.lineProj i v = 0 ↔ v ∈ S.offLine i :=
  Submodule.projectionOnto_apply_eq_zero_iff _

theorem lineProj_apply_coe (i : Fin q) (v : S.line i) : S.lineProj i (v : V) = v :=
  Submodule.projectionOnto_apply_left _ _

theorem sub_lineProj_mem_offLine (i : Fin q) (v : V) :
    v - (S.lineProj i v : V) ∈ S.offLine i := by
  rw [← S.lineProj_eq_zero_iff, map_sub, S.lineProj_apply_coe, sub_self]

theorem lineProj_surjective (i : Fin q) : Function.Surjective (S.lineProj i) :=
  fun v => ⟨(v : V), S.lineProj_apply_coe i v⟩

theorem natCard_line (i : Fin q) : Nat.card (S.line i) = p := by
  have : Finite V := S.finite_of_finite_line
  have : Fintype V := Fintype.ofFinite _
  have : Fintype (S.line i) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p) (V := S.line i),
    S.finrank_line i, pow_one, ZMod.card]

theorem mulAutHom_symm_apply (u : U) (v : V) :
    (S.mulAutHom u).symm (Multiplicative.ofAdd v) = Multiplicative.ofAdd ((S.act u).symm v) := by
  have h : S.mulAutHom u (Multiplicative.ofAdd ((S.act u).symm v)) = Multiplicative.ofAdd v := by
    rw [S.mulAutHom_apply]; simp
  rw [← h, MulEquiv.symm_apply_apply]

theorem inv_mul_inl_mul (x : S.grp) (v : V) :
    x⁻¹ * (inl (Multiplicative.ofAdd v) : S.grp) * x
      = inl (Multiplicative.ofAdd (S.act x.right⁻¹ v)) := by
  have h : x⁻¹ * (inl (Multiplicative.ofAdd v) : S.grp) * x
      = inl (Multiplicative.ofAdd ((S.act x.right).symm v)) := by
    apply SemidirectProduct.ext
    · simp [mul_left, inv_left, S.mulAutHom_symm_apply]
    · simp [mul_right, inv_right]
  rw [h]
  congr 2
  show (S.act x.right).symm v = S.act x.right⁻¹ v
  rw [map_inv]
  rfl

noncomputable def baseChar (χ : Multiplicative V →* ℂˣ) : S.base → ℂ :=
  linearCharFun χ ∘ S.baseEquiv.symm

theorem baseChar_apply (χ : Multiplicative V →* ℂˣ) (y : Multiplicative V) :
    S.baseChar χ (S.baseHom y) = (χ y : ℂ) := by
  have h : S.baseEquiv.symm (S.baseHom y) = y := by
    rw [← S.baseEquiv_apply]; exact S.baseEquiv.symm_apply_apply y
  simp [baseChar, h, linearCharFun_apply]

theorem baseChar_one (χ : Multiplicative V →* ℂˣ) : S.baseChar χ 1 = 1 := by
  have := S.baseChar_apply χ 1
  simpa using this

theorem baseChar_mem_Irr (χ : Multiplicative V →* ℂˣ) : S.baseChar χ ∈ Irr S.base :=
  FrobeniusInduction.mem_Irr_comp_mulEquiv (linearCharFun_mem_Irr χ) S.baseEquiv.symm

theorem baseChar_injective : Function.Injective S.baseChar := by
  intro χ χ' h
  refine linearCharFun_injective (A := Multiplicative V) ?_
  funext y
  have := congrFun h (S.baseHom y)
  rw [S.baseChar_apply, S.baseChar_apply] at this
  simpa [linearCharFun_apply] using this

theorem exists_baseChar_eq {lam : S.base → ℂ} (h : lam ∈ Irr S.base) :
    ∃ χ : Multiplicative V →* ℂˣ, S.baseChar χ = lam := by
  obtain ⟨χ, hχ⟩ := exists_linearCharFun_eq_of_mem_Irr (S.comp_baseEquiv_mem_Irr h)
  refine ⟨χ, ?_⟩
  funext x
  have := congrFun hχ (S.baseEquiv.symm x)
  simpa [baseChar] using this

noncomputable def charAct (u : U) (χ : Multiplicative V →* ℂˣ) : Multiplicative V →* ℂˣ :=
  χ.comp (S.mulAutHom u).toMonoidHom

theorem charAct_apply (u : U) (χ : Multiplicative V →* ℂˣ) (v : V) :
    S.charAct u χ (Multiplicative.ofAdd v) = χ (Multiplicative.ofAdd (S.act u v)) := by
  rw [charAct, MonoidHom.comp_apply]
  congr 1
  exact S.mulAutHom_apply u v

theorem charAct_one (χ : Multiplicative V →* ℂˣ) : S.charAct 1 χ = χ :=
  MonoidHom.ext fun x => by
    induction x using Multiplicative.rec with
    | _ v => rw [S.charAct_apply]; simp

theorem charAct_mul (u u' : U) (χ : Multiplicative V →* ℂˣ) :
    S.charAct (u * u') χ = S.charAct u' (S.charAct u χ) :=
  MonoidHom.ext fun x => by
    induction x using Multiplicative.rec with
    | _ v =>
      rw [S.charAct_apply, S.charAct_apply, S.charAct_apply]
      congr 2
      show S.act (u * u') v = S.act u (S.act u' v)
      rw [map_mul]; rfl

theorem conjClassFun_baseChar (t : S.grp) (χ : Multiplicative V →* ℂˣ) :
    conjClassFun S.base t (S.baseChar χ) = S.baseChar (S.charAct t.right⁻¹ χ) := by
  funext x
  obtain ⟨y, hy⟩ : ∃ y : Multiplicative V, S.baseHom y = x :=
    ⟨S.baseEquiv.symm x, by rw [← S.baseEquiv_apply, MulEquiv.apply_symm_apply]⟩
  subst hy
  rw [conjClassFun_apply, S.baseChar_apply]
  induction y using Multiplicative.rec with
  | _ v =>
    rw [S.charAct_apply]
    have hc : (MulAut.conjNormal t⁻¹) (S.baseHom (Multiplicative.ofAdd v))
        = S.baseHom (Multiplicative.ofAdd (S.act t.right⁻¹ v)) := by
      refine Subtype.ext ?_
      rw [MulAut.conjNormal_apply, S.coe_baseHom_apply, S.coe_baseHom_apply, inv_inv]
      exact S.inv_mul_inl_mul t v
    rw [hc, S.baseChar_apply]

section Quot

theorem commutator_le_ker_act : commutator U ≤ S.act.ker := fun _ hu =>
  MonoidHom.mem_ker.2 (LinearEquiv.ext fun v =>
    S.mem_totalCentralizer.1 (S.commutator_le_totalCentralizer hu) v)

noncomputable def quotAct : (U ⧸ commutator U) →* (V ≃ₗ[ZMod p] V) :=
  QuotientGroup.lift _ S.act S.commutator_le_ker_act

theorem quotAct_mk (u : U) : S.quotAct (QuotientGroup.mk u) = S.act u := (rfl)

noncomputable def quot [Finite U] : ScalarCoordinateSystem p q V (U ⧸ commutator U) where
  two_le_q := S.two_le_q
  line := S.line
  finrank_line := S.finrank_line
  indep_line := S.indep_line
  iSup_line := S.iSup_line
  act := S.quotAct
  map_line := by
    intro u i v hv
    induction u using QuotientGroup.induction_on with
    | _ w => rw [S.quotAct_mk]; exact S.map_line w i v hv
  coprime_card := Nat.Coprime.coprime_dvd_right (Subgroup.card_quotient_dvd_card _) S.coprime_card

variable [Finite U]

theorem quot_line : (S.quot).line = S.line := (rfl)

theorem quot_act : (S.quot).act = S.quotAct := (rfl)

theorem quot_mulAutHom_mk (u : U) :
    (S.quot).mulAutHom (QuotientGroup.mk u) = S.mulAutHom u :=
  MulEquiv.ext fun x => by
    induction x using Multiplicative.rec with
    | _ v => rw [mulAutHom_apply, mulAutHom_apply, quot_act, S.quotAct_mk]

noncomputable def quotHom : S.grp →* (S.quot).grp :=
  SemidirectProduct.map (MonoidHom.id (Multiplicative V))
    (QuotientGroup.mk' (commutator U)) fun u => MonoidHom.ext fun x => by
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom]
      rw [show (QuotientGroup.mk' (commutator U)) u = QuotientGroup.mk u from rfl,
        S.quot_mulAutHom_mk]

theorem quotHom_left (x : S.grp) : (S.quotHom x).left = x.left := (rfl)

theorem quotHom_right (x : S.grp) : (S.quotHom x).right = QuotientGroup.mk x.right := (rfl)

theorem quotHom_surjective : Function.Surjective S.quotHom := fun y => by
  obtain ⟨u, hu⟩ : ∃ u : U, (QuotientGroup.mk u : U ⧸ commutator U) = y.right :=
    Quotient.exists_rep y.right
  exact ⟨⟨y.left, u⟩, SemidirectProduct.ext (S.quotHom_left _) ((S.quotHom_right _).trans hu)⟩

theorem quotHom_inl (v : Multiplicative V) : S.quotHom (inl v) = inl v :=
  SemidirectProduct.ext (by rw [quotHom_left, left_inl, left_inl])
    (by rw [quotHom_right, right_inl, right_inl]; simp)

theorem quotHom_inr (u : U) : S.quotHom (inr u) = inr (QuotientGroup.mk u) :=
  SemidirectProduct.ext (by rw [quotHom_left, left_inr, left_inr])
    (by rw [quotHom_right, right_inr, right_inr])

theorem mem_ker_quotHom {x : S.grp} :
    x ∈ (S.quotHom).ker ↔ x.left = 1 ∧ x.right ∈ commutator U := by
  rw [MonoidHom.mem_ker]
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨h1, h2⟩ => SemidirectProduct.ext ?_ ?_⟩
  · have := congrArg SemidirectProduct.left h
    rw [quotHom_left, one_left] at this; exact this
  · have := congrArg SemidirectProduct.right h
    rw [quotHom_right, one_right] at this
    exact (QuotientGroup.eq_one_iff _).1 this
  · rw [quotHom_left, h1, one_left]
  · rw [quotHom_right, one_right]
    exact (QuotientGroup.eq_one_iff _).2 h2

end Quot

def IsAxisChar (i : Fin q) (χ : Multiplicative V →* ℂˣ) : Prop :=
  (∃ v ∈ S.line i, χ (Multiplicative.ofAdd v) ≠ 1) ∧
    ∀ j, j ≠ i → ∀ v ∈ S.line j, χ (Multiplicative.ofAdd v) = 1

theorem isAxisChar_def (i : Fin q) (χ : Multiplicative V →* ℂˣ) :
    S.IsAxisChar i χ ↔ (∃ v ∈ S.line i, χ (Multiplicative.ofAdd v) ≠ 1) ∧
      ∀ j, j ≠ i → ∀ v ∈ S.line j, χ (Multiplicative.ofAdd v) = 1 := Iff.rfl

variable {S}

theorem IsAxisChar.exists_ne_one {i : Fin q} {χ : Multiplicative V →* ℂˣ}
    (h : S.IsAxisChar i χ) : ∃ v ∈ S.line i, χ (Multiplicative.ofAdd v) ≠ 1 :=
  ((S.isAxisChar_def i χ).1 h).1

theorem IsAxisChar.eq_one_of_ne {i : Fin q} {χ : Multiplicative V →* ℂˣ}
    (h : S.IsAxisChar i χ) {j : Fin q} (hj : j ≠ i) {v : V} (hv : v ∈ S.line j) :
    χ (Multiplicative.ofAdd v) = 1 :=
  ((S.isAxisChar_def i χ).1 h).2 j hj v hv

theorem isAxisChar_of {i : Fin q} {χ : Multiplicative V →* ℂˣ}
    (h1 : ∃ v ∈ S.line i, χ (Multiplicative.ofAdd v) ≠ 1)
    (h2 : ∀ j, j ≠ i → ∀ v ∈ S.line j, χ (Multiplicative.ofAdd v) = 1) : S.IsAxisChar i χ :=
  (S.isAxisChar_def i χ).2 ⟨h1, h2⟩

variable (S)

theorem map_offLine_le (u : U) (i : Fin q) :
    ∀ v ∈ S.offLine i, S.act u v ∈ S.offLine i := by
  intro v hv
  refine S.offLine_induction (motive := fun v => S.act u v ∈ S.offLine i)
    (fun j hj w hw => S.line_le_offLine hj (S.map_line u j w hw)) (by simp) ?_ hv
  intro v w hv hw
  rw [map_add]
  exact Submodule.add_mem _ hv hw

theorem act_inv_act (u : U) (v : V) : S.act u (S.act u⁻¹ v) = v := by
  change (S.act u * S.act u⁻¹) v = v
  rw [← map_mul, mul_inv_cancel, map_one]
  rfl

variable {S}

theorem IsAxisChar.eq_one_of_mem_offLine {i : Fin q} {χ : Multiplicative V →* ℂˣ}
    (h : S.IsAxisChar i χ) {v : V} (hv : v ∈ S.offLine i) : χ (Multiplicative.ofAdd v) = 1 := by
  refine S.offLine_induction (motive := fun v => χ (Multiplicative.ofAdd v) = 1)
    (fun j hj w hw => h.2 j hj w hw) (by simp) (fun v w hv hw => ?_) hv
  rw [ofAdd_add, map_mul, hv, hw, one_mul]

theorem IsAxisChar.unique {i j : Fin q} {χ : Multiplicative V →* ℂˣ}
    (hi : S.IsAxisChar i χ) (hj : S.IsAxisChar j χ) : i = j := by
  by_contra hne
  obtain ⟨v, hv, hvne⟩ := hi.1
  exact hvne (hj.2 i hne v hv)

theorem IsAxisChar.apply_eq_lineProj {i : Fin q} {χ : Multiplicative V →* ℂˣ}
    (h : S.IsAxisChar i χ) (v : V) :
    χ (Multiplicative.ofAdd v) = χ (Multiplicative.ofAdd (S.lineProj i v : V)) := by
  set w : V := (S.lineProj i v : V) with hw
  have hoff : v - w ∈ S.offLine i := S.sub_lineProj_mem_offLine i v
  have h1 : χ (Multiplicative.ofAdd (w + (v - w))) = χ (Multiplicative.ofAdd w) := by
    rw [ofAdd_add, map_mul, h.eq_one_of_mem_offLine hoff, mul_one]
  have h2 : w + (v - w) = v := by abel
  rw [h2] at h1
  exact h1

theorem IsAxisChar.charAct_eq_self_of_mem_lineCentralizer {i : Fin q}
    {χ : Multiplicative V →* ℂˣ} (h : S.IsAxisChar i χ) {u : U}
    (hu : u ∈ S.lineCentralizer i) : S.charAct u χ = χ := by
  refine MonoidHom.ext fun x => ?_
  induction x using Multiplicative.rec with
  | _ v =>
    rw [S.charAct_apply]
    set w : V := (S.lineProj i v : V) with hw
    have hwline : w ∈ S.line i := (S.lineProj i v).2
    have hoff : v - w ∈ S.offLine i := S.sub_lineProj_mem_offLine i v
    have hact : S.act u v = w + S.act u (v - w) := by
      have h0 : S.act u v = S.act u w + S.act u (v - w) := by rw [← map_add]; congr 1; abel
      rw [h0, S.mem_lineCentralizer.1 hu w hwline]
    have hoff' : S.act u (v - w) ∈ S.offLine i := S.map_offLine_le u i _ hoff
    have h1 : χ (Multiplicative.ofAdd (S.act u v)) = χ (Multiplicative.ofAdd w) := by
      rw [hact, ofAdd_add, map_mul, h.eq_one_of_mem_offLine hoff', mul_one]
    rw [h1, h.apply_eq_lineProj v]

theorem IsAxisChar.mem_lineCentralizer_of_charAct_eq_self {i : Fin q}
    {χ : Multiplicative V →* ℂˣ} (h : S.IsAxisChar i χ) {u : U}
    (hu : S.charAct u χ = χ) : u ∈ S.lineCentralizer i := by
  obtain ⟨v, hv, hvne⟩ := h.1
  refine S.mem_lineCentralizer_of_apply_eq χ hv hvne ?_
  rw [← S.charAct_apply, hu]

theorem IsAxisChar.charAct_eq_self_iff {i : Fin q} {χ : Multiplicative V →* ℂˣ}
    (h : S.IsAxisChar i χ) {u : U} :
    S.charAct u χ = χ ↔ u ∈ S.lineCentralizer i :=
  ⟨h.mem_lineCentralizer_of_charAct_eq_self, h.charAct_eq_self_of_mem_lineCentralizer⟩

theorem IsAxisChar.charAct {i : Fin q} {χ : Multiplicative V →* ℂˣ}
    (h : S.IsAxisChar i χ) (u : U) : S.IsAxisChar i (S.charAct u χ) := by
  refine ⟨?_, fun j hj v hv => ?_⟩
  · obtain ⟨v, hv, hvne⟩ := h.1
    refine ⟨S.act u⁻¹ v, S.map_line u⁻¹ i v hv, ?_⟩
    rw [S.charAct_apply, S.act_inv_act]
    exact hvne
  · rw [S.charAct_apply]
    exact h.2 j hj _ (S.map_line u j v hv)

theorem inertiaGroup_baseChar [Finite U] {i : Fin q} {χ : Multiplicative V →* ℂˣ}
    (h : S.IsAxisChar i χ) :
    inertiaGroup S.base (S.baseChar χ) = (S.lineCentralizer i).comap rightHom := by
  ext t
  rw [mem_inertiaGroup, S.conjClassFun_baseChar, Subgroup.mem_comap, rightHom_eq_right]
  refine ⟨fun hc => ?_, fun hu => ?_⟩
  · have h2 := h.mem_lineCentralizer_of_charAct_eq_self (S.baseChar_injective hc)
    simpa using (S.lineCentralizer i).inv_mem h2
  · exact congrArg _ (h.charAct_eq_self_of_mem_lineCentralizer ((S.lineCentralizer i).inv_mem hu))

theorem index_inertiaGroup_baseChar [Finite U] {i : Fin q} {χ : Multiplicative V →* ℂˣ}
    (h : S.IsAxisChar i χ) :
    (inertiaGroup S.base (S.baseChar χ)).index = (S.lineCentralizer i).index := by
  rw [inertiaGroup_baseChar h]
  exact Subgroup.index_comap_of_surjective _ rightHom_surjective

variable (S)

def offLineSub (i : Fin q) : Subgroup (Multiplicative V) :=
  AddSubgroup.toSubgroup (S.offLine i).toAddSubgroup

theorem mem_offLineSub {i : Fin q} {v : V} :
    Multiplicative.ofAdd v ∈ S.offLineSub i ↔ v ∈ S.offLine i := Iff.rfl

theorem natCard_offLineSub (i : Fin q) : Nat.card (S.offLineSub i) = Nat.card (S.offLine i) :=
  Nat.card_congr (Equiv.refl _)

theorem index_offLineSub (i : Fin q) : (S.offLineSub i).index = p := by
  have hfin : Finite V := S.finite_of_finite_line
  have hprod : Nat.card (S.line i) * Nat.card (S.offLine i) = Nat.card V := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (Submodule.prodEquivOfIsCompl _ _ (S.isCompl_line_offLine i)).toEquiv
  have hmul := Subgroup.card_mul_index (S.offLineSub i)
  rw [S.natCard_offLineSub] at hmul
  have hcardV : Nat.card (Multiplicative V) = Nat.card V := Nat.card_congr (Equiv.refl _)
  rw [hcardV, ← hprod, mul_comm (Nat.card (S.line i))] at hmul
  rw [Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero Nat.card_pos.ne') hmul, S.natCard_line]

theorem isAxisChar_iff {i : Fin q} {χ : Multiplicative V →* ℂˣ} :
    S.IsAxisChar i χ ↔ (∀ w ∈ S.offLineSub i, χ w = 1) ∧ χ ≠ 1 := by
  refine Iff.trans (S.isAxisChar_def i χ) ?_
  refine ⟨fun h => ⟨fun w hw => ?_, ?_⟩, fun h => ⟨?_, fun j hj v hv => ?_⟩⟩
  · induction w using Multiplicative.rec with
    | _ v =>
      exact IsAxisChar.eq_one_of_mem_offLine ((S.isAxisChar_def i χ).2 h)
        ((S.mem_offLineSub).1 hw)
  · intro hcon
    obtain ⟨v, hv, hvne⟩ := h.1
    rw [hcon] at hvne; simp at hvne
  · by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    refine h.2 (MonoidHom.ext fun x => ?_)
    induction x using Multiplicative.rec with
    | _ v =>
      set w : V := (S.lineProj i v : V) with hw
      have hwline : w ∈ S.line i := (S.lineProj i v).2
      have hoff : v - w ∈ S.offLine i := S.sub_lineProj_mem_offLine i v
      have hvw : w + (v - w) = v := by abel
      rw [← hvw, ofAdd_add, map_mul, hcon w hwline, h.1 _ ((S.mem_offLineSub).2 hoff)]
      simp
  · exact h.1 _ ((S.mem_offLineSub).2 (S.line_le_offLine hj hv))

theorem natCard_setOf_isAxisChar (i : Fin q) :
    Nat.card {χ : Multiplicative V →* ℂˣ // S.IsAxisChar i χ} = p - 1 := by
  have hfin : Finite V := S.finite_of_finite_line
  have : Finite (Multiplicative V) := hfin
  have hfinC := finite_monoidHom_units (Multiplicative V)
  set T := {χ : Multiplicative V →* ℂˣ // ∀ w ∈ S.offLineSub i, χ w = 1} with hT
  have hcardT : Nat.card T = p := by
    rw [hT, natCard_monoidHom_units_trivialOn, S.index_offLineSub]
  have hone : ∀ w ∈ S.offLineSub i, (1 : Multiplicative V →* ℂˣ) w = 1 := fun _ _ => rfl
  have hequiv : {χ : Multiplicative V →* ℂˣ // S.IsAxisChar i χ}
      ≃ {t : T // t ≠ (⟨1, hone⟩ : T)} :=
    ⟨fun x => ⟨⟨x.1, ((S.isAxisChar_iff).1 x.2).1⟩,
        fun hcon => ((S.isAxisChar_iff).1 x.2).2 (congrArg Subtype.val hcon)⟩,
      fun t => ⟨(t.1 : Multiplicative V →* ℂˣ), (S.isAxisChar_iff).2
        ⟨t.1.2, fun hcon => t.2 (Subtype.ext hcon)⟩⟩, fun _ => rfl, fun _ => rfl⟩
  rw [Nat.card_congr hequiv, CFSG.FeitThompson.natCard_subtype_ne, hcardT]

theorem exists_inl_eq_of_mem_base {x : S.grp} (hx : x ∈ S.base) :
    ∃ v : Multiplicative V, inl v = x := by rw [S.base_eq_range_inl] at hx; exact hx

include S in
theorem natCard_module_eq_pow : Nat.card V = p ^ finrank (ZMod p) V := by
  have h1 : Finite V := S.finite_of_finite_line
  have : Fintype V := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p) (V := V), ZMod.card]

theorem coprime_natCard_base [Finite U] : (Nat.card S.base).Coprime (Nat.card U) := by
  rw [S.natCard_base, S.natCard_module_eq_pow]
  exact Nat.Coprime.pow_left _ S.coprime_card

def complSub : Subgroup S.grp := (inr : U →* S.grp).range

theorem mem_complSub {x : S.grp} : x ∈ S.complSub ↔ ∃ u : U, inr u = x := Iff.rfl

theorem inr_mem_complSub (u : U) : (inr u : S.grp) ∈ S.complSub := ⟨u, rfl⟩

theorem sup_base_complSub : S.base ⊔ S.complSub = ⊤ := by
  rw [S.base_eq_range_inl, complSub]
  exact (isComplement'_range_inl_range_inr S.mulAutHom).sup_eq_top

theorem inf_base_complSub : S.base ⊓ S.complSub = ⊥ := by
  rw [S.base_eq_range_inl, complSub]
  exact (isComplement'_range_inl_range_inr S.mulAutHom).disjoint.eq_bot

theorem natCard_complSub : Nat.card S.complSub = Nat.card U :=
  Nat.card_range_of_injective (inr_injective (φ := S.mulAutHom))

instance complSub_isMulCommutative [IsMulCommutative U] : IsMulCommutative (S.complSub) := by
  refine ⟨⟨?_⟩⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨x, rfl⟩ := (S.mem_complSub).1 ha
  obtain ⟨y, rfl⟩ := (S.mem_complSub).1 hb
  refine Subtype.ext ?_
  change (inr x : S.grp) * inr y = inr y * inr x
  rw [← map_mul, ← map_mul, IsMulCommutative.is_comm.comm]

instance finite_grp [Finite U] : Finite S.grp := by
  have h1 : Finite V := S.finite_of_finite_line
  have h2 : Finite (Multiplicative V) := h1
  exact Finite.of_equiv _ (Equiv.symm (⟨fun x => (x.left, x.right), fun x => ⟨x.1, x.2⟩,
    fun _ => rfl, fun _ => rfl⟩ : S.grp ≃ Multiplicative V × U))

noncomputable instance fintypeGrp [Finite U] : Fintype S.grp := Fintype.ofFinite _

noncomputable instance fintypeBase [Finite U] : Fintype S.base := Fintype.ofFinite _

theorem inf_complSub_inertiaGroup_eq [Finite U] {i : Fin q} {χ : Multiplicative V →* ℂˣ}
    (h : S.IsAxisChar i χ) :
    S.complSub ⊓ inertiaGroup S.base (S.baseChar χ)
      = (S.lineCentralizer i).map (inr : U →* S.grp) := by
  rw [S.inertiaGroup_baseChar h]
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_map]
  constructor
  · intro ⟨h1, h2⟩
    obtain ⟨u, rfl⟩ := (S.mem_complSub).1 h1
    rw [rightHom_eq_right, right_inr] at h2
    exact ⟨u, h2, rfl⟩
  · intro ⟨u, hu, hx⟩
    subst hx
    refine ⟨⟨u, rfl⟩, ?_⟩
    rw [rightHom_eq_right, right_inr]
    exact hu

end ScalarCoordinateSystem

end CFSG.FeitThompson
