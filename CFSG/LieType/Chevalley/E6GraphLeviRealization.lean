module

public import CFSG.LieType.Chevalley.E6GraphLeviIntertwine
public import CFSG.LinearAlgebra.LinearGroups.Generation

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphLevi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LieType.Chevalley.ExteriorCube Matrix
open scoped commutatorElement

variable {E : Type} [Field E]

@[expose] def adjacentSet (E : Type) [Field E] : Set (SpecialLinearGroup (Fin 6) E) :=
  {B | ∃ (t : Fin 5) (c : E), B = SpecialLinearGroup.transvection (castSucc_ne_succ t) c ∨
    B = SpecialLinearGroup.transvection (castSucc_ne_succ t).symm c}

theorem commutator_mem_subgroup' {G : Type*} [Group G] {S : Subgroup G} {a b : G} (ha : a ∈ S)
    (hb : b ∈ S) : ⁅a, b⁆ ∈ S := by
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem adj_up_mem {H : Subgroup (SpecialLinearGroup (Fin 6) E)} (hH : adjacentSet E ⊆ H)
    {a b : Fin 6} (hab : a ≠ b) (hb : b.val = a.val + 1) (c : E) :
    SpecialLinearGroup.transvection hab c ∈ H := by
  obtain ⟨t, rfl, rfl⟩ : ∃ t : Fin 5, t.castSucc = a ∧ t.succ = b :=
    ⟨⟨a.val, by omega⟩, Fin.ext rfl, Fin.ext (by simp [hb])⟩
  exact hH ⟨t, c, Or.inl rfl⟩

theorem adj_down_mem {H : Subgroup (SpecialLinearGroup (Fin 6) E)} (hH : adjacentSet E ⊆ H)
    {a b : Fin 6} (hab : a ≠ b) (ha : a.val = b.val + 1) (c : E) :
    SpecialLinearGroup.transvection hab c ∈ H := by
  obtain ⟨t, rfl, rfl⟩ : ∃ t : Fin 5, t.succ = a ∧ t.castSucc = b :=
    ⟨⟨b.val, by omega⟩, Fin.ext (by simp [ha]), Fin.ext rfl⟩
  exact hH ⟨t, c, Or.inr rfl⟩

theorem upper_mem {H : Subgroup (SpecialLinearGroup (Fin 6) E)} (hH : adjacentSet E ⊆ H) :
    ∀ (d : ℕ) {i j : Fin 6} (hij : i < j), j.val = i.val + d + 1 →
      ∀ c : E, SpecialLinearGroup.transvection hij.ne c ∈ H := by
  intro d
  induction d with
  | zero =>
    intro i j hij hd c
    exact adj_up_mem hH hij.ne (by omega) c
  | succ d ih =>
    intro i j hij hd c
    have hk : i.val + 1 < 6 := by omega
    set k : Fin 6 := ⟨i.val + 1, hk⟩
    have hik : i < k := Fin.lt_def.mpr (by simp [k])
    have hkj : k < j := Fin.lt_def.mpr (by simp [k]; omega)
    have h := Matrix.SpecialLinearGroup.commutatorElement_transvection hik.ne hkj.ne hij.ne c 1
    rw [mul_one] at h
    rw [← h]
    exact commutator_mem_subgroup' (adj_up_mem hH hik.ne (by simp [k]) c)
      (ih hkj (by simp [k]; omega) 1)

theorem lower_mem {H : Subgroup (SpecialLinearGroup (Fin 6) E)} (hH : adjacentSet E ⊆ H) :
    ∀ (d : ℕ) {i j : Fin 6} (hji : j < i), i.val = j.val + d + 1 →
      ∀ c : E, SpecialLinearGroup.transvection hji.ne' c ∈ H := by
  intro d
  induction d with
  | zero =>
    intro i j hji hd c
    exact adj_down_mem hH hji.ne' (by omega) c
  | succ d ih =>
    intro i j hji hd c
    have hk : i.val - 1 < 6 := by omega
    set k : Fin 6 := ⟨i.val - 1, hk⟩
    have hki : k < i := Fin.lt_def.mpr (by simp [k]; omega)
    have hjk : j < k := Fin.lt_def.mpr (by simp [k]; omega)
    have h := Matrix.SpecialLinearGroup.commutatorElement_transvection hki.ne' hjk.ne' hji.ne' c 1
    rw [mul_one] at h
    rw [← h]
    exact commutator_mem_subgroup' (adj_down_mem hH hki.ne' (by simp [k]; omega) c)
      (ih hjk (by simp [k]; omega) 1)

theorem closure_adjacentSet : Subgroup.closure (adjacentSet E) = ⊤ := by
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 6) (K := E),
    Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  have hH := Subgroup.subset_closure (k := adjacentSet E)
  rcases lt_or_gt_of_ne hij with h | h
  · exact upper_mem hH (j.val - i.val - 1) h (by omega) c
  · exact lower_mem hH (i.val - j.val - 1) h (by omega) c

@[expose] def realizeEnd
    (h2 : (2 : E) = 0) :
    SpecialLinearGroup (Fin 6) E →* Module.End E (RootModule TwistTag.E6.tag E) where
  toFun B := fromModel ∘ₗ modelHom B ∘ₗ toModel
  map_one' := by
    refine LinearMap.ext fun v => ?_
    rw [map_one]
    exact fromModel_toModel h2 v
  map_mul' B C := by
    refine LinearMap.ext fun v => ?_
    rw [map_mul]
    simp only [LinearMap.comp_apply, Module.End.mul_apply, toModel_fromModel h2]

@[expose] def realize
    (h2 : (2 : E) = 0) :
    SpecialLinearGroup (Fin 6) E →* ModGL TwistTag.E6.tag E :=
  (realizeEnd h2).toHomUnits

theorem coe_realize
    (h2 : (2 : E) = 0) (B : SpecialLinearGroup (Fin 6) E) :
    (realize h2 B : Module.End E (RootModule TwistTag.E6.tag E)) =
      fromModel ∘ₗ modelLin (B : Matrix (Fin 6) (Fin 6) E)
        ((B⁻¹ : SpecialLinearGroup (Fin 6) E) : Matrix (Fin 6) (Fin 6) E) ∘ₗ toModel :=
  rfl

theorem realize_x
    (h2 : (2 : E) = 0) (t : Fin 5) (c : E) :
    realize h2 (SpecialLinearGroup.transvection (castSucc_ne_succ t) c) =
      xUnit TwistTag.E6.tag E (pathIdx t) c := by
  refine Units.ext ?_
  rw [coe_realize, SpecialLinearGroup.transvection_inv]
  change fromModel ∘ₗ modelLin (xMat t c) (xMat t (-c)) ∘ₗ toModel = xOp TwistTag.E6.tag E _ c
  rw [← toModel_comp_xOp h2, ← LinearMap.comp_assoc]
  refine LinearMap.ext fun v => ?_
  exact fromModel_toModel h2 _

theorem realize_y
    (h2 : (2 : E) = 0) (t : Fin 5) (c : E) :
    realize h2 (SpecialLinearGroup.transvection (castSucc_ne_succ t).symm c) =
      yUnit TwistTag.E6.tag E (pathIdx t) c := by
  refine Units.ext ?_
  rw [coe_realize, SpecialLinearGroup.transvection_inv]
  change fromModel ∘ₗ modelLin (yMat t c) (yMat t (-c)) ∘ₗ toModel = yOp TwistTag.E6.tag E _ c
  rw [← toModel_comp_yOp h2, ← LinearMap.comp_assoc]
  refine LinearMap.ext fun v => ?_
  exact fromModel_toModel h2 _


@[expose] def setA : Set (Fin TwistTag.E6.tag.rank) := {i | i ≠ e6Idx 1}

theorem mem_setA_iff : ∀ i : Fin 6, e6Idx i ∈ setA ↔ ∃ t : Fin 5, pathIdx t = e6Idx i := by
  simp only [setA, Set.mem_ofPred_eq]
  decide

theorem pathIdx_mem_setA (t : Fin 5) : pathIdx t ∈ setA := by
  simp only [setA, Set.mem_ofPred_eq]
  revert t
  decide

theorem range_realize
    (h2 : (2 : E) = 0) :
    (realize h2).range = subsystemGroup TwistTag.E6.tag E setA := by
  rw [MonoidHom.range_eq_map, ← closure_adjacentSet, MonoidHom.map_closure, subsystemGroup]
  congr 1
  ext g
  constructor
  · rintro ⟨B, ⟨t, c, rfl | rfl⟩, rfl⟩
    · exact ⟨pathIdx t, pathIdx_mem_setA t, c, Or.inl (realize_x h2 t c)⟩
    · exact ⟨pathIdx t, pathIdx_mem_setA t, c, Or.inr (realize_y h2 t c)⟩
  · rintro ⟨i, hi, c, rfl | rfl⟩
    · obtain ⟨t, ht⟩ := (mem_setA_iff i).1 hi
      exact ⟨_, ⟨t, c, Or.inl rfl⟩, by rw [realize_x h2, ht]⟩
    · obtain ⟨t, ht⟩ := (mem_setA_iff i).1 hi
      exact ⟨_, ⟨t, c, Or.inr rfl⟩, by rw [realize_y h2, ht]⟩

theorem map_smul_id (l : E) :
    exteriorPower.map 3 (l • (LinearMap.id : (Fin 6 → E) →ₗ[E] (Fin 6 → E))) =
      l ^ 3 • LinearMap.id := by
  refine cubeBasis.ext fun S => ?_
  rw [← wedgeBasis_eq_basis, wedgeBasis, exteriorPower.map_apply_ιMulti_family]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, exteriorPower.ιMulti_family]
  rw [show ((⇑(l • (LinearMap.id : (Fin 6 → E) →ₗ[E] (Fin 6 → E))) ∘
      fun i => (Pi.single i 1 : Fin 6 → E)) ∘ (Set.powersetCard.ofFinEmbEquiv.symm S)) =
      fun x => (fun _ => l) x • ((fun i => (Pi.single i 1 : Fin 6 → E)) ∘
        (Set.powersetCard.ofFinEmbEquiv.symm S)) x from rfl,
    AlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]


theorem realize_eq_one_iff
    (h2 : (2 : E) = 0) (B : SpecialLinearGroup (Fin 6) E) :
    realize h2 B = 1 ↔ modelHom B = 1 := by
  constructor
  · intro h
    have h' : fromModel ∘ₗ modelHom B ∘ₗ toModel =
        (LinearMap.id : RootModule TwistTag.E6.tag E →ₗ[E] _) := congrArg Units.val h
    refine LinearMap.ext fun x => ?_
    have h1 := congrArg toModel (LinearMap.congr_fun h' (fromModel x))
    simp only [LinearMap.comp_apply, LinearMap.id_apply, toModel_fromModel h2] at h1
    exact h1
  · intro h
    refine Units.ext ?_
    change fromModel ∘ₗ modelHom B ∘ₗ toModel = LinearMap.id
    rw [h]
    exact LinearMap.ext (fromModel_toModel h2)

theorem toLin'_scalar (l : E) :
    Matrix.toLin' (Matrix.scalar (Fin 6) l) = l • (LinearMap.id : (Fin 6 → E) →ₗ[E] _) := by
  refine LinearMap.ext fun v => ?_
  funext i
  rw [Matrix.toLin'_apply, Matrix.scalar_apply, Matrix.mulVec_diagonal]
  rfl

theorem pow_three_eq_one_of_pow_six (h2 : (2 : E) = 0) {l : E} (h : l ^ 6 = 1) : l ^ 3 = 1 := by
  have h' : (l ^ 3 - 1) ^ 2 = 0 := by linear_combination h + (1 - l ^ 3) * h2
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h')

theorem mem_ker_realize
    (h2 : (2 : E) = 0) (B : SpecialLinearGroup (Fin 6) E) :
    B ∈ (realize h2).ker ↔ ∃ l : E, l ^ 3 = 1 ∧
      (B : Matrix (Fin 6) (Fin 6) E) = Matrix.scalar (Fin 6) l := by
  rw [MonoidHom.mem_ker, realize_eq_one_iff]
  have hBB : ((B⁻¹ : SpecialLinearGroup (Fin 6) E) : Matrix (Fin 6) (Fin 6) E) *
      (B : Matrix (Fin 6) (Fin 6) E) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hBB' : (B : Matrix (Fin 6) (Fin 6) E) *
      ((B⁻¹ : SpecialLinearGroup (Fin 6) E) : Matrix (Fin 6) (Fin 6) E) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  constructor
  · intro h
    have hcomm : ∀ A : Matrix (Fin 6) (Fin 6) E, (B : Matrix (Fin 6) (Fin 6) E) * A =
        A * (B : Matrix (Fin 6) (Fin 6) E) := by
      intro A
      have h1 := congrArg Prod.fst (LinearMap.congr_fun h ((A, 0, 0, 0, 0) : Model E))
      change (modelLin (B : Matrix (Fin 6) (Fin 6) E) ((B⁻¹ : SpecialLinearGroup (Fin 6) E) :
        Matrix (Fin 6) (Fin 6) E) ((A, 0, 0, 0, 0) : Model E)).1 = A at h1
      rw [modelLin_xMat_mat] at h1
      dsimp only at h1
      calc (B : Matrix (Fin 6) (Fin 6) E) * A =
            (B : Matrix (Fin 6) (Fin 6) E) * A *
              (((B⁻¹ : SpecialLinearGroup (Fin 6) E) : Matrix (Fin 6) (Fin 6) E) *
                (B : Matrix (Fin 6) (Fin 6) E)) := by rw [hBB, Matrix.mul_one]
        _ = A * (B : Matrix (Fin 6) (Fin 6) E) := by rw [← Matrix.mul_assoc, h1]
    obtain ⟨l, hl⟩ := Matrix.mem_range_scalar_of_commute_single
      (n := Fin 6) (M := (B : Matrix (Fin 6) (Fin 6) E)) fun i j _ => (hcomm _).symm
    refine ⟨l, pow_three_eq_one_of_pow_six h2 ?_, hl.symm⟩
    have hdet := B.2
    rw [← hl, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hdet
    exact hdet
  · rintro ⟨l, hl3, hl⟩
    refine LinearMap.ext fun x => ?_
    change modelLin (B : Matrix (Fin 6) (Fin 6) E) ((B⁻¹ : SpecialLinearGroup (Fin 6) E) :
      Matrix (Fin 6) (Fin 6) E) x = x
    rw [modelLin_apply, hl, toLin'_scalar, map_smul_id, hl3, one_smul]
    have hc : Matrix.scalar (Fin 6) l * x.1 = x.1 * Matrix.scalar (Fin 6) l :=
      (Matrix.scalar_commute l (fun r => Commute.all l r) x.1)
    rw [hc, Matrix.mul_assoc, ← hl, hBB', Matrix.mul_one]
    rfl


@[expose] def realizeQuotient
    (h2 : (2 : E) = 0) :
    SpecialLinearGroup (Fin 6) E ⧸ (realize h2).ker ≃* subsystemGroup TwistTag.E6.tag E setA :=
  (QuotientGroup.quotientKerEquivRange (realize h2)).trans
    (MulEquiv.subgroupCongr (range_realize h2))

theorem realizeQuotient_mk
    (h2 : (2 : E) = 0) (B : SpecialLinearGroup (Fin 6) E) :
    (realizeQuotient h2 (QuotientGroup.mk B) : ModGL TwistTag.E6.tag E) = realize h2 B :=
  rfl

variable (E) in
@[expose] def antiId : Matrix (Fin 6) (Fin 6) E :=
  Matrix.of fun i j => if j = Fin.rev i then 1 else 0

theorem antiId_mul_mul_antiId (A : Matrix (Fin 6) (Fin 6) E) :
    antiId E * A * antiId E = A.submatrix Fin.rev Fin.rev := by
  ext i k
  have hk : ∀ j : Fin 6, (k = Fin.rev j) ↔ (j = Fin.rev k) := fun j =>
    ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩
  simp [antiId, Matrix.mul_apply, hk]

theorem antiId_mul_self : antiId E * antiId E = 1 := by
  have h := antiId_mul_mul_antiId (E := E) 1
  rw [Matrix.mul_one] at h
  rw [h]
  ext i k
  simp [Matrix.one_apply, Fin.rev_inj]

theorem det_antiId_sq : (antiId E).det * (antiId E).det = 1 := by
  rw [← Matrix.det_mul, antiId_mul_self, Matrix.det_one]

variable (E) in
@[expose] def graphSL : SpecialLinearGroup (Fin 6) E →* SpecialLinearGroup (Fin 6) E where
  toFun B := ⟨antiId E * ((B⁻¹ : SpecialLinearGroup (Fin 6) E) : Matrix (Fin 6) (Fin 6) E)ᵀ *
    antiId E, by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, (B⁻¹).2, mul_one, det_antiId_sq]⟩
  map_one' := Subtype.ext (by
    change antiId E * (((1 : SpecialLinearGroup (Fin 6) E)⁻¹ : SpecialLinearGroup (Fin 6) E) :
      Matrix (Fin 6) (Fin 6) E)ᵀ * antiId E = 1
    rw [inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.mul_one,
      antiId_mul_self])
  map_mul' B C := Subtype.ext (by
    change antiId E * (((B * C)⁻¹ : SpecialLinearGroup (Fin 6) E) :
      Matrix (Fin 6) (Fin 6) E)ᵀ * antiId E =
      antiId E * ((B⁻¹ : SpecialLinearGroup (Fin 6) E) : Matrix (Fin 6) (Fin 6) E)ᵀ * antiId E *
        (antiId E * ((C⁻¹ : SpecialLinearGroup (Fin 6) E) : Matrix (Fin 6) (Fin 6) E)ᵀ *
          antiId E)
    rw [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (antiId E) (antiId E), antiId_mul_self, Matrix.one_mul])

theorem coe_graphSL (B : SpecialLinearGroup (Fin 6) E) :
    (graphSL E B : Matrix (Fin 6) (Fin 6) E) = antiId E *
      ((B⁻¹ : SpecialLinearGroup (Fin 6) E) : Matrix (Fin 6) (Fin 6) E)ᵀ * antiId E :=
  rfl

theorem graphSL_transvection (h2 : (2 : E) = 0) {i j : Fin 6} (hij : i ≠ j) (c : E) :
    graphSL E (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection (fun h => hij (Fin.rev_injective h).symm) c := by
  apply Subtype.ext
  rw [coe_graphSL, SpecialLinearGroup.transvection_inv]
  change antiId E * (Matrix.transvection i j (-c))ᵀ * antiId E = Matrix.transvection _ _ c
  rw [antiId_mul_mul_antiId]
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.transvection,
    Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  have h1 : (Fin.rev b = Fin.rev a) ↔ (a = b) :=
    ⟨fun h => (Fin.rev_injective h).symm, fun h => h ▸ rfl⟩
  have h2' : (i = Fin.rev b ∧ j = Fin.rev a) ↔ (Fin.rev j = a ∧ Fin.rev i = b) := by
    constructor <;> rintro ⟨h₁, h₂⟩ <;> subst h₁ h₂ <;> simp
  simp only [h1, h2']
  split_ifs <;> simp [neg_eq_self_of_two h2]

theorem perm_pathIdx : ∀ t : Fin 5, TwistTag.E6.perm (pathIdx t) = pathIdx (Fin.rev t) := by
  decide

theorem diagramMap_conj_realize
    (h2 : (2 : E) = 0) (B : SpecialLinearGroup (Fin 6) E) :
    diagramMap TwistTag.E6 E * realize h2 B * (diagramMap TwistTag.E6 E)⁻¹ =
      realize h2 (graphSL E B) := by
  have h := MonoidHom.eq_of_eqOn_dense (closure_adjacentSet (E := E))
    (f := (MulAut.conj (diagramMap TwistTag.E6 E)).toMonoidHom.comp (realize h2))
    (g := (realize h2).comp (graphSL E)) (by
      rintro _ ⟨t, c, rfl | rfl⟩
      · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [realize_x h2, diagramMap_mul_xUnit_mul_inv, graphSL_transvection h2, perm_pathIdx]
        have e : SpecialLinearGroup.transvection
            (fun h => (castSucc_ne_succ t) (Fin.rev_injective h).symm) c =
            SpecialLinearGroup.transvection (castSucc_ne_succ (Fin.rev t)) c := by
          congr 1 <;> simp [Fin.rev_castSucc, Fin.rev_succ]
        rw [e, realize_x h2]
      · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [realize_y h2, diagramMap_mul_yUnit_mul_inv, graphSL_transvection h2, perm_pathIdx]
        have e : SpecialLinearGroup.transvection
            (fun h => (castSucc_ne_succ t).symm (Fin.rev_injective h).symm) c =
            SpecialLinearGroup.transvection (castSucc_ne_succ (Fin.rev t)).symm c := by
          congr 1 <;> simp [Fin.rev_castSucc, Fin.rev_succ]
        rw [e, realize_y h2])
  exact DFunLike.congr_fun h B


theorem two_eq_zero_of_ringHom {E' : Type} [Field E'] (f : E →+* E') (h2 : (2 : E) = 0) :
    (2 : E') = 0 := by
  rw [← map_ofNat f 2, h2, map_zero]

theorem map_transvection {E' : Type} [Field E'] (f : E →+* E') {i j : Fin 6} (hij : i ≠ j)
    (c : E) : Matrix.SpecialLinearGroup.map f (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection hij (f c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  change (Matrix.transvection i j c).map f = Matrix.transvection i j (f c)
  rw [Matrix.transvection, Matrix.transvection, Matrix.map_add _ (map_add f),
    Matrix.map_one (⇑f) f.map_zero f.map_one, Matrix.map_single]

theorem baseChangeGL_realize
    {E' : Type} [Field E'] (f : E →+* E') (h2 : (2 : E) = 0)
    (B : SpecialLinearGroup (Fin 6) E) :
    baseChangeGL f (realize h2 B) =
      realize (two_eq_zero_of_ringHom f h2) (Matrix.SpecialLinearGroup.map f B) := by
  have h := MonoidHom.eq_of_eqOn_dense (closure_adjacentSet (E := E))
    (f := (baseChangeGL (τ := TwistTag.E6.tag) f).comp (realize h2))
    (g := (realize (two_eq_zero_of_ringHom f h2)).comp (Matrix.SpecialLinearGroup.map f)) (by
      rintro _ ⟨t, c, rfl | rfl⟩
      · simp only [MonoidHom.comp_apply]
        rw [realize_x h2, baseChangeGL_xUnit, map_transvection, realize_x]
      · simp only [MonoidHom.comp_apply]
        rw [realize_y h2, baseChangeGL_yUnit, map_transvection, realize_y])
  exact DFunLike.congr_fun h B

theorem commutator_pinnedX_of_two
    (h2 : (2 : E) = 0) {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α) (hβ : IsRoot TwistTag.E6.tag β) (hne : α ≠ β)
    (hne' : α ≠ -β) (hab : IsRoot TwistTag.E6.tag (α + β)) (c d : E) :
    ⁅pinnedX TwistTag.E6.tag E α c, pinnedX TwistTag.E6.tag E β d⁆ =
      pinnedX TwistTag.E6.tag E (α + β) (c * d) := by
  obtain ⟨h, -⟩ := simply_laced_root_commutator_unit TwistTag.E6.tag (Or.inr (Or.inl rfl)) hα hβ
    hne hne'
  obtain ⟨hε, hc⟩ := h hab
  rw [hc E c d]
  congr 1
  rcases hε with hε | hε <;> rw [hε]
  · simp
  · rw [Int.cast_neg, Int.cast_one, neg_eq_self_of_two h2, one_mul]

@[expose] def pathSum (k : Fin 5) : Fin TwistTag.E6.tag.rank → ℤ :=
  ∑ t ∈ Finset.Iic k, Pi.single (pathIdx t) 1

theorem pathSum_facts : ∀ k : Fin 4,
    pathSum k.castSucc ∈ rootFinset TwistTag.E6.tag ∧
      Pi.single (pathIdx k.succ) 1 ∈ rootFinset TwistTag.E6.tag ∧
      pathSum k.castSucc ≠ Pi.single (pathIdx k.succ) 1 ∧
      pathSum k.castSucc ≠ -Pi.single (pathIdx k.succ) 1 ∧
      pathSum k.castSucc + Pi.single (pathIdx k.succ) 1 = pathSum k.succ ∧
      pathSum k.succ ∈ rootFinset TwistTag.E6.tag := by
  decide +kernel

theorem pathSum_zero : pathSum 0 = Pi.single (pathIdx 0) 1 := by decide

theorem pathSum_last : pathSum 4 = sRoot := by decide

theorem realize_upper
    (h2 : (2 : E) = 0) (c : E) : ∀ k : Fin 5,
    realize h2 (SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ k.succ from
      (Fin.succ_ne_zero k).symm) c) = pinnedX TwistTag.E6.tag E (pathSum k) c := by
  intro k
  induction k using Fin.induction with
  | zero =>
    rw [pathSum_zero, pinnedX_single]
    exact realize_x h2 0 c
  | succ k ih =>
    obtain ⟨h1, h2', h3, h4, h5, h6⟩ := pathSum_facts k
    have h01 : (0 : Fin 6) ≠ k.succ.castSucc := (Fin.succ_ne_zero k.castSucc).symm
    have h02 : (0 : Fin 6) ≠ k.succ.succ := (Fin.succ_ne_zero k.succ).symm
    have hcomm : ⁅SpecialLinearGroup.transvection h01 c,
        SpecialLinearGroup.transvection (castSucc_ne_succ k.succ) (1 : E)⁆ =
          SpecialLinearGroup.transvection h02 c := by
      have := Matrix.SpecialLinearGroup.commutatorElement_transvection h01
        (castSucc_ne_succ k.succ) h02 c (1 : E)
      rwa [mul_one] at this
    have hih : realize h2 (SpecialLinearGroup.transvection h01 c) =
        pinnedX TwistTag.E6.tag E (pathSum k.castSucc) c := ih
    calc realize h2 (SpecialLinearGroup.transvection h02 c)
        = ⁅realize h2 (SpecialLinearGroup.transvection h01 c),
            realize h2 (SpecialLinearGroup.transvection (castSucc_ne_succ k.succ) 1)⁆ := by
          rw [← map_commutatorElement, hcomm]
      _ = ⁅pinnedX TwistTag.E6.tag E (pathSum k.castSucc) c,
            pinnedX TwistTag.E6.tag E (Pi.single (pathIdx k.succ) 1) 1⁆ := by
          rw [hih, realize_x h2, pinnedX_single]
      _ = pinnedX TwistTag.E6.tag E (pathSum k.succ) c := by
          rw [commutator_pinnedX_of_two h2 (mem_rootFinset.1 h1) (mem_rootFinset.1 h2') h3 h4
            (by rw [h5]; exact mem_rootFinset.1 h6), h5, mul_one]

theorem realize_transvection_zero_five
    (h2 : (2 : E) = 0) (c : E) :
    realize h2 (SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 5 by decide) c) =
      pinnedX TwistTag.E6.tag E sRoot c := by
  rw [← pathSum_last]
  exact realize_upper h2 c 4


theorem cubeRoot_weight : ∀ S : Finset (Fin 6), S.card = 3 → ∀ i : Fin 5,
    CFSG.LieType.Steinberg.Adjoint.iform (Pi.single (pathIdx i) 1) (cubeRoot S) =
      (if i.castSucc ∈ S then 1 else 0) - (if i.succ ∈ S then 1 else 0) := by
  decide +kernel

theorem negCube_weight : ∀ S : Finset (Fin 6), S.card = 3 → ∀ i : Fin 5,
    CFSG.LieType.Steinberg.Adjoint.iform (Pi.single (pathIdx i) 1) (-cubeRoot Sᶜ) =
      (if i.castSucc ∈ S then 1 else 0) - (if i.succ ∈ S then 1 else 0) := by
  decide +kernel

theorem hImage_two : hImage (E := E) (e6Idx 1) =
    (Matrix.single 3 3 1 + Matrix.single 4 4 1 + Matrix.single 5 5 1, 0, 0, 0, 0) := by
  have h : (fun i => (diagCoeff (e6Idx 1) i : E)) =
      Pi.single 3 1 + Pi.single 4 1 + Pi.single 5 1 := by
    funext i
    fin_cases i <;> simp [diagCoeff]
  rw [hImage, h, show (Pi.single 3 1 + Pi.single 4 1 + Pi.single 5 1 : Fin 6 → E) =
    fun i => Pi.single (3 : Fin 6) (1 : E) i + Pi.single 4 1 i + Pi.single 5 1 i from rfl,
    ← Matrix.diagonal_add, ← Matrix.diagonal_add, Matrix.diagonal_single, Matrix.diagonal_single,
    Matrix.diagonal_single]

theorem _root_.CFSG.LieType.Chevalley.even_E6_graph_A5_polynomial_Levi_realization
    (E : Type) [Field E] (hE : ringChar E = 2) :
    (∀ t : Fin 5, modelEquiv (two_eq_zero_of_ringChar hE) (hVec TwistTag.E6.tag E (pathIdx t)) =
      (Matrix.single t.castSucc t.castSucc 1 + Matrix.single t.succ t.succ 1, 0, 0, 0, 0)) ∧
    modelEquiv (two_eq_zero_of_ringChar hE) (hVec TwistTag.E6.tag E (e6Idx 1)) =
      (Matrix.single 3 3 1 + Matrix.single 4 4 1 + Matrix.single 5 5 1, 0, 0, 0, 0) ∧
    (∀ β, IsRoot TwistTag.E6.tag β →
      modelEquiv (two_eq_zero_of_ringChar hE) (rootVec TwistTag.E6.tag E β) = rootImage β) ∧
    (∀ β ∈ rootFinset TwistTag.E6.tag, (∃ a b : Fin 6, a ≠ b ∧ matRoot a b = β) ∨
      β = e6HighestRoot ∨ β = -e6HighestRoot ∨
      (∃ S : Finset (Fin 6), S.card = 3 ∧ cubeRoot S = β) ∨
      ∃ S : Finset (Fin 6), S.card = 3 ∧ -cubeRoot Sᶜ = β) ∧
    (∀ a b : Fin 6, a ≠ b → rootImage (E := E) (matRoot a b) = (Matrix.single a b 1, 0, 0, 0, 0)) ∧
    rootImage (E := E) e6HighestRoot = (0, 1, 0, 0, 0) ∧
    rootImage (E := E) (-e6HighestRoot) = (0, 0, 1, 0, 0) ∧
    (∀ S : Set.powersetCard (Fin 6) 3,
      rootImage (E := E) (cubeRoot S.1) = (0, 0, 0, cubeBasis S, 0)) ∧
    (∀ S : Set.powersetCard (Fin 6) 3,
      rootImage (E := E) (-cubeRoot S.1ᶜ) = (0, 0, 0, 0, cubeBasis S)) ∧
    (∀ S : Finset (Fin 6), S.card = 3 → ∀ i : Fin 5,
      CFSG.LieType.Steinberg.Adjoint.iform (Pi.single (pathIdx i) 1) (cubeRoot S) =
        (if i.castSucc ∈ S then 1 else 0) - (if i.succ ∈ S then 1 else 0) ∧
      CFSG.LieType.Steinberg.Adjoint.iform (Pi.single (pathIdx i) 1) (-cubeRoot Sᶜ) =
        (if i.castSucc ∈ S then 1 else 0) - (if i.succ ∈ S then 1 else 0)) ∧
    (∀ (B : SpecialLinearGroup (Fin 6) E) (x : Model E), modelHom B x =
      ((B : Matrix (Fin 6) (Fin 6) E) * x.1 *
          ((B⁻¹ : SpecialLinearGroup (Fin 6) E) : Matrix (Fin 6) (Fin 6) E), x.2.1, x.2.2.1,
        exteriorPower.map 3 (Matrix.toLin' (B : Matrix (Fin 6) (Fin 6) E)) x.2.2.2.1,
        exteriorPower.map 3 (Matrix.toLin' (B : Matrix (Fin 6) (Fin 6) E)) x.2.2.2.2)) ∧
    (∀ B : SpecialLinearGroup (Fin 6) E,
      (realize (two_eq_zero_of_ringChar hE) B : Module.End E (RootModule TwistTag.E6.tag E)) =
        (modelEquiv (two_eq_zero_of_ringChar hE)).symm.toLinearMap ∘ₗ modelHom B ∘ₗ
          (modelEquiv (two_eq_zero_of_ringChar hE)).toLinearMap) ∧
    (∀ (t : Fin 5) (c : E), realize (two_eq_zero_of_ringChar hE)
      (SpecialLinearGroup.transvection (castSucc_ne_succ t) c) =
        xUnit TwistTag.E6.tag E (pathIdx t) c) ∧
    (∀ (t : Fin 5) (c : E), realize (two_eq_zero_of_ringChar hE)
      (SpecialLinearGroup.transvection (castSucc_ne_succ t).symm c) =
        yUnit TwistTag.E6.tag E (pathIdx t) c) ∧
    (realize (two_eq_zero_of_ringChar hE)).range = subsystemGroup TwistTag.E6.tag E setA ∧
    (∀ B : SpecialLinearGroup (Fin 6) E, B ∈ (realize (two_eq_zero_of_ringChar hE)).ker ↔
      ∃ l : E, l ^ 3 = 1 ∧ (B : Matrix (Fin 6) (Fin 6) E) = Matrix.scalar (Fin 6) l) ∧
    (∀ B : SpecialLinearGroup (Fin 6) E,
      (realizeQuotient (two_eq_zero_of_ringChar hE) (QuotientGroup.mk B) :
        ModGL TwistTag.E6.tag E) = realize (two_eq_zero_of_ringChar hE) B) ∧
    (∀ B : SpecialLinearGroup (Fin 6) E, diagramMap TwistTag.E6 E *
      realize (two_eq_zero_of_ringChar hE) B * (diagramMap TwistTag.E6 E)⁻¹ =
        realize (two_eq_zero_of_ringChar hE) (graphSL E B)) ∧
    (∀ B : SpecialLinearGroup (Fin 6) E, (graphSL E B : Matrix (Fin 6) (Fin 6) E) =
      antiId E * ((B⁻¹ : SpecialLinearGroup (Fin 6) E) : Matrix (Fin 6) (Fin 6) E)ᵀ *
        antiId E) ∧
    (∀ i j : Fin 6, antiId E i j = if j = Fin.rev i then 1 else 0) ∧
    (∀ (E' : Type) [Field E'] (f : E →+* E') (B : SpecialLinearGroup (Fin 6) E),
      baseChangeGL f (realize (two_eq_zero_of_ringChar hE) B) =
        realize (two_eq_zero_of_ringHom f (two_eq_zero_of_ringChar hE))
          (Matrix.SpecialLinearGroup.map f B)) ∧
    ∀ c : E, realize (two_eq_zero_of_ringChar hE)
      (SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 5 by decide) c) =
        pinnedX TwistTag.E6.tag E sRoot c := by
  have h2 : (2 : E) = 0 := two_eq_zero_of_ringChar hE
  refine ⟨fun t => ?_, ?_, fun β hβ => toModel_rootVec β, root_cases, fun a b hab =>
    rootImage_matRoot hab, rootImage_e6HighestRoot, rootImage_neg_e6HighestRoot,
    rootImage_cubeRoot, rootImage_neg_cubeRoot,
    fun S hS i => ⟨cubeRoot_weight S hS i, negCube_weight S hS i⟩, fun B x => modelLin_apply _ _ x,
    fun B => rfl, realize_x h2, realize_y h2, range_realize h2, mem_ker_realize h2,
    realizeQuotient_mk h2, diagramMap_conj_realize h2, coe_graphSL, fun i j => rfl,
    fun E' _ f B => baseChangeGL_realize f h2 B, realize_transvection_zero_five h2⟩
  · change toModel (hVec TwistTag.E6.tag E (pathIdx t)) = _
    rw [toModel_hVec, hImage, diagonal_coeff_path]
  · change toModel (hVec TwistTag.E6.tag E (e6Idx 1)) = _
    rw [toModel_hVec, hImage_two]

end CFSG.LieType.Chevalley.E6GraphLevi
