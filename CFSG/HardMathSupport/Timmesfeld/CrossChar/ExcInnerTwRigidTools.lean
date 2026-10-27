module

public import CFSG.LieType.Chevalley.LangFiniteRootCentralizer
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.Chevalley.G2SplitPrimeToralCentralizers
public import CFSG.RankThree.Classical.SL2SemilinearRoots

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical CFSG.RankThree.Chevalley Polynomial
open scoped MatrixGroups

variable {τ : Tag} {L : Type} [Field L]

theorem apply_coord_of_diag {D : Module.End L (RootModule τ L)} {μ : Label τ → L}
    (hD : ∀ b, D (Finsupp.single b 1) = μ b • Finsupp.single b 1) (x : RootModule τ L)
    (b : Label τ) : D x b = μ b * x b := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply, mul_add]
  | single c r =>
    rw [← Finsupp.smul_single_one, map_smul, hD, smul_smul, Finsupp.smul_apply,
      Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, Finsupp.single_apply]
    split_ifs with hcb
    · subst hcb
      ring
    · simp

theorem exists_label_of_conj_diag {ι : Type*} (z : (Module.End L (RootModule τ L))ˣ)
    (D D' : ι → Module.End L (RootModule τ L)) (μ μ' : ι → Label τ → L)
    (hD : ∀ t b, D t (Finsupp.single b 1) = μ t b • Finsupp.single b 1)
    (hD' : ∀ t b, D' t (Finsupp.single b 1) = μ' t b • Finsupp.single b 1)
    (hz : ∀ t, (z : Module.End L (RootModule τ L)) * D' t = D t * z) (α : Label τ) :
    ∃ b, ∀ t, μ t b = μ' t α := by
  classical
  set v : RootModule τ L := (z : Module.End L (RootModule τ L)) (Finsupp.single α 1) with hv
  have hv0 : v ≠ 0 := by
    intro h0
    have h1 : ((z⁻¹ : (Module.End L (RootModule τ L))ˣ) : Module.End L (RootModule τ L)) v =
        Finsupp.single α 1 := by
      rw [hv, ← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
    rw [h0, map_zero] at h1
    exact one_ne_zero (Finsupp.single_eq_zero.1 h1.symm)
  obtain ⟨b, hb⟩ : ∃ b, v b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv0 (Finsupp.ext hcon)
  refine ⟨b, fun t => ?_⟩
  have h1 : D t v = μ' t α • v := by
    have h2 := congrArg (fun f : Module.End L (RootModule τ L) => f (Finsupp.single α 1)) (hz t)
    simp only [Module.End.mul_apply, hD', map_smul] at h2
    rw [hv, ← h2]
  have h3 := congrArg (fun w : RootModule τ L => w b) h1
  simp only [apply_coord_of_diag (hD t), Finsupp.smul_apply, smul_eq_mul] at h3
  exact mul_right_cancel₀ hb h3

theorem units_map_rootChar (σ : L →+* L) (a : Fin τ.rank → Lˣ) (v : Fin τ.rank → ℤ) :
    Units.map σ.toMonoidHom (rootChar a v) =
      rootChar (fun i => Units.map σ.toMonoidHom (a i)) v := by
  simp [rootChar, map_prod, map_zpow]

theorem entrywise_rootDiag (σ : L →+* L) (a : Fin τ.rank → Lˣ) :
    entrywise σ (rootDiag a : Module.End L (RootModule τ L)) =
      rootDiag fun i => Units.map σ.toMonoidHom (a i) := by
  refine end_ext_single fun b => ?_
  rw [entrywise_single, rootDiag_single, rootDiag_single, Finsupp.smul_single_one,
    Finsupp.mapRange_single, Finsupp.smul_single_one, ← units_map_rootChar]
  rfl

theorem units_map_entrywiseHom_rootDiagUnit (σ : L →+* L) (a : Fin τ.rank → Lˣ) :
    Units.map (entrywiseHom σ) (rootDiagUnit τ a) =
      rootDiagUnit τ fun i => Units.map σ.toMonoidHom (a i) :=
  Units.ext (entrywise_rootDiag σ a)

theorem exists_label_of_conj_rootDiagUnit {ι : Type*} (z : ModGL τ L)
    (a a' : ι → Fin τ.rank → Lˣ)
    (hz : ∀ t, z * rootDiagUnit τ (a' t) * z⁻¹ = rootDiagUnit τ (a t)) (α : Label τ) :
    ∃ b, ∀ t, rootChar (a t) (labelWt τ b) = rootChar (a' t) (labelWt τ α) := by
  obtain ⟨b, hb⟩ := exists_label_of_conj_diag z (fun t => rootDiag (a t))
    (fun t => rootDiag (a' t)) (fun t b => (rootChar (a t) (labelWt τ b) : L))
    (fun t b => (rootChar (a' t) (labelWt τ b) : L)) (fun t b => rootDiag_single (a t) b)
    (fun t b => rootDiag_single (a' t) b) (fun t => by
      have h : z * rootDiagUnit τ (a' t) = rootDiagUnit τ (a t) * z := by
        rw [← hz t]
        group
      exact congrArg Units.val h) α
  exact ⟨b, fun t => Units.ext (hb t)⟩

theorem exists_label_of_conj_entrywise_rootDiagUnit {ι : Type*} (σ : L →+* L) (z : ModGL τ L)
    (a : ι → Fin τ.rank → Lˣ)
    (hz : ∀ t, z * Units.map (entrywiseHom σ) (rootDiagUnit τ (a t)) * z⁻¹ =
      rootDiagUnit τ (a t)) (α : Label τ) :
    ∃ b, ∀ t, rootChar (a t) (labelWt τ b) =
      Units.map σ.toMonoidHom (rootChar (a t) (labelWt τ α)) := by
  simp only [units_map_entrywiseHom_rootDiagUnit] at hz
  obtain ⟨b, hb⟩ := exists_label_of_conj_rootDiagUnit z a _ hz α
  exact ⟨b, fun t => (hb t).trans (units_map_rootChar σ (a t) _).symm⟩

theorem entrywise_torusElt'
    (σ : L →+* L) (i : Fin τ.rank) (t : Lˣ) :
    entrywise σ (torusElt τ L i t : Module.End L (RootModule τ L)) =
      (torusElt τ L i (Units.map σ.toMonoidHom t) : Module.End L (RootModule τ L)) := by
  refine end_ext_single fun b => ?_
  rw [entrywise_single, torusElt_single_eq, torusElt_single_eq, Finsupp.smul_single_one,
    Finsupp.mapRange_single, Finsupp.smul_single_one, ← map_zpow]
  rfl

theorem units_map_entrywiseHom_torusElt
    (σ : L →+* L) (i : Fin τ.rank) (t : Lˣ) :
    Units.map (entrywiseHom σ) (torusElt τ L i t) = torusElt τ L i (Units.map σ.toMonoidHom t) :=
  Units.ext (entrywise_torusElt' σ i t)

theorem exists_label_of_conj_torusElt
    (z : ModGL τ L) (ζ ζ' : Lˣ) (hz : ∀ i, z * torusElt τ L i ζ' * z⁻¹ = torusElt τ L i ζ)
    (α : Label τ) :
    ∃ b : Label τ, ∀ i, ζ ^ (∑ j, τ.cartan i j * b.latticeWeight j) =
      ζ' ^ (∑ j, τ.cartan i j * α.latticeWeight j) := by
  obtain ⟨b, hb⟩ := exists_label_of_conj_diag z (fun i => (torusElt τ L i ζ : Module.End L _))
    (fun i => (torusElt τ L i ζ' : Module.End L _))
    (fun i b => ((ζ ^ (∑ j, τ.cartan i j * b.latticeWeight j) : Lˣ) : L))
    (fun i b => ((ζ' ^ (∑ j, τ.cartan i j * b.latticeWeight j) : Lˣ) : L))
    (fun i b => torusElt_single_eq i ζ b) (fun i b => torusElt_single_eq i ζ' b) (fun i => by
      have h : z * torusElt τ L i ζ' = torusElt τ L i ζ * z := by
        rw [← hz i]
        group
      exact congrArg Units.val h) α
  exact ⟨b, fun i => Units.ext (hb i)⟩

theorem rootSL2_single
    (i : Fin τ.rank) :
    rootSL2 τ L (Pi.single i 1) = simpleRootSL2 τ L i := by
  ext A : 1
  simp [rootSL2, pinnedWeyl, pinnedData_single]

theorem exists_sl2_conjSL [IsAlgClosed L] (P : GL (Fin 2) L) :
    ∃ P' : SL2 L, ∀ B : SL2 L, conjSL P B = P' * B * P'⁻¹ := by
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq ((P : Matrix (Fin 2) (Fin 2) L).det) two_pos
  have hdet : (P : Matrix (Fin 2) (Fin 2) L).det ≠ 0 :=
    Matrix.det_ne_zero_of_right_inverse (B := ((P⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L))
      (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hμ
    exact hdet hμ.symm
  have hdet' : (μ⁻¹ • (P : Matrix (Fin 2) (Fin 2) L)).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, inv_pow, ← hμ, inv_mul_cancel₀ (pow_ne_zero 2 hμ0)]
  set P' : SL2 L := ⟨μ⁻¹ • (P : Matrix (Fin 2) (Fin 2) L), hdet'⟩ with hP'
  have hP'v : (P' : Matrix (Fin 2) (Fin 2) L) = μ⁻¹ • (P : Matrix (Fin 2) (Fin 2) L) := rfl
  have h1 : (P' : Matrix (Fin 2) (Fin 2) L) *
      (μ • ((P⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)) = 1 := by
    rw [hP'v, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hμ0, one_smul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ((P'⁻¹ : SL2 L) : Matrix (Fin 2) (Fin 2) L) * (P' : Matrix (Fin 2) (Fin 2) L) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hinv : ((P'⁻¹ : SL2 L) : Matrix (Fin 2) (Fin 2) L) =
      μ • ((P⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
    calc ((P'⁻¹ : SL2 L) : Matrix (Fin 2) (Fin 2) L) =
        ((P'⁻¹ : SL2 L) : Matrix (Fin 2) (Fin 2) L) * ((P' : Matrix (Fin 2) (Fin 2) L) *
          (μ • ((P⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L))) := by rw [h1, Matrix.mul_one]
      _ = μ • ((P⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
        rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  refine ⟨P', fun B => Subtype.ext ?_⟩
  change (P : Matrix (Fin 2) (Fin 2) L) * (B : Matrix (Fin 2) (Fin 2) L) *
      ((P⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
    ((P' * B * P'⁻¹ : SL2 L) : Matrix (Fin 2) (Fin 2) L)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv, hP'v,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hμ0, one_smul]

theorem commute_conj_iff {G : Type*} [Group G] (z g x : G) :
    Commute z (g * x * g⁻¹) ↔ Commute (g⁻¹ * z * g) x := by
  simp only [Commute, SemiconjBy]
  constructor <;> intro h
  · calc g⁻¹ * z * g * x = g⁻¹ * (z * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * z) * g := by rw [h]
      _ = x * (g⁻¹ * z * g) := by group
  · calc z * (g * x * g⁻¹) = g * ((g⁻¹ * z * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * z * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * z := by group

theorem sl2_map_uSL {K₀ : Type} [Field K₀] (ι : K₀ →+* L) (c : K₀) :
    Matrix.SpecialLinearGroup.map ι (uSL c) = uSL (ι c) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL, RingHom.mapMatrix_apply]

theorem sl2_map_vSL {K₀ : Type} [Field K₀] (ι : K₀ →+* L) (c : K₀) :
    Matrix.SpecialLinearGroup.map ι (vSL c) = vSL (ι c) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vSL, RingHom.mapMatrix_apply]


theorem commute_rootRankOneGroup_of_twisted [IsAlgClosed L] {K₀ : Type} [Field K₀] [Fintype K₀]
    (ι : K₀ →+* L) (hcard : entryDegreeBound τ < Fintype.card K₀) (β : Fin τ.rank → ℤ)
    (P : GL (Fin 2) L) {z : ModGL τ L}
    (hz : ∀ A : SL2 K₀,
      Commute z (rootSL2 τ L β (conjSL P (Matrix.SpecialLinearGroup.map ι A)))) :
    ∀ x ∈ rootRankOneGroup τ L β, Commute z x := by
  obtain ⟨P', hP'⟩ := exists_sl2_conjSL P
  obtain ⟨j, hj⟩ : ∃ j, j = (pinnedData τ β).1 := ⟨_, rfl⟩
  have hρ0 : ∀ B : SL2 L, rootSL2 τ L β B =
      pinnedWeyl τ L β * simpleRootSL2 τ L j B * (pinnedWeyl τ L β)⁻¹ := fun B => by
    rw [hj]
    rfl
  set g : ModGL τ L := pinnedWeyl τ L β * simpleRootSL2 τ L j P' with hg
  have hρ : ∀ B : SL2 L, rootSL2 τ L β (conjSL P B) = g * simpleRootSL2 τ L j B * g⁻¹ := by
    intro B
    rw [hP' B, hρ0, map_mul, map_mul, map_inv, hg]
    group
  set y : ModGL τ L := g⁻¹ * z * g with hy
  have hcomm : ∀ B : SL2 K₀,
      Commute y (simpleRootSL2 τ L j (Matrix.SpecialLinearGroup.map ι B)) := fun B =>
    (commute_conj_iff z g _).1 (by rw [← hρ]; exact hz B)
  have hx : ∀ t : L, (y : Module.End L (RootModule τ L)) * xOp τ L j t =
      xOp τ L j t * (y : Module.End L (RootModule τ L)) := by
    intro t
    refine commute_of_polynomial_entries (F := xOp τ L j) (fun a b => ?_) _ ι ι.injective hcard
      (fun c => ?_) t
    · obtain ⟨p, q, hp, -, hpq⟩ := exists_entry_polynomial (R := L) τ j a b
      exact ⟨p, hp, fun c => (hpq c).1⟩
    · have h := congrArg Units.val (hcomm (uSL c)).eq
      rwa [sl2_map_uSL, simpleRootSL2_uSL, Units.val_mul, Units.val_mul, coe_xUnit] at h
  have hy' : ∀ t : L, (y : Module.End L (RootModule τ L)) * yOp τ L j t =
      yOp τ L j t * (y : Module.End L (RootModule τ L)) := by
    intro t
    refine commute_of_polynomial_entries (F := yOp τ L j) (fun a b => ?_) _ ι ι.injective hcard
      (fun c => ?_) t
    · obtain ⟨p, q, -, hq, hpq⟩ := exists_entry_polynomial (R := L) τ j a b
      exact ⟨q, hq, fun c => (hpq c).2⟩
    · have h := congrArg Units.val (hcomm (vSL c)).eq
      rwa [sl2_map_vSL, simpleRootSL2_vSL, Units.val_mul, Units.val_mul, coe_yUnit] at h
  have hall : ∀ B : SL2 L, Commute y (simpleRootSL2 τ L j B) := by
    intro B
    have hB : B ∈ Subgroup.closure (Set.range (sl2Upper L) ∪ Set.range (sl2Lower L)) := by
      rw [sl2_closure_upper_lower]
      exact Subgroup.mem_top B
    induction hB using Subgroup.closure_induction with
    | mem B hB =>
      rcases hB with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · change Commute y (simpleRootSL2 τ L j (uSL t))
        rw [simpleRootSL2_uSL]
        exact Units.ext (by rw [Units.val_mul, Units.val_mul, coe_xUnit]; exact hx t)
      · change Commute y (simpleRootSL2 τ L j (vSL t))
        rw [simpleRootSL2_vSL]
        exact Units.ext (by rw [Units.val_mul, Units.val_mul, coe_yUnit]; exact hy' t)
    | one => rw [map_one]; exact Commute.one_right y
    | mul B C _ _ hB hC => rw [map_mul]; exact hB.mul_right hC
    | inv B _ hB => rw [map_inv]; exact hB.inv_right
  rintro _ ⟨A, rfl⟩
  have hA : rootSL2 τ L β A = g * simpleRootSL2 τ L j (conjSL P⁻¹ A) * g⁻¹ := by
    rw [← hρ, ← conjSL_mul, mul_inv_cancel, conjSL_one]
  rw [hA]
  exact (commute_conj_iff z g _).2 (hall _)

theorem eq_one_of_commute_rootRankOneGroup_simple {z : ModGL τ L} (hzC : z ∈ adjointGroup τ L)
    (h : ∀ i : Fin τ.rank, ∀ x ∈ rootRankOneGroup τ L (Pi.single i 1), Commute z x) : z = 1 := by
  have hxy : ∀ (i : Fin τ.rank) (c : L),
      Commute z (xUnit τ L i c) ∧ Commute z (yUnit τ L i c) := fun i c =>
    ⟨h i _ ⟨uSL c, by rw [rootSL2_single, simpleRootSL2_uSL]⟩,
      h i _ ⟨vSL c, by rw [rootSL2_single, simpleRootSL2_vSL]⟩⟩
  have hle : adjointGroup τ L ≤ Subgroup.centralizer {z} := by
    rw [adjointGroup, Subgroup.closure_le]
    rintro g ⟨i, c, hg | hg⟩
    · have hgx : g = xUnit τ L i c := Units.ext (hg.trans (coe_xUnit i c).symm)
      rw [hgx]
      exact Subgroup.mem_centralizer_singleton_iff.2 (hxy i c).1.symm.eq
    · have hgy : g = yUnit τ L i c := Units.ext (hg.trans (coe_yUnit i c).symm)
      rw [hgy]
      exact Subgroup.mem_centralizer_singleton_iff.2 (hxy i c).2.symm.eq
  have hcent : (⟨z, hzC⟩ : adjointGroup τ L) ∈ Subgroup.center (adjointGroup τ L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hle g.2))
  rw [center_adjointGroup_eq_bot_field, Subgroup.mem_bot] at hcent
  exact congrArg Subtype.val hcent

end CFSG.HardMathSupport.Timmesfeld.CrossChar
