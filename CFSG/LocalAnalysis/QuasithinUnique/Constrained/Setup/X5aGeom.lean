module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineHexagon

public section

namespace CFSG.QuasithinUnique.Setup.X5

open Matrix CFSG.LinearGroups.UnitaryThreeOverNine CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

@[expose] def coordVec : Fin 3 → (Fin 3 → F) := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]

theorem coordVec_ne_zero (j : Fin 3) : (coordVec j : Fin 3 → F) ≠ 0 := by
  intro h
  have := congrFun h j
  fin_cases j <;> simp [coordVec] at this

theorem gramForm_coordVec_self (h : UnitaryFieldData 3 1 F) (j : Fin 3) :
    gramForm h (1 : Matrix (Fin 3) (Fin 3) F) (coordVec j) (coordVec j) = 1 := by
  rw [gramForm_one_apply (h := h)]
  fin_cases j <;> simp [coordVec, Fin.sum_univ_three]

theorem gramForm_coordVec_ne (h : UnitaryFieldData 3 1 F) {j k : Fin 3} (hjk : j ≠ k) :
    gramForm h (1 : Matrix (Fin 3) (Fin 3) F) (coordVec j) (coordVec k) = 0 := by
  rw [gramForm_one_apply (h := h)]
  fin_cases j <;> fin_cases k <;> simp [coordVec, Fin.sum_univ_three] at hjk ⊢

@[expose] noncomputable def coordLine (hF : Nat.card F = 9) (j : Fin 3) : NonisoLine F :=
  lineOf (h := unitaryFieldData_of_card hF) (coordVec j)
    (by rw [gramForm_coordVec_self]; exact one_ne_zero)

theorem coordLine_val (hF : Nat.card F = 9) (j : Fin 3) :
    (coordLine hF j).1 = F ∙ (coordVec j : Fin 3 → F) := rfl

theorem orth_coordLine (hF : Nat.card F = 9) {j k : Fin 3} (hjk : j ≠ k) :
    Orth (coordLine hF j) (coordLine hF k) := by
  have h := unitaryFieldData_of_card hF
  rw [orth_iff h]
  intro x hx y hy
  rw [coordLine_val, Submodule.mem_span_singleton] at hx hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rw [gramForm_smul_left, gramForm_smul_right, gramForm_coordVec_ne h hjk]
  simp

theorem coordLine_injective (hF : Nat.card F = 9) : Function.Injective (coordLine hF) := by
  intro j k hjk
  by_contra hne
  have h := unitaryFieldData_of_card hF
  have horth := orth_coordLine hF hne
  rw [hjk] at horth
  have := (orth_iff h _ _).mp horth (coordVec k) (by rw [coordLine_val]; exact Submodule.mem_span_singleton_self _)
    (coordVec k) (by rw [coordLine_val]; exact Submodule.mem_span_singleton_self _)
  rw [gramForm_coordVec_self] at this
  exact one_ne_zero this

variable (hF : Nat.card F = 9)

include hF in
theorem lineAct_coordLine_eq_iff (g : StatedSU 3 3 F) (j k : Fin 3) :
    lineAct hF g (coordLine hF j) = coordLine hF k ↔
      ∃ c : F, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ coordVec j = c • coordVec k := by
  constructor
  · intro h
    have hmem : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ coordVec j ∈
        (lineAct hF g (coordLine hF j)).1 := by
      rw [lineAct_val]
      exact ⟨coordVec j, by rw [coordLine_val]; exact Submodule.mem_span_singleton_self _,
        Matrix.toLin'_apply _ _⟩
    rw [h, coordLine_val, Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact coordVec_ne_zero j (mulVec_injective (g : GL (Fin 3) F)
        (show _ *ᵥ coordVec j = _ *ᵥ (0 : Fin 3 → F) by rw [hc, Matrix.mulVec_zero]))
    apply Subtype.ext
    rw [lineAct_val, coordLine_val, coordLine_val, Submodule.map_span, Set.image_singleton,
      Matrix.toLin'_apply, hc]
    exact Submodule.span_singleton_smul_eq hc0.isUnit _

@[expose] def pointStab (L : NonisoLine F) : Subgroup (StatedSU 3 3 F) where
  carrier := {g | lineAct hF g L = L}
  one_mem' := lineAct_one hF L
  mul_mem' := fun {a b} ha hb => by
    have ha' : lineAct hF a L = L := ha
    have hb' : lineAct hF b L = L := hb
    show lineAct hF (a * b) L = L
    rw [lineAct_mul, hb', ha']
  inv_mem' := fun {a} ha => by
    have ha' : lineAct hF a L = L := ha
    show lineAct hF a⁻¹ L = L
    have := congrArg (lineAct hF a⁻¹) ha'
    rw [← lineAct_mul, inv_mul_cancel, lineAct_one] at this
    exact this.symm

theorem mem_pointStab (L : NonisoLine F) (g : StatedSU 3 3 F) :
    g ∈ pointStab hF L ↔ lineAct hF g L = L := Iff.rfl

@[expose] def frameStab (T : HexLine F) : Subgroup (StatedSU 3 3 F) where
  carrier := {g | lineActLin hF g T = T}
  one_mem' := lineActLin_one hF T
  mul_mem' := fun {a b} ha hb => by
    have ha' : lineActLin hF a T = T := ha
    have hb' : lineActLin hF b T = T := hb
    show lineActLin hF (a * b) T = T
    rw [lineActLin_mul, hb', ha']
  inv_mem' := fun {a} ha => by
    have ha' : lineActLin hF a T = T := ha
    show lineActLin hF a⁻¹ T = T
    have := congrArg (lineActLin hF a⁻¹) ha'
    rw [← lineActLin_mul, inv_mul_cancel, lineActLin_one] at this
    exact this.symm

open Classical in
@[expose] noncomputable def coordFrame : HexLine F :=
  ⟨{coordLine hF 0, coordLine hF 1, coordLine hF 2}, by
      rw [Finset.card_eq_three]
      refine ⟨coordLine hF 0, coordLine hF 1, coordLine hF 2, ?_, ?_, ?_, rfl⟩ <;>
        exact fun h => absurd (coordLine_injective hF h) (by decide),
    by
      intro a ha b hb hab
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        first | exact absurd rfl hab | exact orth_coordLine hF (by decide)⟩

open Classical in
theorem mem_coordFrame_iff (x : NonisoLine F) :
    x ∈ (coordFrame hF).1 ↔ ∃ j : Fin 3, x = coordLine hF j := by
  simp only [coordFrame, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨j, rfl⟩
    fin_cases j
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem mem_frameStab_coordFrame_iff (g : StatedSU 3 3 F) :
    g ∈ frameStab hF (coordFrame hF) ↔ ∀ j : Fin 3, ∃ k : Fin 3, ∃ c : F,
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ coordVec j = c • coordVec k := by
  classical
  constructor
  · intro hg j
    have hmem : lineAct hF g (coordLine hF j) ∈ (lineActLin hF g (coordFrame hF)).1 :=
      (lineAct_mem_lineActLin hF g _ _).mpr ((mem_coordFrame_iff hF _).mpr ⟨j, rfl⟩)
    have hg' : lineActLin hF g (coordFrame hF) = coordFrame hF := hg
    rw [hg'] at hmem
    obtain ⟨k, hk⟩ := (mem_coordFrame_iff hF _).mp hmem
    exact ⟨k, (lineAct_coordLine_eq_iff hF g j k).mp hk⟩
  · intro h
    show lineActLin hF g (coordFrame hF) = coordFrame hF
    apply Subtype.ext
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := (mem_lineActLin hF g _ x).mp hx
      obtain ⟨j, rfl⟩ := (mem_coordFrame_iff hF a).mp ha
      obtain ⟨k, c, hc⟩ := h j
      exact (mem_coordFrame_iff hF _).mpr
        ⟨k, (lineAct_coordLine_eq_iff hF g j k).mpr ⟨c, hc⟩⟩
    · rw [(coordFrame hF).2.1, (lineActLin hF g (coordFrame hF)).2.1]

@[expose] def swapMat : Matrix (Fin 3) (Fin 3) F := !![0, 1, 0; 1, 0, 0; 0, 0, -1]

theorem swapMat_mul_self : (swapMat : Matrix (Fin 3) (Fin 3) F) * swapMat = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [swapMat, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def swapGL : GL (Fin 3) F := ⟨swapMat, swapMat, swapMat_mul_self, swapMat_mul_self⟩

theorem coe_swapGL : ((swapGL : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = swapMat := rfl

include hF in
theorem swapGL_mem_statedSU : (swapGL : GL (Fin 3) F) ∈ StatedSU 3 3 F := by
  rw [← SetLike.mem_coe, coe_statedSU hF, Set.mem_ofPred_eq, coe_swapGL]
  refine ⟨?_, ?_⟩
  · have hmap : (swapMat : Matrix (Fin 3) (Fin 3) F).map (· ^ 3) = swapMat := by
      ext a b
      fin_cases a <;> fin_cases b <;> norm_num [swapMat]
    have htr : (swapMat : Matrix (Fin 3) (Fin 3) F)ᵀ = swapMat := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [swapMat]
    rw [hmap, htr, swapMat_mul_self]
  · simp [swapMat, Matrix.det_fin_three]

@[expose] def swapSU : StatedSU 3 3 F := ⟨swapGL, swapGL_mem_statedSU hF⟩

theorem swapMat_mulVec_coordVec_zero :
    (swapMat : Matrix (Fin 3) (Fin 3) F) *ᵥ coordVec 0 = (1 : F) • coordVec 1 := by
  ext i; fin_cases i <;> simp [swapMat, coordVec, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem swapMat_mulVec_coordVec_one :
    (swapMat : Matrix (Fin 3) (Fin 3) F) *ᵥ coordVec 1 = (1 : F) • coordVec 0 := by
  ext i; fin_cases i <;> simp [swapMat, coordVec, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem swapMat_mulVec_coordVec_two :
    (swapMat : Matrix (Fin 3) (Fin 3) F) *ᵥ coordVec 2 = (-1 : F) • coordVec 2 := by
  ext i; fin_cases i <;> simp [swapMat, coordVec, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem swapSU_mem_frameStab : swapSU hF ∈ frameStab hF (coordFrame hF) := by
  rw [mem_frameStab_coordFrame_iff]
  intro j
  fin_cases j
  · exact ⟨1, 1, swapMat_mulVec_coordVec_zero⟩
  · exact ⟨0, 1, swapMat_mulVec_coordVec_one⟩
  · exact ⟨2, -1, swapMat_mulVec_coordVec_two⟩

theorem lineAct_swapSU_coordLine_zero :
    lineAct hF (swapSU hF) (coordLine hF 0) = coordLine hF 1 :=
  (lineAct_coordLine_eq_iff hF _ 0 1).mpr ⟨1, swapMat_mulVec_coordVec_zero⟩

theorem mulVec_coordVec (M : Matrix (Fin 3) (Fin 3) F) (j : Fin 3) :
    M *ᵥ coordVec j = fun i => M i j := by
  ext i; fin_cases j <;> simp [coordVec, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

include hF in
theorem exists_diagonal_of_fix (g : StatedSU 3 3 F)
    (hg : ∀ j, lineAct hF g (coordLine hF j) = coordLine hF j) :
    ∃ c : Fin 3 → F, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal c ∧
      ∀ j, c j ^ 4 = 1 := by
  have h := unitaryFieldData_of_card hF
  choose c hc using fun j => (lineAct_coordLine_eq_iff hF g j j).mp (hg j)
  refine ⟨c, ?_, fun j => ?_⟩
  · ext i j
    have h1 := congrFun (hc j) i
    rw [mulVec_coordVec, Pi.smul_apply, smul_eq_mul] at h1
    change ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j = c j * coordVec j i at h1
    rw [h1, Matrix.diagonal_apply]
    fin_cases i <;> fin_cases j <;> simp [coordVec]
  · have hiso := isometry_of_mem hF h g (coordVec j) (coordVec j)
    rw [hc j, gramForm_smul_left, gramForm_smul_right, gramForm_coordVec_self h,
      bar_eq_cube h] at hiso
    have : c j ^ 3 * c j = 1 := by simpa using hiso
    calc c j ^ 4 = c j ^ 3 * c j := by ring
      _ = 1 := this

include hF in
theorem lineAct_coordLine_two_of_fix {g : StatedSU 3 3 F}
    (h0 : lineAct hF g (coordLine hF 0) = coordLine hF 0)
    (h1 : lineAct hF g (coordLine hF 1) = coordLine hF 1) :
    lineAct hF g (coordLine hF 2) = coordLine hF 2 := by
  have hne : coordLine hF 0 ≠ coordLine hF 1 := fun h =>
    absurd (coordLine_injective hF h) (by decide)
  obtain ⟨c, -, hc⟩ := existsUnique_orth hF hne (orth_coordLine hF (by decide))
  have h2 : Orth (coordLine hF 0) (coordLine hF 2) ∧ Orth (coordLine hF 1) (coordLine hF 2) :=
    ⟨orth_coordLine hF (by decide), orth_coordLine hF (by decide)⟩
  have h3 : Orth (coordLine hF 0) (lineAct hF g (coordLine hF 2)) ∧
      Orth (coordLine hF 1) (lineAct hF g (coordLine hF 2)) := by
    refine ⟨?_, ?_⟩
    · have := (orth_lineAct_iff hF g (coordLine hF 0) (coordLine hF 2)).mpr h2.1
      rwa [h0] at this
    · have := (orth_lineAct_iff hF g (coordLine hF 1) (coordLine hF 2)).mpr h2.2
      rwa [h1] at this
  rw [hc _ h3, hc _ h2]

theorem card_fourth_roots_le : Nat.card {c : F // c ^ 4 = 1} ≤ 4 := by
  classical
  have h1 := Polynomial.card_nthRoots 4 (1 : F)
  have h2 : {c : F | c ^ 4 = 1} = ↑(Polynomial.nthRoots 4 (1 : F)).toFinset := by
    ext c
    simp [Polynomial.mem_nthRoots]
  show Nat.card ↥{c : F | c ^ 4 = 1} ≤ 4
  rw [Nat.card_coe_set_eq, h2, Set.ncard_coe_finset]
  exact (Multiset.toFinset_card_le _).trans h1

include hF in
theorem det_eq_one (g : StatedSU 3 3 F) :
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  have := g.2
  rw [← SetLike.mem_coe, coe_statedSU hF, Set.mem_ofPred_eq] at this
  exact this.2

include hF in
theorem card_stabilizer_pair_le :
    Nat.card ↥(pointStab hF (coordLine hF 0) ⊓ pointStab hF (coordLine hF 1)) ≤ 16 := by
  classical
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  have hfix : ∀ x : ↥(pointStab hF (coordLine hF 0) ⊓ pointStab hF (coordLine hF 1)),
      ∀ j, lineAct hF x.1 (coordLine hF j) = coordLine hF j := by
    intro x j
    have h0 : lineAct hF x.1 (coordLine hF 0) = coordLine hF 0 := x.2.1
    have h1 : lineAct hF x.1 (coordLine hF 1) = coordLine hF 1 := x.2.2
    fin_cases j
    · exact h0
    · exact h1
    · exact lineAct_coordLine_two_of_fix hF h0 h1
  have hent : ∀ x : ↥(pointStab hF (coordLine hF 0) ⊓ pointStab hF (coordLine hF 1)), ∀ j,
      (((x.1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) j j) ^ 4 = 1 := by
    intro x j
    obtain ⟨c, hc, h4⟩ := exists_diagonal_of_fix hF x.1 (hfix x)
    rw [hc, Matrix.diagonal_apply_eq]
    exact h4 j
  let f : ↥(pointStab hF (coordLine hF 0) ⊓ pointStab hF (coordLine hF 1)) →
      {c : F // c ^ 4 = 1} × {c : F // c ^ 4 = 1} := fun x =>
    (⟨((x.1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0, hent x 0⟩,
      ⟨((x.1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 1, hent x 1⟩)
  have hinj : Function.Injective f := by
    intro x y hxy
    have h00 : ((x.1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 =
        ((y.1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 := congrArg (fun p => (p.1 : F)) hxy
    have h11 : ((x.1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 1 =
        ((y.1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 1 := congrArg (fun p => (p.2 : F)) hxy
    obtain ⟨c, hc, -⟩ := exists_diagonal_of_fix hF x.1 (hfix x)
    obtain ⟨c', hc', -⟩ := exists_diagonal_of_fix hF y.1 (hfix y)
    have hdx := det_eq_one hF x.1
    have hdy := det_eq_one hF y.1
    rw [hc, Matrix.det_diagonal, Fin.prod_univ_three] at hdx
    rw [hc', Matrix.det_diagonal, Fin.prod_univ_three] at hdy
    rw [hc, Matrix.diagonal_apply_eq] at h00 h11
    rw [hc', Matrix.diagonal_apply_eq] at h00 h11
    have h22 : c 2 = c' 2 := by
      have hne : c 0 * c 1 ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hdx
        exact zero_ne_one hdx
      apply mul_left_cancel₀ hne
      rw [hdx, h00, h11, hdy]
    have hcc : c = c' := by
      funext j; fin_cases j
      · exact h00
      · exact h11
      · exact h22
    exact Subtype.ext (Subtype.ext (Units.ext (by rw [hc, hc', hcc])))
  calc Nat.card ↥(pointStab hF (coordLine hF 0) ⊓ pointStab hF (coordLine hF 1))
      ≤ Nat.card ({c : F // c ^ 4 = 1} × {c : F // c ^ 4 = 1}) := by
        exact Nat.card_le_card_of_injective f hinj
    _ = Nat.card {c : F // c ^ 4 = 1} * Nat.card {c : F // c ^ 4 = 1} := Nat.card_prod _ _
    _ ≤ 4 * 4 := Nat.mul_le_mul (card_fourth_roots_le) (card_fourth_roots_le)

@[expose, instance_reducible] noncomputable def lineMulAction :
    MulAction (StatedSU 3 3 F) (NonisoLine F) where
  smul := lineAct hF
  one_smul := lineAct_one hF
  mul_smul := lineAct_mul hF

include hF in
theorem card_pointStab_coord_zero :
    Nat.card (pointStab hF (coordLine hF 0)) = 96 := by
  have h := unitaryFieldData_of_card hF
  have hst : pointStab hF (coordLine hF 0) =
      Subgroup.centralizer {(tauLine h hF (coordLine hF 0) : StatedSU 3 3 F)} := by
    ext g
    exact lineAct_eq_self_iff (h := h) (hF := hF) g (coordLine hF 0)
  rw [hst]
  exact card_centralizer_tauLine (h := h) (hF := hF) (L₀ := coordLine hF 0) rfl

include hF in
theorem pointStab_transitive_orth (q q' : NonisoLine F)
    (hq : Orth (coordLine hF 0) q) (hq' : Orth (coordLine hF 0) q') :
    ∃ a ∈ pointStab hF (coordLine hF 0), lineAct hF a q = q' := by
  classical
  let _ := lineMulAction hF
  have hfin : Finite (NonisoLine F) := finite_nonisoLine hF
  have hfinS : Finite (StatedSU 3 3 F) :=
    Nat.finite_of_card_ne_zero (by rw [card_statedSU hF]; norm_num)
  set A := pointStab hF (coordLine hF 0) with hA
  set q₁ := coordLine hF 1 with hq₁
  have key : ∀ q, Orth (coordLine hF 0) q → q ∈ MulAction.orbit A q₁ := by
    have hsub : MulAction.orbit A q₁ ⊆ {q | Orth (coordLine hF 0) q} := by
      rintro _ ⟨a, rfl⟩
      show Orth (coordLine hF 0) (lineAct hF a.1 q₁)
      have := (orth_lineAct_iff hF a.1 (coordLine hF 0) q₁).mpr (orth_coordLine hF (by decide))
      rwa [show lineAct hF a.1 (coordLine hF 0) = coordLine hF 0 from a.2] at this
    have hcard : 6 ≤ (MulAction.orbit A q₁).ncard := by
      have h1 := MulAction.index_stabilizer A q₁
      have h2 := (MulAction.stabilizer A q₁).index_mul_card
      have hstab : Nat.card (MulAction.stabilizer A q₁) ≤ 16 := by
        have hinj : Function.Injective (fun g : MulAction.stabilizer A q₁ =>
            (⟨g.1.1, ⟨g.1.2, (MulAction.mem_stabilizer_iff.mp g.2 : lineAct hF g.1.1 q₁ = q₁)⟩⟩ :
              ↥(pointStab hF (coordLine hF 0) ⊓ pointStab hF (coordLine hF 1)))) := by
          intro x y hxy
          have h1 : x.1.1 = y.1.1 := congrArg (fun z => z.1) hxy
          exact Subtype.ext (Subtype.ext h1)
        exact (Nat.card_le_card_of_injective _ hinj).trans (card_stabilizer_pair_le hF)
      rw [card_pointStab_coord_zero hF, h1] at h2
      have hpos : 0 < Nat.card ↥(MulAction.stabilizer A q₁) := Nat.card_pos
      by_contra hlt
      push Not at hlt
      have : (MulAction.orbit A q₁).ncard * Nat.card ↥(MulAction.stabilizer A q₁) ≤ 5 * 16 :=
        Nat.mul_le_mul (by omega) hstab
      omega
    have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [ncard_orth hF]; exact hcard)
      (Set.toFinite _)
    intro q hq
    rw [heq]
    exact hq
  obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp (key q hq)
  obtain ⟨a', ha'⟩ := MulAction.mem_orbit_iff.mp (key q' hq')
  have ha1 : lineAct hF a.1 q₁ = q := ha
  have ha2 : lineAct hF a'.1 q₁ = q' := ha'
  refine ⟨a'.1 * a.1⁻¹, (a' * a⁻¹).2, ?_⟩
  rw [← ha1, ← lineAct_mul, inv_mul_cancel_right]
  exact ha2

omit hF in
theorem orth_of_pointGraph_adj {a b : NonisoLine F} (h : (pointGraph F).Adj a b) : Orth a b := by
  rw [pointGraph, SimpleGraph.fromRel_adj] at h
  obtain ⟨hne, hr⟩ := h
  rcases hr with ⟨T, ha, hb⟩ | ⟨T, hb, ha⟩
  · exact orth_of_mem T ha hb hne
  · exact orth_of_mem T ha hb hne

include hF in
theorem exists_mem_sup_lineAct_eq (x : NonisoLine F) :
    ∃ d ∈ pointStab hF (coordLine hF 0) ⊔ frameStab hF (coordFrame hF),
      lineAct hF d (coordLine hF 0) = x := by
  have h := unitaryFieldData_of_card hF
  set D := pointStab hF (coordLine hF 0) ⊔ frameStab hF (coordFrame hF) with hD
  have hA : pointStab hF (coordLine hF 0) ≤ D := le_sup_left
  have hB : frameStab hF (coordFrame hF) ≤ D := le_sup_right
  have hclosed : ∀ x y : NonisoLine F, (∃ d ∈ D, lineAct hF d (coordLine hF 0) = x) →
      Orth x y → ∃ d ∈ D, lineAct hF d (coordLine hF 0) = y := by
    rintro x y ⟨d, hdD, rfl⟩ hxy
    have hy' : Orth (coordLine hF 0) (lineAct hF d⁻¹ y) := by
      have := (orth_lineAct_iff hF d⁻¹ (lineAct hF d (coordLine hF 0)) y).mpr hxy
      rwa [← lineAct_mul, inv_mul_cancel, lineAct_one] at this
    obtain ⟨a, haA, ha⟩ := pointStab_transitive_orth hF (coordLine hF 1) (lineAct hF d⁻¹ y)
      (orth_coordLine hF (by decide)) hy'
    refine ⟨d * a * swapSU hF, D.mul_mem (D.mul_mem hdD (hA haA)) (hB (swapSU_mem_frameStab hF)), ?_⟩
    rw [lineAct_mul, lineAct_mul, lineAct_swapSU_coordLine_zero, ha, ← lineAct_mul,
      mul_inv_cancel, lineAct_one]
  have hconn := (hexagon_facts hF).2.2.2.1
  have hreach := hconn.preconnected (coordLine hF 0) x
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach with
  | refl => exact ⟨1, D.one_mem, lineAct_one hF _⟩
  | tail _ hadj ih => exact hclosed _ _ ih (orth_of_pointGraph_adj hadj)

include hF in
theorem pointStab_sup_frameStab_eq_top :
    pointStab hF (coordLine hF 0) ⊔ frameStab hF (coordFrame hF) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨d, hd, hdg⟩ := exists_mem_sup_lineAct_eq hF (lineAct hF g (coordLine hF 0))
  have : d⁻¹ * g ∈ pointStab hF (coordLine hF 0) := by
    show lineAct hF (d⁻¹ * g) (coordLine hF 0) = coordLine hF 0
    rw [lineAct_mul, ← hdg, ← lineAct_mul, inv_mul_cancel, lineAct_one]
  have := (pointStab hF (coordLine hF 0) ⊔ frameStab hF (coordFrame hF)).mul_mem hd
    (Subgroup.mem_sup_left this)
  rwa [mul_inv_cancel_left] at this

@[expose, instance_reducible] noncomputable def hexLineMulAction :
    MulAction (StatedSU 3 3 F) (HexLine F) where
  smul := lineActLin hF
  one_smul := lineActLin_one hF
  mul_smul := lineActLin_mul hF

include hF in
theorem exists_lineActLin_eq (T T' : HexLine F) :
    ∃ g : StatedSU 3 3 F, lineActLin hF g T = T' := by
  have step1 : ∀ T : HexLine F, ∃ g, coordLine hF 0 ∈ (lineActLin hF g T).1 := by
    intro T
    obtain ⟨x, hx⟩ : T.1.Nonempty := by rw [← Finset.card_pos, T.2.1]; norm_num
    obtain ⟨g, hg⟩ := lineAct_transitive hF x (coordLine hF 0)
    exact ⟨g, (mem_lineActLin hF g T _).mpr ⟨x, hx, hg⟩⟩
  have step2 : ∀ T T' : HexLine F, coordLine hF 0 ∈ T.1 → coordLine hF 0 ∈ T'.1 →
      ∃ g, lineActLin hF g T = T' := by
    intro T T' hT hT'
    obtain ⟨q, hq, hqne⟩ := Finset.exists_mem_ne (by rw [T.2.1]; norm_num) (coordLine hF 0)
    obtain ⟨q', hq', hqne'⟩ := Finset.exists_mem_ne (by rw [T'.2.1]; norm_num) (coordLine hF 0)
    obtain ⟨a, haA, ha⟩ := pointStab_transitive_orth hF q q' (orth_of_mem T hT hq hqne.symm)
      (orth_of_mem T' hT' hq' hqne'.symm)
    refine ⟨a, eq_of_mem_of_mem hF hqne'.symm (T := lineActLin hF a T) (T' := T') ?_ ?_ hT' hq'⟩
    · have := (lineAct_mem_lineActLin hF a T (coordLine hF 0)).mpr hT
      rwa [show lineAct hF a (coordLine hF 0) = coordLine hF 0 from haA] at this
    · have := (lineAct_mem_lineActLin hF a T q).mpr hq
      rwa [ha] at this
  obtain ⟨g₁, h₁⟩ := step1 T
  obtain ⟨g₂, h₂⟩ := step1 T'
  obtain ⟨a, ha⟩ := step2 _ _ h₁ h₂
  refine ⟨g₂⁻¹ * a * g₁, ?_⟩
  rw [lineActLin_mul, lineActLin_mul, ha, ← lineActLin_mul, inv_mul_cancel, lineActLin_one]

include hF in
theorem card_frameStab_coordFrame : Nat.card (frameStab hF (coordFrame hF)) = 96 := by
  let _ := hexLineMulAction hF
  have hfinS : Finite (StatedSU 3 3 F) :=
    Nat.finite_of_card_ne_zero (by rw [card_statedSU hF]; norm_num)
  have hfinL : Finite (HexLine F) := finite_hexLine hF
  have hstab : frameStab hF (coordFrame hF) =
      MulAction.stabilizer (StatedSU 3 3 F) (coordFrame hF) := by
    ext g
    rw [MulAction.mem_stabilizer_iff]
    exact Iff.rfl
  have hidx := MulAction.index_stabilizer (StatedSU 3 3 F) (coordFrame hF)
  have horb : MulAction.orbit (StatedSU 3 3 F) (coordFrame hF) = Set.univ := by
    ext T
    simp only [MulAction.mem_orbit_iff, Set.mem_univ, iff_true]
    obtain ⟨g, hg⟩ := exists_lineActLin_eq hF (coordFrame hF) T
    exact ⟨g, hg⟩
  have hmul := (MulAction.stabilizer (StatedSU 3 3 F) (coordFrame hF)).index_mul_card
  rw [hidx, horb, Set.ncard_univ, card_hexLine hF, card_statedSU hF] at hmul
  rw [hstab]
  omega

end CFSG.QuasithinUnique.Setup.X5
