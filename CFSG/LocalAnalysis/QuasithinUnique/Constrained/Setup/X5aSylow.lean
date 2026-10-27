module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5aGeom
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Setup.X5

open Matrix CFSG.LinearGroups.UnitaryThreeOverNine CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank

theorem isPrimeFormGram_one' {K : Type} [Field K] {n : ℕ} : IsPrimeFormGram (1 : GL (Fin n) K) := by
  refine ⟨by rw [Units.val_one, transpose_one], fun i j => ?_⟩
  rw [Units.val_one, one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

@[expose] noncomputable def unitaryBarEquiv {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) : K ≃+* K :=
  RingEquiv.ofBijective h.bar (Function.Involutive.bijective h.bar_bar)

theorem unitaryBarEquiv_apply {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) (c : K) :
    unitaryBarEquiv h c = h.bar c := rfl

theorem unitaryBarEquiv_mul_self {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) :
    unitaryBarEquiv h * unitaryBarEquiv h = 1 :=
  RingEquiv.ext fun c => h.bar_bar c

variable {F : Type} [Field F] (hF : Nat.card F = 9)

@[expose] noncomputable def barAut : F ≃+* F := unitaryBarEquiv (unitaryFieldData_of_card hF)


theorem barAut_apply (c : F) : barAut hF c = c ^ 3 := by
  have h := unitaryFieldData_of_card hF
  rw [barAut, unitaryBarEquiv_apply, UnitaryFieldData.bar_apply]
  simp

theorem barAut_mul_self : barAut hF * barAut hF = 1 := unitaryBarEquiv_mul_self _

theorem glAut_barAut_mem (g : GL (Fin 3) F) (hg : g ∈ StatedSU 3 3 F) :
    glAut (barAut hF) g ∈ StatedSU 3 3 F := by
  have h := unitaryFieldData_of_card hF
  rw [statedSU_eq_gramSU hF h] at hg ⊢
  exact glAut_mem_gramSU h isPrimeFormGram_one' (barAut hF) hg

theorem glAut_barAut_glAut_barAut (g : GL (Fin 3) F) :
    glAut (barAut hF) (glAut (barAut hF) g) = g := by
  rw [← MulAut.mul_apply, ← map_mul, barAut_mul_self, map_one, MulAut.one_apply]

@[expose] noncomputable def frobSU : MulAut (StatedSU 3 3 F) where
  toFun g := ⟨glAut (barAut hF) (g : GL (Fin 3) F), glAut_barAut_mem hF _ g.2⟩
  invFun g := ⟨glAut (barAut hF) (g : GL (Fin 3) F), glAut_barAut_mem hF _ g.2⟩
  left_inv := fun _ => Subtype.ext (glAut_barAut_glAut_barAut hF _)
  right_inv := fun _ => Subtype.ext (glAut_barAut_glAut_barAut hF _)
  map_mul' g g' := Subtype.ext (map_mul (glAut (barAut hF)) (g : GL (Fin 3) F) g')

theorem coe_frobSU (g : StatedSU 3 3 F) :
    ((frobSU hF g : StatedSU 3 3 F) : GL (Fin 3) F) = glAut (barAut hF) (g : GL (Fin 3) F) := rfl

theorem coe_coe_frobSU (g : StatedSU 3 3 F) (i j : Fin 3) :
    (((frobSU hF g : StatedSU 3 3 F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j =
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j ^ 3 := by
  rw [coe_frobSU, coe_glAut]
  simp [Matrix.map_apply, barAut_apply]

theorem frobSU_frobSU (g : StatedSU 3 3 F) : frobSU hF (frobSU hF g) = g :=
  Subtype.ext (glAut_barAut_glAut_barAut hF _)

theorem frobSU_mul_self : frobSU hF * frobSU hF = 1 :=
  MulEquiv.ext fun g => frobSU_frobSU hF g


include hF in
theorem mapsCoord_frobSU {g : StatedSU 3 3 F} {j k : Fin 3}
    (h : ∃ c : F, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ coordVec j = c • coordVec k) :
    ∃ c : F, (((frobSU hF g : StatedSU 3 3 F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      coordVec j = c • coordVec k := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c ^ 3, ?_⟩
  rw [mulVec_coordVec]
  funext i
  have h1 := congrFun hc i
  rw [mulVec_coordVec, Pi.smul_apply, smul_eq_mul] at h1
  change ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j = c * coordVec k i at h1
  have h2 : (coordVec k i : F) ^ 3 = coordVec k i := by
    fin_cases k <;> fin_cases i <;> simp [coordVec]
  show (((frobSU hF g : StatedSU 3 3 F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j =
    c ^ 3 * coordVec k i
  rw [coe_coe_frobSU, h1, mul_pow, h2]

include hF in
theorem frobSU_mem_pointStab_iff (j : Fin 3) (g : StatedSU 3 3 F) :
    frobSU hF g ∈ pointStab hF (coordLine hF j) ↔ g ∈ pointStab hF (coordLine hF j) := by
  rw [mem_pointStab, mem_pointStab, lineAct_coordLine_eq_iff hF, lineAct_coordLine_eq_iff hF]
  constructor
  · intro h
    have := mapsCoord_frobSU hF h
    rwa [frobSU_frobSU] at this
  · exact mapsCoord_frobSU hF

include hF in
theorem frobSU_mem_frameStab_iff (g : StatedSU 3 3 F) :
    frobSU hF g ∈ frameStab hF (coordFrame hF) ↔ g ∈ frameStab hF (coordFrame hF) := by
  rw [mem_frameStab_coordFrame_iff hF, mem_frameStab_coordFrame_iff hF]
  constructor
  · intro h j
    obtain ⟨k, hk⟩ := h j
    have := mapsCoord_frobSU hF hk
    rw [frobSU_frobSU] at this
    exact ⟨k, this⟩
  · intro h j
    obtain ⟨k, hk⟩ := h j
    exact ⟨k, mapsCoord_frobSU hF hk⟩

theorem map_eq_self_of_mem_iff {G : Type*} [Group G] (φ : MulAut G) (H : Subgroup G)
    (h : ∀ g, φ g ∈ H ↔ g ∈ H) : H.map φ.toMonoidHom = H := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (h y).mpr hy
  · intro hx
    refine ⟨φ.symm x, ?_, φ.apply_symm_apply x⟩
    have := (h (φ.symm x)).mp (by rwa [φ.apply_symm_apply])
    exact this


theorem diagonal_mulVec_coordVec (d : Fin 3 → F) (j : Fin 3) :
    (Matrix.diagonal d : Matrix (Fin 3) (Fin 3) F) *ᵥ coordVec j = d j • coordVec j := by
  ext i
  fin_cases i <;> fin_cases j <;> simp [coordVec, Matrix.mulVec_diagonal]

theorem wreath_mulVec_coordVec_zero :
    (!![-1, 0, 0; 0, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F) *ᵥ coordVec 0 =
      (-1 : F) • coordVec 0 := by
  ext i; fin_cases i <;> simp [coordVec, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem wreath_mulVec_coordVec_one :
    (!![-1, 0, 0; 0, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F) *ᵥ coordVec 1 =
      (1 : F) • coordVec 2 := by
  ext i; fin_cases i <;> simp [coordVec, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem wreath_mulVec_coordVec_two :
    (!![-1, 0, 0; 0, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F) *ᵥ coordVec 2 =
      (1 : F) • coordVec 1 := by
  ext i; fin_cases i <;> simp [coordVec, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

include hF in
theorem diagonal_mem_pointStab {g : StatedSU 3 3 F} {d : Fin 3 → F}
    (hg : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal d) (j : Fin 3) :
    g ∈ pointStab hF (coordLine hF j) := by
  rw [mem_pointStab, lineAct_coordLine_eq_iff hF]
  exact ⟨d j, by rw [hg, diagonal_mulVec_coordVec]⟩

include hF in
theorem diagonal_mem_frameStab {g : StatedSU 3 3 F} {d : Fin 3 → F}
    (hg : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal d) :
    g ∈ frameStab hF (coordFrame hF) := by
  rw [mem_frameStab_coordFrame_iff hF]
  intro j
  exact ⟨j, d j, by rw [hg, diagonal_mulVec_coordVec]⟩

include hF in
theorem wreath_mem_pointStab_zero {g : StatedSU 3 3 F}
    (hg : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = !![-1, 0, 0; 0, 0, 1; 0, 1, 0]) :
    g ∈ pointStab hF (coordLine hF 0) := by
  rw [mem_pointStab, lineAct_coordLine_eq_iff hF]
  exact ⟨-1, by rw [hg, wreath_mulVec_coordVec_zero]⟩

include hF in
theorem wreath_mem_frameStab {g : StatedSU 3 3 F}
    (hg : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = !![-1, 0, 0; 0, 0, 1; 0, 1, 0]) :
    g ∈ frameStab hF (coordFrame hF) := by
  rw [mem_frameStab_coordFrame_iff hF]
  intro j
  fin_cases j
  · exact ⟨0, -1, by rw [hg]; exact wreath_mulVec_coordVec_zero⟩
  · exact ⟨2, 1, by rw [hg]; exact wreath_mulVec_coordVec_one⟩
  · exact ⟨1, 1, by rw [hg]; exact wreath_mulVec_coordVec_two⟩

theorem coe_frobSU_diagonal (s : StatedSU 3 3 F) (d : Fin 3 → F)
    (hs : ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal d) :
    (((frobSU hF s : StatedSU 3 3 F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal (fun k => d k ^ 3) := by
  ext a b
  rw [coe_coe_frobSU, hs]
  by_cases hab : a = b
  · subst hab; simp
  · simp [Matrix.diagonal_apply_ne _ hab]

theorem frobSU_eq_inv_of_diagonal (s : StatedSU 3 3 F) (d : Fin 3 → F)
    (hs : ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal d)
    (hd : ∀ k, d k ^ 4 = 1) : frobSU hF s = s⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply Subtype.ext
  apply Units.ext
  show (((frobSU hF s : StatedSU 3 3 F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
    ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1
  rw [coe_frobSU_diagonal hF s d hs, hs, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext k
  rw [← pow_succ]
  exact hd k

theorem frobSU_eq_self_of_entries (w : StatedSU 3 3 F)
    (hw : ∀ a b, ((w : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) a b ^ 3 =
      ((w : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) a b) : frobSU hF w = w := by
  apply Subtype.ext
  apply Units.ext
  ext a b
  rw [coe_coe_frobSU]
  exact hw a b


include hF in
theorem map_frobSU_closure (i : Fˣ) (hi : orderOf i = 4) (s t w : StatedSU 3 3 F)
    (hs : ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![(i : F)⁻¹, i, 1])
    (ht : ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![(i : F)⁻¹, 1, i])
    (hw : ((w : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = !![-1, 0, 0; 0, 0, 1; 0, 1, 0]) :
    (Subgroup.closure {s, t, w}).map (frobSU hF).toMonoidHom = Subgroup.closure {s, t, w} := by
  have hi4 : (i : F) ^ 4 = 1 := by
    have := congrArg Units.val (pow_orderOf_eq_one i)
    rwa [hi, Units.val_pow_eq_pow_val, Units.val_one] at this
  have hi0 : (i : F) ≠ 0 := i.ne_zero
  have hfs : frobSU hF s = s⁻¹ := by
    refine frobSU_eq_inv_of_diagonal hF s _ hs fun k => ?_
    fin_cases k
    · show ((i : F)⁻¹) ^ 4 = 1
      rw [inv_pow, hi4, inv_one]
    · exact hi4
    · show (1 : F) ^ 4 = 1
      exact one_pow 4
  have hft : frobSU hF t = t⁻¹ := by
    refine frobSU_eq_inv_of_diagonal hF t _ ht fun k => ?_
    fin_cases k
    · show ((i : F)⁻¹) ^ 4 = 1
      rw [inv_pow, hi4, inv_one]
    · show (1 : F) ^ 4 = 1
      exact one_pow 4
    · exact hi4
  have hfw : frobSU hF w = w := by
    refine frobSU_eq_self_of_entries hF w fun a b => ?_
    rw [hw]
    fin_cases a <;> fin_cases b <;> norm_num
  set P := Subgroup.closure ({s, t, w} : Set (StatedSU 3 3 F)) with hP
  have hsP : s ∈ P := Subgroup.subset_closure (by simp)
  have htP : t ∈ P := Subgroup.subset_closure (by simp)
  have hwP : w ∈ P := Subgroup.subset_closure (by simp)
  have hle : P.map (frobSU hF).toMonoidHom ≤ P := by
    rw [Subgroup.map_le_iff_le_comap, hP, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · show frobSU hF x ∈ P
      rw [hfs]; exact P.inv_mem hsP
    · show frobSU hF x ∈ P
      rw [hft]; exact P.inv_mem htP
    · show frobSU hF x ∈ P
      rw [hfw]; exact hwP
  have hfin : Finite (StatedSU 3 3 F) := Nat.finite_of_card_ne_zero (by rw [card_statedSU hF]; norm_num)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (frobSU hF).injective]


include hF in
theorem coordinate_sylow_overgroups (i : Fˣ) (hi : orderOf i = 4) (s t w : StatedSU 3 3 F)
    (hs : ((s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![(i : F)⁻¹, i, 1])
    (ht : ((t : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![(i : F)⁻¹, 1, i])
    (hw : ((w : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = !![-1, 0, 0; 0, 0, 1; 0, 1, 0]) :
    Nat.card (StatedSU 3 3 F) = 6048 ∧
    CFSG.QuasithinUnique.IsSylowTwoOf (Subgroup.closure {s, t, w}) ⊤ ∧
    Nat.card (Subgroup.closure {s, t, w}) = 32 ∧
    Nat.card (pointStab hF (coordLine hF 0)) = 96 ∧
    Nat.card (frameStab hF (coordFrame hF)) = 96 ∧
    pointStab hF (coordLine hF 0) ⊔ frameStab hF (coordFrame hF) = ⊤ ∧
    pointStab hF (coordLine hF 0) ≠ ⊤ ∧ frameStab hF (coordFrame hF) ≠ ⊤ ∧
    Subgroup.closure {s, t, w} ≤ pointStab hF (coordLine hF 0) ∧
    Subgroup.closure {s, t, w} ≤ frameStab hF (coordFrame hF) ∧
    (frobSU hF * frobSU hF = 1 ∧ frobSU hF ≠ 1) ∧
    (Subgroup.closure {s, t, w}).map (frobSU hF).toMonoidHom = Subgroup.closure {s, t, w} ∧
    (pointStab hF (coordLine hF 0)).map (frobSU hF).toMonoidHom = pointStab hF (coordLine hF 0) ∧
    (frameStab hF (coordFrame hF)).map (frobSU hF).toMonoidHom = frameStab hF (coordFrame hF) := by
  have hS := card_statedSU hF
  have hfin : Finite (StatedSU 3 3 F) := Nat.finite_of_card_ne_zero (by rw [hS]; norm_num)
  obtain ⟨-, hs4, -, -, -, -, -, -, hcard, ⟨P, hP⟩, -⟩ :=
    (wreath_sylow_model hF i hi).2 s t w hs ht hw
  have hsA : s ∈ pointStab hF (coordLine hF 0) := diagonal_mem_pointStab hF hs 0
  have htA : t ∈ pointStab hF (coordLine hF 0) := diagonal_mem_pointStab hF ht 0
  have hwA : w ∈ pointStab hF (coordLine hF 0) := wreath_mem_pointStab_zero hF hw
  have hsB : s ∈ frameStab hF (coordFrame hF) := diagonal_mem_frameStab hF hs
  have htB : t ∈ frameStab hF (coordFrame hF) := diagonal_mem_frameStab hF ht
  have hwB : w ∈ frameStab hF (coordFrame hF) := wreath_mem_frameStab hF hw
  have hAcard := card_pointStab_coord_zero hF
  have hBcard := card_frameStab_coordFrame hF
  refine ⟨hS, ?_, hcard, hAcard, hBcard, pointStab_sup_frameStab_eq_top hF, ?_, ?_, ?_, ?_,
    ⟨frobSU_mul_self hF, ?_⟩, map_frobSU_closure hF i hi s t w hs ht hw, ?_, ?_⟩
  · refine CFSG.QuasithinUnique.isSylowTwoOf_iff.mpr ⟨le_top, ?_, ?_⟩
    · rw [← hP]; exact P.isPGroup'
    · rw [← hP, CFSG.QuasithinUnique.twoPart, Subgroup.card_top]
      exact P.card_eq_multiplicity
  · intro h
    rw [h, Subgroup.card_top, hS] at hAcard
    omega
  · intro h
    rw [h, Subgroup.card_top, hS] at hBcard
    omega
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · intro h
    have hi4 : (i : F) ^ 4 = 1 := by
      have := congrArg Units.val (pow_orderOf_eq_one i)
      rwa [hi, Units.val_pow_eq_pow_val, Units.val_one] at this
    have hfs : frobSU hF s = s⁻¹ := by
      refine frobSU_eq_inv_of_diagonal hF s _ hs fun k => ?_
      fin_cases k
      · show ((i : F)⁻¹) ^ 4 = 1
        rw [inv_pow, hi4, inv_one]
      · exact hi4
      · show (1 : F) ^ 4 = 1
        exact one_pow 4
    rw [h, MulAut.one_apply] at hfs
    have : s ^ 2 = 1 := by rw [pow_two]; exact mul_eq_one_iff_eq_inv.mpr hfs
    have := orderOf_dvd_of_pow_eq_one this
    rw [hs4] at this
    omega
  · exact map_eq_self_of_mem_iff _ _ (fun g => frobSU_mem_pointStab_iff hF 0 g)
  · exact map_eq_self_of_mem_iff _ _ (fun g => frobSU_mem_frameStab_iff hF g)

end CFSG.QuasithinUnique.Setup.X5
