module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutionsClass

public section

namespace CFSG.LinearGroups.UnitaryThreeOverNine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

abbrev NonisoLine (F : Type) [Field F] : Type :=
  {L : Submodule F (Fin 3 → F) // Module.finrank F L = 1 ∧ ∃ v ∈ L, ∑ j, v j ^ 3 * v j ≠ 0}

variable {h : UnitaryFieldData 3 1 F}

theorem gramForm_self_ne_zero_iff (v : Fin 3 → F) :
    gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v ≠ 0 ↔ ∑ j, v j ^ 3 * v j ≠ 0 := by
  rw [gramForm_one_apply]

theorem eq_span_of_mem (L : NonisoLine F) {v : Fin 3 → F} (hv : v ∈ L.1) (hv0 : v ≠ 0) :
    L.1 = F ∙ v :=
  (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem v L.1).mpr hv)
    (by rw [finrank_span_singleton hv0, L.2.1])).symm

theorem gramForm_ne_zero_of_mem (L : NonisoLine F) {v : Fin 3 → F} (hv : v ∈ L.1)
    (hv0 : v ≠ 0) : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v ≠ 0 := by
  obtain ⟨u, huL, hu⟩ := L.2.2
  rw [← gramForm_self_ne_zero_iff (h := h)] at hu
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hu (by simp)
  rw [eq_span_of_mem L huL hu0] at hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  have hc : c ≠ 0 := by
    rintro rfl
    exact hv0 (zero_smul F u)
  rw [gramForm_smul_left, gramForm_smul_right]
  exact mul_ne_zero ((h.bar_eq_zero_iff).not.mpr hc) (mul_ne_zero hc hu)

@[expose] noncomputable def lineOf (v : Fin 3 → F)
    (hv : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v ≠ 0) : NonisoLine F :=
  ⟨F ∙ v, finrank_span_singleton (fun h0 => hv (by rw [h0]; simp)),
    v, Submodule.mem_span_singleton_self v, (gramForm_self_ne_zero_iff v).mp hv⟩

@[expose] noncomputable def NonisoLine.gen (L : NonisoLine F) : Fin 3 → F := L.2.2.choose

theorem NonisoLine.gen_mem (L : NonisoLine F) : L.gen ∈ L.1 := L.2.2.choose_spec.1

theorem NonisoLine.gen_norm (L : NonisoLine F) : ∑ j, L.gen j ^ 3 * L.gen j ≠ 0 :=
  L.2.2.choose_spec.2

theorem NonisoLine.gramForm_gen (L : NonisoLine F) :
    gramForm h (1 : Matrix (Fin 3) (Fin 3) F) L.gen L.gen ≠ 0 :=
  (gramForm_self_ne_zero_iff _).mpr L.gen_norm

theorem NonisoLine.gen_ne_zero (L : NonisoLine F) : L.gen ≠ 0 := fun h0 =>
  L.gen_norm (by rw [h0]; simp)

theorem NonisoLine.eq_span_gen (L : NonisoLine F) : L.1 = F ∙ L.gen :=
  eq_span_of_mem L L.gen_mem L.gen_ne_zero

theorem tauGL_line_eq (L : NonisoLine F) {v : Fin 3 → F} (hv : v ∈ L.1) (hv0 : v ≠ 0)
    (hvv : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v ≠ 0) :
    tauGL v hvv = tauGL L.gen (L.gramForm_gen (h := h)) := by
  have hL := L.eq_span_gen
  rw [hL] at hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  have hc : c ≠ 0 := by
    rintro rfl
    exact hv0 (zero_smul F _)
  exact tauGL_smul _ hc hvv

variable (h) (hF : Nat.card F = 9)

@[expose] noncomputable def tauLine (L : NonisoLine F) : {g : StatedSU 3 3 F // orderOf g = 2} :=
  ⟨⟨tauGL L.gen (L.gramForm_gen (h := h)), tauGL_mem_statedSU _ hF⟩, by
    rw [Subgroup.orderOf_mk]
    exact orderOf_tauGL _⟩

theorem coe_tauLine (L : NonisoLine F) :
    (((tauLine h hF L : StatedSU 3 3 F)) : GL (Fin 3) F) = tauGL L.gen (L.gramForm_gen (h := h)) :=
  rfl

variable {h} {hF}

theorem tauLine_mulVec (L : NonisoLine F) {v : Fin 3 → F} (hv : v ∈ L.1) (hv0 : v ≠ 0)
    (y : Fin 3 → F) :
    ((((tauLine h hF L : StatedSU 3 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y =
      tauLin h v y := by
  rw [coe_tauLine, ← tauGL_line_eq L hv hv0 (gramForm_ne_zero_of_mem L hv hv0), tauGL_mulVec]

theorem mem_line_iff_tauLine (L : NonisoLine F) (y : Fin 3 → F) :
    y ∈ L.1 ↔ ((((tauLine h hF L : StatedSU 3 3 F)) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ y = y := by
  rw [coe_tauLine, tauGL_mulVec, tauLin_eq_self_iff (L.gramForm_gen (h := h)), ← L.eq_span_gen]

theorem tauLine_injective : Function.Injective (tauLine h hF) := by
  intro L M hLM
  apply Subtype.ext
  ext y
  rw [mem_line_iff_tauLine (h := h) (hF := hF) L, mem_line_iff_tauLine (h := h) (hF := hF) M, hLM]

theorem tauLine_surjective : Function.Surjective (tauLine h hF) := by
  rintro ⟨g, hg⟩
  obtain ⟨v, hv, hgv⟩ := exists_tauGL_eq_of_orderOf (h := h) hF g.2
    (by rw [← Subgroup.orderOf_coe] at hg; exact hg)
  refine ⟨lineOf v hv, Subtype.ext (Subtype.ext ?_)⟩
  rw [coe_tauLine, hgv]
  exact (tauGL_line_eq (lineOf v hv) (Submodule.mem_span_singleton_self v)
    (fun h0 => hv (by rw [h0]; simp)) hv).symm

variable (h) (hF)

@[expose] noncomputable def tauLineEquiv : NonisoLine F ≃ {g : StatedSU 3 3 F // orderOf g = 2} :=
  Equiv.ofBijective (tauLine h hF) ⟨tauLine_injective, tauLine_surjective⟩

theorem tauLineEquiv_apply (L : NonisoLine F) : tauLineEquiv h hF L = tauLine h hF L := rfl

theorem isometry_of_mem (hF : Nat.card F = 9) (h : UnitaryFieldData 3 1 F) (g : StatedSU 3 3 F)
    (x y : Fin 3 → F) :
    gramForm h (1 : Matrix (Fin 3) (Fin 3) F)
        (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x)
        (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y) =
      gramForm h (1 : Matrix (Fin 3) (Fin 3) F) x y := by
  have hg : (g : GL (Fin 3) F) ∈ gramSU h 1 := by
    rw [← statedSU_eq_gramSU hF h]
    exact g.2
  exact (mem_gramSU_iff_isometry.mp hg).1 x y

theorem mulVec_injective (g : GL (Fin 3) F) :
    Function.Injective (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ·) := by
  intro x y hxy
  have := congrArg (((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ·) hxy
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec] at this
  exact this

@[expose] noncomputable def lineAct (hF : Nat.card F = 9) (g : StatedSU 3 3 F)
    (L : NonisoLine F) : NonisoLine F :=
  ⟨L.1.map (Matrix.toLin' ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)), by
    have hinj : Function.Injective
        (Matrix.toLin' ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
      intro x y hxy
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at hxy
      exact mulVec_injective (g : GL (Fin 3) F) hxy
    refine ⟨by rw [← (Submodule.equivMapOfInjective _ hinj L.1).finrank_eq, L.2.1], ?_⟩
    obtain ⟨v, hvL, hv⟩ := L.2.2
    refine ⟨_, Submodule.mem_map_of_mem hvL, ?_⟩
    rw [Matrix.toLin'_apply, ← gramForm_self_ne_zero_iff (h := unitaryFieldData_of_card hF),
      isometry_of_mem hF, gramForm_self_ne_zero_iff]
    exact hv⟩

theorem lineAct_val (hF : Nat.card F = 9) (g : StatedSU 3 3 F) (L : NonisoLine F) :
    (lineAct hF g L).1 = L.1.map (Matrix.toLin' ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :=
  rfl

theorem lineAct_one (hF : Nat.card F = 9) (L : NonisoLine F) : lineAct hF 1 L = L :=
  Subtype.ext (by
    rw [lineAct_val, Subgroup.coe_one, Units.val_one, Matrix.toLin'_one, Submodule.map_id])

theorem lineAct_mul (hF : Nat.card F = 9) (g g' : StatedSU 3 3 F) (L : NonisoLine F) :
    lineAct hF (g * g') L = lineAct hF g (lineAct hF g' L) :=
  Subtype.ext (by
    rw [lineAct_val, lineAct_val, lineAct_val, Subgroup.coe_mul, Units.val_mul,
      Matrix.toLin'_mul, Submodule.map_comp])

theorem tauLine_lineAct (hF : Nat.card F = 9) (g : StatedSU 3 3 F) (L : NonisoLine F) :
    (tauLine h hF (lineAct hF g L) : StatedSU 3 3 F) = g * tauLine h hF L * g⁻¹ := by
  have hgv : gramForm h (1 : Matrix (Fin 3) (Fin 3) F)
      (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ L.gen)
      (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ L.gen) ≠ 0 := by
    rw [isometry_of_mem hF]
    exact L.gramForm_gen
  have hmem : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ L.gen ∈ (lineAct hF g L).1 := by
    rw [lineAct_val]
    exact ⟨L.gen, L.gen_mem, Matrix.toLin'_apply _ _⟩
  have hne : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ L.gen ≠ 0 := by
    intro h0
    apply L.gen_ne_zero
    exact mulVec_injective (g : GL (Fin 3) F)
      (show _ *ᵥ L.gen = _ *ᵥ (0 : Fin 3 → F) by rw [h0, Matrix.mulVec_zero])
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_tauLine, coe_tauLine,
    tauGL_conj _ (isometry_of_mem hF h g) hgv]
  exact (tauGL_line_eq (lineAct hF g L) hmem hne hgv).symm

end CFSG.LinearGroups.UnitaryThreeOverNine
