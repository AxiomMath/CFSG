module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutionsLines

public section

namespace CFSG.LinearGroups.UnitaryThreeOverNine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.LinearGroups

variable {F : Type} [Field F] {h : UnitaryFieldData 3 1 F}

theorem exists_normOne_mem (L : NonisoLine F) :
    ∃ u ∈ L.1, gramForm h (1 : Matrix (Fin 3) (Fin 3) F) u u = 1 := by
  set a := gramForm h (1 : Matrix (Fin 3) (Fin 3) F) L.gen L.gen with ha
  have ha0 : a ≠ 0 := L.gramForm_gen
  have hafix : a⁻¹ ∈ h.fixedField := by
    rw [UnitaryFieldData.mem_fixedField, map_inv₀, ha, bar_gramForm]
  obtain ⟨c, hc⟩ := h.normHom_surjective ⟨a⁻¹, hafix⟩
  have hc' : c * h.bar c = a⁻¹ := congrArg Subtype.val hc
  refine ⟨c • L.gen, L.1.smul_mem c L.gen_mem, ?_⟩
  rw [gramForm_smul_left, gramForm_smul_right, ← ha, ← mul_assoc, mul_comm (h.bar c), hc',
    inv_mul_cancel₀ ha0]

@[expose] noncomputable def NonisoLine.normOne (h : UnitaryFieldData 3 1 F) (L : NonisoLine F) :
    Fin 3 → F :=
  (exists_normOne_mem (h := h) L).choose

theorem NonisoLine.normOne_mem (L : NonisoLine F) : L.normOne h ∈ L.1 :=
  (exists_normOne_mem (h := h) L).choose_spec.1

theorem NonisoLine.gramForm_normOne (L : NonisoLine F) :
    gramForm h (1 : Matrix (Fin 3) (Fin 3) F) (L.normOne h) (L.normOne h) = 1 :=
  (exists_normOne_mem (h := h) L).choose_spec.2

theorem NonisoLine.normOne_ne_zero (L : NonisoLine F) : L.normOne h ≠ 0 := by
  intro h0
  have := L.gramForm_normOne (h := h)
  simp [h0] at this

theorem NonisoLine.eq_span_normOne (L : NonisoLine F) : L.1 = F ∙ L.normOne h :=
  eq_span_of_mem L L.normOne_mem L.normOne_ne_zero

theorem gramForm_smul_smul (c : F) (v : Fin 3 → F) :
    gramForm h (1 : Matrix (Fin 3) (Fin 3) F) (c • v) (c • v) =
      h.norm c * gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v := by
  rw [gramForm_smul_left, gramForm_smul_right, UnitaryFieldData.norm]
  ring

theorem card_lines_le (h : UnitaryFieldData 3 1 F)
    (W : Submodule F (Fin 3 → F)) :
    Nat.card {L : NonisoLine F // L.1 ≤ W} * 4 =
      Nat.card {v : Fin 3 → F // v ∈ W ∧ gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v = 1} := by
  have hcard4 : Nat.card {c : F // h.norm c = 1} = 4 := card_norm_eq_one h
  let ψ : {L : NonisoLine F // L.1 ≤ W} × {c : F // h.norm c = 1} →
      {v : Fin 3 → F // v ∈ W ∧ gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v = 1} :=
    fun x => ⟨x.2.1 • x.1.1.normOne h, x.1.2 (x.1.1.1.smul_mem _ x.1.1.normOne_mem), by
      rw [gramForm_smul_smul, x.1.1.gramForm_normOne, mul_one, x.2.2]⟩
  have hψ : Function.Bijective ψ := by
    constructor
    · rintro ⟨⟨L, hL⟩, ⟨c, hc⟩⟩ ⟨⟨M, hM⟩, ⟨d, hd⟩⟩ hxy
      have hxy' : c • L.normOne h = d • M.normOne h := congrArg Subtype.val hxy
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [UnitaryFieldData.norm, zero_mul] at hc
        exact zero_ne_one hc
      have hcu : c • L.normOne h ≠ 0 := smul_ne_zero hc0 L.normOne_ne_zero
      have hLM : L = M := by
        apply Subtype.ext
        rw [eq_span_of_mem L (L.1.smul_mem c L.normOne_mem) hcu,
          eq_span_of_mem M (hxy' ▸ M.1.smul_mem d M.normOne_mem) hcu]
      subst hLM
      have hcd : c = d := smul_left_injective F L.normOne_ne_zero hxy'
      subst hcd
      rfl
    · rintro ⟨v, hvW, hv1⟩
      have hv0 : v ≠ 0 := by
        rintro rfl
        simp at hv1
      have hvv : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v ≠ 0 := by rw [hv1]; exact one_ne_zero
      set L := lineOf (h := h) v hvv with hL
      have hLW : L.1 ≤ W := (Submodule.span_singleton_le_iff_mem v W).mpr hvW
      have hvL : v ∈ L.1 := Submodule.mem_span_singleton_self v
      rw [L.eq_span_normOne (h := h)] at hvL
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hvL
      have hNc : h.norm c = 1 := by
        have := gramForm_smul_smul (h := h) c (L.normOne h)
        rw [hc, hv1, L.gramForm_normOne, mul_one] at this
        exact this.symm
      exact ⟨(⟨L, hLW⟩, ⟨c, hNc⟩), Subtype.ext hc⟩
  rw [← Nat.card_congr (Equiv.ofBijective ψ hψ), Nat.card_prod, hcard4]

theorem card_nonisoLine (hF : Nat.card F = 9) : Nat.card (NonisoLine F) = 63 := by
  have h := unitaryFieldData_of_card hF
  have hc := card_lines_le h ⊤
  have h1 : Nat.card {L : NonisoLine F // L.1 ≤ ⊤} = Nat.card (NonisoLine F) :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun L => le_top)
  have h2 : Nat.card {v : Fin 3 → F // v ∈ (⊤ : Submodule F (Fin 3 → F)) ∧
      gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v = 1} = 252 := by
    rw [← ncard_normOne_three hF, ← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun v => by
      rw [gramForm_one_apply, Set.mem_ofPred_eq]
      exact ⟨fun hv => hv.2, fun hv => ⟨Submodule.mem_top, hv⟩⟩)
  rw [h1, h2] at hc
  omega

@[expose] noncomputable def perpZero (F : Type) [Field F] : Submodule F (Fin 3 → F) :=
  LinearMap.ker (LinearMap.proj 0)

theorem mem_perpZero {y : Fin 3 → F} : y ∈ perpZero F ↔ y 0 = 0 := by
  rw [perpZero, LinearMap.mem_ker, LinearMap.proj_apply]

theorem card_lines_perp (hF : Nat.card F = 9) :
    Nat.card {L : NonisoLine F // L.1 ≤ perpZero F} = 6 := by
  have h := unitaryFieldData_of_card hF
  have hc := card_lines_le h (perpZero F)
  have h2 : Nat.card {v : Fin 3 → F // v ∈ perpZero F ∧
      gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v v = 1} = 24 := by
    rw [← ncard_normOne_two hF, ← Nat.card_coe_set_eq]
    refine Nat.card_congr
      { toFun := fun v => ⟨![v.1 1, v.1 2], by
          have hv := v.2
          rw [mem_perpZero, gramForm_one_apply, Fin.sum_univ_three] at hv
          rw [Set.mem_ofPred_eq, Fin.sum_univ_two]
          simpa [hv.1] using hv.2⟩
        invFun := fun u => ⟨![0, u.1 0, u.1 1], by
          have hu := u.2
          rw [Set.mem_ofPred_eq, Fin.sum_univ_two] at hu
          rw [mem_perpZero, gramForm_one_apply, Fin.sum_univ_three]
          simpa using hu⟩
        left_inv := fun v => Subtype.ext (by
          have hv := (mem_perpZero.mp v.2.1)
          funext k
          fin_cases k <;> simp [hv])
        right_inv := fun u => Subtype.ext (by
          funext k
          fin_cases k <;> simp) }
  rw [h2] at hc
  omega

end CFSG.LinearGroups.UnitaryThreeOverNine
