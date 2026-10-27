module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutionsAction

public section

namespace CFSG.LinearGroups.UnitaryThreeOverNine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank

theorem unitary_three_over_nine_involutions_orthogonality_and_faithful_point_action
    {F : Type} [Field F] (hF : Nat.card F = 9) :
    let bar : F → F := fun c => c ^ 3
    let h : (Fin 3 → F) → (Fin 3 → F) → F := fun u v => ∑ j, bar (u j) * v j
    let P := {L : Submodule F (Fin 3 → F) // Module.finrank F L = 1 ∧ ∃ v ∈ L, h v v ≠ 0}
    let E : (Fin 3 → F) → (Fin 3 → F) → (Fin 3 → F) := fun v y => (h v y / h v v) • v
    let act : StatedSU 3 3 F → Submodule F (Fin 3 → F) → Submodule F (Fin 3 → F) :=
      fun g L => L.map (Matrix.toLin' ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    let U₂ : Set (GL (Fin 2) F) :=
      {A : GL (Fin 2) F | ((A : Matrix (Fin 2) (Fin 2) F).map bar)ᵀ * A = 1}
    (StatedSU 3 3 F : Set (GL (Fin 3) F)) =
      {A : GL (Fin 3) F | ((A : Matrix (Fin 3) (Fin 3) F).map bar)ᵀ * A = 1 ∧
        (A : Matrix (Fin 3) (Fin 3) F).det = 1} ∧
    (∀ L : P, ∀ v ∈ L.1, v ≠ 0 → h v v ≠ 0) ∧
    (∀ L : P, ∀ v ∈ L.1, ∀ w ∈ L.1, v ≠ 0 → w ≠ 0 → ∀ y,
      (2 : F) • E v y - y = (2 : F) • E w y - y) ∧
    (∀ (g : StatedSU 3 3 F) (L : P), ∃ L' : P, L'.1 = act g L.1) ∧
    ∃ τ : P ≃ {g : StatedSU 3 3 F // orderOf g = 2},
      (∀ L : P, ∀ v ∈ L.1, v ≠ 0 → ∀ y,
        (((τ L : StatedSU 3 3 F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y =
          (2 : F) • E v y - y) ∧
      (∀ (g : StatedSU 3 3 F) (L L' : P), L'.1 = act g L.1 →
        (τ L' : StatedSU 3 3 F) = g * τ L * g⁻¹) ∧
      Nat.card P = 63 ∧
      (∀ L L' : P, ∃ g : StatedSU 3 3 F, act g L.1 = L'.1) ∧
      (∀ a b : StatedSU 3 3 F, orderOf a = 2 → orderOf b = 2 → IsConj a b) ∧
      (∀ L M : P, L ≠ M →
        ((τ L : StatedSU 3 3 F) * τ M = τ M * τ L ↔ ∀ x ∈ L.1, ∀ y ∈ M.1, h x y = 0)) ∧
      (∀ L M : P, L ≠ M → (∀ x ∈ L.1, ∀ y ∈ M.1, h x y = 0) →
        ∃ T : P, (T.1 : Set (Fin 3 → F)) = {y | ∀ x ∈ L.1 ⊔ M.1, h x y = 0} ∧
          (τ L : StatedSU 3 3 F) * τ M = τ T) ∧
      (∃ L₀ : P, L₀.1 = Submodule.span F {![1, 0, 0]}) ∧
      (∀ L₀ : P, L₀.1 = Submodule.span F {![1, 0, 0]} →
        (fun g : StatedSU 3 3 F => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ''
            (Subgroup.centralizer {(τ L₀ : StatedSU 3 3 F)} : Set (StatedSU 3 3 F)) =
          (fun A : GL (Fin 2) F => !![(A : Matrix (Fin 2) (Fin 2) F).det⁻¹, 0, 0;
            0, (A : Matrix (Fin 2) (Fin 2) F) 0 0, (A : Matrix (Fin 2) (Fin 2) F) 0 1;
            0, (A : Matrix (Fin 2) (Fin 2) F) 1 0, (A : Matrix (Fin 2) (Fin 2) F) 1 1]) '' U₂ ∧
        Nat.card (Subgroup.centralizer {(τ L₀ : StatedSU 3 3 F)}) = 96 ∧
        {g : StatedSU 3 3 F | g ∈ Subgroup.centralizer {(τ L₀ : StatedSU 3 3 F)} ∧
          orderOf g = 2}.ncard = 7) ∧
      ∀ g : StatedSU 3 3 F, (∀ L : P, act g L.1 = L.1) → g = 1 := by
  intro bar h P E act U₂
  have hU := unitaryFieldData_of_card hF
  have hB : ∀ u v : Fin 3 → F, gramForm hU (1 : Matrix (Fin 3) (Fin 3) F) u v = h u v :=
    gramForm_one_apply hU
  have hform : ∀ L : NonisoLine F, ∀ v ∈ L.1, v ≠ 0 → ∀ y,
      (((tauLine hU hF L : StatedSU 3 3 F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y =
        (2 : F) • E v y - y := fun L v hv hv0 y => by
    rw [tauLine_mulVec L hv hv0, tauLin_apply]
    show _ = (2 : F) • ((h v y / h v v) • v) - y
    rw [smul_smul, hB, hB]
  refine ⟨coe_statedSU hF, fun L v hv hv0 => ?_, fun L v hv w hw hv0 hw0 y => ?_,
    fun g L => ⟨lineAct hF g L, lineAct_val hF g L⟩, tauLineEquiv hU hF,
    fun L v hv hv0 y => hform L v hv hv0 y, fun g L L' hL' => ?_, card_nonisoLine hF,
    fun L L' => ?_, fun a b ha hb => isConj_of_orderOf_eq_two hF ha hb,
    fun L M hLM => ?_, fun L M hLM horth => ?_, ?_, fun L₀ hL₀ => ?_,
    fun g hg => eq_one_of_lineAct_eq hF g hg⟩
  · rw [← hB]
    exact gramForm_ne_zero_of_mem L hv hv0
  · rw [← hform L v hv hv0 y, ← hform L w hw hw0 y]
  · obtain rfl : L' = lineAct hF g L := Subtype.ext hL'
    exact tauLine_lineAct hU hF g L
  · obtain ⟨g, hg⟩ := lineAct_transitive hF L L'
    exact ⟨g, congrArg Subtype.val hg⟩
  · have := tauLine_commute_iff (h := hU) (hF := hF) hLM
    simp only [hB] at this
    exact this
  · simp only [← hB] at horth
    obtain ⟨T, hT, hmul⟩ := exists_tauLine_mul_eq (hF := hF) hLM horth
    simp only [hB] at hT
    exact ⟨T, hT, hmul⟩
  · have hv : gramForm hU (1 : Matrix (Fin 3) (Fin 3) F) ![1, 0, 0] ![1, 0, 0] ≠ 0 := by
      rw [gramForm_e0_left]
      exact one_ne_zero
    exact ⟨lineOf _ hv, rfl⟩
  · refine ⟨Set.ext fun M => ⟨?_, ?_⟩, card_centralizer_tauLine (hF := hF) hL₀,
      ncard_involutions_centralizer (hF := hF) hL₀⟩
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨A, hA, hgA⟩ := (mem_centralizer_tauLine_iff (hF := hF) hL₀ g).mp hg
      exact ⟨A, hA, hgA.symm⟩
    · rintro ⟨A, hA, rfl⟩
      exact ⟨blkSU hF A hA,
        (mem_centralizer_tauLine_iff (hF := hF) hL₀ _).mpr ⟨A, hA, rfl⟩, rfl⟩

end CFSG.LinearGroups.UnitaryThreeOverNine
