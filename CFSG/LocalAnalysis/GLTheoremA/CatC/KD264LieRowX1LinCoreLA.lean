module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

abbrev Inv2 (E : Subgroup (V ≃ₗ[ZMod 2] V)) (X : Submodule (ZMod 2) V) : Prop :=
  ∀ g ∈ E, ∀ x ∈ X, g x ∈ X

abbrev IsIrrE (E : Subgroup (V ≃ₗ[ZMod 2] V)) (X : Submodule (ZMod 2) V) : Prop :=
  X ≠ ⊥ ∧ ∀ Y : Submodule (ZMod 2) V, Y ≤ X → Inv2 E Y → Y = ⊥ ∨ Y = X

theorem natCast_zmod2_of_odd {n : ℕ} (h : Odd n) : (n : ZMod 2) = 1 := by
  obtain ⟨k, rfl⟩ := h
  have h2 : (2 : ZMod 2) = 0 := rfl
  push_cast
  rw [h2]
  simp

theorem exists_inv_compl (E : Subgroup (V ≃ₗ[ZMod 2] V)) [Fintype E]
    (hodd : Odd (Fintype.card E)) (X : Submodule (ZMod 2) V) (hX : Inv2 E X) :
    ∃ Y : Submodule (ZMod 2) V, Inv2 E Y ∧ IsCompl X Y := by
  classical
  obtain ⟨Y0, hY0⟩ := Submodule.exists_isCompl (K := ZMod 2) X
  let π : V →ₗ[ZMod 2] V := X.subtype ∘ₗ Submodule.projectionOnto X Y0 hY0
  have hπX : ∀ x ∈ X, π x = x := by
    intro x hx
    have h1 := Submodule.projectionOnto_apply_left (p := X) (q := Y0) hY0 ⟨x, hx⟩
    simp only [π, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [show (Submodule.projectionOnto X Y0 hY0 x : V) = x from by
      have h2 : Submodule.projectionOnto X Y0 hY0 x = ⟨x, hx⟩ := h1
      rw [h2]]
  have hπmem : ∀ v, π v ∈ X := fun v => (Submodule.projectionOnto X Y0 hY0 v).2
  let P : V →ₗ[ZMod 2] V := ∑ g : E,
    ((g : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) ∘ₗ π ∘ₗ
      (((g⁻¹ : E) : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V)
  have hPapply : ∀ v, P v = ∑ g : E,
      (g : V ≃ₗ[ZMod 2] V) (π (((g⁻¹ : E) : V ≃ₗ[ZMod 2] V) v)) := by
    intro v
    simp only [P, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply]
    rfl
  have hPmem : ∀ v, P v ∈ X := by
    intro v
    rw [hPapply]
    exact Submodule.sum_mem _ fun g _ => hX _ g.2 _ (hπmem _)
  have hPX : ∀ x ∈ X, P x = x := by
    intro x hx
    rw [hPapply]
    have hterm : ∀ g : E, (g : V ≃ₗ[ZMod 2] V) (π (((g⁻¹ : E) : V ≃ₗ[ZMod 2] V) x)) = x := by
      intro g
      have hgx : ((g⁻¹ : E) : V ≃ₗ[ZMod 2] V) x ∈ X := hX _ (g⁻¹ : E).2 x hx
      rw [hπX _ hgx]
      rw [show ((g⁻¹ : E) : V ≃ₗ[ZMod 2] V) = ((g : V ≃ₗ[ZMod 2] V))⁻¹ from rfl]
      rw [LinearEquiv.coe_inv]
      exact (g : V ≃ₗ[ZMod 2] V).apply_symm_apply x
    simp only [hterm]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul (ZMod 2),
      natCast_zmod2_of_odd hodd, one_smul]
  have hPinv : ∀ h ∈ E, ∀ v, P (h v) = h (P v) := by
    intro h hh v
    rw [hPapply, hPapply, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨h, hh⟩ : E)⁻¹) _ _ (fun g => ?_)
    set k : E := (⟨h, hh⟩ : E)⁻¹ * g with hk
    have hkinv : ((k⁻¹ : E) : V ≃ₗ[ZMod 2] V) = ((g : V ≃ₗ[ZMod 2] V))⁻¹ * (⟨h, hh⟩ : E) := by
      rw [hk]
      simp [mul_inv_rev]
    have hkv : ((k : V ≃ₗ[ZMod 2] V)) = ((⟨h, hh⟩ : E) : V ≃ₗ[ZMod 2] V)⁻¹ * (g : V ≃ₗ[ZMod 2] V) := by
      rw [hk]
      simp
    show (g : V ≃ₗ[ZMod 2] V) (π (((g⁻¹ : E) : V ≃ₗ[ZMod 2] V) (h v))) =
      (h : V ≃ₗ[ZMod 2] V) (((k : V ≃ₗ[ZMod 2] V)) (π (((k⁻¹ : E) : V ≃ₗ[ZMod 2] V) v)))
    rw [hkv, hkinv]
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply,
      LinearEquiv.symm_apply_apply]
    rfl
  let Y : Submodule (ZMod 2) V := LinearMap.ker P
  have hY : Inv2 E Y := by
    intro g hg y hy
    show P (g y) = 0
    rw [hPinv g hg, show P y = 0 from hy, map_zero]
  refine ⟨Y, hY, ?_, ?_⟩
  · refine Submodule.disjoint_def.2 fun x hxX hxY => ?_
    have h1 : P x = 0 := hxY
    rw [hPX x hxX] at h1
    exact h1
  · refine codisjoint_iff.2 (eq_top_iff.2 fun v _ => ?_)
    refine Submodule.mem_sup.2 ⟨P v, hPmem v, v - P v, ?_, by abel⟩
    show P (v - P v) = 0
    rw [map_sub, hPX _ (hPmem v), sub_self]

theorem exists_inv_compl_within (E : Subgroup (V ≃ₗ[ZMod 2] V)) [Fintype E]
    (hodd : Odd (Fintype.card E)) {W X : Submodule (ZMod 2) V} (hW : Inv2 E W) (hXW : X ≤ W)
    (hX : Inv2 E X) :
    ∃ Y : Submodule (ZMod 2) V, Y ≤ W ∧ Inv2 E Y ∧ X ⊔ Y = W ∧ X ⊓ Y = ⊥ := by
  obtain ⟨Y0, hY0, hc⟩ := exists_inv_compl E hodd X hX
  refine ⟨Y0 ⊓ W, inf_le_right, fun g hg y hy => ⟨hY0 g hg y hy.1, hW g hg y hy.2⟩, ?_, ?_⟩
  · refine le_antisymm (sup_le hXW inf_le_right) fun w hw => ?_
    have hw' : w ∈ X ⊔ Y0 := by rw [hc.sup_eq_top]; trivial
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hw'
    have hyW : y ∈ W := by
      have hyeq : y = w - x := by rw [← hxy]; abel
      rw [hyeq]
      exact W.sub_mem hw (hXW hx)
    exact Submodule.mem_sup.2 ⟨x, hx, y, ⟨hy, hyW⟩, hxy⟩
  · exact disjoint_iff.1 (hc.disjoint.mono_right inf_le_left)

theorem exists_irr_le (E : Subgroup (V ≃ₗ[ZMod 2] V)) {W : Submodule (ZMod 2) V}
    (hW : Inv2 E W) (hne : W ≠ ⊥) :
    ∃ X : Submodule (ZMod 2) V, X ≤ W ∧ Inv2 E X ∧ IsIrrE E X := by
  classical
  let p : ℕ → Prop := fun n => ∃ Y : Submodule (ZMod 2) V, Y ≤ W ∧ Inv2 E Y ∧ Y ≠ ⊥ ∧
    Module.finrank (ZMod 2) Y = n
  have hp : ∃ n, p n := ⟨_, W, le_rfl, hW, hne, rfl⟩
  obtain ⟨Y, hYW, hYinv, hYne, hYn⟩ := Nat.find_spec hp
  refine ⟨Y, hYW, hYinv, hYne, fun Z hZY hZinv => ?_⟩
  by_cases hZ : Z = ⊥
  · exact Or.inl hZ
  · right
    have hmin : Nat.find hp ≤ Module.finrank (ZMod 2) Z :=
      Nat.find_min' hp ⟨Z, hZY.trans hYW, hZinv, hZ, rfl⟩
    have hle : Module.finrank (ZMod 2) Z ≤ Module.finrank (ZMod 2) Y :=
      Submodule.finrank_mono hZY
    exact Submodule.eq_of_le_of_finrank_eq hZY (by omega)

theorem iSup_cons_eq {k : ℕ} (A : Submodule (ZMod 2) V) (Z : Fin k → Submodule (ZMod 2) V) :
    (⨆ i, (Fin.cons A Z : Fin (k + 1) → Submodule (ZMod 2) V) i) = A ⊔ ⨆ i, Z i := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp only [Fin.cons_succ]
      exact le_sup_of_le_right (le_iSup Z j)
  · refine sup_le ?_ (iSup_le fun j => ?_)
    · have := le_iSup (fun i => (Fin.cons A Z : Fin (k + 1) → Submodule (ZMod 2) V) i) 0
      simpa using this
    · have := le_iSup (fun i => (Fin.cons A Z : Fin (k + 1) → Submodule (ZMod 2) V) i) j.succ
      simpa using this

theorem iSupIndep_cons {k : ℕ} (A : Submodule (ZMod 2) V) (Z : Fin k → Submodule (ZMod 2) V)
    (hZ : iSupIndep Z) (hA : Disjoint A (⨆ i, Z i)) :
    iSupIndep (Fin.cons A Z : Fin (k + 1) → Submodule (ZMod 2) V) := by
  rw [iSupIndep_def]
  intro i
  refine Fin.cases ?_ (fun l => ?_) i
  · have hrest : (⨆ (j : Fin (k + 1)) (_ : j ≠ 0),
        (Fin.cons A Z : Fin (k + 1) → Submodule (ZMod 2) V) j) = ⨆ m, Z m := by
      apply le_antisymm
      · refine iSup₂_le fun j hj => ?_
        induction j using Fin.cases with
        | zero => exact absurd rfl hj
        | succ m =>
          simp only [Fin.cons_succ]
          exact le_iSup Z m
      · refine iSup_le fun m => ?_
        exact le_iSup₂_of_le (Fin.succ m) (Fin.succ_ne_zero m) (by simp)
    simp only [Fin.cons_zero]
    rw [hrest]
    exact hA
  · set S : Submodule (ZMod 2) V := ⨆ (m : Fin k) (_ : m ≠ l), Z m with hS
    have hrest : (⨆ (j : Fin (k + 1)) (_ : j ≠ l.succ),
        (Fin.cons A Z : Fin (k + 1) → Submodule (ZMod 2) V) j) = A ⊔ S := by
      apply le_antisymm
      · refine iSup₂_le fun j hj => ?_
        induction j using Fin.cases with
        | zero => exact le_sup_left
        | succ m =>
          simp only [Fin.cons_succ]
          have hm : m ≠ l := fun h => hj (by rw [h])
          exact le_sup_of_le_right (le_iSup₂_of_le m hm le_rfl)
      · refine sup_le ?_ (iSup₂_le fun m hm => ?_)
        · exact le_iSup₂_of_le (0 : Fin (k + 1)) (Fin.succ_ne_zero l).symm (by simp)
        · exact le_iSup₂_of_le (Fin.succ m) (fun h => hm (Fin.succ_injective _ h))
            (by simp)
    have hdZ : Disjoint (Z l) S := iSupIndep_def.1 hZ l
    have hSY : S ≤ ⨆ m, Z m := iSup₂_le fun m _ => le_iSup Z m
    have hZY : Z l ≤ ⨆ m, Z m := le_iSup Z l
    rw [hrest]
    rw [disjoint_iff] at hdZ hA ⊢
    have h2 : Z l ⊓ (A ⊔ S) ≤ S := by
      calc Z l ⊓ (A ⊔ S) ≤ (A ⊔ S) ⊓ (⨆ m, Z m) := by
            rw [inf_comm]; exact inf_le_inf_left _ hZY
        _ = S ⊔ (A ⊓ ⨆ m, Z m) := by rw [sup_comm]; exact sup_inf_assoc_of_le A hSY
        _ = S := by rw [hA, sup_bot_eq]
    exact le_antisymm (le_trans (le_inf inf_le_left h2) (le_of_eq hdZ)) bot_le

theorem exists_decomp (E : Subgroup (V ≃ₗ[ZMod 2] V)) [Fintype E] (hodd : Odd (Fintype.card E)) :
    ∀ (n : ℕ) (W : Submodule (ZMod 2) V), Inv2 E W → Module.finrank (ZMod 2) W = n →
    ∃ (k : ℕ) (X : Fin k → Submodule (ZMod 2) V), (∀ i, Inv2 E (X i) ∧ IsIrrE E (X i)) ∧
      (∀ i, X i ≤ W) ∧ iSupIndep X ∧ iSup X = W ∧
      Module.finrank (ZMod 2) W = ∑ i, Module.finrank (ZMod 2) (X i) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hW hWn
  by_cases hbot : W = ⊥
  · subst hbot
    refine ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      iSupIndep_def.2 fun i => i.elim0, by simp, by simp⟩
  · obtain ⟨X₀, hX₀W, hX₀inv, hX₀irr⟩ := exists_irr_le E hW hbot
    obtain ⟨Y, hYW, hYinv, hsup, hinf⟩ := exists_inv_compl_within E hodd hW hX₀W hX₀inv
    have hfr : Module.finrank (ZMod 2) W =
        Module.finrank (ZMod 2) X₀ + Module.finrank (ZMod 2) Y := by
      rw [← hsup]
      have := Submodule.finrank_sup_add_finrank_inf_eq X₀ Y
      rw [hinf, finrank_bot] at this
      omega
    have hX₀pos : 0 < Module.finrank (ZMod 2) X₀ :=
      Nat.pos_of_ne_zero fun h => hX₀irr.1 (Submodule.finrank_eq_zero.1 h)
    have hYlt : Module.finrank (ZMod 2) Y < n := by omega
    obtain ⟨k, Z, hZirr, hZW, hZind, hZsup, hZfr⟩ := ih _ hYlt Y hYinv rfl
    refine ⟨k + 1, Fin.cons X₀ Z, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ⟨hX₀inv, hX₀irr⟩
      · simpa using hZirr j
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hX₀W
      · simpa using (hZW j).trans hYW
    · refine iSupIndep_cons X₀ Z hZind ?_
      rw [hZsup]
      exact disjoint_iff.2 hinf
    · rw [iSup_cons_eq, hZsup, hsup]
    · rw [Fin.sum_univ_succ, hfr, hZfr]
      rfl

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore

end
