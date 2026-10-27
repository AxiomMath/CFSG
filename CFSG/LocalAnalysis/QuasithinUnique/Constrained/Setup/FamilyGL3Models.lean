module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Irred
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Matrix CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

abbrev Vec3 : Type := Fin 3 → ZMod 2

@[expose] def repTriv : GL32 →* (ZMod 2 ≃ₗ[ZMod 2] ZMod 2) := 1

@[expose] noncomputable def repV : GL32 →* (Vec3 ≃ₗ[ZMod 2] Vec3) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Vec3).toMonoidHom.comp
    Matrix.GeneralLinearGroup.toLin.toMonoidHom

theorem repV_apply (g : GL32) (v : Vec3) : repV g v = (g : Mat3) *ᵥ v := rfl

@[expose] def tauHom : GL32 →* GL32 where
  toFun g := ⟨((g⁻¹ : GL32) : Mat3)ᵀ, (g : Mat3)ᵀ, by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one], by
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by
    simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul])

theorem tauHom_val (g : GL32) : ((tauHom g : GL32) : Mat3) = ((g⁻¹ : GL32) : Mat3)ᵀ := rfl

theorem tauHom_tauHom (g : GL32) : tauHom (tauHom g) = g :=
  Units.ext (by
    change (((tauHom g)⁻¹ : GL32) : Mat3)ᵀ = (g : Mat3)
    change ((g : Mat3)ᵀ)ᵀ = (g : Mat3)
    exact Matrix.transpose_transpose _)

theorem tauHom_surjective : Function.Surjective tauHom :=
  Function.Involutive.surjective tauHom_tauHom

@[expose] noncomputable def repDual : GL32 →* (Vec3 ≃ₗ[ZMod 2] Vec3) := repV.comp tauHom

theorem repDual_apply (g : GL32) (v : Vec3) : repDual g v = ((g⁻¹ : GL32) : Mat3)ᵀ *ᵥ v := rfl

theorem mem_traceZero_iff_trace {X : Mat3} : X ∈ traceZero ↔ X.trace = 0 := by
  simp [traceZero]

theorem trace_conj (g : GL32) (X : Mat3) :
    ((g : Mat3) * X * ((g⁻¹ : GL32) : Mat3)).trace = X.trace := by
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem conj_mem_traceZero (g : GL32) {X : Mat3} (hX : X ∈ traceZero) :
    (g : Mat3) * X * ((g⁻¹ : GL32) : Mat3) ∈ traceZero := by
  rw [mem_traceZero_iff_trace] at hX ⊢
  rw [trace_conj, hX]

theorem mat_conj_inv_conj (g : GL32) (Y : Mat3) :
    (g : Mat3) * (((g⁻¹ : GL32) : Mat3) * Y * (g : Mat3)) * ((g⁻¹ : GL32) : Mat3) = Y := by
  have h1 : (g : Mat3) * ((g⁻¹ : GL32) : Mat3) = 1 := Units.mul_inv g
  calc (g : Mat3) * (((g⁻¹ : GL32) : Mat3) * Y * (g : Mat3)) * ((g⁻¹ : GL32) : Mat3)
      = ((g : Mat3) * ((g⁻¹ : GL32) : Mat3)) * Y * ((g : Mat3) * ((g⁻¹ : GL32) : Mat3)) := by
        simp only [Matrix.mul_assoc]
    _ = Y := by rw [h1, Matrix.one_mul, Matrix.mul_one]

theorem map_conjLin_traceZero (g : GL32) :
    traceZero.map (conjLin g).toLinearMap = traceZero := by
  refine le_antisymm ?_ fun Y hY => ?_
  · rintro _ ⟨X, hX, rfl⟩
    exact conj_mem_traceZero g hX
  · have hX : ((g⁻¹ : GL32) : Mat3) * Y * (g : Mat3) ∈ traceZero := by
      have := conj_mem_traceZero g⁻¹ hY
      rwa [inv_inv] at this
    exact ⟨_, hX, mat_conj_inv_conj g Y⟩

@[expose] noncomputable def conjA (g : GL32) : traceZero ≃ₗ[ZMod 2] traceZero :=
  (conjLin g).ofSubmodules traceZero traceZero (map_conjLin_traceZero g)

theorem conjA_apply (g : GL32) (X : traceZero) :
    ((conjA g X : traceZero) : Mat3) = (g : Mat3) * (X : Mat3) * ((g⁻¹ : GL32) : Mat3) := rfl

@[expose] noncomputable def repA : GL32 →* (traceZero ≃ₗ[ZMod 2] traceZero) where
  toFun := conjA
  map_one' := by
    refine LinearEquiv.ext fun X => Subtype.ext ?_
    rw [conjA_apply]
    simp
  map_mul' g h := by
    refine LinearEquiv.ext fun X => Subtype.ext ?_
    rw [LinearEquiv.mul_apply, conjA_apply, conjA_apply, conjA_apply]
    simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem repA_apply (g : GL32) (X : traceZero) :
    ((repA g X : traceZero) : Mat3) = (g : Mat3) * (X : Mat3) * ((g⁻¹ : GL32) : Mat3) := rfl

theorem isIrr_repTriv : IsIrrRep repTriv := by
  refine isIrrRep_of inferInstance fun N _ => ?_
  by_cases h : N = ⊥
  · exact Or.inl h
  · right
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff N).1 h
    have h1 : x = 1 := by
      have : ∀ y : ZMod 2, y ≠ 0 → y = 1 := by decide
      exact this x hx0
    rw [h1] at hx
    rw [eq_top_iff]
    intro y _
    have := N.smul_mem y hx
    rwa [smul_eq_mul, mul_one] at this

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem closure_natural : ∀ S : Finset Vec3, (0 : Vec3) ∈ S → (∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) →
    (∀ x ∈ S, unitri 1 0 0 *ᵥ x ∈ S) → (∀ x ∈ S, !![0, 0, 1; 1, 0, 0; 0, 1, 0] *ᵥ x ∈ S) →
      S = {0} ∨ S = Finset.univ := by
  decide +kernel

@[expose] def cycGL : GL32 :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide, by decide⟩

theorem isIrr_repV : IsIrrRep repV := by
  classical
  refine isIrrRep_of inferInstance fun N hN => ?_
  have hS := closure_natural (Finset.univ.filter fun v => v ∈ N) (by simp)
    (fun x hx y hy => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
      exact N.add_mem hx hy)
    (fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hN (unitriGL 1 0 0) x hx)
    (fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hN cycGL x hx)
  rcases hS with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ Finset.univ.filter fun v => v ∈ N := by simpa using hx
    rw [h] at this
    simpa using this
  · right
    rw [eq_top_iff]
    intro x _
    have : x ∈ Finset.univ.filter fun v => v ∈ N := by rw [h]; exact Finset.mem_univ x
    simpa using this

theorem isIrr_repDual : IsIrrRep repDual := isIrr_repV.comp_surjective tauHom_surjective

theorem isIrr_repA : IsIrrRep repA := by
  have hE31 : E31 ∈ traceZero := by
    rw [mem_traceZero_iff_trace]
    decide
  have hE31ne : E31 ≠ (0 : Mat3) := by decide
  have hnt : Nontrivial traceZero := ⟨⟨E31, hE31⟩, 0, fun h => hE31ne (congrArg Subtype.val h)⟩
  refine isIrrRep_of hnt fun N hN => ?_
  · have hB : N.map traceZero.subtype ≤ traceZero := by
      rintro _ ⟨n, _, rfl⟩
      exact n.2
    have hinv : ∀ g : GL32, ∀ X ∈ N.map traceZero.subtype,
        (g : Mat3) * X * ((g⁻¹ : GL32) : Mat3) ∈ N.map traceZero.subtype := by
      rintro g _ ⟨n, hn, rfl⟩
      exact ⟨repA g n, hN g n hn, rfl⟩
    rcases traceZero_irreducible hB hinv with h | h
    · left
      rw [eq_bot_iff]
      intro n hn
      have : (n : Mat3) ∈ N.map traceZero.subtype := ⟨n, hn, rfl⟩
      rw [h, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      exact Subtype.ext this
    · right
      rw [eq_top_iff]
      intro n _
      have : (n : Mat3) ∈ N.map traceZero.subtype := by rw [h]; exact n.2
      obtain ⟨n', hn', hn'eq⟩ := this
      have : n' = n := Subtype.ext hn'eq
      rw [← this]
      exact hn'

end CFSG.QuasithinUnique.Setup.Family
