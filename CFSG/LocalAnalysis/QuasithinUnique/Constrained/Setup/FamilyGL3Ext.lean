module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Models
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SemidirectProduct

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace Matrix

noncomputable def invHom {K : Type*} [Group K] (σ : K) (hσ : σ * σ = 1) :
    Multiplicative (ZMod 2) →* K where
  toFun a := if a = 1 then 1 else σ
  map_one' := by simp
  map_mul' a b := by
    have h : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide
    have hh : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide
    have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
    rcases h a with rfl | rfl <;> rcases h b with rfl | rfl <;> simp [hh, hne, hσ]

theorem invHom_one {K : Type*} [Group K] (σ : K) (hσ : σ * σ = 1) : invHom σ hσ 1 = 1 := map_one _

theorem invHom_gen {K : Type*} [Group K] (σ : K) (hσ : σ * σ = 1) :
    invHom σ hσ (Multiplicative.ofAdd 1) = σ := by
  have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  simp [invHom, hne]

@[expose] def tauAut : MulAut GL32 where
  toFun := tauHom
  invFun := tauHom
  left_inv := tauHom_tauHom
  right_inv := tauHom_tauHom
  map_mul' := tauHom.map_mul

theorem tauAut_apply (g : GL32) : tauAut g = tauHom g := rfl

theorem tauAut_mul_self : tauAut * tauAut = 1 := MulEquiv.ext fun g => tauHom_tauHom g

@[expose] noncomputable def tauAction : Multiplicative (ZMod 2) →* MulAut GL32 :=
  invHom tauAut tauAut_mul_self

abbrev H32 : Type := GL32 ⋊[tauAction] Multiplicative (ZMod 2)

@[expose] noncomputable def tGen : H32 := SemidirectProduct.inr (Multiplicative.ofAdd 1)

@[expose] noncomputable def sIncl : GL32 →* H32 := SemidirectProduct.inl

theorem tGen_mul_self : tGen * tGen = 1 := by
  rw [tGen, ← map_mul]
  have : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide
  rw [this, map_one]

theorem tauAction_gen (g : GL32) : tauAction (Multiplicative.ofAdd 1) g = tauHom g := by
  simp only [tauAction, invHom_gen]
  rfl

theorem tGen_conj (g : GL32) : tGen * sIncl g * tGen⁻¹ = sIncl (tauHom g) := by
  have := SemidirectProduct.inl_aut (φ := tauAction) (Multiplicative.ofAdd 1) g
  rw [tGen, sIncl]
  rw [tauAction_gen] at this
  rw [this]
  simp

theorem tGen_mul_sIncl (g : GL32) : tGen * sIncl g = sIncl (tauHom g) * tGen := by
  rw [← tGen_conj]
  group

theorem exists_eq_sIncl_mul (h : H32) : h = sIncl h.left ∨ h = sIncl h.left * tGen := by
  have h0 : h = sIncl h.left * SemidirectProduct.inr h.right :=
    (SemidirectProduct.inl_left_mul_inr_right h).symm
  have hc : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide
  rcases hc h.right with h1 | h1
  · left
    calc h = sIncl h.left * SemidirectProduct.inr h.right := h0
      _ = sIncl h.left := by rw [h1, map_one, mul_one]
  · right
    calc h = sIncl h.left * SemidirectProduct.inr h.right := h0
      _ = sIncl h.left * tGen := by rw [h1]; rfl

abbrev P6 : Type := Vec3 × Vec3

@[expose] noncomputable def repPS : GL32 →* (P6 ≃ₗ[ZMod 2] P6) where
  toFun g := (repV g).prodCongr (repDual g)
  map_one' := LinearEquiv.ext fun x => by
    simp only [map_one]
    rfl
  map_mul' g h := LinearEquiv.ext fun x => by
    simp only [map_mul]
    rfl

@[expose] def swapP : P6 ≃ₗ[ZMod 2] P6 := LinearEquiv.prodComm (ZMod 2) Vec3 Vec3

theorem swapP_mul_self : swapP * swapP = 1 := LinearEquiv.ext fun _ => rfl

theorem repPS_apply (g : GL32) (x : P6) : repPS g x = (repV g x.1, repDual g x.2) := rfl

theorem repPS_tau (g : GL32) : repPS (tauHom g) = swapP * repPS g * swapP⁻¹ := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨u, w⟩ := x
  change (repV (tauHom g) u, repDual (tauHom g) w) = (repDual g u, repV g w)
  refine Prod.ext rfl ?_
  change repV (tauHom (tauHom g)) w = repV g w
  rw [tauHom_tauHom]

@[expose] noncomputable def repP : H32 →* (P6 ≃ₗ[ZMod 2] P6) :=
  SemidirectProduct.lift repPS (invHom swapP swapP_mul_self) (fun a => by
    have hc : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide
    rcases hc a with rfl | rfl
    · refine MonoidHom.ext fun g => ?_
      show repPS ((tauAction 1) g) = MulAut.conj (invHom swapP swapP_mul_self 1) (repPS g)
      rw [map_one tauAction, invHom_one]
      simp
    · refine MonoidHom.ext fun g => ?_
      show repPS ((tauAction (Multiplicative.ofAdd 1)) g) =
        MulAut.conj (invHom swapP swapP_mul_self (Multiplicative.ofAdd 1)) (repPS g)
      rw [invHom_gen, tauAction_gen, MulAut.conj_apply]
      exact repPS_tau g)

theorem repP_sIncl (g : GL32) : repP (sIncl g) = repPS g :=
  SemidirectProduct.lift_inl _ _ _ g

theorem repP_tGen : repP tGen = swapP := by
  rw [tGen, repP, SemidirectProduct.lift_inr, invHom_gen]

theorem map_transpose_traceZero :
    traceZero.map (Matrix.transposeLinearEquiv (Fin 3) (Fin 3) (ZMod 2) (ZMod 2)).toLinearMap =
      traceZero := by
  ext Y
  constructor
  · rintro ⟨X, hX, rfl⟩
    have hX' : X.trace = 0 := mem_traceZero_iff_trace.1 hX
    refine mem_traceZero_iff_trace.2 ?_
    change Xᵀ.trace = 0
    rwa [Matrix.trace_transpose]
  · intro hY
    have hY' : Y.trace = 0 := mem_traceZero_iff_trace.1 hY
    refine ⟨Yᵀ, mem_traceZero_iff_trace.2 ?_, Matrix.transpose_transpose Y⟩
    rwa [Matrix.trace_transpose]

@[expose] noncomputable def transQ : traceZero ≃ₗ[ZMod 2] traceZero :=
  (Matrix.transposeLinearEquiv (Fin 3) (Fin 3) (ZMod 2) (ZMod 2)).ofSubmodules traceZero
    traceZero map_transpose_traceZero

theorem transQ_apply (X : traceZero) : ((transQ X : traceZero) : Mat3) = (X : Mat3)ᵀ := rfl

theorem transQ_mul_self : transQ * transQ = 1 := LinearEquiv.ext fun X => Subtype.ext (by
  change ((X : Mat3)ᵀ)ᵀ = _
  exact Matrix.transpose_transpose _)

theorem repA_tau (g : GL32) : repA (tauHom g) = transQ * repA g * transQ⁻¹ := by
  have hinv : transQ⁻¹ = transQ := inv_eq_of_mul_eq_one_right transQ_mul_self
  rw [hinv]
  refine LinearEquiv.ext fun X => Subtype.ext ?_
  change (repA (tauHom g) X : Mat3) = ((transQ (repA g (transQ X)) : traceZero) : Mat3)
  rw [repA_apply, transQ_apply, repA_apply, transQ_apply]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, tauHom_val]
  rfl

@[expose] noncomputable def repQ : H32 →* (traceZero ≃ₗ[ZMod 2] traceZero) :=
  SemidirectProduct.lift repA (invHom transQ transQ_mul_self) (fun a => by
    have hc : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide
    rcases hc a with rfl | rfl
    · refine MonoidHom.ext fun g => ?_
      show repA ((tauAction 1) g) = MulAut.conj (invHom transQ transQ_mul_self 1) (repA g)
      rw [map_one tauAction, invHom_one]
      simp
    · refine MonoidHom.ext fun g => ?_
      show repA ((tauAction (Multiplicative.ofAdd 1)) g) =
        MulAut.conj (invHom transQ transQ_mul_self (Multiplicative.ofAdd 1)) (repA g)
      rw [invHom_gen, tauAction_gen, MulAut.conj_apply]
      exact repA_tau g)

theorem repQ_sIncl (g : GL32) : repQ (sIncl g) = repA g :=
  SemidirectProduct.lift_inl _ _ _ g

theorem repQ_tGen : repQ tGen = transQ := by
  rw [tGen, repQ, SemidirectProduct.lift_inr, invHom_gen]

@[expose] noncomputable def repHTriv : H32 →* (ZMod 2 ≃ₗ[ZMod 2] ZMod 2) := 1

theorem modIso_of_gens {E E' : Type*} [AddCommMonoid E] [Module (ZMod 2) E] [AddCommMonoid E']
    [Module (ZMod 2) E'] {ρ : H32 →* (E ≃ₗ[ZMod 2] E)} {ρ' : H32 →* (E' ≃ₗ[ZMod 2] E')}
    (f : E ≃ₗ[ZMod 2] E') (hS : ∀ g x, f (ρ (sIncl g) x) = ρ' (sIncl g) (f x))
    (hT : ∀ x, f (ρ tGen x) = ρ' tGen (f x)) : ModIso ρ ρ' := by
  refine ⟨f, fun h x => ?_⟩
  show f (ρ h x) = ρ' h (f x)
  rcases exists_eq_sIncl_mul h with h1 | h1
  · rw [h1]
    exact hS _ x
  · rw [h1, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hS, hT]

theorem isInvRep_of_gens {E : Type*} [AddCommMonoid E] [Module (ZMod 2) E]
    {ρ : H32 →* (E ≃ₗ[ZMod 2] E)} {N : Submodule (ZMod 2) E}
    (hS : ∀ g, ∀ x ∈ N, ρ (sIncl g) x ∈ N) (hT : ∀ x ∈ N, ρ tGen x ∈ N) :
    ∀ h, ∀ x ∈ N, ρ h x ∈ N := by
  intro h x hx
  rcases exists_eq_sIncl_mul h with h1 | h1
  · rw [h1]
    exact hS _ x hx
  · rw [h1, map_mul, LinearEquiv.mul_apply]
    exact hS _ _ (hT x hx)

@[expose] def lowerGL : GL32 :=
  ⟨!![1, 0, 0; 1, 1, 0; 0, 0, 1], !![1, 0, 0; 1, 1, 0; 0, 0, 1], by decide, by decide⟩

end CFSG.QuasithinUnique.Setup.Family