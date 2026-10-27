module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.NormNum.Ineq

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

variable {G : Type*} [Group G]

@[expose] def Partners (z : G) : Set G := {a | IsConj z a ∧ a ≠ z ∧ a * z = z * a}

theorem Partners.symm {z a : G} (h : a ∈ Partners z) : z ∈ Partners a :=
  ⟨h.1.symm, fun h' => h.2.1 h'.symm, h.2.2.symm⟩

theorem Partners.of_isConj {z a b : G} (ha : a ∈ Partners z) (hb : IsConj z b) (hba : b ≠ a)
    (hcomm : b * a = a * b) : b ∈ Partners a :=
  ⟨ha.1.symm.trans hb, hba, hcomm⟩

theorem Partners.mul_self_of {a x : G} (hx : x ∈ Partners a) (ha : a * a = 1) : x * x = 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hx.1
  calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
    _ = 1 := by rw [ha]; group

theorem mem_partners_conj_iff (g z a : G) :
    a ∈ Partners (g * z * g⁻¹) ↔ g⁻¹ * a * g ∈ Partners z := by
  have hz : IsConj z (g * z * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
  have ha : IsConj a (g⁻¹ * a * g) := isConj_iff.2 ⟨g⁻¹, by simp [mul_assoc]⟩
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · exact hz.trans (h1.trans ha)
    · intro h
      apply h2
      calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
        _ = g * z * g⁻¹ := by rw [h]
    · have := congrArg (fun x => g⁻¹ * x * g) h3
      simpa [mul_assoc] using this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · exact hz.symm.trans (h1.trans ha.symm)
    · intro h
      apply h2
      calc g⁻¹ * a * g = g⁻¹ * (g * z * g⁻¹) * g := by rw [h]
        _ = z := by group
    · have := congrArg (fun x => g * x * g⁻¹) h3
      simpa [mul_assoc] using this

structure SwapData (z : G) (n : ℕ) where
  S : Subgroup G
  ι : Equiv.Perm (Fin n) ≃* S
  cent : centralizer ({z} : Set G) = zpowers z ⊔ S
  disj : zpowers z ⊓ S = ⊥
  part : Partners z = {a : G | ∃ τ : Equiv.Perm (Fin n), τ.IsSwap ∧ a = (ι τ : G)}

namespace SwapData

variable {z : G} {n : ℕ}

theorem le_centralizer (D : SwapData z n) : D.S ≤ centralizer ({z} : Set G) := by
  rw [D.cent]
  exact le_sup_right

theorem comm_z (D : SwapData z n) {s : G} (hs : s ∈ D.S) : s * z = z * s :=
  mem_centralizer_singleton_iff.1 (D.le_centralizer hs)

theorem z_notMem (D : SwapData z n) (hz : z ≠ 1) : z ∉ D.S := by
  intro h
  have : z ∈ zpowers z ⊓ D.S := ⟨mem_zpowers z, h⟩
  rw [D.disj] at this
  exact hz (by simpa using this)

theorem centralizer_conj (g z : G) :
    centralizer ({g * z * g⁻¹} : Set G) =
      (centralizer ({z} : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_centralizer_singleton_iff, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [mem_centralizer_singleton_iff]
    have := congrArg (fun y => g⁻¹ * y * g) h
    simpa [mul_assoc] using this
  · rintro ⟨y, hy, rfl⟩
    have := mem_centralizer_singleton_iff.1 hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * y * g⁻¹ * (g * z * g⁻¹) = g * (y * z) * g⁻¹ := by group
      _ = g * (z * y) * g⁻¹ := by rw [this]
      _ = g * z * g⁻¹ * (g * y * g⁻¹) := by group

noncomputable def conj (D : SwapData z n) (g : G) : SwapData (g * z * g⁻¹) n where
  S := D.S.map (MulAut.conj g).toMonoidHom
  ι := D.ι.trans (MulEquiv.subgroupMap (MulAut.conj g) D.S)
  cent := by
    rw [centralizer_conj, D.cent, Subgroup.map_sup, MonoidHom.map_zpowers]
    simp
  disj := by
    have hz : zpowers (g * z * g⁻¹) = (zpowers z).map (MulAut.conj g).toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      simp
    rw [hz, ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, D.disj, Subgroup.map_bot]
  part := by
    ext a
    rw [mem_partners_conj_iff, D.part]
    constructor
    · rintro ⟨τ, hτ, h⟩
      refine ⟨τ, hτ, ?_⟩
      have h' : a = g * (D.ι τ : G) * g⁻¹ := by rw [← h]; group
      rw [h']
      change _ = (((MulEquiv.subgroupMap (MulAut.conj g) D.S) (D.ι τ) :
        D.S.map (MulAut.conj g).toMonoidHom) : G)
      rw [MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
    · rintro ⟨τ, hτ, h⟩
      refine ⟨τ, hτ, ?_⟩
      change a = (((MulEquiv.subgroupMap (MulAut.conj g) D.S) (D.ι τ) :
        D.S.map (MulAut.conj g).toMonoidHom) : G) at h
      rw [MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply] at h
      rw [h]
      group

theorem nonempty_of_isConj (D : SwapData z n) {a : G} (h : IsConj z a) :
    Nonempty (SwapData a n) := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 h
  exact ⟨D.conj g⟩

end SwapData

end CFSG.OddStandard.AltStdSec
