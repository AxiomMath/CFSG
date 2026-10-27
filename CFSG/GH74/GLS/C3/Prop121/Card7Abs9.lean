module

public import CFSG.GH74.GLS.C3.Prop121.Card7Abs8

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

theorem conj_comm_gen {G : Type*} [Group G] (c a b : G) (hc : c * b = b * c) (ha : a * b = b * a) :
    (c * a * c⁻¹) * b = b * (c * a * c⁻¹) := by
  have hinv : c⁻¹ * b = b * c⁻¹ := by
    calc c⁻¹ * b = c⁻¹ * (b * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * b) * c⁻¹ := by rw [hc]
      _ = b * c⁻¹ := by group
  calc c * a * c⁻¹ * b = c * a * (c⁻¹ * b) := by group
    _ = c * a * (b * c⁻¹) := by rw [hinv]
    _ = c * (a * b) * c⁻¹ := by group
    _ = c * (b * a) * c⁻¹ := by rw [ha]
    _ = (c * b) * a * c⁻¹ := by group
    _ = (b * c) * a * c⁻¹ := by rw [hc]
    _ = b * (c * a * c⁻¹) := by group

namespace Ctx

variable {G : Type} [Group G] [Finite G] {C : Ctx G}

theorem Y1.comm_iff (hH : HFacts) (Y : C.Y1) (d : ↥(centralizer ({Y.y1} : Set G))) :
    C.Ψh Y.h1 d * tau1 = tau1 * C.Ψh Y.h1 d ↔ (d : G) * C.s = C.s * (d : G) := by
  obtain ⟨hτ, -⟩ := Y.tau_cases hH
  have key : C.Ψh Y.h1 d * C.Ψh Y.h1 ⟨C.s, Y.mem_cent_y1⟩ =
      C.Ψh Y.h1 ⟨C.s, Y.mem_cent_y1⟩ * C.Ψh Y.h1 d ↔ (d : G) * C.s = C.s * (d : G) := by
    rw [← map_mul, ← map_mul, (C.Ψh Y.h1).injective.eq_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rcases hτ with h | h
  · rw [h] at key; exact key
  · rw [h] at key
    rw [← key]
    exact (Commute.inv_right_iff (a := C.Ψh Y.h1 d) (b := tau1)).symm

theorem Y1.X'_comm_inv (hH : HFacts) (Y : C.Y1) {a : H11} (ha : a ∈ Y.X') :
    a * tau1 = tau1 * a ∧ IsInv a := by
  obtain ⟨w, hw, ⟨hws, hw2, -⟩, rfl⟩ := ha
  exact ⟨Y.psi_comm_tau hH hw hws, Y.psi_isInv hw hw2⟩

omit [Finite G] in
theorem Y1.ystar_notMem_X' (hH : HFacts) (Y : C.Y1) : ystar ∉ Y.X' := by
  intro h
  rw [← Y.psi_y1 hH] at h
  have := (Y.mem_X'_iff ⟨Y.y1, Y.mem_self⟩).1 h
  exact Y.not_isConj_x this.2.2

theorem Y1.X'_closed (hH : HFacts) (Y : C.Y1) {a : H11} (ha : a ∈ Y.X') (g : H11)
    (hg : g * tau1 = tau1 * g) : g * a * g⁻¹ ∈ Y.X' := by
  obtain ⟨w, hw, hwA, rfl⟩ := ha
  obtain ⟨d, rfl⟩ := (C.Ψh Y.h1).surjective g
  have hds : (d : G) * C.s = C.s * (d : G) := (Y.comm_iff hH d).1 hg
  have hdy : (d : G) * Y.y1 = Y.y1 * (d : G) := mem_centralizer_singleton_iff.1 d.2
  have hcy : ((d : G) * w * (d : G)⁻¹) * Y.y1 = Y.y1 * ((d : G) * w * (d : G)⁻¹) :=
    conj_comm_gen _ _ _ hdy hw
  refine ⟨(d : G) * w * (d : G)⁻¹, hcy, ⟨conj_comm_gen _ _ _ hds hwA.1, ?_, ?_⟩, ?_⟩
  · rw [show (d : G) * w * (d : G)⁻¹ = MulAut.conj (d : G) w from rfl, MulEquiv.orderOf_eq]
    exact hwA.2.1
  · exact (CFSG.ShultStronglyClosedTI.InvolutionCounting.isConj_conj_iff (a := C.x) (b := w)
      (d : G)).2 hwA.2.2
  · unfold Y1.psi
    have : (⟨(d : G) * w * (d : G)⁻¹, mem_centralizer_singleton_iff.2 hcy⟩ :
        ↥(centralizer ({Y.y1} : Set G))) =
        d * ⟨w, mem_centralizer_singleton_iff.2 hw⟩ * d⁻¹ := Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv]

theorem Y1.ccard_X' (hH : HFacts) (Y : C.Y1) {b : H11} (hb : b ∈ Y.X') :
    ccard H11 tau1 b = 48 ∨ ccard H11 tau1 b = 96 := by
  have h1 := Y.X'_comm_inv hH hb
  have h2 : b ≠ ystar := fun h => Y.ystar_notMem_X' hH (h ▸ hb)
  exact hH.B0inv b h1.1 h1.2 h2

theorem Y1.card_X' (hF : FFacts) (hH : HFacts) (Y : C.Y1) : Nat.card ↥Y.X' = 18 := by
  classical
  have h96 : Nat.card {b : H11 // b ∈ Y.X' ∧ ccard H11 tau1 b = 96} = 6 := by
    rw [Ny_eq_two_Nx hF hH Y 96, hF.N96]
  have h48 : Nat.card {b : H11 // b ∈ Y.X' ∧ ccard H11 tau1 b = 48} = 12 := by
    rw [Ny_eq_two_Nx hF hH Y 48, hF.N48]
  have e : ↥Y.X' ≃ {b : H11 // b ∈ Y.X' ∧ ccard H11 tau1 b = 96} ⊕
      {b : H11 // b ∈ Y.X' ∧ ccard H11 tau1 b = 48} :=
    { toFun := fun b => if h : ccard H11 tau1 b.1 = 96 then Sum.inl ⟨b.1, b.2, h⟩ else
        Sum.inr ⟨b.1, b.2, by
          rcases Y.ccard_X' hH b.2 with h' | h'
          · exact h'
          · exact absurd h' h⟩
      invFun := fun s => Sum.elim (fun b => ⟨b.1, b.2.1⟩) (fun b => ⟨b.1, b.2.1⟩) s
      left_inv := by
        intro b
        by_cases h : ccard H11 tau1 b.1 = 96 <;> simp [h]
      right_inv := by
        intro s
        rcases s with b | b
        · have h := b.2.2
          simp [h]
        · have h : ¬ ccard H11 tau1 b.1 = 96 := by rw [b.2.2]; norm_num
          simp [h] }
  rw [Nat.card_congr e, Nat.card_sum, h96, h48]

end Ctx

end CFSG.GH74.GLS.C3.Prop121.Card7
