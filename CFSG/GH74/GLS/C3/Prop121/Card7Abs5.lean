module

public import CFSG.GH74.GLS.C3.Prop121.Card7Abs4

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace Ctx

variable {G : Type} [Group G] [Finite G] {C : Ctx G}

omit [Finite G] in
theorem ty_cases (hF : FFacts) (h : G) (hsw : C.s ∈ centralizer ({h * C.x * h⁻¹} : Set G)) :
    Ty3 (C.ιh h ⟨C.s, hsw⟩) ∨ Ty33 (C.ιh h ⟨C.s, hsw⟩) := by
  have h3 : (C.ιh h ⟨C.s, hsw⟩) ^ 3 = 1 := by
    have : (⟨C.s, hsw⟩ : ↥(centralizer ({h * C.x * h⁻¹} : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using C.s_pow_three)
    rw [← map_pow, this, map_one]
  have h1 : C.ιh h ⟨C.s, hsw⟩ ≠ 1 := by
    intro h'
    have h'' : (⟨C.s, hsw⟩ : ↥(centralizer ({h * C.x * h⁻¹} : Set G))) = 1 :=
      (C.ιh h).injective (by rw [h', map_one])
    exact C.s_ne_one (congrArg Subtype.val h'')
  exact hF.ord3 _ h3 h1

theorem exists_conj_X_B (hF : FFacts) (hH : HFacts) (Y : C.Y1) {w : G} (hw2 : orderOf w = 2)
    (hwy : w * Y.y1 = Y.y1 * w) (hws : w * C.s = C.s * w) (hx : IsConj C.x w) :
    ∃ c : G, c * C.s = C.s * c ∧ c * C.x * c⁻¹ = w := by
  obtain ⟨h, rfl⟩ := isConj_iff.1 hx
  have hsw : C.s ∈ centralizer ({h * C.x * h⁻¹} : Set G) :=
    mem_centralizer_singleton_iff.2 hws.symm
  have hyw : Y.y1 ∈ centralizer ({h * C.x * h⁻¹} : Set G) :=
    mem_centralizer_singleton_iff.2 hwy.symm
  rcases ty_cases hF h hsw with h3 | h33
  · exact C.exists_conj_x hF h hsw h3
  · exfalso
    set f' := C.ιh h ⟨C.s, hsw⟩ with hf'
    set b' := C.ιh h ⟨Y.y1, hyw⟩ with hb'
    have hcomm : b' * f' = f' * b' := by
      rw [hb', hf', ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext Y.y1_comm_s
    have hord : orderOf (⟨Y.y1, hyw⟩ : ↥(centralizer ({h * C.x * h⁻¹} : Set G))) = 2 := by
      rw [← Subgroup.orderOf_coe]; exact Y.orderOf_y1
    have hbinv : IsInv b' := by
      rw [isInv_iff_orderOf, hb', MulEquiv.orderOf_eq]
      exact hord
    have hne : ¬ IsConj Y.y1 (h * C.x * h⁻¹) := by
      intro hc
      apply Y.not_isConj_x
      have : IsConj Y.y1 C.x :=
        (CFSG.ShultStronglyClosedTI.InvolutionCounting.isConj_conj_iff (a := Y.y1) (b := C.x) h).1 hc
      exact isConj_comm.1 this
    have hn4 : nm7 (b' : Amb 7) ≠ 4 := fun h4 => hne ((C.lab_h h _ hord).2 h4)
    have hn8 : nm7 (b' : Amb 7) = 8 := by
      rcases hF.inv_nm b' hbinv with h4 | h8
      · exact absurd h4 hn4
      · exact h8
    have h12 := hF.c33 f' h33 b' hcomm ⟨hbinv, hn8⟩
    have hc3 : cc3 (h * C.x * h⁻¹) C.s Y.y1 = ccard F7 f' b' :=
      cc3_eq_ccard (a := h * C.x * h⁻¹) (u := C.s) (v := Y.y1) (C.ιh h) hsw hyw
    have hge := Y.ge_48 hH hwy hws hw2
    rw [cc3_swap13, hc3, h12] at hge
    omega

theorem exists_conj_Y_B (hH : HFacts) (Y : C.Y1) {w : G} (hw2 : orderOf w = 2)
    (hwy : w * Y.y1 = Y.y1 * w) (hws : w * C.s = C.s * w) (hx : ¬ IsConj C.x w) :
    ∃ c : G, c * C.s = C.s * c ∧ c * Y.y1 * c⁻¹ = w := by
  have hy0 : IsConj C.y0 w := (C.hcl w hw2).resolve_left hx
  have hy1 : IsConj Y.y1 w := Y.isConj_y0.symm.trans hy0
  obtain ⟨h, rfl⟩ := isConj_iff.1 hy1
  have hsw : C.s ∈ centralizer ({h * Y.y1 * h⁻¹} : Set G) :=
    mem_centralizer_singleton_iff.2 hws.symm
  set τw := (C.Ψh Y.h1) (conjCentEquiv Y.y1 h ⟨C.s, hsw⟩) with hτw
  have h3 : τw ^ 3 = 1 := by
    have : (⟨C.s, hsw⟩ : ↥(centralizer ({h * Y.y1 * h⁻¹} : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using C.s_pow_three)
    rw [hτw, ← map_pow, ← map_pow, this, map_one, map_one]
  have h1 : τw ≠ 1 := by
    intro h'
    have h'' : (⟨C.s, hsw⟩ : ↥(centralizer ({h * Y.y1 * h⁻¹} : Set G))) = 1 := by
      apply (conjCentEquiv Y.y1 h).injective
      apply (C.Ψh Y.h1).injective
      rw [← hτw, h', map_one, map_one]
    exact C.s_ne_one (congrArg Subtype.val h'')
  have hcc : cc3 (h * Y.y1 * h⁻¹) C.s C.s = ccard H11 τw τw :=
    cc3_eq_ccard (a := h * Y.y1 * h⁻¹) (u := C.s) (v := C.s)
      ((conjCentEquiv Y.y1 h).trans (C.Ψh Y.h1)) hsw hsw
  have hge : 48 ≤ cc3 (h * Y.y1 * h⁻¹) C.s C.s := by
    have := Y.ge_48 hH hwy hws hw2
    rw [cc3_swap13] at this
    exact this.trans (cc3_le_cc3 _ _ _)
  rcases hH.ord3 τw h3 h1 with ⟨hτ, -⟩ | hle
  · exact C.exists_conj_y hH Y h hsw hτ
  · rw [hcc] at hge
    omega

theorem exists_conj_X_or_Y (hF : FFacts) (hH : HFacts) (Y : C.Y1) (w : G) (hw : orderOf w = 2)
    (hws : w * C.s = C.s * w) :
    (∃ c : G, c * C.s = C.s * c ∧ c * C.x * c⁻¹ = w) ∨
      (∃ c : G, c * C.s = C.s * c ∧ c * Y.y1 * c⁻¹ = w) := by
  obtain ⟨c0, hc0, hc0y⟩ := exists_conj_mem_B hF hH Y w hw hws
  set w' := c0 * w * c0⁻¹ with hw'
  have hw'2 : orderOf w' = 2 := by
    rw [hw', show c0 * w * c0⁻¹ = MulAut.conj c0 w from rfl, MulEquiv.orderOf_eq]
    exact hw
  have hinv : c0⁻¹ * C.s = C.s * c0⁻¹ := by
    calc c0⁻¹ * C.s = c0⁻¹ * (C.s * c0) * c0⁻¹ := by group
      _ = c0⁻¹ * (c0 * C.s) * c0⁻¹ := by rw [hc0]
      _ = C.s * c0⁻¹ := by group
  have hw's : w' * C.s = C.s * w' := by
    calc w' * C.s = c0 * w * (c0⁻¹ * C.s) := by rw [hw']; group
      _ = c0 * w * (C.s * c0⁻¹) := by rw [hinv]
      _ = c0 * (w * C.s) * c0⁻¹ := by group
      _ = c0 * (C.s * w) * c0⁻¹ := by rw [hws]
      _ = (c0 * C.s) * (w * c0⁻¹) := by group
      _ = (C.s * c0) * (w * c0⁻¹) := by rw [hc0]
      _ = C.s * w' := by rw [hw']; group
  have key : ∀ (a : G) (c1 : G), c1 * C.s = C.s * c1 → c1 * a * c1⁻¹ = w' →
      (c0⁻¹ * c1) * C.s = C.s * (c0⁻¹ * c1) ∧ (c0⁻¹ * c1) * a * (c0⁻¹ * c1)⁻¹ = w := by
    intro a c1 hc1 hc1a
    refine ⟨?_, ?_⟩
    · calc c0⁻¹ * c1 * C.s = c0⁻¹ * (c1 * C.s) := by group
        _ = c0⁻¹ * (C.s * c1) := by rw [hc1]
        _ = (c0⁻¹ * C.s) * c1 := by group
        _ = (C.s * c0⁻¹) * c1 := by rw [hinv]
        _ = C.s * (c0⁻¹ * c1) := by group
    · calc c0⁻¹ * c1 * a * (c0⁻¹ * c1)⁻¹ = c0⁻¹ * (c1 * a * c1⁻¹) * c0 := by group
        _ = c0⁻¹ * w' * c0 := by rw [hc1a]
        _ = w := by rw [hw']; group
  by_cases hx : IsConj C.x w'
  · left
    obtain ⟨c1, hc1, hc1x⟩ := exists_conj_X_B hF hH Y hw'2 hc0y hw's hx
    exact ⟨c0⁻¹ * c1, (key C.x c1 hc1 hc1x).1, (key C.x c1 hc1 hc1x).2⟩
  · right
    obtain ⟨c1, hc1, hc1y⟩ := exists_conj_Y_B hH Y hw'2 hc0y hw's hx
    exact ⟨c0⁻¹ * c1, (key Y.y1 c1 hc1 hc1y).1, (key Y.y1 c1 hc1 hc1y).2⟩

theorem exists_conj_X (hF : FFacts) (hH : HFacts) (Y : C.Y1) {w : G} (hw : orderOf w = 2)
    (hws : w * C.s = C.s * w) (hx : IsConj C.x w) :
    ∃ c : G, c * C.s = C.s * c ∧ c * C.x * c⁻¹ = w := by
  rcases exists_conj_X_or_Y hF hH Y w hw hws with h | ⟨c, -, hc⟩
  · exact h
  · exfalso
    exact Y.not_isConj_x (hx.trans (isConj_iff.2 ⟨c, hc⟩).symm)

theorem exists_conj_Y (hF : FFacts) (hH : HFacts) (Y : C.Y1) {w : G} (hw : orderOf w = 2)
    (hws : w * C.s = C.s * w) (hx : ¬ IsConj C.x w) :
    ∃ c : G, c * C.s = C.s * c ∧ c * Y.y1 * c⁻¹ = w := by
  rcases exists_conj_X_or_Y hF hH Y w hw hws with ⟨c, -, hc⟩ | h
  · exact absurd (isConj_iff.2 ⟨c, hc⟩) hx
  · exact h

end Ctx

end CFSG.GH74.GLS.C3.Prop121.Card7
