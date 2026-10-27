module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosure

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace LinClosure

open Subgroup

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  (Γ : Subgroup (V ≃ₗ[K] V))

@[expose] def stabG (U : Submodule K V) : Subgroup Γ where
  carrier := {g | ∀ x, g • x ∈ U ↔ x ∈ U}
  mul_mem' {a b} ha hb := fun x => by rw [mul_smul, ha, hb]
  one_mem' := fun x => by simp
  inv_mem' {a} ha := fun x => by
    have := ha (a⁻¹ • x)
    rw [smul_inv_smul] at this
    exact this.symm

variable {Γ}

theorem ext_smul {g h : Γ} (H : ∀ x : V, g • x = h • x) : g = h :=
  Subtype.ext (LinearEquiv.ext H)

theorem smul_smul_K (g : Γ) (c : K) (x : V) : g • (c • x) = c • (g • x) :=
  map_smul (g : V ≃ₗ[K] V) c x

theorem mem_stabG_of_forall {U : Submodule K V} {g : Γ} (h1 : ∀ x ∈ U, g • x ∈ U)
    (h2 : ∀ x ∈ U, g⁻¹ • x ∈ U) : g ∈ stabG Γ U := fun x =>
  ⟨fun hx => by simpa using h2 _ hx, h1 x⟩

theorem smul_mem_of_mem_stabG {U : Submodule K V} {g : Γ} (hg : g ∈ stabG Γ U) {x : V}
    (hx : x ∈ U) : g • x ∈ U := (hg x).2 hx

theorem inv_smul_mem_of_mem_stabG {U : Submodule K V} {g : Γ} (hg : g ∈ stabG Γ U) {x : V}
    (hx : x ∈ U) : g⁻¹ • x ∈ U := smul_mem_of_mem_stabG ((stabG Γ U).inv_mem hg) hx

theorem mem_stabG_of_forall_fin [Finite V] {U : Submodule K V} {g : Γ}
    (h : ∀ x ∈ U, g • x ∈ U) : g ∈ stabG Γ U := by
  let f : U → U := fun x => ⟨g • x, h x x.2⟩
  have hf : Function.Injective f := fun a b hab =>
    Subtype.ext (MulAction.injective g (congrArg Subtype.val hab))
  have hs : Function.Surjective f := Finite.injective_iff_surjective.1 hf
  refine mem_stabG_of_forall h (fun x hx => ?_)
  obtain ⟨y, hy⟩ := hs ⟨x, hx⟩
  have : g • (y : V) = x := congrArg Subtype.val hy
  rw [← this, inv_smul_smul]
  exact y.2

theorem le_stabG_of_invariant {U : Submodule K V} {E : Subgroup Γ}
    (h : ∀ e ∈ E, ∀ x ∈ U, e • x ∈ U) : E ≤ stabG Γ U := fun e he =>
  mem_stabG_of_forall (h e he) (h e⁻¹ (E.inv_mem he))

section Flag

variable (Γ) (P : Submodule K V → Submodule K V)

@[expose] def flagU (W : Submodule K V) (hW : W ≤ P W) : Subgroup Γ where
  carrier := {g | (∀ x ∈ W, g • x = x) ∧ (∀ x ∈ P W, g • x - x ∈ W) ∧ ∀ x, g • x - x ∈ P W}
  mul_mem' {a b} ha hb := by
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x => ?_⟩
    · rw [mul_smul, hb.1 x hx, ha.1 x hx]
    · have hbx : b • x ∈ P W := by
        have := (P W).add_mem hx (hW (hb.2.1 x hx))
        simpa using this
      have := W.add_mem (ha.2.1 _ hbx) (hb.2.1 x hx)
      rw [mul_smul]
      simpa using this
    · have := (P W).add_mem (ha.2.2 (b • x)) (hb.2.2 x)
      rw [mul_smul]
      simpa using this
  one_mem' := ⟨fun x _ => one_smul _ x, fun x _ => by simp, fun x => by simp⟩
  inv_mem' {a} ha := by
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x => ?_⟩
    · have := ha.1 x hx
      calc a⁻¹ • x = a⁻¹ • (a • x) := by rw [this]
        _ = x := inv_smul_smul a x
    · have h3 := ha.2.2 (a⁻¹ • x)
      rw [smul_inv_smul] at h3
      have hy : a⁻¹ • x ∈ P W := by
        have := (P W).sub_mem hx h3
        simpa using this
      have h2 := ha.2.1 (a⁻¹ • x) hy
      rw [smul_inv_smul] at h2
      have := W.neg_mem h2
      simpa using this
    · have h3 := ha.2.2 (a⁻¹ • x)
      rw [smul_inv_smul] at h3
      have := (P W).neg_mem h3
      simpa using this

variable {Γ P} {W : Submodule K V} {hW : W ≤ P W}

theorem flagU_pow_four (h2 : (2 : K) = 0) {g : Γ} (hg : g ∈ flagU Γ P W hW) :
    g * g * g * g = 1 := by
  refine ext_smul fun x => ?_
  have hdbl : ∀ y : V, y + y = 0 := fun y => by rw [← two_smul K y, h2, zero_smul]
  have hb : g • x - x ∈ P W := hg.2.2 x
  have hw : g • (g • x - x) - (g • x - x) ∈ W := hg.2.1 _ hb
  rw [smul_sub] at hw
  set w := g • g • x - g • x - (g • x - x) with hwdef
  have hx2 : g • g • x = x + w := by
    have h : g • g • x - x - w = (g • x + g • x) - (x + x) := by rw [hwdef]; abel
    rw [hdbl, hdbl, sub_zero, sub_sub, sub_eq_zero] at h
    exact h
  have hgw : g • w = w := hg.1 w hw
  rw [one_smul, mul_smul, mul_smul, mul_smul, hx2, smul_add, smul_add, hgw, hgw, hx2, add_assoc,
    hdbl, add_zero]

theorem isPGroup_two_flagU (h2 : (2 : K) = 0) : IsPGroup 2 (flagU Γ P W hW) := by
  intro g
  refine ⟨2, ?_⟩
  apply Subtype.ext
  have := flagU_pow_four h2 g.2
  simpa [pow_succ] using this

variable (hP : ∀ {h : Γ}, h ∈ stabG Γ W → ∀ y, h • y ∈ P W ↔ y ∈ P W)
include hP

theorem conj_mem_flagU {h g : Γ} (hh : h ∈ stabG Γ W) (hg : g ∈ flagU Γ P W hW) :
    h * g * h⁻¹ ∈ flagU Γ P W hW := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x => ?_⟩
  · have hx' : h⁻¹ • x ∈ W := inv_smul_mem_of_mem_stabG hh hx
    rw [mul_smul, mul_smul, hg.1 _ hx', smul_inv_smul]
  · have hx' : h⁻¹ • x ∈ P W := (hP ((stabG Γ W).inv_mem hh) x).2 hx
    have := smul_mem_of_mem_stabG hh (hg.2.1 _ hx')
    rw [mul_smul, mul_smul]
    rwa [smul_sub, smul_inv_smul] at this
  · have := (hP hh _).2 (hg.2.2 (h⁻¹ • x))
    rw [mul_smul, mul_smul]
    rwa [smul_sub, smul_inv_smul] at this

theorem stabG_le_normalizer_flagU : stabG Γ W ≤ normalizer (flagU Γ P W hW : Set Γ) := by
  intro h hh
  rw [mem_normalizer_iff]
  intro g
  constructor
  · exact fun hg => conj_mem_flagU hP hh hg
  · intro hg
    have := conj_mem_flagU hP ((stabG Γ W).inv_mem hh) hg
    simpa [mul_assoc] using this

theorem stabG_le_twoLocalClosure (h2 : (2 : K) = 0) (hne : flagU Γ P W hW ≠ ⊥) {E : Subgroup Γ}
    (hE : E ≤ stabG Γ W) : stabG Γ W ≤ twoLocalClosure E :=
  le_iSup₂_of_le (normalizer (flagU Γ P W hW : Set Γ))
    ⟨⟨flagU Γ P W hW, hne, isPGroup_two_flagU h2, rfl⟩,
      hE.trans (stabG_le_normalizer_flagU hP)⟩ (stabG_le_normalizer_flagU hP)

end Flag

end LinClosure

end CFSG.LocalAnalysis.RankThreeUC
