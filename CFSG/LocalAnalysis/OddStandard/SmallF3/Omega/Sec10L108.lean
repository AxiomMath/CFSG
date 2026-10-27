module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Aux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L108a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L108b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Statements2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Conj

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem asc82Lemma108_of (h106 : Asc82Lemma106) (hb : Asc82Basic10) (hO5 : Asc82FactOut5)
    (hN7 : Asc82FactN7) : Asc82Lemma108 := by
  intro G _ _ t L S z K1 K2 hctx g
  set x : G := g⁻¹ * t * g with hxdef
  intro hxL
  obtain ⟨hpsp, -, htnotL, htS, hSN, hsylL⟩ := hb G t L S z hctx.toSec10Z
  have hsyl : IsSylow2Of S (centralizer ({t} : Set G)) := hctx.sylow
  have hS : IsPGroup 2 S := hsyl.2.1
  have hLC : L ⊓ centralizer (L : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_psp43 hctx.component.isQuasisimple hpsp
  have hSC : centralizer (L : Set G) ⊓ S = zpowers t := h106 G t L S z K1 K2 hctx
  have hI : (L ⊔ centralizer (L : Set G)).relIndex (normalizer (L : Set G)) ≤ 2 :=
    hO5 G L hpsp
  have hU : S ⊓ (L ⊔ centralizer (L : Set G)) ≤ (S ⊓ L) ⊔ zpowers t :=
    sec10_inf_join_le hS hsylL hLC hSC
  have hc : ∀ s ∈ S, s * t = t * s := by
    intro s hs
    exact ((Subgroup.mem_centralizer_iff.mp (hsyl.1 hs)) t (by simp)).symm
  have hcommL : ∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ * s₂ * s₁⁻¹ * s₂⁻¹ ∈ L :=
    sec10_comm_mem_L hSN hI hU htS hc
  have hSS : ⁅S, S⁆ ≤ L :=
    Subgroup.commutator_le.mpr fun s₁ hs₁ s₂ hs₂ => by
      rw [commutatorElement_def]
      exact hcommL s₁ hs₁ s₂ hs₂
  have hx2 : orderOf x = 2 := by
    have h1 : orderOf ((MulAut.conj g⁻¹) t) = orderOf t := MulEquiv.orderOf_eq _ _
    have h2 : (MulAut.conj g⁻¹) t = x := by
      rw [hxdef, MulAut.conj_apply]
      group
    rw [h2, hctx.involution] at h1
    exact h1
  obtain ⟨P', hP'⟩ := exists_isSylow2Of (L ⊓ centralizer ({x} : Set G))
  have hxP' : x ∈ ⁅P', P'⁆ := hN7 G L hpsp x hxL hx2 P' hP'
  obtain ⟨S', hS', hP'S'⟩ :=
    exists_isSylow2Of_ge hP'.2.1 (hP'.1.trans inf_le_right)
  have hxS' : x ∈ ⁅S', S'⁆ := Subgroup.commutator_mono hP'S' hP'S' hxP'
  have hconjSyl : IsSylow2Of (CFSG.conjugate S g) (centralizer ({x} : Set G)) := by
    have h := hsyl.conjugate g
    rwa [conjugate_centralizer_singleton t g, ← hxdef] at h
  obtain ⟨a, ha, hiff⟩ := IsSylow2Of.exists_conj_mem hconjSyl hS'
  have hax : a * x = x * a := ((Subgroup.mem_centralizer_iff.mp ha) x (by simp)).symm
  let φ : MulAut G := MulAut.conj (g * a⁻¹)
  have hφapply : ∀ y : G, φ y = g * (a⁻¹ * y * a) * g⁻¹ := by
    intro y
    show MulAut.conj (g * a⁻¹) y = g * (a⁻¹ * y * a) * g⁻¹
    rw [MulAut.conj_apply]
    group
  have hφiff : ∀ y : G, y ∈ S' ↔ φ y ∈ S := by
    intro y
    have h1 : y ∈ S' ↔ a⁻¹ * y * a ∈ CFSG.conjugate S g := hiff y
    rw [h1, mem_conjugate_iff']
    constructor
    · intro h
      rwa [← hφapply y] at h
    · intro h
      rwa [hφapply y] at h
  have hφS' : S'.map φ.toMonoidHom = S := by
    ext w
    rw [Subgroup.mem_map_equiv]
    simpa using hφiff (φ.symm w)
  have hφx : φ x = t := by
    rw [hφapply x]
    have hax' : a⁻¹ * x * a = x := by
      calc a⁻¹ * x * a = a⁻¹ * (x * a) := by group
        _ = a⁻¹ * (a * x) := by rw [← hax]
        _ = x := by group
    rw [hax', hxdef]
    group
  have htSS : t ∈ ⁅S, S⁆ := by
    have hmem : φ x ∈ (⁅S', S'⁆).map φ.toMonoidHom :=
      Subgroup.mem_map_of_mem φ.toMonoidHom hxS'
    rw [Subgroup.map_commutator, hφS', hφx] at hmem
    exact hmem
  exact htnotL (hSS htSS)

end CFSG.OddStandard.SmallF3.Omega