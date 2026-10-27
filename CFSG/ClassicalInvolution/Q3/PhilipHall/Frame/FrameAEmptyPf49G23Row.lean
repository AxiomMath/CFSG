module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf49G3Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Core CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ComponentClassification.AS76b

section Model

theorem lieModel_g2_facts {X : Type} [Group X] {p f : ℕ} (hp2 : p ≠ 2)
    (hm : CFSG.Blueprint.LieModel X .G2 0 p f) :
    CFSG.IsQuasisimple X ∧
      ∀ a b : X, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 → ∃ c : X, c * a * c⁻¹ = b := by
  obtain ⟨hadm, K, _, _, hcard, ⟨e⟩⟩ := hm.chevalleyExceptionalModel (by decide)
  obtain ⟨hp, -, -, hq⟩ := hadm
  let e' : X ≃* ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K))).trans
      QuotientGroup.quotientBot)
  have h3 : 3 ≤ Nat.card K := by rw [hcard]; exact hq
  have hodd : Odd (Nat.card K) := by rw [hcard]; exact (hp.odd_of_ne_two hp2).pow
  refine ⟨CFSG.IsQuasisimple.of_mulEquiv e'
    (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card K h3), ?_⟩
  intro a b ha ha1 hb hb1
  have hea : e' a * e' a = 1 := by rw [← map_mul, ha, map_one]
  have heb : e' b * e' b = 1 := by rw [← map_mul, hb, map_one]
  obtain ⟨c, hc⟩ := CFSG.ClassicalInvolution.Balance.Bootstrap.g2_involutions_conj hodd hea heb
    (e'.map_ne_one_iff.mpr ha1) (e'.map_ne_one_iff.mpr hb1)
  refine ⟨e'.symm c, e'.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact hc

end Model

section Lift

variable {T : Type} [Group T] [Finite T]

theorem conj_of_oddQuot_involutions_conj {H : Subgroup T} {z : T}
    (hconj : ∀ a b : ↥H ⧸ classicalInvolutionOddCore ↥H, a * a = 1 → a ≠ 1 → b * b = 1 →
      b ≠ 1 → ∃ c, c * a * c⁻¹ = b)
    (hzH : z ∈ H) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    ∀ x ∈ H, x * x = 1 → x ≠ 1 → ∃ h ∈ H, h * z * h⁻¹ = x := by
  intro x hxH hx2 hx1
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥H)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥H
  set z' : ↥H := ⟨z, hzH⟩ with hz'
  set x' : ↥H := ⟨x, hxH⟩ with hx'
  have hz'2 : z' * z' = 1 := Subtype.ext hz2
  have hx'2 : x' * x' = 1 := Subtype.ext hx2
  have hne : ∀ y : ↥H, y * y = 1 → (y : T) ≠ 1 →
      QuotientGroup.mk' (classicalInvolutionOddCore ↥H) y ≠ 1 := fun y hy2 hy1 h =>
    hy1 (congrArg Subtype.val (T3Typed.eq_one_of_mul_self_of_mem_odd hodd
      ((QuotientGroup.eq_one_iff _).mp h) hy2))
  obtain ⟨c, hc⟩ := hconj (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) z')
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) x') (by rw [← map_mul, hz'2, map_one])
    (hne z' hz'2 hz1) (by rw [← map_mul, hx'2, map_one]) (hne x' hx'2 hx1)
  obtain ⟨h₁, hh₁⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥H) c
  have hconj' : QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (h₁ * z' * h₁⁻¹) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥H) x' := by
    rw [map_mul, map_mul, map_inv, hh₁]
    exact hc
  have hu2 : h₁ * z' * h₁⁻¹ * (h₁ * z' * h₁⁻¹) = 1 := by
    calc h₁ * z' * h₁⁻¹ * (h₁ * z' * h₁⁻¹) = h₁ * (z' * z') * h₁⁻¹ := by group
      _ = 1 := by rw [hz'2]; group
  obtain ⟨m, -, hm⟩ := exists_conj_of_map_eq_of_involutions hodd hu2 hx'2 hconj'
  refine ⟨((m * h₁ : ↥H) : T), (m * h₁).2, ?_⟩
  have := congrArg Subtype.val hm
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this ⊢
  have hx'v : (x' : T) = x := rfl
  have hz'v : (z' : T) = z := rfl
  rw [hz'v, hx'v] at this
  rw [← this]
  group

end Lift

section Section

theorem g2Section_of_rowG2 {T : Type} [Group T] [Finite T] {H : Subgroup T} {z : T}
    (hrow : Thm3RowG2 (⊤ : Subgroup ↥H)) (hzH : z ∈ H) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    G2Section H z := by
  obtain ⟨p, f, hp2, hm⟩ := hrow
  let E : SecQuot (⊤ : Subgroup ↥H) ≃* (↥H ⧸ classicalInvolutionOddCore ↥H) :=
    QuotientGroup.congr _ _ Subgroup.topEquiv
      (CFSG.ComponentClassification.OddCore.equiv_invariant Subgroup.topEquiv)
  obtain ⟨hq, hc⟩ := lieModel_g2_facts hp2 (hm.of_mulEquiv E)
  exact ⟨hq, conj_of_oddQuot_involutions_conj hc hzH hz2 hz1⟩

end Section

section Case

@[expose] def FrameC201G23Sec : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (R : Subgroup T) (t : T) (J : Subgroup T)
    (zK zJ : T), FrameCaseIHyps T R t J zK zJ → ∀ H : Subgroup T,
      omegaGen (aStar (CoreAssembly.conjClass R) R) = H →
        Thm3A.Thm3RowG23 (⊤ : Subgroup ↥H) → G2Section H zK

theorem g2Section_of_frameCaseIHyps {T : Type} [Group T] [Finite T] {R : Subgroup T} {t : T}
    {J : Subgroup T} {zK zJ : T} (hh : FrameCaseIHyps T R t J zK zJ) {H : Subgroup T}
    (hH : omegaGen (aStar (CoreAssembly.conjClass R) R) = H) (hrow : Thm3RowG2 (⊤ : Subgroup ↥H)) :
    G2Section H zK := by
  have hKS : R ∈ aStar (CoreAssembly.conjClass R) R := Relation.ReflTransGen.refl
  have hKH : R ≤ H := hH ▸ le_omegaGen hKS
  have hz : IsUniqueInvolution R zK := hh.viol.hzK
  exact g2Section_of_rowG2 hrow (hKH hz.mem) hz.sq hz.ne_one

theorem frameC201G23Sec_proved : FrameC201G23Sec :=
  fun _ _ _ _ _ _ _ _ hh _ hH hrow => g2Section_of_frameCaseIHyps hh hH hrow.toRowG2

end Case

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
