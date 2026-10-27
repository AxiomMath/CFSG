module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConnPrelude
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscAlpha
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpClass

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc


structure SettingR (r n : ℕ) {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R)
    (t₀ : Y) (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y) : Prop where
  core : TwinStdR r n Y R S t₀
  disc : ¬ Disconnected.DConnected (CoreAssembly.conjClass (tightCore R))
  data : Data (CoreAssembly.conjClass (tightCore R)) K K' z u J t W
  huW : u ∈ W

section Clause

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem TwinStdR.classicalClause (h : TwinStdR r n Y R S t) :
    Q3CL.ClassicalClause (CoreAssembly.conjClass (tightCore R)) where
  subnormal := by
    rintro K ⟨g, rfl⟩
    have hz := (Q8Datum.isUniqueInvolution_core h.datum).conj g
    refine ⟨g * t * g⁻¹, hz.mem, ?_, isSubnormal_of_hypOmegaGen h.hyp ⟨g, rfl⟩ hz⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  commOdd := by
    rintro J ⟨g, rfl⟩ u a b hu hu2 huu ha hb hau hbu
    simp only at hu ha hb ⊢
    rw [AscFusion.oddCoreOf_conjSub' g (tightCore R), mem_conjSub_iff]
    have hu' : g⁻¹ * u * g ∈ tightCore R := mem_conjSub_iff.mp hu
    have ha' : g⁻¹ * a * g ∈ tightCore R := mem_conjSub_iff.mp ha
    have hb' : g⁻¹ * b * g ∈ tightCore R := mem_conjSub_iff.mp hb
    have hu2' : IsPGroup 2 (Subgroup.zpowers (g⁻¹ * u * g)) := by
      have e : g⁻¹ * u * g = (MulAut.conj g⁻¹).toMonoidHom u := by simp
      rw [e, ← MonoidHom.map_zpowers]
      exact hu2.map _
    have huu' : (g⁻¹ * u * g) * (g⁻¹ * u * g) ≠ 1 := by
      intro h1
      apply huu
      have : u * u = g * ((g⁻¹ * u * g) * (g⁻¹ * u * g)) * g⁻¹ := by group
      rw [this, h1]; group
    have hau' : (g⁻¹ * a * g) * (g⁻¹ * u * g) = (g⁻¹ * u * g) * (g⁻¹ * a * g) := by
      calc (g⁻¹ * a * g) * (g⁻¹ * u * g) = g⁻¹ * (a * u) * g := by group
        _ = g⁻¹ * (u * a) * g := by rw [hau]
        _ = (g⁻¹ * u * g) * (g⁻¹ * a * g) := by group
    have hbu' : (g⁻¹ * b * g) * (g⁻¹ * u * g) = (g⁻¹ * u * g) * (g⁻¹ * b * g) := by
      calc (g⁻¹ * b * g) * (g⁻¹ * u * g) = g⁻¹ * (b * u) * g := by group
        _ = g⁻¹ * (u * b) * g := by rw [hbu]
        _ = (g⁻¹ * u * g) * (g⁻¹ * b * g) := by group
    have key := TwinPerp.commOdd_core h.datum hu' hu2' huu' ha' hb' hau' hbu'
    have e : g⁻¹ * (a * b * a⁻¹ * b⁻¹) * g =
        (g⁻¹ * a * g) * (g⁻¹ * b * g) * (g⁻¹ * a * g)⁻¹ * (g⁻¹ * b * g)⁻¹ := by group
    rw [e]
    exact key

theorem aEmpty_allR (h : TwinStdR r n Y R S t) :
    ∀ J ∈ CoreAssembly.conjClass (tightCore R), AEmpty (CoreAssembly.conjClass (tightCore R)) J := by
  rintro J ⟨g, rfl⟩
  exact aEmpty_conj h.hyp.conjInvariant h.aEmpty g

theorem partIHypGR (h : TwinStdR r n Y R S t) :
    Q3CL.PartIHypG (CoreAssembly.conjClass (tightCore R)) :=
  ⟨h.hyp, h.classicalClause, aEmpty_allR h⟩

end Clause

section Setup

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' J W : Subgroup Y} {z u t : Y}

theorem quat_conjClassR {k : ℕ} {K₀ : Subgroup Y}
    (h : ∃ P : Subgroup Y, IsSylow2In P K₀ ∧ Nonempty (↥P ≃* QuaternionGroup k)) :
    ∀ M ∈ CoreAssembly.conjClass K₀, ∀ P : Subgroup Y, IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup k) := by
  rintro _ ⟨g, rfl⟩
  apply forall_sylow_iso_of_exists
  obtain ⟨P, hP, ⟨e⟩⟩ := h
  exact ⟨conjSub g P, hP.conj g, ⟨(Subgroup.equivMapOfInjective P (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.trans e⟩⟩

theorem setup_membersR (s : SettingR r n R S t₀ K K' z u J t W) :
    (∀ M ∈ CoreAssembly.conjClass (tightCore R),
      IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) ∧
    (∀ M ∈ CoreAssembly.conjClass (tightCore R), ∀ P : Subgroup Y, IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2)))) ∧
    (∀ M ∈ CoreAssembly.conjClass (tightCore R), AEmpty (CoreAssembly.conjClass (tightCore R)) M) := by
  refine ⟨?_, ?_, aEmpty_allR s.core⟩
  · exact TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) s.core.datum.twoGroup)
  · refine quat_conjClassR ⟨_, s.core.datum.sylow_core, ⟨?_⟩⟩
    exact (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans
      s.core.quat.some

theorem center_eq_bot_R (h : TwinStdR r n Y R S t₀) : Subgroup.center Y = ⊥ :=
  PhilipHall.InductionBridge.center_eq_bot_of_fstar_simple h.simple h.nonab

theorem not_mem_center_of_ne_oneR (s : SettingR r n R S t₀ K K' z u J t W) {c : Y} (hc : c ≠ 1) :
    c ∉ Subgroup.center Y := by
  rw [center_eq_bot_R s.core]
  exact fun h => hc (Subgroup.mem_bot.mp h)

theorem isSolvable_members_R (h : TwinStdR r n Y R S t₀) :
    ∀ M ∈ CoreAssembly.conjClass (tightCore R), Group.IsSolvable ↥M := by
  rintro _ ⟨g, rfl⟩
  have hR := Q8Datum.isSolvable h.datum
  have hK : Group.IsSolvable ↥(tightCore R) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (tightCore_le R))
      (Subgroup.inclusion_injective _)
  exact isSolvable_conjSub_of hK g

@[expose] def TwinDiscBaseR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y) (K K' : Subgroup Y)
    (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    SettingR r n R S t₀ K K' z u J t W → AlphaSteps (CoreAssembly.conjClass (tightCore R))

theorem twinDiscBaseR_of (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n) : TwinDiscBaseR r n := by
  intro Y _ _ R S t₀ K K' z u J t W s
  exact ⟨s.core.hyp, TwinFrame.trans_conjClass _,
    hyp51_allR h4 hT s.core (center_eq_bot_R s.core) (isSolvable_members_R s.core)⟩

theorem alphaStepsR {n r : ℕ} (I : TwinDiscBaseR r n) (s : SettingR r n R S t₀ K K' z u J t W) :
    AlphaSteps (CoreAssembly.conjClass (tightCore R)) :=
  I Y R S t₀ K K' z u J t W s

end Setup

end CFSG.CGT.PushingUpLit.SolKNA.R4
