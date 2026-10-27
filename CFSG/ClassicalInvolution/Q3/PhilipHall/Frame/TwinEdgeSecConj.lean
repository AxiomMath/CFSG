module

public import CFSG.ClassicalInvolution.Q3.TL3GlueMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm7RCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecDatum

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Conj

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem conjDatum (hd : Q8TwinDatum R S t) (g : Y) :
    ∃ S' : Sylow 2 ↥(conjSub g R), Q8TwinDatum (conjSub g R) S' (g * t * g⁻¹) ∧
      Nonempty ((S' : Subgroup ↥(conjSub g R)) ≃* (S : Subgroup R)) := by
  classical
  set σ : Y →* Y := (MulAut.conj g).toMonoidHom with hσ
  have hσinj : Function.Injective σ := (MulAut.conj g).injective
  set e : ↥R ≃* ↥(conjSub g R) := R.equivMapOfInjective σ hσinj with he
  set S' : Sylow 2 ↥(conjSub g R) := S.mapSurjective (f := e.toMonoidHom) e.surjective with hS'
  have hS'eq : (S' : Subgroup ↥(conjSub g R)) = (S : Subgroup R).map e.toMonoidHom := rfl
  have eS : (S : Subgroup R) ≃* (S' : Subgroup ↥(conjSub g R)) := by
    rw [hS'eq]
    exact (S : Subgroup R).equivMapOfInjective e.toMonoidHom e.injective
  have hσt : σ t = g * t * g⁻¹ := rfl
  have hcent : conjSub g R ≤ Subgroup.centralizer ({g * t * g⁻¹} : Set Y) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : r * t = t * r := Subgroup.mem_centralizer_singleton_iff.mp (hd.cent hr)
    show g * r * g⁻¹ * (g * t * g⁻¹) = g * t * g⁻¹ * (g * r * g⁻¹)
    calc g * r * g⁻¹ * (g * t * g⁻¹) = g * (r * t) * g⁻¹ := by group
      _ = g * (t * r) * g⁻¹ := by rw [h1]
      _ = g * t * g⁻¹ * (g * r * g⁻¹) := by group
  refine ⟨S', ⟨?_, ?_, ?_, hcent, ?_⟩, ⟨eS.symm⟩⟩
  · obtain ⟨r, hr, ⟨e'⟩⟩ := hd.quat
    exact ⟨r, hr, ⟨eS.symm.trans e'⟩⟩
  · obtain ⟨s, hs, rfl⟩ := hd.mem
    refine ⟨e s, ⟨s, hs, rfl⟩, rfl⟩
  · rw [← hσt]
    exact (orderOf_injective σ hσinj t).trans hd.order
  · have hO : (classicalInvolutionOddCore ↥R).map e.toMonoidHom =
        classicalInvolutionOddCore ↥(conjSub g R) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    exact hd.twoGroup.of_equiv (QuotientGroup.congr _ _ e hO)

end Conj

section Hyp

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {n : ℕ}

theorem twinCoreHyp_conj (h : TwinCoreHyp n Y R S t) (g : Y) :
    ∃ S' : Sylow 2 ↥(conjSub g R), TwinCoreHyp n Y (conjSub g R) S' (g * t * g⁻¹) := by
  obtain ⟨S', hd', ⟨e'⟩⟩ := conjDatum h.datum g
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hΩ := h.hyp.conjInvariant
  refine ⟨S', ⟨h.card, h.simple, h.nonab, h.below, h.tbelow, h.twinBelow, hd',
    ⟨e'.trans h.q8.some⟩, ?_, h.oddFree, ?_, ?_, ?_⟩⟩
  ·
    have hgen : (⨆ x : Y, conjSub x (tightCore R)) = ⊤ := h.gen
    unfold TightSelfGen
    rw [← conjSub_tightCore, eq_top_iff, ← hgen]
    refine iSup_le fun x => ?_
    have : conjSub x (tightCore R) = conjSub (x * g⁻¹) (conjSub g (tightCore R)) := by
      rw [← conjSub_mul]
      simp
    rw [this]
    exact le_iSup (fun y : Y => conjSub y (conjSub g (tightCore R))) (x * g⁻¹)
  · rw [hfam]
    exact h.hyp
  · rw [hfam, ← conjSub_tightCore]
    exact aEmpty_conj h.hyp.conjInvariant h.aEmpty g
  · rw [hfam, ← conjSub_tightCore]
    obtain ⟨K', hK', hne⟩ := h.twin
    refine ⟨conjSub g K', twinSet_conj h.hyp.conjInvariant hK' g, fun heq => hne ?_⟩
    exact Generic.conjSub_injective g heq

theorem twinCoreHyp_core (h : TwinCoreHyp n Y R S t) :
    ∃ S₀ : Sylow 2 ↥(tightCore R), TwinCoreHyp n Y (tightCore R) S₀ t := by
  obtain ⟨S₀, hd₀, ⟨e₀⟩⟩ := toCore h.datum
  have hid := tightCore_idem R
  refine ⟨S₀, ⟨h.card, h.simple, h.nonab, h.below, h.tbelow, h.twinBelow, hd₀,
    ⟨e₀.trans h.q8.some⟩, ?_, h.oddFree, ?_, ?_, ?_⟩⟩
  · unfold TightSelfGen
    rw [hid]
    exact h.gen
  · rw [hid]
    exact h.hyp
  · rw [hid]
    exact h.aEmpty
  · rw [hid]
    exact h.twin

end Hyp

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
