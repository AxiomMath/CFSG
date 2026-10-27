module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpClass
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.SharedRecog

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Datum

variable {T : Type} [Group T] [Finite T]

theorem classicalClause_of_datum {R : Subgroup T} {t : T} (hD : FrameTightDatum R t) :
    Q3CL.ClassicalClause (CoreAssembly.conjClass R) where
  subnormal := by
    rintro K ⟨g, rfl⟩
    have hz := hD.unique.conj g
    refine ⟨g * t * g⁻¹, hz.mem, orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one, ?_⟩
    exact isSubnormal_map_conj_centralizer hD.subnormal g
  commOdd := by
    rintro J ⟨g, rfl⟩ u a b hu hu2 huu ha hb hau hbu
    simp only at hu ha hb ⊢
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨S⟩ : Nonempty (Sylow 2 ↥R) := inferInstance
    obtain ⟨hdat, -⟩ := hD.q8TwinDatum S
    have hc := hD.tightCore_eq
    rw [AscFusion.oddCoreOf_conjSub' g R, mem_conjSub_iff]
    have hu' : g⁻¹ * u * g ∈ R := mem_conjSub_iff.mp hu
    have ha' : g⁻¹ * a * g ∈ R := mem_conjSub_iff.mp ha
    have hb' : g⁻¹ * b * g ∈ R := mem_conjSub_iff.mp hb
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
    have key := Frame.TwinPerp.commOdd_core hdat (u := g⁻¹ * u * g) (a := g⁻¹ * a * g)
      (b := g⁻¹ * b * g) (by rw [hc]; exact hu') hu2' huu' (by rw [hc]; exact ha')
      (by rw [hc]; exact hb') hau' hbu'
    rw [hc] at key
    have e : g⁻¹ * (a * b * a⁻¹ * b⁻¹) * g =
        (g⁻¹ * a * g) * (g⁻¹ * b * g) * (g⁻¹ * a * g)⁻¹ * (g⁻¹ * b * g)⁻¹ := by group
    rw [e]
    exact key

theorem frameIIHyp_of_datum (hnab : ∃ a b : T, a * b ≠ b * a) {R : Subgroup T} {t : T}
    (hD : FrameTightDatum R t) {J : Subgroup T} {zK zJ a g : T}
    (hv : AViol (CoreAssembly.conjClass R) R J zK zJ) (ha : a ∈ pairNormalizers R J zK zJ)
    (hac : a * zJ * a⁻¹ = zK) (hne : conjSub a J ≠ R) (hg : conjSub g R = conjSub a J)
    (hgK : g * zK * g⁻¹ = zK)
    (hs : aStar (CoreAssembly.conjClass R) R = CoreAssembly.conjClass R) :
    FrameIIHyp R J zK zJ a g := by
  have hgen : (⨆ M ∈ CoreAssembly.conjClass R, M) = ⊤ := by
    rw [iSup_range (f := fun g : T => conjSub g R) (g := fun M => M)]
    exact hD.selfGen
  exact ⟨hnab, hgen, hD.hyp, classicalClause_of_datum hD, hD.twoGroup,
    fun P hP => card_sylow_of_datum hD hP, hv, ha, hac, hne, hg, hgK, hs⟩

end Datum

end FrameAEmptyPf

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
