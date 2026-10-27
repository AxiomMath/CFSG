module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpClass
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz
public import CFSG.ClassicalInvolution.Q3.Q3T7C231Final

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

structure CoreData (n : ℕ) (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R)
    (t : Y) : Prop where
  card : Nat.card Y = n
  simple : IsSimpleGroup ↥(genFittingFStar Y)
  nonab : ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a
  below : CIT3Below n
  tbelow : TightBelow n
  datum : QuaternionBridge.Q8TwinDatum R S t
  q8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)
  gen : TightSelfGen R
  oddFree : TightOddFree Y
  hyp : HypOmegaGen (CoreAssembly.conjClass (tightCore R))
  aEmpty : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R)
  twin : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), K' ≠ tightCore R

theorem CoreData.of_S (h : TwinCoreHypS n Y R S t) : CoreData n Y R S t :=
  ⟨h.card, h.simple, h.nonab, h.below, h.tbelow, h.datum, h.q8, h.gen, h.oddFree, h.hyp, h.aEmpty,
    h.twin⟩

structure PerpHypS (n : ℕ) (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R)
    (t : Y) : Prop where
  core : TwinCoreHypS n Y R S t
  disc : ¬ Disconnected.DConnected (CoreAssembly.conjClass (tightCore R))
  perp : KPerp (CoreAssembly.conjClass (tightCore R)) (tightCore R) =
    twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R)

theorem twinCorePerpSE'_iff {n : ℕ} :
    TwinCorePerpSE' n ↔
      ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
        PerpHypS n Y R S t → TwinE4 Y ∨ LongFundSetE3 R t :=
  ⟨fun h Y _ _ R S t hP => h Y R S t hP.core hP.disc hP.perp,
    fun h Y _ _ R S t hc hd hp => h Y R S t ⟨hc, hd, hp⟩⟩

theorem CoreData.classicalClause (h : CoreData n Y R S t) :
    Q3CL.ClassicalClause (CoreAssembly.conjClass (tightCore R)) where
  subnormal := by
    rintro K ⟨g, rfl⟩
    have hz := (Inner.isUniqueInvolution_core h.datum).conj g
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
    have key := commOdd_core h.datum hu' hu2' huu' ha' hb' hau' hbu'
    have e : g⁻¹ * (a * b * a⁻¹ * b⁻¹) * g =
        (g⁻¹ * a * g) * (g⁻¹ * b * g) * (g⁻¹ * a * g)⁻¹ * (g⁻¹ * b * g)⁻¹ := by group
    rw [e]
    exact key

theorem CoreData.aEmpty_all (h : CoreData n Y R S t) :
    ∀ J ∈ CoreAssembly.conjClass (tightCore R), AEmpty (CoreAssembly.conjClass (tightCore R)) J := by
  rintro J ⟨g, rfl⟩
  exact aEmpty_conj h.hyp.conjInvariant h.aEmpty g

theorem CoreData.partIHypG (h : CoreData n Y R S t) :
    Q3CL.PartIHypG (CoreAssembly.conjClass (tightCore R)) :=
  ⟨h.hyp, h.classicalClause, h.aEmpty_all⟩

theorem CoreData.exists_wset_mem (h : CoreData n Y R S t) :
    ∃ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), t ∈ W :=
  wz_of_hypOmegaGen h.hyp (CoreAssembly.mem_conjClass_self _)
    (Inner.isUniqueInvolution_core h.datum)

theorem CoreData.perpMu (h : CoreData n Y R S t)
    (hperp : KPerp (CoreAssembly.conjClass (tightCore R)) (tightCore R) =
      twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (h2 : TwoTwins R) {W : Subgroup Y} (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) :
    MuIsoE4 (CoreAssembly.conjClass (tightCore R)) W ∨
      MuIsoS4 (CoreAssembly.conjClass (tightCore R)) W := by
  obtain ⟨K', hK', hne⟩ := h.twin
  have hP := h.partIHypG
  have hperp' : KPerp (CoreAssembly.conjClass (tightCore R)) (tightCore R) = {tightCore R, K'} :=
    hperp.trans (twinSet_eq_pair h2 hK' hne)
  exact Q3T7.c231_mu_iso_of_clique hP hW
    (Q3T7.c231_clique hP (CoreAssembly.mem_conjClass_self _)
      (fun J ⟨g, hg⟩ => ⟨g, hg⟩) (Inner.isUniqueInvolution_core h.datum) hK' hne hperp' hW)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
