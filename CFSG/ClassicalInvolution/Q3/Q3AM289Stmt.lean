module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadS3Lift
public import CFSG.ClassicalInvolution.Q3.Q3AMLYBase
public import CFSG.ClassicalInvolution.Q3.Q3T8B10

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL

section Defs

structure S3Setting {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) : Prop where
  bad : BadStd8 Ω K J S R T W z t
  hint : IsIntrinsicU (.sl2 3 1) K z
  noTri : NoTriangleAtEdge Ω K J
  layer : LayerS3 Ω K z

@[expose] def S3VertexALeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), S3Setting Ω K J S R T W z t →
      ∀ s : G, S3AxisL Ω K J z t s →
        (∃ J₂ ∈ omegaNbr Ω K, IsUniqueInvolution J₂ (t * s)) →
          Hyp51At (Subgroup.closure ({z, t, s} : Set G)) (z * t) ∧
            Hyp51At (Subgroup.closure ({z, t, s} : Set G)) (z * s) ∧
              Hyp51At (Subgroup.closure ({z, t, s} : Set G)) (z * t * s)

@[expose] def C28_9S3L : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), S3Setting Ω K J S R T W z t → False

end Defs

end CFSG.ClassicalInvolution.Q3.Q3AM

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap

section Route

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t s : G}

theorem s3_false_of_frame (hbad : BadStd8 Ω K J S R T W z t) (hs : Q3AM.S3AxisL Ω K J z t s)
    (vz : Hyp51At (Subgroup.closure ({z, t, s} : Set G)) z)
    (vt : Hyp51At (Subgroup.closure ({z, t, s} : Set G)) t ∧
      Hyp51At (Subgroup.closure ({z, t, s} : Set G)) s ∧
        Hyp51At (Subgroup.closure ({z, t, s} : Set G)) (t * s))
    (va : Hyp51At (Subgroup.closure ({z, t, s} : Set G)) (z * t) ∧
      Hyp51At (Subgroup.closure ({z, t, s} : Set G)) (z * s) ∧
        Hyp51At (Subgroup.closure ({z, t, s} : Set G)) (z * t * s))
    (link : ∀ J' ∈ omegaNbr Ω K, ∀ t' : G, IsUniqueInvolution J' t' →
      ∃ y ∈ rankTwoSpan (Subgroup.closure ({z, t, s} : Set G)),
        y * z * y⁻¹ = z ∧ y * t * y⁻¹ = t') : False := by
  have hstd := hbad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hstd.stand.trans hstd.noTwins hM
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hstd.hz hstd.hJ hstd.ht
  have hne : z ≠ t := fun e => by
    have : IsUniqueInvolution J z := e ▸ hstd.ht
    exact hstd.hJ.2.1 (hnt K hstd.stand.mem J ⟨hstd.hJ.1, z, hstd.hz, this⟩)
  have hz2 := hstd.hz.sq
  have ht2 := hstd.ht.sq
  have helem := T8T.isElemAbelian_closure_three hz2 ht2 hs.sq hzt hs.comm_z hs.comm_t
  have hcard := T8T.natCard_closure_three hz2 ht2 hs.sq hzt hs.comm_z hs.comm_t
    hstd.hz.ne_one hstd.ht.ne_one hne hs.ne_one hs.indep
  have hvert : ∀ c ∈ Subgroup.closure ({z, t, s} : Set G), c ≠ 1 →
      Hyp51At (Subgroup.closure ({z, t, s} : Set G)) c := by
    intro c hc hc1
    rcases T8T.mem_closure_three_involutions hz2 ht2 hs.sq hzt hs.comm_z hs.comm_t hc with
      h | h | h | h | h | h | h | h
    · exact absurd h hc1
    · rw [h]; exact vz
    · rw [h]; exact vt.1
    · rw [h]; exact vt.2.1
    · rw [h]; exact va.1
    · rw [h]; exact va.2.1
    · rw [h]; exact vt.2.2
    · rw [h]; exact va.2.2
  have hB : Hyp51 (Subgroup.closure ({z, t, s} : Set G)) := ⟨helem, hcard, hvert⟩
  have hzt_le : Subgroup.closure ({t, z} : Set G) ≤ Subgroup.closure ({z, t, s} : Set G) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  exact hbad.false_of_linkAxis ⟨hzt_le, lemma52 G _ hB, link⟩

end Route

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

