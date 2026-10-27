module

public import CFSG.ClassicalInvolution.Q3.Q3T8B04

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap

section Plain

structure LinkAxis3 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (z t : G) (B : Subgroup G) : Prop where
  pair_le : Subgroup.closure ({t, z} : Set G) ≤ B
  balance : RankThreeBalance B
  link : ∀ J' ∈ omegaNbr Ω K, ∀ t' : G, IsUniqueInvolution J' t' →
    ∃ y ∈ rankTwoSpan B, y * z * y⁻¹ = z ∧ y * t * y⁻¹ = t'

structure E4Axis {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K J R : Subgroup G)
    (z t s : G) : Prop where
  sq : s * s = 1
  ne_one : s ≠ 1
  comm_z : z * s = s * z
  comm_t : t * s = s * t
  indep : s ∉ Subgroup.closure ({z, t} : Set G)
  mem_X : s ∈ omegaNbrGen Ω K
  cent_R : ∀ r ∈ R, r * s = s * r
  norm_J : conjSub s J = J
  nbr₁ : ∃ J₁ ∈ omegaNbr Ω K, IsUniqueInvolution J₁ s
  nbr₂ : ∃ J₂ ∈ omegaNbr Ω K, IsUniqueInvolution J₂ (t * s)

end Plain

section Defs


structure E4Setting {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) : Prop where
  bad : BadStd8 Ω K J S R T W z t
  proper : omegaNbrGen Ω K ≠ ⊤
  mu : MuIsoE4 Ω W

@[expose] def SectionE4 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G))
    (K : Subgroup G) : Prop :=
  SectionLieTypeU 3 1 Ω (omegaNbrGen Ω K) .PSL 3 ∨
    SectionCompU 3 1 Ω (omegaNbrGen Ω K) Q3.CompData.m11

@[expose] def E4AxisLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), E4Setting Ω K J S R T W z t →
      ∃ s : G, E4Axis Ω K J R z t s

@[expose] def SectionLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), E4Setting Ω K J S R T W z t →
      SectionE4 Ω K

@[expose] def VertexZLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), E4Setting Ω K J S R T W z t →
      ∀ s : G, E4Axis Ω K J R z t s →
        Hyp51At (Subgroup.closure ({z, t, s} : Set G)) z

@[expose] def VertexTLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), E4Setting Ω K J S R T W z t →
      SectionE4 Ω K → ∀ s : G, E4Axis Ω K J R z t s →
        Hyp51At (Subgroup.closure ({z, t, s} : Set G)) t ∧
          Hyp51At (Subgroup.closure ({z, t, s} : Set G)) s ∧
            Hyp51At (Subgroup.closure ({z, t, s} : Set G)) (t * s)

@[expose] def VertexALeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), E4Setting Ω K J S R T W z t →
      SectionE4 Ω K → ∀ s : G, E4Axis Ω K J R z t s →
        Hyp51At (Subgroup.closure ({z, t, s} : Set G)) (z * t) ∧
          Hyp51At (Subgroup.closure ({z, t, s} : Set G)) (z * s) ∧
            Hyp51At (Subgroup.closure ({z, t, s} : Set G)) (z * t * s)

@[expose] def LinkLeaf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), E4Setting Ω K J S R T W z t →
      SectionE4 Ω K → ∀ s : G, E4Axis Ω K J R z t s →
        ∀ J' ∈ omegaNbr Ω K, ∀ t' : G, IsUniqueInvolution J' t' →
          ∃ y ∈ rankTwoSpan (Subgroup.closure ({z, t, s} : Set G)),
            y * z * y⁻¹ = z ∧ y * t * y⁻¹ = t'

structure CFBLeaves : Prop where
  axis : E4AxisLeaf
  sect : SectionLeaf
  vertexZ : VertexZLeaf
  vertexT : VertexTLeaf
  vertexA : VertexALeaf
  link : LinkLeaf

end Defs

section Route


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem BadStd8.false_of_linkAxis [IsSimpleGroup G] (h : BadStd8 Ω K J S R T W z t)
    {B : Subgroup G} (hB : LinkAxis3 Ω K z t B) : False := by
  have hD := h.isElemAbelian2_pair
  have hD4 : Nat.card ↥(Subgroup.closure ({t, z} : Set G)) = 4 := by simpa using hD.1
  have hodd := odd_card_alphaOf_of_rankThreeBalance hB.balance hB.pair_le hD4
  have heq : ∀ F ∈ signalizerFunctorEk 2 2 B,
      alphaOf F = alphaOf (Subgroup.closure ({t, z} : Set G)) := fun F hF =>
    alphaOf_eq_alphaOf_of_rankThreeBalance hB.balance hF.1 hB.pair_le (by simpa using hF.2) hD4
  have hspan : rankTwoSpan B ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
    unfold rankTwoSpan
    exact iSup₂_le fun F hF => T8T.centralizer_le_normalizer_of_alphaOf_eq (heq F hF)
  refine h.false_of_linkConst (fun J' hJ' t' ht' => ?_) hodd
  obtain ⟨y, hy, hyz, hyt⟩ := hB.link J' hJ' t' ht'
  have h1 : conjSub y (Subgroup.closure ({t, z} : Set G)) =
      Subgroup.closure ({t', z} : Set G) := by
    rw [conjSub_closure_pair, hyz, hyt]
  have h2 := mem_normalizer_iff_conjSub_eq.mp (hspan hy)
  rw [← h1, alphaOf_conjSub]
  exact h2

theorem cfb_of_leaves (L : CFBLeaves) : CFB := by
  intro G _ _ _ Ω K J S R T W z t hbad hX hE
  have hset : E4Setting Ω K J S R T W z t := ⟨hbad, hX, hE⟩
  obtain ⟨s, hs⟩ := L.axis G Ω K J S R T W z t hset
  have hsec := L.sect G Ω K J S R T W z t hset
  have vz := L.vertexZ G Ω K J S R T W z t hset s hs
  have vt := L.vertexT G Ω K J S R T W z t hset hsec s hs
  have va := L.vertexA G Ω K J S R T W z t hset hsec s hs
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
  exact hbad.false_of_linkAxis
    ⟨hzt_le, lemma52 G _ hB, L.link G Ω K J S R T W z t hset hsec s hs⟩

end Route

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
