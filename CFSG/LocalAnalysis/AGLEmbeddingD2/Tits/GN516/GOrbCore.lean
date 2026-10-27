module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbIndep
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbEdge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbAdj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbConn
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbTree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParOneNode
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Core

open CFSG.Open CFSG.Quasithin CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.GN516.Nodes CFSG.AGLEmbeddingD2.Tits.GN516.Indep
  CFSG.AGLEmbeddingD2.Tits.GN516.Edge

variable {K S : Type} [Group K] [Finite K] [Group S] [Finite S] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* S} {M : ℕ}

@[expose] def EdgeCond (D : UniversalRootDatum K) (H : Fin D.rank → Subgroup K) (u v : Fin D.rank) :
    Prop :=
  EdgeLevi D u v ∨
    (TauCeti.diagramGraph D.cartan).degree u ≠ (TauCeti.diagramGraph D.cartan).degree v ∨
    Nat.card ↥(parJ D H {u}) ≠ Nat.card ↥(parJ D H {v})

@[expose] def HasBQGraph (Y : Type) [Group Y] : Prop :=
  ∃ (K : Type) (_ : Group K) (_ : Finite K) (D : UniversalRootDatum K) (n : Fin D.rank → K)
    (H : Fin D.rank → Subgroup K) (π : K →* Y) (M : ℕ),
    BorelQuotient D n H π M ∧ (∀ i, NodeLevi D i) ∧
      (3 ≤ D.rank → ∀ u v, (TauCeti.diagramGraph D.cartan).Adj u v → EdgeCond D H u v)

open scoped Pointwise in
private theorem mul_eq_parJ_iff_nodePerm (h : BorelQuotient D n H π M) (α : MulAut S)
    (hα : ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π)
    (j k : Fin D.rank) :
    (((parJ D H {nodePerm h α hα j}).map π : Set S) *
        ((parJ D H {nodePerm h α hα k}).map π : Set S) =
        ((parJ D H {nodePerm h α hα j, nodePerm h α hα k}).map π : Set S)) ↔
      (((parJ D H {j}).map π : Set S) * ((parJ D H {k}).map π : Set S) =
        ((parJ D H {j, k}).map π : Set S)) := by
  have c1 : ((parJ D H {nodePerm h α hα j}).map π : Set S) =
      α.toMonoidHom '' ((parJ D H {j}).map π : Set S) := by
    rw [← map_parJ_singleton_nodePerm h α hα j]
    exact Subgroup.coe_map _ _
  have c2 : ((parJ D H {nodePerm h α hα k}).map π : Set S) =
      α.toMonoidHom '' ((parJ D H {k}).map π : Set S) := by
    rw [← map_parJ_singleton_nodePerm h α hα k]
    exact Subgroup.coe_map _ _
  have c3 : ((parJ D H {nodePerm h α hα j, nodePerm h α hα k}).map π : Set S) =
      α.toMonoidHom '' ((parJ D H {j, k}).map π : Set S) := by
    have e := map_parJ_nodePerm h α hα {j, k}
    rw [Set.image_pair] at e
    rw [← e]
    exact Subgroup.coe_map _ _
  rw [c1, c2, c3, ← Set.image_mul]
  exact (Set.image_injective.2 α.injective).eq_iff

theorem nodePerm_adj_iff (h : BorelQuotient D n H π M) (α : MulAut S)
    (hα : ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π) (j k : Fin D.rank) :
    (TauCeti.diagramGraph D.cartan).Adj (nodePerm h α hα j) (nodePerm h α hα k) ↔
      (TauCeti.diagramGraph D.cartan).Adj j k := by
  rw [D.isFiniteType.diagramGraph_adj_iff, D.isFiniteType.diagramGraph_adj_iff]
  by_cases hjk : j = k
  · subst hjk
    simp
  · have hσ : nodePerm h α hα j ≠ nodePerm h α hα k := (nodePerm h α hα).injective.ne hjk
    have e1 := Adj.map_parJ_mul_eq_iff h hjk
    have e2 := Adj.map_parJ_mul_eq_iff h hσ
    have e3 := mul_eq_parJ_iff_nodePerm h α hα j k
    constructor
    · rintro ⟨-, hc⟩
      exact ⟨hjk, fun h0 => hc (e2.1 (e3.2 (e1.2 h0)))⟩
    · rintro ⟨-, hc⟩
      exact ⟨hσ, fun h0 => hc (e1.1 (e3.1 (e2.2 h0)))⟩

private theorem card_parJ_eq (h : BorelQuotient D n H π M) (J : Set (Fin D.rank)) :
    Nat.card ↥(parJ D H J) = Nat.card ↥((parJ D H J).map π) * Nat.card ↥π.ker := by
  have h1 := Subgroup.relIndex_mul_card (H := π.ker) (K := parJ D H J)
  rw [Subgroup.relIndex_ker, inf_eq_left.2 (ker_le_parJ h J)] at h1
  exact h1.symm

theorem card_parJ_nodePerm (h : BorelQuotient D n H π M) (α : MulAut S)
    (hα : ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π) (j : Fin D.rank) :
    Nat.card ↥(parJ D H {nodePerm h α hα j}) = Nat.card ↥(parJ D H {j}) := by
  have e : Nat.card ↥((parJ D H {nodePerm h α hα j}).map π) =
      Nat.card ↥((parJ D H {j}).map π) := by
    rw [← map_parJ_singleton_nodePerm h α hα j]
    exact Subgroup.card_map_of_injective α.injective
  rw [card_parJ_eq h, card_parJ_eq h, e]

private theorem degree_nodePerm (h : BorelQuotient D n H π M) (α : MulAut S)
    (hα : ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π) (j : Fin D.rank) :
    (TauCeti.diagramGraph D.cartan).degree (nodePerm h α hα j) =
      (TauCeti.diagramGraph D.cartan).degree j := by
  let f : TauCeti.diagramGraph D.cartan ≃g TauCeti.diagramGraph D.cartan :=
    { toEquiv := nodePerm h α hα
      map_rel_iff' := fun {a b} => nodePerm_adj_iff h α hα a b }
  exact f.degree_eq j

theorem core_alternative (h : BorelQuotient D n H π M) (hnode : ∀ j, NodeLevi D j)
    (hedge : 3 ≤ D.rank → ∀ u v, (TauCeti.diagramGraph D.cartan).Adj u v → EdgeCond D H u v)
    [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (𝒜 : Subgroup (MulAut S)) (h𝒜2 : IsPGroup 2 ↥𝒜)
    (h𝒜 : ∀ α ∈ 𝒜, ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π)
    (i : Fin D.rank) (hmove : ∃ a : ↥𝒜, nodeHom h 𝒜 h𝒜 a i ≠ i) :
    Group.IsSolvable ↥((unipJ D (orbitSet h 𝒜 h𝒜 i)).map π) ∨
    (∃ C : Subgroup S, C ≤ pElementSubgroup 2 C ∧ C ≤ (unipJ D (orbitSet h 𝒜 h𝒜 i)).map π ∧
      (unipJ D (orbitSet h 𝒜 h𝒜 i)).map π ≤ Subgroup.normalizer (C : Set S) ∧
      (unipJ D (orbitSet h 𝒜 h𝒜 i)).map π ≤ ⨆ a : ↥𝒜, C.map a.1.toMonoidHom ∧
      ∀ a : ↥𝒜, nodeHom h 𝒜 h𝒜 a i ≠ i →
        ⁅C, C.map a.1.toMonoidHom⁆ ≤ pCoreOf 2 ((unipJ D (orbitSet h 𝒜 h𝒜 i)).map π)) ∨
    QuasisimpleModTwoNonab ↥(twoResidual ((unipJ D (orbitSet h 𝒜 h𝒜 i)).map π)) := by
  classical
  letI : MulAction ↥𝒜 (Fin D.rank) := MulAction.compHom (Fin D.rank) (nodeHom h 𝒜 h𝒜)
  have hT : (TauCeti.diagramGraph D.cartan).IsTree := Conn.diagram_isTree h hnc
  have hadj : ∀ (a : ↥𝒜) (u v : Fin D.rank),
      (TauCeti.diagramGraph D.cartan).Adj (a • u) (a • v) ↔
        (TauCeti.diagramGraph D.cartan).Adj u v :=
    fun a u v => nodePerm_adj_iff h a.1 (h𝒜 a.1 a.2) u v
  by_cases hind : ∀ j ∈ orbitSet h 𝒜 h𝒜 i, ∀ k ∈ orbitSet h 𝒜 h𝒜 i, j ≠ k → D.cartan j k = 0
  · rcases indep_alternative h hnode 𝒜 h𝒜 i hind with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · refine Or.inr (Or.inr ?_)
    push Not at hind
    obtain ⟨j, ⟨a₁, ha₁⟩, k, ⟨a₂, ha₂⟩, hjk, hc⟩ := hind
    have ha₁' : a₁ • i = j := ha₁
    have ha₂' : a₂ • i = k := ha₂
    have hadjjk : (TauCeti.diagramGraph D.cartan).Adj j k :=
      D.isFiniteType.diagramGraph_adj_iff.2 ⟨hjk, hc⟩
    have hy : ∃ g : ↥𝒜, g • j = k :=
      ⟨a₂ * a₁⁻¹, by rw [← ha₁', ← ha₂', ← mul_smul, mul_assoc, inv_mul_cancel, mul_one]⟩
    have hJ : orbitSet h 𝒜 h𝒜 i = {j, k} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨b, hb⟩
        have hb' : b • i = x := hb
        have e : (b * a₁⁻¹) • j = x := by
          rw [← ha₁', ← mul_smul, mul_assoc, inv_mul_cancel, mul_one, hb']
        rcases Tree.orbit_subset_of_adj hT h𝒜2 hadj hadjjk hy (b * a₁⁻¹) with h1 | h1
        · exact Or.inl (e.symm.trans h1)
        · exact Or.inr (e.symm.trans h1)
      · rintro (hx | hx)
        · exact ⟨a₁, ha₁.trans hx.symm⟩
        · exact ⟨a₂, ha₂.trans hx.symm⟩
    rw [hJ]
    obtain ⟨g, hg⟩ := hy
    have hgk : nodePerm h g.1 (h𝒜 g.1 g.2) j = k := hg
    by_cases hr : 3 ≤ D.rank
    · rcases hedge hr j k hadjjk with he | hdeg | hcard
      · exact quasisimpleModTwoNonab_of_edgeLevi h he
      · exact absurd (by rw [← hgk, degree_nodePerm]) hdeg
      · exact absurd (by rw [← hgk]; exact (card_parJ_nodePerm h g.1 (h𝒜 g.1 g.2) j).symm) hcard
    · have hr' : D.rank ≤ 2 := by omega
      have huniv : ∀ x : Fin D.rank, x = j ∨ x = k := by
        intro x
        have hx := x.isLt
        have hj := j.isLt
        have hk := k.isLt
        have hjk' : j.val ≠ k.val := fun e => hjk (Fin.ext e)
        simp only [Fin.ext_iff]
        omega
      have hU : unipJ D {j, k} = ⊤ := by
        rw [eq_top_iff, ← iSup_rankOne_eq_top h.ct h.extras]
        refine iSup_le fun x => rankOne_le_unipJ ?_
        rcases huniv x with hx | hx
        · exact Or.inl hx
        · exact Or.inr hx
      have hW : (unipJ D {j, k}).map π = ⊤ := by
        rw [hU]
        exact Subgroup.map_top_of_surjective π h.surj
      rw [hW]
      obtain ⟨Q, hQ, a, ha, b, hb, hab⟩ := exists_nonabelian_two_of_adj h hjk hc
      have hS : IsSimpleGroup ↥(⊤ : Subgroup S) := Subgroup.topEquiv.isSimpleGroup
      have hQ' : ∃ Q' : Subgroup ↥(⊤ : Subgroup S), IsPGroup 2 Q' ∧
          ∃ a ∈ Q', ∃ b ∈ Q', a * b ≠ b * a := by
        refine ⟨Q.map (Subgroup.topEquiv (G := S)).symm.toMonoidHom, hQ.map _,
          (Subgroup.topEquiv (G := S)).symm a, ⟨a, ha, rfl⟩,
          (Subgroup.topEquiv (G := S)).symm b, ⟨b, hb, rfl⟩, fun hcomm => hab ?_⟩
        apply (Subgroup.topEquiv (G := S)).symm.injective
        rw [map_mul, map_mul]
        exact hcomm
      have hP : pElementSubgroup 2 (⊤ : Subgroup S) = ⊤ := by
        haveI := normal_pElementSubgroup_top S
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pElementSubgroup 2 (⊤ : Subgroup S))
          with e | e
        · exfalso
          have ha' : a ∈ pElementSubgroup 2 (⊤ : Subgroup S) :=
            le_pElementSubgroup_of_isPGroup le_top hQ ha
          rw [e, Subgroup.mem_bot] at ha'
          exact hab (by rw [ha']; simp)
        · exact e
      have key := quasisimpleModTwoNonab_of_simple hS hQ'
      rw [hP] at key
      exact key

end CFSG.AGLEmbeddingD2.Tits.GN516.Core
