module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Bad63 (V : Subgroup G) (v : G) : Prop :=
  orderOf v = 2 ∧ IsComponentIn V (centralizer ({v} : Set G)) ∧ InFStar V ∧
    ∃ W : Subgroup G, W ≠ V ∧ IsComponentIn W (centralizer ({v} : Set G)) ∧ InFStar W

@[expose] def PlainChain (X Y : Subgroup G) : Prop :=
  Relation.ReflTransGen WalterArrow X Y

theorem sec63_bad_swap {V W : Subgroup G} {v : G} (h : Bad63 V v) (hne : W ≠ V)
    (hW : IsComponentIn W (centralizer ({v} : Set G))) (hWF : InFStar W) : Bad63 W v := by
  obtain ⟨hv, hVc, hVF, -⟩ := h
  exact ⟨hv, hW, hWF, V, hne.symm, hVc, hVF⟩

theorem sec63_last_bad (hA : AschA2 G) {X Y : Subgroup G} (hch : WalterChain X Y)
    (hX : ∃ x : G, Bad63 X x) : ∃ (V : Subgroup G) (v : G), Bad63 V v ∧ PlainChain V Y := by
  unfold WalterChain at hch
  induction hch with
  | refl =>
      obtain ⟨x, hx⟩ := hX
      exact ⟨X, x, hx, Relation.ReflTransGen.refl⟩
  | @tail Z W hab hbc ih =>
      rcases hbc with hstep | hstep
      · obtain ⟨V, v, hV, hVY⟩ := ih
        exact ⟨V, v, hV, hVY.tail hstep⟩
      · obtain ⟨x0, hx0⟩ := hX
        have hZF : InFStar Z := inFStar_of_walterChain hA hab hx0.2.2.1
        have hWF : InFStar W := inFStar_of_walterArrowDiag hA hstep hZF
        unfold WalterArrowDiag at hstep
        obtain ⟨x, y, -, hy, hxy, -, hWc, -, hne⟩ := hstep
        have hxCy : x ∈ centralizer ({y} : Set G) :=
          Subgroup.mem_centralizer_singleton_iff.mpr hxy
        refine ⟨W, y, ⟨hy, hWc, hWF, CFSG.conjugate W x, ?_, hWc.conjugate hxCy,
          hWF.conjugate x⟩, Relation.ReflTransGen.refl⟩
        intro heq
        exact hne (by rw [heq, sup_idem])

theorem sec63_bad_shape [Finite G] (h36 : Asc82Lemma36) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) {V : Subgroup G} {v : G} (h : Bad63 V v) :
    IsL29 V ∨ IsL281 V := by
  obtain ⟨hv, hVc, hVF, W, hWne, hWc, hWF⟩ := h
  have hone : ¬ (InF V ∨ IsL3Eps3 V) := fun hcase =>
    hWne ((h36 G t L hS v V hv hVc hcase).2 W hWc hWF)
  unfold InFStar IsFStarGroup at hVF
  rcases hVF with hF | ⟨-, hQ⟩
  · exact absurd (Or.inl hF) hone
  · unfold SmallF3StarQuotient at hQ
    rcases hQ with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (Or.inr (Or.inl h)) hone
    · exact absurd (Or.inr (Or.inr h)) hone

end CFSG.OddStandard.SmallF3.Omega
