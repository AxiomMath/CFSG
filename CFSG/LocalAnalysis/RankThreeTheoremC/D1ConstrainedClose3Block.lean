module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedClose3Perfect
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7Defs
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding

@[expose] def KFactBlockPerfectCoreThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), BlockL28Hyps M S L →
    (NineThreeTwo M S L ∨ NineThreeThree M S L ∨ NineThreeFive M L) →
    PerfectCoreThree ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L))

section Shapes

variable {G : Type} [Group G]

theorem isPGroup_ker_comp_pCore_quotient {J Q : Type*} [Group J] [Group Q]
    (e : J ⧸ CFSG.pCore 2 J ≃* Q) :
    IsPGroup 2 (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 J))).ker := by
  refine (CFSG.pCore_isPGroup (p := 2) (G := J)).to_le fun x hx => ?_
  have h1 : e (QuotientGroup.mk' (CFSG.pCore 2 J) x) = 1 := hx
  rw [e.map_eq_one_iff] at h1
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem perfectCoreThree_of_pCore_quotient {J Q : Type*} [Group J] [Finite J] [Group Q]
    (e : J ⧸ CFSG.pCore 2 J ≃* Q) (hQ : PerfectCoreThree Q) : PerfectCoreThree J := by
  refine PerfectCoreThree.of_surjective
    (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 J)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) ?_ hQ
  have : Group.IsNilpotent ↥(e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 J))).ker :=
    (isPGroup_ker_comp_pCore_quotient e).isNilpotent
  infer_instance

theorem perfectCoreThree_of_central_extension {K : Type*} [Group K] (P : Subgroup K)
    (hP : Nonempty (↥(P.map (QuotientGroup.mk' (Subgroup.center K))) ≃*
      Equiv.Perm (Fin 4))) : PerfectCoreThree ↥P := by
  obtain ⟨e⟩ := hP
  set q : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K) with hq
  let f : P →* K ⧸ Subgroup.center K := q.comp P.subtype
  have hrange : f.range = P.map q := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hS4 : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
  have hQ : PerfectCoreThree ↥f.range :=
    PerfectCoreThree.of_mulEquiv ((MulEquiv.subgroupCongr hrange).trans e)
      (PerfectCoreThree.of_isSolvable (P := Equiv.Perm (Fin 4)))
  refine PerfectCoreThree.of_surjective f.rangeRestrict f.rangeRestrict_surjective ?_ hQ
  rw [MonoidHom.ker_rangeRestrict]
  have hcomm : ∀ x ∈ f.ker, ∀ y : P, ((x : P) : K) * (y : K) = (y : K) * (x : P) := by
    intro x hx y
    have h1 : q (x : K) = 1 := hx
    have hx' : (x : K) ∈ Subgroup.center K := (QuotientGroup.eq_one_iff _).mp h1
    exact (Subgroup.mem_center_iff.mp hx' (y : K)).symm
  let incl : f.ker →* Subgroup.center K :=
    (P.subtype.comp f.ker.subtype).codRestrict (Subgroup.center K) fun x => by
      have h1 : q ((x : P) : K) = 1 := x.2
      exact (QuotientGroup.eq_one_iff _).mp h1
  have hinj : Function.Injective incl := fun x y hxy =>
    Subtype.ext (Subtype.ext (congrArg (Subtype.val : ↥(Subgroup.center K) → K) hxy))
  exact Group.isSolvable_of_isSolvable_injective hinj

end Shapes

variable {G : Type} [Group G] [Finite G]

theorem perfectCoreThree_of_blockHyps (hK : KFactBlockPerfectCoreThree) {M S L : Subgroup G}
    (hyps : BlockL28Hyps M S L) :
    PerfectCoreThree ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) := by
  have hLM : L ≤ M := hyps.2.2.1.le
  rcases hyps.2.2.2.1 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hyps.2.2.2.2.1
  · exact hK G M S L hyps (Or.inl h2)
  · exact hK G M S L hyps (Or.inr (Or.inl h3))
  · obtain ⟨-, -, -, -, hP⟩ := h4
    exact PerfectCoreThree.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (barM_mono (inf_le_right : Subgroup.normalizer (S : Set G) ⊓ L
        ≤ L))).symm (perfectCoreThree_of_central_extension _ hP)
  · exact hK G M S L hyps (Or.inr (Or.inr h5))
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h6
    exact perfectCoreThree_of_pCore_quotient e (perfectCoreThree_perm n)
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h7
    exact perfectCoreThree_of_pCore_quotient e (perfectCoreThree_perm n)
  · obtain ⟨-, N, r, -, -, -, -, -, -, φ, -⟩ := h8
    exact perfectCoreThree_of_pCore_quotient φ (perfectCoreThree_perm_prod r (N - 2 * r))

theorem isSolvable_normalizer_inf_of_blockHyps (hK : KFactBlockPerfectCoreThree)
    {M S L : Subgroup G} (hyps : BlockL28Hyps M S L)
    (hperf : ∀ D : Subgroup G, D ≤ Subgroup.normalizer (S : Set G) ⊓ L → ⁅D, D⁆ = D →
      ¬ 3 ∣ Nat.card D) :
    Group.IsSolvable ↥(Subgroup.normalizer (S : Set G) ⊓ L) := by
  have hLM : L ≤ M := hyps.2.2.1.le
  set Y : Subgroup G := Subgroup.normalizer (S : Set G) ⊓ L with hY
  have hYM : Y ≤ M := inf_le_right.trans hLM
  let g : ↥Y →* ↥M ⧸ CFSG.pCore 2 ↥M :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hYM)
  have hrange : g.range = barM M Y := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hQ : PerfectCoreThree ↥g.range :=
    PerfectCoreThree.of_mulEquiv (MulEquiv.subgroupCongr hrange)
      (perfectCoreThree_of_blockHyps hK hyps)
  have hker : IsPGroup 2 g.ker := by
    refine (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).of_injective
      (((Subgroup.inclusion hYM).comp g.ker.subtype).codRestrict (CFSG.pCore 2 ↥M) fun x => ?_) ?_
    · exact (QuotientGroup.eq_one_iff _).mp x.2
    · intro x y hxy
      have h1 := congrArg (Subtype.val : ↥(CFSG.pCore 2 ↥M) → ↥M) hxy
      exact Subtype.ext (Subtype.ext (congrArg (Subtype.val : ↥M → G) h1))
  have hYsolv : Group.IsSolvable g.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    have : Group.IsNilpotent ↥g.ker := hker.isNilpotent
    infer_instance
  have hPY : PerfectCoreThree ↥Y :=
    PerfectCoreThree.of_surjective g.rangeRestrict g.rangeRestrict_surjective hYsolv hQ
  refine isSolvable_of_perfectCoreThree hPY fun D hDD => ?_
  have hmapD : ⁅D.map Y.subtype, D.map Y.subtype⁆ = D.map Y.subtype := by
    rw [← Subgroup.map_commutator, hDD]
  have hcard : Nat.card (D.map Y.subtype) = Nat.card D :=
    Subgroup.card_map_of_injective Y.subtype_injective
  rw [← hcard]
  exact hperf _ (Subgroup.map_subtype_le D) hmapD

end CFSG.LocalAnalysis.RankThreeTheoremC
