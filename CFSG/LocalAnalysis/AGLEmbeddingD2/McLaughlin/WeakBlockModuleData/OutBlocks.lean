module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OutCover
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OutAltSix
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

theorem autThreePowInner_alt_six : AutThreePowInner (alternatingGroup (Fin 6)) := by
  intro ψ k hψ
  have hpow : ψ ^ (3 ^ k) = 1 := by
    have hit : ∀ (n : ℕ) (x : alternatingGroup (Fin 6)), (ψ ^ n) x = ψ^[n] x := by
      intro n
      induction n with
      | zero => intro x; rfl
      | succ n ih =>
        intro x
        rw [pow_succ', MulAut.mul_apply, ih, Function.iterate_succ_apply']
    apply MulEquiv.ext
    intro x
    rw [hit, hψ]
    rfl
  obtain ⟨a, ha⟩ := exists_conj_eq_of_pow_eq_one_alt_six ψ hpow
  exact ⟨a, fun x => by rw [← ha]; simp [MulAut.conj_apply]⟩

@[expose] def ClauseO {G : Type} [Group G] (M L : Subgroup G) : Prop :=
  ∀ u ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
    IsPGroup 3 (Subgroup.zpowers u) →
      u ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))

variable {G : Type} [Group G]

theorem barM_perfect {M L : Subgroup G} (hLM : L ≤ M) (hL : ⁅L, L⁆ = L) :
    ⁅barM M L, barM M L⁆ = barM M L := by
  unfold barM
  rw [← Subgroup.map_commutator]
  congr 1
  apply Subgroup.map_injective M.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLM, hL]

theorem five_le_of_perfect_alt {X : Type*} [Group X] [Nontrivial X] (hX : commutator X = ⊤)
    {m : ℕ} (e : X ≃* alternatingGroup (Fin m)) : 5 ≤ m := by
  by_contra hm
  have hsolv : Group.IsSolvable (alternatingGroup (Fin m)) :=
    alternatingGroup.isSolvable (by simp; omega)
  have hsolvX : Group.IsSolvable X :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have : Group.IsPerfect X := Group.isPerfect_def.mpr hX
  exact Group.IsPerfect.not_isSolvable (G := X) hsolvX

theorem autThreePowInner_alt_of_five_le {N : ℕ} (hN : 5 ≤ N) :
    AutThreePowInner (alternatingGroup (Fin N)) := by
  by_cases h6 : N = 6
  · subst h6; exact autThreePowInner_alt_six
  · exact autThreePowInner_alt hN h6

theorem clauseO_of_cover {M L : Subgroup G} (hLM : L ≤ M) (hL : ⁅L, L⁆ = L) {X : Type*} [Group X]
    (hX : AutThreePowInner X) (e : ↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* X) :
    ClauseO M L := by
  intro u hu hp
  obtain ⟨k, hk⟩ := hp ⟨u, Subgroup.mem_zpowers u⟩
  exact mem_sup_centralizer_of_three_pow_normalizer_cover hX (barM M L) (barM_perfect hLM hL) e hu
    (by simpa using congrArg Subtype.val hk)

theorem five_le_of_quasisimple_cover_alt {M L : Subgroup G} (hLM : L ≤ M) (hL : ⁅L, L⁆ = L)
    (hq : CFSG.Open.IsQuasisimple ↥(barM M L)) {m : ℕ}
    (e : ↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin m)) : 5 ≤ m := by
  have hsimple := hq.2
  have : Nontrivial (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := hsimple.toNontrivial
  have hperf : Group.IsPerfect ↥(barM M L) := Subgroup.isPerfect_iff.mpr (barM_perfect hLM hL)
  have hperf' : Group.IsPerfect (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := inferInstance
  exact five_le_of_perfect_alt (Group.isPerfect_def.mp hperf') e

theorem clauseO_nineThreeFive {M L : Subgroup G} (h : NineThreeFive M L) : ClauseO M L := by
  obtain ⟨-, ⟨e⟩, -⟩ := h
  intro u hu hp
  exact mem_sup_centralizer_of_isPGroup_three_normalizer_alt (by norm_num) (by norm_num) _ e hu hp

theorem clauseO_nineThreeFour {M S L : Subgroup G} (hLM : L ≤ M) (hL : ⁅L, L⁆ = L)
    (h : NineThreeFour M S L) : ClauseO M L := by
  obtain ⟨-, -, ⟨e⟩, -⟩ := h
  exact clauseO_of_cover hLM hL autThreePowInner_alt_six e

theorem clauseO_nineThreeSix [Finite G] {M S L : Subgroup G} (hL : IsWeakSBlock M S L)
    (h : NineThreeSix M S L) : ClauseO M L := by
  obtain ⟨-, n, ⟨e⟩, -⟩ := h
  have h5 := five_le_of_quasisimple_cover_alt hL.le hL.perfect hL.component.2.2 e
  exact clauseO_of_cover hL.le hL.perfect (autThreePowInner_alt_of_five_le h5) e

theorem clauseO_nineThreeSeven [Finite G] {M S L : Subgroup G} (hL : IsWeakSBlock M S L)
    (h : NineThreeSeven M S L) : ClauseO M L := by
  obtain ⟨-, n, ⟨e⟩, -⟩ := h
  have hperf : Group.IsPerfect ↥(barM M L) :=
    Subgroup.isPerfect_iff.mpr (barM_perfect hL.le hL.perfect)
  have hq : Nontrivial (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
    (hL.component.2.2).2.toNontrivial
  have : Nontrivial ↥(barM M L) := (QuotientGroup.mk_surjective (s := Subgroup.center ↥(barM M L))).nontrivial
  have h5 : 5 ≤ 4 * n := five_le_of_perfect_alt (Group.isPerfect_def.mp hperf) e
  intro u hu hp
  exact mem_sup_centralizer_of_isPGroup_three_normalizer_alt h5 (by omega) _ e hu hp

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
