module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevParabolicInputs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParK
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAtomTransport
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbAdj

public section

namespace CFSG.GroupTheory

open CFSG.ABGLocalTools Subgroup CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
open scoped Pointwise

variable {K₀ K : Type} [Group K₀] [Finite K₀] [Group K] [Finite K] {D : UniversalRootDatum K₀}
  {n : Fin D.rank → K₀} {H : Fin D.rank → Subgroup K₀} {π : K₀ →* K} {M : ℕ}

private theorem exists_sylow_of_isSylowOf_top' {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsSylowOf 2 T ⊤) : ∃ T' : Sylow 2 G, (T' : Subgroup G) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hT2, hdvd⟩ := isSylowOf_iff.1 hT
  rw [Subgroup.relIndex_top_right] at hdvd
  exact ⟨hT2.toSylow hdvd, IsPGroup.toSylow_coe _ _⟩

theorem exists_borelQuotient_map_posUnipotent_eq (h : BorelQuotient D n H π M) {S : Subgroup K}
    (hS : IsSylowOf 2 S ⊤) :
    ∃ π' : K₀ →* K, BorelQuotient D n H π' M ∧ (posUnipotent D).map π' = S := by
  obtain ⟨Q, hQ⟩ := exists_sylow_of_isSylowOf_top' hS
  obtain ⟨π', hπ', hker, hconj⟩ := h.exists_conj_eq Q
  refine ⟨π', ⟨h.ct, h.extras, h.pGroup, hπ', h.odd, h.torus_pow,
    fun z hz => h.ker_central z (hker ▸ hz), fun z hz => h.ker_pow z (hker ▸ hz)⟩, ?_⟩
  rw [← hconj, hQ]

theorem isGomiAtom_iff_exists_eq_map_parJ (h : BorelQuotient D n H π M) {A : Subgroup K} :
    IsGomiAtom ⊤ ((posUnipotent D).map π) A ↔ ∃ i, A = (parJ D H {i}).map π := by
  rw [isGomiAtom_iff_isMinOverBorel ⊤ ((posUnipotent D).map π) A]
  refine ⟨fun hA => exists_eq_map_parJ h hA, ?_⟩
  rintro ⟨i, rfl⟩
  exact isMinOverBorel_map_parJ h i

theorem exists_map_map_parJ_eq (h : BorelQuotient D n H π M) {α : MulAut K}
    (hα : ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π)
    (i : Fin D.rank) : ∃ j, ((parJ D H {i}).map π).map α.toMonoidHom = (parJ D H {j}).map π := by
  have hA : IsGomiAtom ⊤ ((posUnipotent D).map π) ((parJ D H {i}).map π) :=
    (isGomiAtom_iff_exists_eq_map_parJ h).2 ⟨i, rfl⟩
  have h2 : IsGomiAtom ⊤ ((posUnipotent D).map π)
      (((parJ D H {i}).map π).map α.toMonoidHom) := by
    rw [← hα]
    exact (isGomiAtom_top_map_mulEquiv_iff α ((posUnipotent D).map π)
      ((parJ D H {i}).map π)).2 hA
  exact (isGomiAtom_iff_exists_eq_map_parJ h).1 h2

omit [Finite K₀] [Finite K] in
theorem map_parJ_sup_map_parJ (j k : Fin D.rank) :
    (parJ D H {j}).map π ⊔ (parJ D H {k}).map π = (parJ D H {j, k}).map π := by
  have h : parJ D H {j} ⊔ parJ D H {k} = parJ D H {j, k} := by
    simp only [parJ, iSup_pair, iSup_singleton]
    rw [sup_sup_sup_comm, sup_idem]
  rw [← Subgroup.map_sup, h]

omit [Finite K₀] [Finite K] in
theorem diagramGraph_adj_iff_mul_ne_sup (h : BorelQuotient D n H π M) {j k : Fin D.rank} :
    (TauCeti.diagramGraph D.cartan).Adj j k ↔ j ≠ k ∧
      ((parJ D H {j}).map π : Set K) * ((parJ D H {k}).map π : Set K) ≠
        (((parJ D H {j}).map π ⊔ (parJ D H {k}).map π : Subgroup K) : Set K) := by
  rw [D.isFiniteType.diagramGraph_adj_iff, map_parJ_sup_map_parJ]
  by_cases hjk : j = k
  · subst hjk
    simp
  · have hiff := CFSG.AGLEmbeddingD2.Tits.GN516.Adj.map_parJ_mul_eq_iff h hjk
    exact ⟨fun hh => ⟨hh.1, fun h0 => hh.2 (hiff.1 h0)⟩,
      fun hh => ⟨hh.1, fun h0 => hh.2 (hiff.2 h0)⟩⟩

theorem diagramGraph_adj_iff_of_map_map_parJ_eq (h : BorelQuotient D n H π M) (α : MulAut K)
    {i j i' j' : Fin D.rank}
    (hi : ((parJ D H {i}).map π).map α.toMonoidHom = (parJ D H {i'}).map π)
    (hj : ((parJ D H {j}).map π).map α.toMonoidHom = (parJ D H {j'}).map π) :
    (TauCeti.diagramGraph D.cartan).Adj i' j' ↔ (TauCeti.diagramGraph D.cartan).Adj i j := by
  rw [diagramGraph_adj_iff_mul_ne_sup (j := i') (k := j') h,
    diagramGraph_adj_iff_mul_ne_sup (j := i) (k := j) h]
  have himg_sp : α.toMonoidHom '' (((parJ D H {i}).map π : Set K) *
      ((parJ D H {j}).map π : Set K)) =
      (((parJ D H {i'}).map π : Set K) * ((parJ D H {j'}).map π : Set K)) := by
    rw [Set.image_mul, ← Subgroup.coe_map, ← Subgroup.coe_map, hi, hj]
  have himg_jn : α.toMonoidHom '' ((((parJ D H {i}).map π ⊔
      (parJ D H {j}).map π : Subgroup K) : Set K)) =
      ((((parJ D H {i'}).map π ⊔ (parJ D H {j'}).map π : Subgroup K) : Set K)) := by
    rw [← Subgroup.coe_map, Subgroup.map_sup, hi, hj]
  have hiff : (((parJ D H {i'}).map π : Set K) * ((parJ D H {j'}).map π : Set K) =
      (((parJ D H {i'}).map π ⊔ (parJ D H {j'}).map π : Subgroup K) : Set K)) ↔
      (((parJ D H {i}).map π : Set K) * ((parJ D H {j}).map π : Set K) =
      (((parJ D H {i}).map π ⊔ (parJ D H {j}).map π : Subgroup K) : Set K)) := by
    rw [← himg_sp, ← himg_jn]
    exact (α.injective.image_injective).eq_iff
  have hne : (((parJ D H {i'}).map π : Set K) * ((parJ D H {j'}).map π : Set K) ≠
      (((parJ D H {i'}).map π ⊔ (parJ D H {j'}).map π : Subgroup K) : Set K)) ↔
      (((parJ D H {i}).map π : Set K) * ((parJ D H {j}).map π : Set K) ≠
      (((parJ D H {i}).map π ⊔ (parJ D H {j}).map π : Subgroup K) : Set K)) :=
    not_congr hiff
  by_cases hij : i = j
  · have hii' : i' = j' := by
      apply parJ_map_injective h
      show (parJ D H {i'}).map π = (parJ D H {j'}).map π
      rw [← hi, ← hj, hij]
    simp [hii', hij]
  · have hne' : i' ≠ j' := by
      intro heq
      apply hij
      apply parJ_map_injective h
      have h1 : ((parJ D H {i}).map π).map α.toMonoidHom =
          ((parJ D H {j}).map π).map α.toMonoidHom := by rw [hi, hj, heq]
      exact Subgroup.map_injective α.injective h1
    exact ⟨fun hh => ⟨hij, hne.1 hh.2⟩, fun hh => ⟨hne', hne.2 hh.2⟩⟩

end CFSG.GroupTheory
