module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootData
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Kernel
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.ComponentClassification.CatLeaf
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem orbitGroup_eq_bot_of_simpleRootsJ_eq_empty
    {τ : Tag} (D : OrthogonalSemilinearFixedRootDatum τ p k) (h : D.simpleRootsJ = ∅) :
    D.orbitGroup = ⊥ := by
  refine le_bot_iff.1 ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨O, ⟨β, hβ, -⟩, -⟩
  rw [h] at hβ
  exact absurd hβ (Set.notMem_empty β)

theorem simpleRootsJ_eq_empty_or_eq
    {τ : Tag} (D : OrthogonalSemilinearFixedRootDatum τ p k) {S : Set (Fin τ.rank → ℤ)}
    (hΔ : simpleUnion D.χ = S)
    (hcls : ∀ i, simpleUnion D.χ ∩ componentRoots D.χ i = ∅ ∨
      simpleUnion D.χ ∩ componentRoots D.χ i = S) :
    D.simpleRootsJ = ∅ ∨ D.simpleRootsJ = S := by
  have hmem : ∀ β, β ∈ D.simpleRootsJ ↔ β ∈ simpleUnion D.χ ∧ ∃ i ∈ D.J, β ∈ componentRoots D.χ i
      := fun β => by
    constructor
    · rintro ⟨⟨i, -, hβi⟩, h, hJβ⟩
      exact ⟨Set.mem_iUnion.2 ⟨i, hβi⟩, _, hJβ, h, rfl⟩
    · rintro ⟨hβ, i, hi, h, rfl⟩
      obtain ⟨i', hi'⟩ := Set.mem_iUnion.1 hβ
      exact ⟨⟨i', Set.mem_univ _, hi'⟩, h, hi⟩
  by_cases hex : ∃ i ∈ D.J, simpleUnion D.χ ∩ componentRoots D.χ i = S
  · obtain ⟨i, hi, hiS⟩ := hex
    refine Or.inr (Set.ext fun β => ⟨fun hβ => hΔ ▸ ((hmem β).1 hβ).1, fun hβ => ?_⟩)
    rw [← hiS] at hβ
    exact (hmem β).2 ⟨hβ.1, i, hi, hβ.2⟩
  · refine Or.inl (Set.eq_empty_of_forall_notMem fun β hβ => ?_)
    obtain ⟨hβΔ, i, hi, hβi⟩ := (hmem β).1 hβ
    rcases hcls i with h | h
    · exact (Set.eq_empty_iff_forall_notMem.1 h) β ⟨hβΔ, hβi⟩
    · exact hex ⟨i, hi, h⟩

theorem e7Word2_1_facts :
    (∀ d ∈ e7Delta2, d < e7Certificate.roots.length ∧ applyWordIdx e7Certificate e7Word2_1
        (applyWordIdx e7Certificate e7Word2_1 d) = d) ∧
      (∀ d ∈ e7Delta3, d < e7Certificate.roots.length ∧ applyWordIdx e7Certificate e7Word2_1
        (applyWordIdx e7Certificate e7Word2_1 d) = d) ∧
      applyWordIdx e7Certificate e7Word2_1 2 = 6 := by
  decide +kernel

theorem thetaMap_one_apply
    {τ : Tag} (ω : WeylGroup τ) (v : Fin τ.rank → ℤ) : thetaMap ω 1 v = ω • v :=
  rfl

theorem thetaMap_e7Word2_1_twice
    {m : ℕ} (hm : m = 2 ∨ m = 3) {β : Fin (Tag.rank .E7) → ℤ}
    (hβ : β ∈ simpleUnion (signMaskChar .E7 m)) :
    thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1
      (thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 β) = β := by
  obtain ⟨h2, h3, -⟩ := e7Word2_1_facts
  have key : ∀ d, d < e7Certificate.roots.length → applyWordIdx e7Certificate e7Word2_1
      (applyWordIdx e7Certificate e7Word2_1 d) = d →
        thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1
          (thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 (e7Certificate.root d)) =
            e7Certificate.root d := by
    intro d hd hdd
    obtain ⟨hd1, he1⟩ := applyWordIdx_spec e7Certificate_check e7Word2_1 hd
    obtain ⟨-, he2⟩ := applyWordIdx_spec e7Certificate_check e7Word2_1 hd1
    rw [thetaMap_one_apply, thetaMap_one_apply, ← he1, ← he2, hdd]
  rcases hm with rfl | rfl
  · obtain ⟨d, hd, rfl⟩ := (mem_simpleUnion_iff_of_decompCheck e7Certificate_check e7_splus2
      e7_delta2 e7_decomp2).1 hβ
    exact key d (h2 d hd).1 (h2 d hd).2
  · obtain ⟨d, hd, rfl⟩ := (mem_simpleUnion_iff_of_decompCheck e7Certificate_check e7_splus3
      e7_delta3 e7_decomp3).1 hβ
    exact key d (h3 d hd).1 (h3 d hd).2

theorem thetaMap_e7Word2_1_alpha3 :
    thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 (Pi.single (e7Node 2) 1) =
      Pi.single (e7Node 6) 1 := by
  obtain ⟨-, -, h⟩ := e7Word2_1_facts
  obtain ⟨hl2, hr2⟩ := root_fin e7Certificate_check (e7Node 2)
  obtain ⟨-, hr6⟩ := root_fin e7Certificate_check (e7Node 6)
  obtain ⟨-, he⟩ := applyWordIdx_spec e7Certificate_check e7Word2_1 hl2
  rw [thetaMap_one_apply, ← hr2, ← he]
  change e7Certificate.root (applyWordIdx e7Certificate e7Word2_1 2) = _
  rw [h, ← hr6]
  rfl

theorem family_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {p : ℕ}
    (h : ∀ α : MulAut B, orderOf α = 2 →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L → OddLieCentralQuotient p L)
    (α : MulAut A) (hα : orderOf α = 2) (L : Subgroup (fixedSubgroup α)) (hL : IsComponent L) :
    OddLieCentralQuotient p L := by
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  exact oddLieCentralQuotient_of_component_equiv (fixedSubgroupCongrEquiv e α) (h _ hβ) hL

end CFSG.ComponentClassification.CatLeafProof
