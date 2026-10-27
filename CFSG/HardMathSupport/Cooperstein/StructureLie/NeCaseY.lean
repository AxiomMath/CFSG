module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.NeCaseThompson

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock IsTwoPrimeComponent barM charTwo_of_twoCore_le)
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.HardMathSupport.Cooperstein.Coordinator

variable {G : Type} [Group G]

@[expose] def neY (S L : Subgroup G) : Subgroup G :=
  L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)

@[expose] def neX1 (S L : Subgroup G) : Subgroup G := neY S L ⊔ S

theorem neY_le_left (S L : Subgroup G) : neY S L ≤ L := inf_le_left

theorem le_normalizer_neY {S L : Subgroup G} (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    S ≤ Subgroup.normalizer ((neY S L : Subgroup G) : Set G) := by
  intro s hs
  have hsR : s ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs, hSL hs⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hSL hs) y).mp hy.1
    · have := Subgroup.mul_mem _ (Subgroup.mul_mem _ hsR hy.2) (Subgroup.inv_mem _ hsR)
      exact this
  · intro hy
    have hs' : s⁻¹ ∈ S := S.inv_mem hs
    have hsR' : s⁻¹ ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
      Subgroup.inv_mem _ hsR
    have hsL' : s⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ (hSL hs)
    refine ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp hsL' (s * y * s⁻¹)).mp hy.1
      have e : s⁻¹ * (s * y * s⁻¹) * s⁻¹⁻¹ = y := by group
      rwa [e] at this
    · have := Subgroup.mul_mem _ (Subgroup.mul_mem _ hsR' hy.2) (Subgroup.inv_mem _ hsR')
      have e' : s⁻¹ * (s * y * s⁻¹) * s⁻¹⁻¹ = y := by group
      rwa [e'] at this

theorem neX1_le_sup (S L : Subgroup G) : neX1 S L ≤ L ⊔ S := sup_le_sup_right (neY_le_left S L) S

theorem le_neX1 (S L : Subgroup G) : S ≤ neX1 S L := le_sup_right

theorem neY_le_neX1 (S L : Subgroup G) : neY S L ≤ neX1 S L := le_sup_left

theorem inf_normalizer_sup_le_neX1 {S L : Subgroup G}
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    (L ⊔ S) ⊓ Subgroup.normalizer (S : Set G) ≤ neX1 S L := by
  rintro g ⟨hg, hgN⟩
  have hgSL : g ∈ ((S ⊔ L : Subgroup G) : Set G) := by rwa [sup_comm]
  rw [Subgroup.coe_mul_of_left_le_normalizer_right S L hSL] at hgSL
  obtain ⟨s, hs, l, hl, rfl⟩ := hgSL
  have hlN : l ∈ Subgroup.normalizer (S : Set G) := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hs : s ∈
      Subgroup.normalizer (S : Set G))) hgN
    simpa using this
  have hlY : l ∈ neY S L :=
    ⟨hl, Subgroup.inf_normalizer_le_normalizer_inf ⟨hlN, Subgroup.le_normalizer hl⟩⟩
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hs) (Subgroup.mem_sup_left hlY)

theorem asc81bHyp_neX1 {X S L : Subgroup G} [Finite G] (hA : Asc81bHyp X S)
    (hL : IsTwoPrimeComponent X L) (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    Asc81bHyp (neX1 S L) S := by
  have hA' := asc81bHyp_sup hA hL hSL
  have h1 : neX1 S L ≤ X := (neX1_le_sup S L).trans (sup_le hL.le hA.twoRadical.1)
  have hN : neX1 S L ⊓ Subgroup.normalizer (S : Set G) =
      (L ⊔ S) ⊓ Subgroup.normalizer (S : Set G) := by
    refine le_antisymm (inf_le_inf_right _ (neX1_le_sup S L)) ?_
    exact le_inf (inf_normalizer_sup_le_neX1 hSL) inf_le_right
  refine ⟨⟨le_neX1 S L, hA.twoRadical.2.1, ?_⟩,
    charTwo_of_twoCore_le hA.charTwo (hA.twoCore_le.trans (le_neX1 S L)) h1,
    cgsIn_eq_of_le hA h1⟩
  rw [hN]
  exact hA'.twoRadical.2.2

theorem isKGroup_neX1 {X S L : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsTwoPrimeComponent X L) :
    CFSG.Open.IsKGroup ↥(neX1 S L) :=
  CFSG.AGLEmbedding.AscEightFour.isKGroup_mono hX
    ((neX1_le_sup S L).trans (sup_le hL.le hA.twoRadical.1))

theorem normalizer_barM_le_of_forall {X S L : Subgroup G} (hQ : pCoreOf 2 X ≤ S) (hLX : L ≤ X)
    (h : ∀ y ∈ neY S L, y ∈ Subgroup.normalizer (S : Set G)) :
    Subgroup.normalizer (barM X (S ⊓ L) : Set (↥X ⧸ CFSG.pCore 2 ↥X)) ⊓ barM X L ≤
      Subgroup.normalizer (barM X S : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
  intro γ hγ
  obtain ⟨hγR, hγL⟩ := hγ
  obtain ⟨x, hxL, rfl⟩ := mem_barM_iff.mp hγL
  have hnorm : ∀ z : ↥X, (z : G) ∈ L →
      barHom X z ∈ Subgroup.normalizer (barM X (S ⊓ L) : Set _) →
      (z : G) ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    intro z hzL hz
    refine mem_normalizer_of_conj_mem (fun r hr => ?_) fun r hr => ?_
    · exact conj_mem_inf_of_barHom hQ hzL hz hr (hLX hr.2)
    · have hzL' : ((z⁻¹ : ↥X) : G) ∈ L := by simpa using L.inv_mem hzL
      have hz' : barHom X z⁻¹ ∈ Subgroup.normalizer (barM X (S ⊓ L) : Set _) := by
        rw [map_inv]
        exact Subgroup.inv_mem _ hz
      simpa using conj_mem_inf_of_barHom hQ hzL' hz' hr (hLX hr.2)
  exact barHom_mem_normalizer_of_mem (h _ ⟨hxL, hnorm x hxL hγR⟩)

end CFSG.HardMathSupport.Cooperstein.StructureLie
