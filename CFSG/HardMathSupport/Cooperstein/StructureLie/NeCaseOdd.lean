module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.NeCaseBar
public import CFSG.HardMathSupport.Cooperstein.StructureLie.NeCaseY

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock IsTwoPrimeComponent barM Asc81bEightFour)
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G]

theorem le_normalizer_inf_of_le_normalizer {S L : Subgroup G}
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    S ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := fun _ hs =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs, hSL hs⟩

theorem neX1_le_normalizer_inf {S L : Subgroup G} (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    neX1 S L ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
  sup_le (fun _ hy => hy.2) (le_normalizer_inf_of_le_normalizer hSL)

theorem inf_le_pCoreOf_neX1 [Finite G] {X S L : Subgroup G} (hA : Asc81bHyp X S)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) : S ⊓ L ≤ pCoreOf 2 (neX1 S L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine normal_pGroup_le_pCoreOf 2 (S ⊓ L) (neX1 S L) (inf_le_left.trans (le_neX1 S L))
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left.trans (le_neX1 S L))).mpr
      (neX1_le_normalizer_inf hSL)) ?_
  exact (hA.twoRadical.isPGroup.to_le inf_le_left)

theorem mem_neY_of_pow_three [Finite G] {X S L : Subgroup G} (hA : Asc81bHyp X S)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) {g : G} (hg : g ∈ neX1 S L) (hg3 : g ^ 3 = 1) :
    g ∈ neY S L := by
  have hS2 : IsPGroup 2 S := hA.twoRadical.isPGroup
  have hgYS : g ∈ ((neY S L ⊔ S : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (neY S L) S
    (le_normalizer_neY hSL)] at hgYS
  obtain ⟨y, hy, s, hs, rfl⟩ := hgYS
  obtain ⟨k, hk⟩ := CFSG.Quasithin.A4.exists_pow_mem_of_mul (H := neY S L) (M := neX1 S L)
    (R := S) (sup_le Subgroup.le_normalizer (le_normalizer_neY hSL)) hS2 hg hy hs rfl
    (neY_le_neX1 S L)
  have hcop : Nat.Coprime (2 ^ k) (orderOf (y * s)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hg3)
      (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3))
  have hmem : y * s ∈ Subgroup.zpowers ((y * s) ^ 2 ^ k) := mem_zpowers_pow_iff.mpr hcop
  exact (Subgroup.zpowers_le).2 hk hmem

theorem centralizes_pPrimeCore_neX1 [Finite G] (h84 : Asc81bEightFour) {X S L : Subgroup G}
    (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hcent : CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.CentralizerInRadical
      (barM X L) (barM X (S ⊓ L))) :
    CFSG.pPrimeCore 2 (↥(neX1 S L) ⧸ CFSG.pCore 2 ↥(neX1 S L)) ≤
      Subgroup.centralizer (barM (neX1 S L) S : Set (↥(neX1 S L) ⧸ CFSG.pCore 2 ↥(neX1 S L))) := by
  rcases h84 G (neX1 S L) S (isKGroup_neX1 hX hA hL) (asc81bHyp_neX1 hA hL hSL) with
    h | ⟨Z, hZX, hZsub, ⟨e⟩⟩
  · exact h
  · exfalso
    have hX1X : neX1 S L ≤ X := (neX1_le_sup S L).trans (sup_le hL.le hA.twoRadical.1)
    exact noA4 (X₁ := neX1 S L) (L := L) (R := S ⊓ L) (Q := pCoreOf 2 X) (Z := Z)
      (pCoreOf_isPGroup 2 X) (hA.twoCore_le.trans (le_neX1 S L))
      (fun g hg => localGroup_le_normalizer_pCoreOf 2 X (hX1X hg))
      (fun g hg hc => hA.charTwo ⟨hX1X hg, Subgroup.mem_centralizer_iff.mpr
        (fun q hq => (hc q hq).symm)⟩)
      (fun l hl => localGroup_le_normalizer_pCoreOf 2 X (hL.le hl)) hL.perfect
      (inf_le_pCoreOf_neX1 hA hSL)
      (fun g hg hg3 => (mem_neY_of_pow_three hA hSL hg hg3).1)
      (hlie_of_centralizerInRadical hA hL hcent) hZX e hZsub

end CFSG.HardMathSupport.Cooperstein.StructureLie
