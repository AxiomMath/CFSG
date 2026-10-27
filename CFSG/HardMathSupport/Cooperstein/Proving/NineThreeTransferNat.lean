module

public import CFSG.HardMathSupport.Cooperstein.Proving.NineThreeTwoTransfer
public import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofAsc93
public import CFSG.HardMathSupport.Cooperstein.Transport

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open CFSG.AGLEmbedding CFSG.RankThree.PartTwo.Sec19

variable {G : Type} [Group G] {X Y L S : Subgroup G}

theorem isElemAbelian_of_mulEquiv_sub {Q Q' : Type} [Group Q] [Group Q'] {p : ℕ}
    {A : Subgroup Q} {A' : Subgroup Q'} (e : ↥A ≃* ↥A') (hA : CFSG.Open.IsElemAbelian p A) :
    CFSG.Open.IsElemAbelian p A' := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · apply e.symm.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    exact CFSG.HardMathSupport.Cooperstein.Transport.comm_of_isElemAbelian hA (e.symm a).2 (e.symm b).2
  · have h1 := hA.2 _ (e.symm ⟨y, hy⟩).2
    have h2 : (e.symm ⟨y, hy⟩) ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h1)
    have h3 : (⟨y, hy⟩ : ↥A') ^ p = 1 := by
      rw [← e.apply_symm_apply ⟨y, hy⟩, ← map_pow, h2, map_one]
    simpa using congrArg Subtype.val h3

theorem nineThreeSixNat_of_le (hYX : Y ≤ X) (hLY : L ≤ Y)
    (h : L ⊓ CFSG.Open.pCoreOf 2 X = L ⊓ CFSG.Open.pCoreOf 2 Y) :
    NineThreeSixNat Y S L → NineThreeSixNat X S L := by
  have hLX : L ≤ X := hLY.trans hYX
  rintro ⟨hV, n, hn, ⟨ea⟩, hpc, hab, hcard, ⟨hq⟩⟩
  have hKL : Subgroup.normalizer (S : Set G) ⊓ L ≤ L := inf_le_right
  have hSL : S ⊓ L ≤ L := inf_le_right
  let eL := barMEquiv hLY hLX h.symm
  have heK := barMEquiv_map_subgroupOf hLY hLX h.symm hKL
  have heS := barMEquiv_map_subgroupOf hLY hLX h.symm hSL
  let φS := subgroupOfMapEquiv (barM_mono (M := Y) hSL) (barM_mono (M := X) hSL) eL heS
  let φK := subgroupOfMapEquiv (barM_mono (M := Y) hKL) (barM_mono (M := X) hKL) eL heK
  have hpcK := CFSG.pCore_map_iso 2 φK
  refine ⟨hV, n, hn, ⟨eL.symm.trans ea⟩,
    barM_pCore_transfer hLY hLX h hSL hKL hpc, ?_, ?_, ?_⟩
  · exact isElemAbelian_of_mulEquiv_sub φS hab
  · exact (Nat.card_congr φS.toEquiv).symm.trans hcard
  · exact ⟨(QuotientGroup.congr (CFSG.pCore 2 ↥(barM Y (Subgroup.normalizer (S : Set G) ⊓ L)))
      (CFSG.pCore 2 ↥(barM X (Subgroup.normalizer (S : Set G) ⊓ L))) φK hpcK).symm.trans hq⟩

theorem nineThreeSevenNat_of_le (hYX : Y ≤ X) (hLY : L ≤ Y)
    (h : L ⊓ CFSG.Open.pCoreOf 2 X = L ⊓ CFSG.Open.pCoreOf 2 Y) :
    NineThreeSevenNat Y S L → NineThreeSevenNat X S L := by
  have hLX : L ≤ X := hLY.trans hYX
  rintro ⟨hV, n, hn, ⟨ea⟩, ⟨hq⟩⟩
  have hKL : Subgroup.normalizer (S : Set G) ⊓ L ≤ L := inf_le_right
  let eL := barMEquiv hLY hLX h.symm
  have heK := barMEquiv_map_subgroupOf hLY hLX h.symm hKL
  let φK := subgroupOfMapEquiv (barM_mono (M := Y) hKL) (barM_mono (M := X) hKL) eL heK
  have hpcK := CFSG.pCore_map_iso 2 φK
  refine ⟨hV, n, hn, ⟨eL.symm.trans ea⟩, ?_⟩
  exact ⟨(QuotientGroup.congr (CFSG.pCore 2 ↥(barM Y (Subgroup.normalizer (S : Set G) ⊓ L)))
      (CFSG.pCore 2 ↥(barM X (Subgroup.normalizer (S : Set G) ⊓ L))) φK hpcK).symm.trans hq⟩

end CFSG.HardMathSupport.Cooperstein.Proving

end
