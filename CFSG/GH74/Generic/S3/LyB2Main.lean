module

public import CFSG.GH74.Generic.S3.LyB2G2
public import CFSG.GH74.Generic.S3.LyB2Closure
public import CFSG.GH74.Generic.S3.LyB2Term
public import CFSG.GH74.Generic.S3.LyVertMain

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup

theorem lyVertB2SL2_proved
    (hF : GenericKnownFacts) (hKG : TwoThinKGroupFactQ Gen4Cen) : LyVertB2SL2 := by
  intro G _ _ x K hset hmax hnt honly t p f y Iw Iv hnd himg L hL hv hle hB2
  by_contra hnot
  have hKP : IsKProperSimple G :=
    ⟨hset.simple, hset.nonab, CFSG.GH74.kProper_of_kgh hset.kgh⟩
  have hG2 : G2Table G := g2Table_of_jmax hF hset hmax
  have h3 : 3 ≤ pRank 2 G := by
    rw [pRank_two_eq_twoRank]
    exact hset.rank
  have hR : ∀ z : G, orderOf z = 2 → 3 ≤ pRank 2 ↥(centralizer ({z} : Set G)) :=
    fun z hz => rankThreeCentralizers G hset.simple hset.nonab h3 z hz
  obtain ⟨Î, hÎ, ⟨e⟩⟩ := exists_pComponent_of_component hL
  have hPair : IsB2Pair y Î := by
    refine ⟨⟨hnd.y_inv, by simpa [oBound] using hR y hnd.y_inv, hÎ⟩, ?_⟩
    exact inB2_of_mulEquiv e.symm hB2
  have hcls : ¬ HasSL2Model (↥Î ⧸ pPrimeCore 2 ↥Î) Odd := fun ⟨F, hF', hfin, hodd, ⟨eS⟩⟩ =>
    hnot ⟨F, hF', hfin, hodd, ⟨e.symm.trans eS⟩⟩
  have hclosed : ClsClosed (G := G)
      (fun _ K' => ¬ HasSL2Model (↥K' ⧸ pPrimeCore 2 ↥K') Odd) :=
    fun _ _ _ _ hP hc hlt htype => closure_exc hset.gen4 hKP hKG hG2 hP hc hlt htype
  exact hnt (hasTwoThinConfiguration_of_cls _ hR hclosed ⟨y, Î, hPair, hcls⟩)

end CFSG.GH74.Generic.S3
