module

public import CFSG.GH74.Generic.BProg.NS.Promote
public import CFSG.GH74.Generic.S3.BFreeNbhd

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.L5U5 CFSG.GH74.GLS.TwoThin
  CFSG.GH74.E2 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

theorem lxyLiftAt_of_liftJ2NS
    (hG : GenericKnownFacts) (hE : E2ComponentFacts) (hFR : L3FRank)
    (hL1 : B_Gen4_liftJ2NS) (hTab : B_S3_pumpupStep)
    {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S3Setup G x K) (hmax : IsJMax x K) (hthin : ¬ GLS.HasTwoThinConfiguration G) :
    LxyLiftAt x K := by
  rintro t p f y Iw Iv hnd himg L hLc hle ⟨t', ht', hmodelL, -⟩
  have hy2 : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hnd.y_inv, pow_two] at this
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hnd.x_inv, pow_two] at this
  have hyx2 : orderOf (y * x) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · calc (y * x) ^ 2 = (y * x) * (y * x) := by rw [pow_two]
        _ = y * (x * y) * x := by group
        _ = y * (y * x) * x := by rw [hnd.comm]
        _ = (y * y) * (x * x) := by group
        _ = 1 := by rw [hy2, hx2, one_mul]
    · intro h
      apply hnd.ne
      calc y = y * (x * x) := by rw [hx2, mul_one]
        _ = (y * x) * x := by rw [mul_assoc]
        _ = x := by rw [h, one_mul]
  obtain ⟨⟨p₀, f₀, -, -, -, hmodelK₀⟩, -⟩ := hset.shape
  have hKcen : center ↥K = ⊥ := center_eq_bot_of_quasisimple_lieModel_L3 hset.comp.1 hmodelK₀
  have hKnt : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hset.comp.1
  have hmodelK : LieModel ↥K t 3 p f := hnd.lxy_lieModel_K himg hKcen hKnt
  have hmodelL' : LieModel ↥L .PSL 3 p f ∨ LieModel ↥L .PSU 3 p f := by
    rcases ht' with rfl | rfl
    · exact Or.inl hmodelL
    · exact Or.inr hmodelL
  have hLcen : center ↥L = ⊥ := center_eq_bot_of_quasisimple_lieModel_L3 hLc.1 hmodelL'
  have hxbarL : xbar (y * x) ∉ L := xbar_not_mem_of_center_eq_bot hyx2 hLcen
  have hshapeL : ShapeS3 (y * x) L :=
    ⟨⟨p, f, hnd.prime.1, hnd.prime.2.1, hnd.prime.2.2, hmodelL'⟩, hxbarL⟩
  have hKP : GLS.IsKProperSimple G :=
    ⟨hset.simple, hset.nonab, CFSG.GH74.kProper_of_kgh hset.kgh⟩
  have hgenK : Gen4Comp ↥K := gen4Comp_of_gen4Cen (gen4Cen_barQ hset.gen4 hset.inv) K
  have hgenL : Gen4Comp ↥L := gen4Comp_of_gen4Cen (gen4Cen_barQ hset.gen4 hyx2) L
  have hFK := hFR ↥K t p f hnd.tag hnd.prime.1 hnd.prime.2.1 hnd.prime.2.2 hgenK hmodelK
  have hFL := hFR ↥L t' p f ht' hnd.prime.1 hnd.prime.2.1 hnd.prime.2.2 hgenL hmodelL
  have hLcl := l3_not_inC2_not_inT2 hG hE ht' hnd.prime.1 hnd.prime.2.1 hnd.prime.2.2 hgenL hmodelL
  have hG2L : GLS.InG2 ↥L :=
    ⟨GLS.inCalK2_of_isComponent hKP hyx2 hLc, hLcl.1, hLcl.2⟩
  have hsetL : S3Setup G (y * x) L :=
    ⟨hset.simple, hset.nonab, hset.rank, hset.gen4, hset.kgh, hset.sylow, hset.layerNe, hyx2, hLc,
      hG2L, hshapeL⟩
  have hd2K : d2 ↥K = 7 := d2_eq_seven_of_shapeS3 hset.comp hset.g2 hset.shape
  have hd2L : d2 ↥L = 7 := d2_eq_seven_of_shapeS3 hLc hG2L hshapeL
  have hFeq : FRank ↥K = FRank ↥L := by rw [hFK, hFL]
  have hmaxL : IsJMax (y * x) L :=
    ⟨⟨hyx2, hLc, hG2L⟩, fun y' L' hp' => by
      obtain ⟨h1, h2⟩ := hmax.2 y' L' hp'
      refine ⟨by omega, fun hd => ?_⟩
      have h3 := h2 (by omega)
      omega⟩
  exact liftCentralAt_of_isJMaxNS hL1 hTab hsetL hmaxL hthin

end CFSG.GH74.Generic.BProg
