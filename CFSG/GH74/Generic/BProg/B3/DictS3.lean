module

public import CFSG.GH74.Generic.BProg.B3.DictRepair
public import CFSG.GH74.Generic.BProg.B3.DictCommon
public import CFSG.GH74.Generic.BProg.B3.DictS3Adm
public import CFSG.GH74.Generic.BProg.B3.DictS3Nbr
public import CFSG.GH74.Generic.BProg.B1.PilotS3

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup

theorem dictS3J_proved : DictS3J := by
  intro G _ _ x K hset hmax hthin honly t p f y Iw Iv hnd himg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx : orderOf x = 2 := hset.inv
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hIwC : Iw ≤ centralizer ({x} : Set G) := hnd.comp_w.1.1
  have hIwq : IsQuasisimple ↥Iw := hnd.comp_w.1.isQuasisimple
  have hyIw : y ∈ Iw := hnd.Iv_le hnd.y_Iv
  have hIwP : IsPCompIn 2 (centralizer ({x} : Set G)) Iw :=
    S3.isPCompIn_of_subnormal_block hIwC hnd.comp_w.1.2.2 hIwq
  have hmin : ∀ (z : G) (L : Subgroup (CentralizerBar z)), G2Pair z L → d2 ↥K ≤ d2 ↥L :=
    fun z L hp => (hmax.2 z L hp).1
  have hd7 : d2 ↥K = 7 := d2_eq_seven_of_shapeS3 hset.comp hset.g2 hset.shape
  have hNo : NoAltJ2 G :=
    noAltJ2_of_minDepth hset.simple hset.nonab hset.rank hset.kgh hx hset.comp hset.g2 hmin (Or.inr hd7)
  have hJ2 : IsJ2 x Iw :=
    isJ2_of_isPCompIn hset.simple hset.nonab hset.rank hset.kgh hx hset.comp hset.g2 hmin honly hIwP himg
  refine ⟨hNo, hJ2, ?_⟩
  obtain ⟨eK⟩ := B1.PilotS5.hat_equiv_imgBar hIwP
  have eK' : (↥Iw ⧸ pPrimeCore 2 ↥Iw) ≃* ↥K := eK.trans (MulEquiv.subgroupCongr himg)
  have h3 : QShape3 (↥Iw ⧸ pPrimeCore 2 ↥Iw) := by
    obtain ⟨⟨p', f', hp', hp2', hq5', hmodel'⟩, -⟩ := hset.shape
    refine ⟨p', f', hp', hp2', by omega, ?_⟩
    rcases hmodel' with hm | hm
    · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eK'.symm hm)
    · exact Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eK'.symm hm)
  have hxIw : x ∉ Iw := by
    intro hxI
    have h1 : xbar x ∈ S3.imgBar x Iw := S3.mem_imgBar.2 ⟨⟨x, hxC⟩, hxI, rfl⟩
    rw [himg] at h1
    exact hset.shape.2 h1
  obtain ⟨E, hEIw, hyE, hEel, hE4⟩ := exists_four_mem_of_nbrData hnd
  refine ⟨E ⊔ zpowers x, isSource2_of_four hx hIwP hxIw h3 hEIw hEel hE4, ?_⟩
  have hZ := B1.PilotS3.center_trivial_of_shape3 hIwP h3
  obtain ⟨F, _, _, P, _, ⟨e⟩, hP⟩ := B1.PilotS3.exists_equiv_grpS3_of_qShape3 h3
  have hY : B1.PilotS3.Split3Like F (S3.imgBar x Iw) :=
    B1.PilotS3.Split3Like.of_equiv (eK.symm.trans e) hP (B1.PilotS3.center_trivial_of_equiv eK hZ)
  have hy1 : y ≠ 1 := by
    intro hh
    have := hnd.y_inv
    rw [hh, orderOf_one] at this
    omega
  obtain ⟨hbmem, -, hb2⟩ := B1.PilotS5.bar_facts hIwC hyIw hnd.y_inv
  obtain ⟨J, hJY, hJ⟩ := hY.split (bar x y) hbmem hb2
  rw [imgBar_Iv_eq_split3 hnd hJY hJ]
  exact isAdmPair_of_split3_at hx hIwP hxIw hY hEIw rfl hEel hE4 hyE hy1 hJY hJ

end CFSG.GH74.Generic.BProg.B3
