module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011Cons
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011Type

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20 CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.ABGLocalTools

section Basic

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylowOf_of_le {K T : Subgroup G} (hT : IsPGroup 2 ↥T) (hTK : T ≤ K) :
    ∃ P : Subgroup G, IsSylowOf 2 P K ∧ T ≤ P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsPGroup 2 ↥(T.subgroupOf K) := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm
  obtain ⟨Q, hQ⟩ := hT'.exists_le_sylow
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hTK hx⟩, hQ (Subgroup.mem_subgroupOf.2 hx), rfl⟩

theorem card_barOf_eq {z : G} {S R : Subgroup G} (hS2 : IsPGroup 2 ↥S) (hSC : S ≤ Cen z) (hR : R ≤ S) :
    Nat.card ↥(barOf z R) = Nat.card ↥R := by
  have hRC : R ≤ Cen z := hR.trans hSC
  let f : ↥(R.subgroupOf (Cen z)) →* CentralizerBar z := (toBar z).comp (R.subgroupOf (Cen z)).subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (a : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) := (QuotientGroup.eq_one_iff _).1 ha
    have hodd := P34.odd_orderOf_of_mem_pPrimeCore h1
    have haS : ((a : ↥(Cen z)) : G) ∈ S := hR (Subgroup.mem_subgroupOf.1 a.2)
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hS2) ⟨((a : ↥(Cen z)) : G), haS⟩
    have hoa : orderOf (a : ↥(Cen z)) = 2 ^ j := by
      rw [← Subgroup.orderOf_coe (a : ↥(Cen z)), ← hj,
        ← Subgroup.orderOf_coe (⟨((a : ↥(Cen z)) : G), haS⟩ : ↥S)]
    rw [hoa] at hodd
    have hj0 : j = 0 := by
      by_contra hne
      exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, hne⟩)
    rw [hj0, pow_zero, orderOf_eq_one_iff] at hoa
    exact Subtype.ext hoa
  have h1 : barOf z R = f.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]; rfl
  rw [h1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv

theorem card_S_le {z : G} {S : Subgroup G} (hS : IsSylowOf 2 S (Cen z)) (hidx : (RC S z).relIndex S ≤ 4) :
    Nat.card ↥S ≤ 4 * 2 ^ (Nat.card ↥(LBar z)).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 ↥S := hS.isPGroup
  have hSC : S ≤ Cen z := hS.le
  have hRS : RC S z ≤ S := inf_le_left
  have h1 : (RC S z).relIndex S * Nat.card ↥(RC S z) = Nat.card ↥S := by
    have := Subgroup.relIndex_mul_card (RC S z) S
    rwa [inf_eq_left.2 hRS] at this
  have hR2 : IsPGroup 2 ↥(RC S z) := hS2.to_le hRS
  obtain ⟨m, hm⟩ := hR2.exists_card_eq
  have h2 : Nat.card ↥(RC S z) ∣ Nat.card ↥(LBar z) := by
    rw [← card_barOf_eq hS2 hSC hRS]
    exact Subgroup.card_dvd_of_le (barOf_mono' (inf_le_right : RC S z ≤ LC z))
  have hLpos : Nat.card ↥(LBar z) ≠ 0 := Nat.card_pos.ne'
  have hm' : m ≤ (Nat.card ↥(LBar z)).factorization 2 := by
    rw [hm] at h2
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hLpos).1 h2
  calc Nat.card ↥S = (RC S z).relIndex S * Nat.card ↥(RC S z) := h1.symm
    _ ≤ 4 * 2 ^ m := by rw [hm]; exact Nat.mul_le_mul_right _ hidx
    _ ≤ 4 * 2 ^ (Nat.card ↥(LBar z)).factorization 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hm')

end Basic

section Main

variable {G : Type} [Group G] [Finite G]

theorem sylowIn20_of (hCF : CFTypeAut) (h20b : Coprime20b) (hcore : CentCoreProp) : SylowIn20 := by
  intro G _ _ z k S hC g hg hJ
  obtain ⟨q, L₁, L₂, K₁, K₂, hP, hidx, hK⟩ := exists_data2011 hC
  have hconcl := typeData20 hCF h20b hcore hC hg hJ hP hK
  have hctx : Stage2Ctx G z k S := hC.1.ctx.ctx17.ctx
  have hz2 : orderOf z = 2 := hctx.orderOf_z
  have hS : IsSylowOf 2 S (Cen z) := hctx.sylow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzb2 : orderOf (mkH (J0 z g) ⟨z, hJ.z_mem⟩) = 2 := hJ.central.1
  set CJ : Subgroup G := ((Cen z).subgroupOf (J0 z g)).map (J0 z g).subtype with hCJ
  have hCJC : CJ ≤ Cen z := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 hx
  have hCJJ : CJ ≤ J0 z g := by
    rintro _ ⟨x, hx, rfl⟩
    exact x.2
  have htC : zc z g ∈ Cen z := hctx.S_le_Cen hg.t_mem
  have htCJ : zc z g ∈ CJ := ⟨⟨zc z g, hJ.t_mem⟩, Subgroup.mem_subgroupOf.2 htC, rfl⟩
  have hLcard : Nat.card ↥(LBar z) = Nat.card ↥(IVK.Ez (mkH (J0 z g) ⟨z, hJ.z_mem⟩)) := by
    have hq1 : Nat.card ↥L₁ = q * (q ^ 2 - 1) := IVK.Proofs2.card_of_hasSL2Model hP.sl₁
    have hq2 : Nat.card ↥L₂ = q * (q ^ 2 - 1) := IVK.Proofs2.card_of_hasSL2Model hP.sl₂
    have hq1' : Nat.card ↥(barIn (J0 z g) K₁) = q * (q ^ 2 - 1) :=
      IVK.Proofs2.card_of_hasSL2Model hconcl.sl₁
    have hq2' : Nat.card ↥(barIn (J0 z g) K₂) = q * (q ^ 2 - 1) :=
      IVK.Proofs2.card_of_hasSL2Model hconcl.sl₂
    have hprodL := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute L₁ L₂ hP.prod.2.1).1
    have hprodE := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (barIn (J0 z g) K₁)
      (barIn (J0 z g) K₂) hconcl.comm).1
    rw [hP.prod.1, hP.prod.2.2, hq1, hq2] at hprodL
    rw [hconcl.sup, hconcl.inf, Nat.card_zpowers, hzb2, hq1', hq2'] at hprodE
    omega
  have hCenZ : centralizer ({mkH (J0 z g) ⟨z, hJ.z_mem⟩} : Set (HBar (J0 z g))) =
      barIn (J0 z g) (Cen z) := centralizer_mk_eq (J0 z g) hz2 hJ.z_mem
  have hEzle : IVK.Ez (mkH (J0 z g) ⟨z, hJ.z_mem⟩) ≤
      centralizer ({mkH (J0 z g) ⟨z, hJ.z_mem⟩} : Set (HBar (J0 z g))) := Subgroup.map_subtype_le _
  have hA3 : (Nat.card ↥(centralizer ({mkH (J0 z g) ⟨z, hJ.z_mem⟩} : Set (HBar (J0 z g))))).factorization 2 =
      (Nat.card ↥(IVK.Ez (mkH (J0 z g) ⟨z, hJ.z_mem⟩))).factorization 2 + 2 := by
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hEzle
    have hmpos : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hm
      exact Nat.card_pos.ne' hm
    have hdiv : Nat.card ↥(centralizer ({mkH (J0 z g) ⟨z, hJ.z_mem⟩} : Set (HBar (J0 z g)))) /
        Nat.card ↥(IVK.Ez (mkH (J0 z g) ⟨z, hJ.z_mem⟩)) = m := by
      rw [hm]; exact Nat.mul_div_cancel_left m Nat.card_pos
    have hv := hconcl.val2
    rw [hdiv] at hv
    rw [hm, Nat.factorization_mul Nat.card_pos.ne' hmpos, Finsupp.add_apply, hv]
  have hA4 : Nat.card ↥(barIn (J0 z g) (Cen z)) ∣ Nat.card ↥CJ := by
    have h1 : Nat.card ↥(barIn (J0 z g) (Cen z)) ∣ Nat.card ↥((Cen z).subgroupOf (J0 z g)) :=
      Subgroup.card_map_dvd _ _
    have h2 : Nat.card ↥CJ = Nat.card ↥((Cen z).subgroupOf (J0 z g)) :=
      Subgroup.card_map_of_injective (J0 z g).subtype_injective
    rwa [h2]
  have hvdvd : (Nat.card ↥(centralizer ({mkH (J0 z g) ⟨z, hJ.z_mem⟩} : Set (HBar (J0 z g))))).factorization 2 ≤
      (Nat.card ↥CJ).factorization 2 := by
    rw [hCenZ]
    exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hA4 2
  have hSc : Nat.card ↥S = 2 ^ (Nat.card ↥(Cen z)).factorization 2 := hS.card_eq
  have hvC : (Nat.card ↥(Cen z)).factorization 2 ≤ (Nat.card ↥CJ).factorization 2 := by
    have h1 : 2 ^ (Nat.card ↥(Cen z)).factorization 2 ≤
        4 * 2 ^ (Nat.card ↥(LBar z)).factorization 2 := hSc ▸ card_S_le hS hidx
    rw [hLcard] at h1
    have h2 : 4 * 2 ^ (Nat.card ↥(IVK.Ez (mkH (J0 z g) ⟨z, hJ.z_mem⟩))).factorization 2 =
        2 ^ ((Nat.card ↥(IVK.Ez (mkH (J0 z g) ⟨z, hJ.z_mem⟩))).factorization 2 + 2) := by ring
    rw [h2] at h1
    have h3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
    omega
  have hTp : IsPGroup 2 ↥(zpowers (zc z g)) := hS.isPGroup.to_le (Subgroup.zpowers_le.2 hg.t_mem)
  obtain ⟨S₀, hS₀, htS₀⟩ := exists_isSylowOf_of_le (K := CJ) hTp (Subgroup.zpowers_le.2 htCJ)
  have hcardS₀ : Nat.card ↥S₀ = 2 ^ (Nat.card ↥CJ).factorization 2 := hS₀.card_eq
  have hvle : (Nat.card ↥CJ).factorization 2 ≤ (Nat.card ↥(Cen z)).factorization 2 :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
      (Subgroup.card_dvd_of_le hCJC) 2
  refine ⟨S₀, isSylowOf_of_card (hS₀.le.trans hCJC) ?_, hS₀.le.trans hCJJ,
    htS₀ (Subgroup.mem_zpowers _)⟩
  rw [hcardS₀]
  congr 1
  omega

end Main

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
