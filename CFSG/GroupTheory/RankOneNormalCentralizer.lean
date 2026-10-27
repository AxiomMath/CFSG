module

public import CFSG.Open.LocalVocabulary
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.LocalAnalysis.SteinbergBQControlSylowPromotion
import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient
import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarSylow
import CFSG.LocalAnalysis.SectionRank.PRankIndex
import CFSG.HardMathSupport.Timmesfeld.Proving.PRankQuotient
import CFSG.GroupTheory.ElemAbelianRank
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddNormalizerOrderThreeCentralizes
import CFSG.GroupTheory.QuasiDihedralFusion.CharPowerBasic
import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport

public section

namespace CFSG.GroupTheory

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ}

private lemma isCyclic_of_isSylowOf_of_pRank_le_one {L T : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hT : CFSG.ABGLocalTools.IsSylowOf p T L)
    (hr : CFSG.Open.pRank p L ≤ 1) : IsCyclic T := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hTrank : CFSG.Open.pRank p T ≤ 1 :=
    (CFSG.SectionRank.pRank_mono hp.one_lt hT.le).trans hr
  exact CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_of_pRank_le_one hp hp2
    hT.isPGroup (by rwa [CFSG.SectionRank.pRank_coe_eq_openPRank p T])

private lemma mem_of_relIndex_le_two_of_pow_eq_one {K M : Subgroup G} (hKM : K ≤ M)
    (hidx : K.relIndex M ≤ 2) (hp : p.Prime) (hp2 : p ≠ 2) {x : G}
    (hxM : x ∈ M) (hxp : x ^ p = 1) : x ∈ K := by
  let K' : Subgroup ↥M := K.subgroupOf M
  have hK'idx : K'.index = K.relIndex M := rfl
  have hK'le : K'.index ≤ 2 := by rw [hK'idx]; exact hidx
  have hpos : 0 < K'.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hK'pow : ∃ k : ℕ, K'.index = 2 ^ k := by
    rcases (show K'.index = 1 ∨ K'.index = 2 by omega) with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  haveI : K'.Normal := by
    rcases (show K'.index = 1 ∨ K'.index = 2 by omega) with h | h
    · rw [Subgroup.index_eq_one.mp h]; infer_instance
    · exact Subgroup.normal_of_index_eq_two h
  have hodd : Odd (orderOf (⟨x, hxM⟩ : ↥M)) := by
    have h1 : Odd (orderOf x) :=
      Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hxp)
    have hcoe : orderOf (⟨x, hxM⟩ : ↥M) = orderOf x := by
      simpa using (Subgroup.orderOf_coe (⟨x, hxM⟩ : ↥M)).symm
    rw [hcoe]; exact h1
  exact Subgroup.mem_subgroupOf.mp
    (CFSG.QuasiDihedralFusion.mem_of_odd_orderOf_of_two_pow_index K' hK'pow hodd)

theorem pRank_le_two_of_relIndex_sup_le_two (hp : p.Prime) (hp2 : p ≠ 2) {M L C : Subgroup G}
    (hLM : L ≤ M) (hCM : C ≤ M) (hL : M ≤ Subgroup.normalizer (L : Set G))
    (hidx : (L ⊔ C).relIndex M ≤ 2) (hLr : CFSG.Open.pRank p L ≤ 1)
    (hCr : CFSG.Open.pRank p C ≤ 1) : CFSG.Open.pRank p M ≤ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine CFSG.SectionRank.pRank_le hp.one_lt ?_
  intro E hEM hE
  have hE_LC : E ≤ L ⊔ C := fun e he =>
    mem_of_relIndex_le_two_of_pow_eq_one (K := L ⊔ C) (M := M) (sup_le hLM hCM) hidx
      hp hp2 (hEM he) (hE.2 e he)
  let L' : Subgroup ↥M := L.subgroupOf M
  let C' : Subgroup ↥M := C.subgroupOf M
  let E' : Subgroup ↥M := E.subgroupOf M
  haveI hL'normal : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hL
  have hE'le : E' ≤ L' ⊔ C' := by
    intro x hx
    have hx' : x ∈ (L ⊔ C).subgroupOf M :=
      Subgroup.mem_subgroupOf.mpr (hE_LC (Subgroup.mem_subgroupOf.mp hx))
    rwa [Subgroup.subgroupOf_sup hLM hCM] at hx'
  have hL'rank : CFSG.Open.pRank p L' ≤ 1 := by
    rw [CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_subgroupOf p hLM]; exact hLr
  have hC'rank : CFSG.Open.pRank p C' ≤ 1 := by
    rw [CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_subgroupOf p hCM]; exact hCr
  let π : ↥M →* ↥M ⧸ L' := QuotientGroup.mk' L'
  let Cimg : Subgroup (↥M ⧸ L') := C'.map π
  have hCimg : CFSG.Open.pRank p Cimg ≤ 1 := by
    let φ : ↥C' →* ↥Cimg :=
      (π.comp C'.subtype).codRestrict Cimg fun x => Subgroup.mem_map_of_mem π x.2
    have hφ : Function.Surjective φ := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, rfl⟩
    have hC'gr : CFSG.pRank p ↥C' ≤ 1 := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank p C']; exact hC'rank
    have h := CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.pRank_le_one_of_surjective
      hp hp2 hC'gr φ hφ
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank p Cimg] at h
  let Eimg : Subgroup (↥M ⧸ L') := E'.map π
  have hL'bot : L'.map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hEimg_le : Eimg ≤ Cimg := by
    calc Eimg ≤ (L' ⊔ C').map π := Subgroup.map_mono hE'le
      _ = L'.map π ⊔ C'.map π := Subgroup.map_sup L' C' π
      _ = Cimg := by rw [hL'bot, bot_sup_eq]
  have hEimg : CFSG.Open.pRank p Eimg ≤ 1 :=
    (CFSG.SectionRank.pRank_mono hp.one_lt hEimg_le).trans hCimg
  have hsub := CFSG.HardMathSupport.Timmesfeld.Proving.pRank_le_pRank_inf_add_pRank_map
    hp E' L'
  have hInf : CFSG.Open.pRank p (E' ⊓ L') ≤ 1 :=
    (CFSG.SectionRank.pRank_mono hp.one_lt inf_le_right).trans hL'rank
  have hErank : CFSG.Open.pRank p E ≤ 2 := by
    rw [← CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_subgroupOf p hEM]
    change CFSG.Open.pRank p E' ≤ 2
    have hsub' : CFSG.Open.pRank p E' ≤
        CFSG.Open.pRank p (E' ⊓ L') + CFSG.Open.pRank p Eimg := hsub
    omega
  rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp hE]
  exact Nat.pow_le_pow_right hp.pos hErank

private lemma relIndex_inf_centralizer_inf_normalizer_le_two {M A : Subgroup G}
    (hA3 : Nat.card A = 3) :
    (M ⊓ Subgroup.centralizer (A : Set G)).relIndex
      (M ⊓ Subgroup.normalizer (A : Set G)) ≤ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Subgroup G := M ⊓ Subgroup.centralizer (A : Set G)
  let N : Subgroup G := M ⊓ Subgroup.normalizer (A : Set G)
  change C.relIndex N ≤ 2
  have hNM : N ≤ M := inf_le_left
  let ρ : ↥N →* MulAut ↥A := (Subgroup.normalizerMonoidHom A).comp
    (Subgroup.inclusion (inf_le_right : N ≤ Subgroup.normalizer (A : Set G)))
  have hker : ρ.ker = C.subgroupOf N := by
    rw [show ρ = (Subgroup.normalizerMonoidHom A).comp
        (Subgroup.inclusion (inf_le_right : N ≤ Subgroup.normalizer (A : Set G))) from rfl,
      ← MonoidHom.comap_ker, Subgroup.normalizerMonoidHom_ker,
      Subgroup.comap_inclusion_subgroupOf]
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, C]
    simp [hNM x.2]
  have hrel : C.relIndex N = Nat.card ρ.range := by
    rw [← Subgroup.index_ker ρ, hker]
    rfl
  have hAut : Nat.card (MulAut ↥A) = 2 := by
    letI : IsCyclic ↥A := isCyclic_of_prime_card hA3
    rw [IsCyclic.card_mulAut, hA3, Nat.totient_prime Nat.prime_three]
  have hdvd : Nat.card ρ.range ∣ Nat.card (MulAut ↥A) :=
    Subgroup.card_subgroup_dvd_card ρ.range
  rw [hAut] at hdvd
  rw [hrel]
  exact Nat.le_of_dvd (by norm_num) hdvd

theorem relIndex_sup_inf_centralizer_le_two {M L A : Subgroup G} (hLM : L ≤ M)
    (hL : M ≤ Subgroup.normalizer (L : Set G)) (hAL : A ≤ L) (hA3 : Nat.card A = 3)
    (hr : CFSG.Open.pRank 3 L ≤ 1) :
    (L ⊔ (M ⊓ Subgroup.centralizer (A : Set G))).relIndex M ≤ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Subgroup G := M ⊓ Subgroup.centralizer (A : Set G)
  let N : Subgroup G := M ⊓ Subgroup.normalizer (A : Set G)
  change (L ⊔ C).relIndex M ≤ 2
  have hCM : C ≤ M := inf_le_left
  have hCN : C ≤ N := inf_le_inf_left M (Subgroup.centralizer_le_normalizer (A : Set G))
  have hNM : N ≤ M := inf_le_left
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := fun x hx => hL hx.1
  have hCL : C ≤ Subgroup.normalizer (L : Set G) := hCN.trans hNL
  have hA3p : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by rw [hA3]; norm_num)
  obtain ⟨T, hT, hAT⟩ :=
    CFSG.RankThree.PartTwo.Sec11.Item1120V0Bar.exists_isSylowOf_ge hAL hA3p
  have hTcyc : IsCyclic T :=
    isCyclic_of_isSylowOf_of_pRank_le_one Nat.prime_three (by norm_num) hT hr
  have hNT : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (A : Set G) :=
    CFSG.LocalAnalysis.SteinbergBQ.normalizer_le_normalizer_of_le_isCyclic hAT hTcyc
  have hM_le : M ≤ L ⊔ N := by
    intro x hx
    obtain ⟨l, hl, n, hn, hln⟩ :=
      CFSG.RankThree.PartTwo.Sec18.exists_mul_of_isSylowOf hT hL hx
    have hnM : n ∈ M := by
      have h1 : l⁻¹ * x ∈ M := M.mul_mem (M.inv_mem (hLM hl)) hx
      simpa [show n = l⁻¹ * x by rw [hln]; group] using h1
    have hnN : n ∈ N := Subgroup.mem_inf.mpr ⟨hnM, hNT hn⟩
    rw [hln]
    exact Subgroup.mul_mem_sup hl hnN
  have hM_eq : L ⊔ N = M := le_antisymm (sup_le hLM hNM) hM_le
  have hCrelN : C.relIndex N ≤ 2 :=
    relIndex_inf_centralizer_inf_normalizer_le_two hA3
  have hLN : L.relIndex M = (L ⊓ N).relIndex N := by
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hNL).2
    rwa [sup_comm, hM_eq, inf_comm] at h
  have hLC : L.relIndex (L ⊔ C) = (L ⊓ C).relIndex C := by
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hCL).2
    rwa [sup_comm, inf_comm] at h
  have hEN : L ⊓ C ≤ L ⊓ N := inf_le_inf_left L hCN
  have hErelN : (L ⊓ C).relIndex N = (L ⊓ C).relIndex C * C.relIndex N := by
    have h := Subgroup.relIndex_inf_mul_relIndex (H := L ⊓ C) (K := C) (L := N)
    rw [inf_eq_left.mpr hCN, inf_eq_left.mpr inf_le_right] at h
    exact h.symm
  have hDrelN : (L ⊓ N).relIndex N ≤ (L ⊓ C).relIndex C * 2 := by
    calc (L ⊓ N).relIndex N ≤ (L ⊓ C).relIndex N :=
          Subgroup.relIndex_le_of_le_left hEN (by
          dsimp [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
      _ = (L ⊓ C).relIndex C * C.relIndex N := hErelN
      _ ≤ (L ⊓ C).relIndex C * 2 := Nat.mul_le_mul_left _ hCrelN
  have hmul := Subgroup.relIndex_mul_relIndex (H := L) (K := L ⊔ C) (L := M)
    le_sup_left (sup_le hLM hCM)
  rw [hLC] at hmul
  have hineq : (L ⊓ C).relIndex C * (L ⊔ C).relIndex M ≤ (L ⊓ C).relIndex C * 2 := by
    rw [hmul, hLN]
    exact hDrelN
  exact Nat.le_of_mul_le_mul_left hineq
    (Nat.pos_of_ne_zero (by dsimp [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite))

theorem two_le_pRank_inf_centralizer (hp : p.Prime) (hp2 : p ≠ 2) {M L A : Subgroup G}
    (hLM : L ≤ M) (hL : M ≤ Subgroup.normalizer (L : Set G)) (hAL : A ≤ L)
    (hA3 : Nat.card A = 3) (hr3 : CFSG.Open.pRank 3 L ≤ 1) (hrp : CFSG.Open.pRank p L ≤ 1)
    (hM : 3 ≤ CFSG.Open.pRank p M) :
    2 ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (A : Set G)) := by
  by_contra h
  rw [not_le] at h
  have hidx : (L ⊔ (M ⊓ Subgroup.centralizer (A : Set G))).relIndex M ≤ 2 :=
    relIndex_sup_inf_centralizer_le_two hLM hL hAL hA3 hr3
  have hrank := pRank_le_two_of_relIndex_sup_le_two hp hp2 hLM inf_le_left hL hidx hrp
    (by omega)
  omega

theorem dvd_relIndex_of_pRank_lt (hp : p.Prime) {C D : Subgroup G} (hDC : D ≤ C)
    (hlt : CFSG.Open.pRank p D < CFSG.Open.pRank p C) : p ∣ D.relIndex C := by
  by_contra h
  haveI : Fact p.Prime := ⟨hp⟩
  have hnot : ¬ p ∣ (D.subgroupOf C).index := by
    simpa [Subgroup.relIndex] using h
  have hle := CFSG.SectionRank.pRank_top_le_of_not_dvd_index hp (D.subgroupOf C) hnot
  have hDsub : CFSG.Open.pRank p D = CFSG.Open.pRank p (D.subgroupOf C) :=
    (CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_subgroupOf p hDC).symm
  have hCle : CFSG.Open.pRank p C ≤ CFSG.Open.pRank p D := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (H := C), hDsub]
    exact hle
  omega

theorem exists_orderOf_eq_mem_inf_centralizer (hp : p.Prime) (hp2 : p ≠ 2) {C D A : Subgroup G}
    (hDC : D ≤ C) (hD : C ≤ Subgroup.normalizer (D : Set G)) (hAD : A ≤ D)
    (hA3 : Nat.card A = 3) (hr : CFSG.Open.pRank 3 D ≤ 1) (hdvd : p ∣ D.relIndex C) :
    ∃ y ∈ C ⊓ Subgroup.centralizer (A : Set G), orderOf y = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3p : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by rw [hA3]; norm_num)
  obtain ⟨T, hT, hAT⟩ :=
    CFSG.RankThree.PartTwo.Sec11.Item1120V0Bar.exists_isSylowOf_ge hAD hA3p
  have hTcyc : IsCyclic T :=
    isCyclic_of_isSylowOf_of_pRank_le_one Nat.prime_three (by norm_num) hT hr
  have hNTA : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (A : Set G) :=
    CFSG.LocalAnalysis.SteinbergBQ.normalizer_le_normalizer_of_le_isCyclic hAT hTcyc
  let NC : Subgroup G := C ⊓ Subgroup.normalizer (T : Set G)
  have hC_le : C ≤ D ⊔ NC := by
    intro x hx
    obtain ⟨d, hd, n, hn, hdn⟩ :=
      CFSG.RankThree.PartTwo.Sec18.exists_mul_of_isSylowOf hT hD hx
    have hnC : n ∈ C := by
      have h1 : d⁻¹ * x ∈ C := C.mul_mem (C.inv_mem (hDC hd)) hx
      simpa [show n = d⁻¹ * x by rw [hdn]; group] using h1
    have hnNC : n ∈ NC := Subgroup.mem_inf.mpr ⟨hnC, hn⟩
    rw [hdn]
    exact Subgroup.mul_mem_sup hd hnNC
  have hsup : D ⊔ NC = C := le_antisymm (sup_le hDC inf_le_left) hC_le
  have hND : NC ≤ Subgroup.normalizer (D : Set G) := fun x hx => hD hx.1
  have hrel : D.relIndex C = (D ⊓ NC).relIndex NC := by
    have h := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hND).2
    rwa [sup_comm, hsup, inf_comm] at h
  have hdvd' : p ∣ (D ⊓ NC).relIndex NC := by rw [← hrel]; exact hdvd
  have hmul : (D ⊓ NC).relIndex NC * Nat.card ↥(D ⊓ NC) = Nat.card NC := by
    have h := Subgroup.relIndex_mul_card (H := D ⊓ NC) (K := NC)
    rwa [inf_eq_left.mpr (inf_le_right : D ⊓ NC ≤ NC)] at h
  have hdvdNC : p ∣ Nat.card NC := by
    rw [← hmul]
    exact dvd_mul_of_dvd_left hdvd' _
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥NC) p hdvdNC
  have hyA : (y : G) ∈ Subgroup.normalizer (A : Set G) := hNTA y.2.2
  have hodd : Odd (Nat.card (Subgroup.zpowers (y : G))) := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hyord]
    exact hp.odd_of_ne_two hp2
  have hcent : Subgroup.zpowers (y : G) ≤ Subgroup.centralizer (A : Set G) :=
    CFSG.GorensteinWalter.odd_subgroup_le_centralizer_of_le_normalizer_card_three
      (Subgroup.zpowers (y : G)) A hodd hA3 (Subgroup.zpowers_le.mpr hyA)
  refine ⟨(y : G), Subgroup.mem_inf.mpr ⟨y.2.1, hcent (Subgroup.mem_zpowers _)⟩, ?_⟩
  rw [Subgroup.orderOf_coe, hyord]

end CFSG.GroupTheory

end
