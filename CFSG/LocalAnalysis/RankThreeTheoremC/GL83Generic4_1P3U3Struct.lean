module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Basics
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Quot
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3Shadow
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Structb
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Struct

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem u3_reducedCentralizer_normal {M : Subgroup G} {x : G} {J : Subgroup G}
    (hJ : IsU3Normal M x J) : (reducedCentralizerOfJ x J).Normal := by
  have := r1sBar_normal_u3 hJ
  rw [r1s_reducedCentralizerOfJ_eq]
  infer_instance

theorem u3_bar_inf_reducedCentralizer_eq_bot {M : Subgroup G} {x : G} {J : Subgroup G}
    (hJ : IsU3Normal M x J) : r1sBar x J ⊓ reducedCentralizerOfJ x J = ⊥ := by
  have hZ := u3s_bar_center_eq_bot hJ
  refine eq_bot_iff.mpr fun c hc => ?_
  have hcD : c ∈ centralizer ((r1sBar x J : Subgroup (GenericReduced 3 x)) :
      Set (GenericReduced 3 x)) := by
    rw [← r1s_reducedCentralizerOfJ_eq]
    exact hc.2
  have h1 : (⟨c, hc.1⟩ : ↥(r1sBar x J)) ∈ center ↥(r1sBar x J) :=
    mem_center_iff.mpr fun l => Subtype.ext (mem_centralizer_iff.mp hcD l l.2)
  rw [hZ, mem_bot] at h1
  exact mem_bot.mpr (congrArg Subtype.val h1)

theorem u3s_reducedCentralizer_sylow_cyclic (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : U3SylowData) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsU3Normal M x J) (T : Sylow 3 (reducedCentralizerOfJ x J)) :
    IsCyclic ↥(T : Subgroup (reducedCentralizerOfJ x J)) := by
  obtain ⟨S, -, hsh⟩ := exists_genericShadow3 hS hU0 hp rfl hM hgen
  have := r1sBar_normal_u3 hJ
  exact u3s_sylow_centralizer_cyclic hsh.rank_eq.le (r1s_reducedCentralizerOfJ_eq x J)
    (u3_bar_inf_reducedCentralizer_eq_bot hJ) (fun T => (hK1 _ (r1sBar_isU3 hJ) T).2.2.2.1) T

theorem u3_reducedCentralizer_isPGroup (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : U3SylowData) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsU3Normal M x J) : IsPGroup 3 (reducedCentralizerOfJ x J) := by
  obtain ⟨S, -, hsh⟩ := exists_genericShadow3 hS hU0 hp rfl hM hgen
  have hDn : (reducedCentralizerOfJ x J).Normal := u3_reducedCentralizer_normal hJ
  refine isPGroup_three_of_normal_cyclic_sylow hsh.core_eq_bot hsh.mem_center hsh.orderOf_eq ?_
    (u3s_reducedCentralizer_sylow_cyclic hS hU0 hK1 hp hM hgen hJ)
  rw [r1s_reducedCentralizerOfJ_eq]
  exact mem_centralizer_iff.mpr fun h _ => mem_center_iff.mp hsh.mem_center h

theorem u3_reducedCentralizer_isCyclic (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : U3SylowData) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsU3Normal M x J) : IsCyclic ↥(reducedCentralizerOfJ x J) := by
  have hDp := u3_reducedCentralizer_isPGroup hS hU0 hK1 hp hM hgen hJ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T⟩ : Nonempty (Sylow 3 (reducedCentralizerOfJ x J)) := inferInstance
  have hT : (T : Subgroup (reducedCentralizerOfJ x J)) = ⊤ :=
    (T.3 (hDp.of_equiv Subgroup.topEquiv.symm) le_top).symm
  have hc := u3s_reducedCentralizer_sylow_cyclic hS hU0 hK1 hp hM hgen hJ T
  rw [hT] at hc
  exact isCyclic_of_surjective (Subgroup.topEquiv : (⊤ : Subgroup (reducedCentralizerOfJ x J)) ≃*
    reducedCentralizerOfJ x J) Subgroup.topEquiv.surjective

theorem u3_xbar_facts (hS : Setting G) (hU0 : FullCoreLocal G) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) (J : Subgroup G) :
    QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
        ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩ ∈ reducedCentralizerOfJ x J ∧
      orderOf (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
        ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩) = 3 := by
  obtain ⟨S, -, hsh⟩ := exists_genericShadow3 hS hU0 hp rfl hM hgen
  refine ⟨?_, hsh.orderOf_eq⟩
  rw [reducedCentralizerOfJ, mem_centralizer_iff]
  intro h _
  exact (mem_center_iff.mp hsh.mem_center h)

theorem u3_mem_of_ker_of_mem_J {M : Subgroup G} {x : G} {J : Subgroup G} (hJ : IsU3Normal M x J)
    (c : ↥(centralizer ({x} : Set G))) (hcJ : (c : G) ∈ J) (h1 : l34Hom x J c = 1) :
    c ∈ primeComplementCore (G := centralizer ({x} : Set G)) 3 := by
  set O := primeComplementCore (G := centralizer ({x} : Set G)) 3 with hO
  set D := reducedCentralizerOfJ x J with hD
  have hy : QuotientGroup.mk' O c ∈ r1sBar x J := ⟨c, mem_subgroupOf.mpr hcJ, rfl⟩
  have hyD : QuotientGroup.mk' O c ∈ D := by
    have h : QuotientGroup.mk' D.normalCore (QuotientGroup.mk' O c) = 1 := h1
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h
    exact normalCore_le D h
  have hy1 : QuotientGroup.mk' O c = 1 := by
    have h : QuotientGroup.mk' O c ∈ r1sBar x J ⊓ D := ⟨hy, hyD⟩
    rwa [u3_bar_inf_reducedCentralizer_eq_bot hJ, mem_bot] at h
  rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker]
  exact hy1

theorem u3_phi_injective {M : Subgroup G} {x : G} {J : Subgroup G} (hJ : IsU3Normal M x J) :
    Function.Injective ((QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore).comp
      (r1sBar x J).subtype) := by
  have hDn := u3_reducedCentralizer_normal hJ
  have hbot := u3_bar_inf_reducedCentralizer_eq_bot hJ
  rw [injective_iff_map_eq_one]
  intro j hj
  have hjD : (j : GenericReduced 3 x) ∈ reducedCentralizerOfJ x J := by
    have h : (j : GenericReduced 3 x) ∈
        (QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore).ker := hj
    rwa [QuotientGroup.ker_mk', Subgroup.normalCore_eq_self] at h
  have : (j : GenericReduced 3 x) ∈ r1sBar x J ⊓ reducedCentralizerOfJ x J := ⟨j.2, hjD⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact Subtype.ext this

theorem u3s_img_J_eq (x : G) (J : Subgroup G) :
    l34Img x J J =
      (r1sBar x J).map (QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore) := by
  unfold l34Img l34Hom r1sBar
  rw [Subgroup.map_map]

theorem u3s_phi_range (x : G) (J : Subgroup G) :
    ((QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore).comp (r1sBar x J).subtype).range =
      l34Img x J J := by
  rw [u3s_img_J_eq, MonoidHom.range_comp, Subgroup.range_subtype]

theorem u3_quot_data (_hS : Setting G) (_hU0 : FullCoreLocal G) (_hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (_hM : IsCoreMaxLocal 3 P M) {x : G}
    (_hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsU3Normal M x J) :
    (l34Img x J J).Normal ∧
      centralizer ((l34Img x J J : Subgroup (L34Quot x J)) : Set (L34Quot x J)) = ⊥ ∧
      IsRankThreeU3 ↥(l34Img x J J) := by
  have hJbn := r1sBar_normal_u3 hJ
  have hDn := u3_reducedCentralizer_normal hJ
  set D := reducedCentralizerOfJ x J with hD
  have hcore : D.normalCore = D := Subgroup.normalCore_eq_self D
  have hbot := u3_bar_inf_reducedCentralizer_eq_bot hJ
  set q : GenericReduced 3 x →* L34Quot x J := QuotientGroup.mk' D.normalCore with hq
  have hker : q.ker = D := by rw [hq, QuotientGroup.ker_mk', hcore]
  rw [u3s_img_J_eq]
  refine ⟨hJbn.map q (QuotientGroup.mk'_surjective _), ?_, ?_⟩
  · rw [eq_bot_iff]
    intro z hz
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective D.normalCore z
    have hyD : y ∈ D := by
      rw [hD, r1s_reducedCentralizerOfJ_eq, mem_centralizer_iff]
      intro j hj
      have hqj : q j * q y = q y * q j :=
        mem_centralizer_iff.mp hz (q j) ⟨j, hj, rfl⟩
      have hc : j * (y * j⁻¹ * y⁻¹) ∈ r1sBar x J :=
        Subgroup.mul_mem _ hj (hJbn.conj_mem j⁻¹ (Subgroup.inv_mem _ hj) y)
      have hqc : q (j * (y * j⁻¹ * y⁻¹)) = 1 := by
        calc q (j * (y * j⁻¹ * y⁻¹)) = (q j * q y) * (q j)⁻¹ * (q y)⁻¹ := by
              simp only [map_mul, map_inv]; group
          _ = (q y * q j) * (q j)⁻¹ * (q y)⁻¹ := by rw [hqj]
          _ = 1 := by group
      have hcD : j * (y * j⁻¹ * y⁻¹) ∈ D := by
        rw [← hker]
        exact hqc
      have hc1 : j * (y * j⁻¹ * y⁻¹) = 1 := by
        have : j * (y * j⁻¹ * y⁻¹) ∈ r1sBar x J ⊓ D := ⟨hc, hcD⟩
        rw [hbot, Subgroup.mem_bot] at this
        exact this
      calc j * y = (j * (y * j⁻¹ * y⁻¹)) * (y * j) := by group
        _ = y * j := by rw [hc1, one_mul]
    exact Subgroup.mem_bot.mpr (by rw [← hker] at hyD; exact hyD)
  · have hinj := u3_phi_injective hJ
    have hr : (q.comp (r1sBar x J).subtype).range = (r1sBar x J).map q := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact isU3_of_mulEquiv
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hr)).symm (r1sBar_isU3 hJ)

theorem u3_T_data (_hS : Setting G) (_hU0 : FullCoreLocal G) (hK1 : U3SylowData)
    (_hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (_hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsU3Normal M x J) :
    IsSylowOf 3 (l34Img x J ((P : Subgroup G) ⊓ J)) (l34Img x J J) ∧
      (∀ c : ↥(centralizer ({x} : Set G)), (c : G) ∈ (P : Subgroup G) ⊓ J →
        l34Hom x J c = 1 → c = 1) ∧
      Nat.card ↥((P : Subgroup G) ⊓ J) = 3 ^ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJC := hJ.le_centralizer
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hker : ∀ c : ↥C, (c : G) ∈ (P : Subgroup G) ⊓ J → l34Hom x J c = 1 → c = 1 := by
    intro c hc h1
    have hcO := u3_mem_of_ker_of_mem_J hJ c hc.2 h1
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' ⟨(c : G), hc.1⟩
    have hk' : orderOf c = 3 ^ k := by
      rw [← hk, Subgroup.orderOf_mk (c : G) hc.1, Subgroup.orderOf_coe]
    have h2 : orderOf c ∣ Nat.card (primeComplementCore (G := C) 3) :=
      Subgroup.orderOf_dvd_natCard _ hcO
    have h3 : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_left k (primeComplementCore_coprime 3)) (dvd_of_eq hk') h2
    exact orderOf_eq_one_iff.mp h3
  have hSylJ : IsSylowOf 3 (((P : Subgroup G) ⊓ C) ⊓ J) J :=
    hgen.2.2.1.inf_of_le_normalizer hJC hJ.centralizer_le
  have hPJ : ((P : Subgroup G) ⊓ C) ⊓ J = (P : Subgroup G) ⊓ J := by
    rw [inf_assoc, inf_eq_right.mpr hJC]
  rw [hPJ] at hSylJ
  obtain ⟨T, hT⟩ := hSylJ
  set T' : Sylow 3 ↥(r1sBar x J) := T.mapSurjective (r1sHom_surjective x hJC) with hT'
  have hT'c : Nat.card (T' : Subgroup ↥(r1sBar x J)) = 3 ^ 3 := (hK1 _ (r1sBar_isU3 hJ) T').1
  set φ := (QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore).comp
    (r1sBar x J).subtype with hφ
  have hinj := u3_phi_injective hJ
  have hLHS : l34Img x J ((P : Subgroup G) ⊓ J) = (T' : Subgroup ↥(r1sBar x J)).map φ := by
    rw [hT', Sylow.coe_mapSurjective, Subgroup.map_map]
    unfold l34Img
    rw [← hT]
    have h1 : ((T : Subgroup ↥J).map J.subtype).subgroupOf C =
        (T : Subgroup ↥J).map (Subgroup.inclusion hJC) := by
      ext c
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨j, hj, hjc⟩
        exact ⟨j, hj, Subtype.ext hjc⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j, hj, rfl⟩
    have h2 : (l34Hom x J).comp (Subgroup.inclusion hJC) = φ.comp (r1sHom x hJC) :=
      MonoidHom.ext fun j => rfl
    rw [h1, Subgroup.map_map, h2]
  have hcard : Nat.card ↥((P : Subgroup G) ⊓ J) = 3 ^ 3 := by
    set H : Subgroup ↥C := ((P : Subgroup G) ⊓ J).subgroupOf C with hH
    have hinjH : Function.Injective ((l34Hom x J).comp H.subtype) := by
      rw [injective_iff_map_eq_one]
      intro h hh
      exact Subtype.ext (hker h (Subgroup.mem_subgroupOf.mp h.2) hh)
    have hrange : ((l34Hom x J).comp H.subtype).range = l34Img x J ((P : Subgroup G) ⊓ J) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rfl
    have e1 : Nat.card ↥H = Nat.card ↥(l34Img x J ((P : Subgroup G) ⊓ J)) := by
      rw [← hrange]
      exact Nat.card_congr (MonoidHom.ofInjective hinjH).toEquiv
    have e2 : Nat.card ↥H = Nat.card ↥((P : Subgroup G) ⊓ J) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hJC)).toEquiv
    rw [← e2, e1, hLHS, Subgroup.card_map_of_injective hinj, hT'c]
  refine ⟨?_, hker, hcard⟩
  rw [hLHS, ← u3s_phi_range x J]
  refine isSylowOf_of_card (Subgroup.map_le_range φ _) ?_
  rw [Subgroup.card_map_of_injective hinj, Sylow.card_eq_multiplicity,
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]

end CFSG.LocalAnalysis.RankThreeTheoremC
