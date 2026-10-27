module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Quot
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3Shadow
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Struct4
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34b
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Basics

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l34_reducedCentralizer_sylow_cyclic (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J)
    (T : Sylow 3 (reducedCentralizerOfJ x J)) :
    IsCyclic ↥(T : Subgroup (reducedCentralizerOfJ x J)) := by
  obtain ⟨S, -, hsh⟩ := exists_genericShadow3 hS hU0 hp rfl hM hgen
  have := r1sBar_normal_l34 hJ
  have := r1sBar_perfect_l34 hJ
  exact r1s_sylow_centralizer_cyclic hsh.rank_eq.le (r1s_reducedCentralizerOfJ_eq x J)
    (r1sBar_sylow_facts_l34 hK1 hK2 hJ) T

theorem l34_reducedCentralizer_isPGroup (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J) :
    IsPGroup 3 (reducedCentralizerOfJ x J) := by
  obtain ⟨S, -, hsh⟩ := exists_genericShadow3 hS hU0 hp rfl hM hgen
  have := r1sBar_normal_l34 hJ
  have hDn : (reducedCentralizerOfJ x J).Normal := by
    rw [r1s_reducedCentralizerOfJ_eq]
    infer_instance
  refine isPGroup_three_of_normal_cyclic_sylow hsh.core_eq_bot hsh.mem_center hsh.orderOf_eq ?_
    (l34_reducedCentralizer_sylow_cyclic hS hU0 hK1 hK2 hp hM hgen hJ)
  rw [r1s_reducedCentralizerOfJ_eq]
  exact mem_centralizer_iff.mpr fun h _ => mem_center_iff.mp hsh.mem_center h

theorem l34_reducedCentralizer_isCyclic (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J) :
    IsCyclic ↥(reducedCentralizerOfJ x J) := by
  have hDp := l34_reducedCentralizer_isPGroup hS hU0 hK1 hK2 hp hM hgen hJ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T⟩ : Nonempty (Sylow 3 (reducedCentralizerOfJ x J)) := inferInstance
  have hT : (T : Subgroup (reducedCentralizerOfJ x J)) = ⊤ :=
    (T.3 (hDp.of_equiv Subgroup.topEquiv.symm) le_top).symm
  have hc := l34_reducedCentralizer_sylow_cyclic hS hU0 hK1 hK2 hp hM hgen hJ T
  rw [hT] at hc
  exact isCyclic_of_surjective (Subgroup.topEquiv : (⊤ : Subgroup (reducedCentralizerOfJ x J)) ≃*
    reducedCentralizerOfJ x J) Subgroup.topEquiv.surjective

theorem l34_bar_inf_reducedCentralizer_eq_bot {M : Subgroup G} {x : G} {J : Subgroup G}
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hJ : IsL34Normal M x J) :
    r1sBar x J ⊓ reducedCentralizerOfJ x J = ⊥ := by
  have := r1sBar_perfect_l34 hJ
  exact r1s_inf_centralizer_eq_bot (r1s_reducedCentralizerOfJ_eq x J) fun T =>
    ⟨(r1sBar_sylow_facts_l34 hK1 hK2 hJ T).1.1, (r1sBar_sylow_facts_l34 hK1 hK2 hJ T).2.2⟩

theorem l34_inf_ne_bot {P : Sylow 3 G} {x : G} {J : Subgroup G} (hx1 : x ≠ 1)
    (hR1 : L34Prop34 3 P J x) {U : Subgroup G} (hU : IsElemAbelian 3 U)
    (hUc : Nat.card U = 3 ^ 2) (hUP : U ≤ (P : Subgroup G)) (hxU : x ∈ U) : U ⊓ J ≠ ⊥ := by
  obtain ⟨hPC, hEel, hEcard, hΩ, -⟩ := hR1
  by_cases hxJ : x ∈ J
  · intro h
    have : x ∈ U ⊓ J := ⟨hxU, hxJ⟩
    rw [h, Subgroup.mem_bot] at this
    exact hx1 this
  set A : Subgroup G := (P : Subgroup G) ⊓ J with hA
  set E : Subgroup G := A ⊔ zpowers x with hE
  have hx3 : x ^ 3 = 1 := hU.2 x hxU
  have hxA : x ∉ A := fun h => hxJ h.2
  have hAx : ∀ a ∈ A, a * x = x * a := fun a ha =>
    (mem_centralizer_iff.mp (hPC ha.1) x rfl).symm
  have hcardA : Nat.card A = 3 ^ 2 := by
    have h := CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three A hx3 hxA hAx
    rw [← hE, hEcard] at h
    omega
  have hUE : U ≤ E := fun u hu => hΩ u (hUP hu) (hU.2 u hu)
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    p34_comm_of_isMulCommutative hEel.1 ha hb
  intro hUJ
  have hUA : U ⊓ A = ⊥ := eq_bot_iff.mpr fun g hg =>
    (Subgroup.mem_bot).mpr (by
      have : g ∈ U ⊓ J := ⟨hg.1, hg.2.2⟩
      rw [hUJ, Subgroup.mem_bot] at this
      exact this)
  obtain ⟨u₁, hu₁U, hu₁1⟩ : ∃ u ∈ U, u ≠ 1 := by
    by_contra hno
    push Not at hno
    have h1 : U ≤ ⊥ := fun u hu => (Subgroup.mem_bot).mpr (hno u hu)
    have := Subgroup.card_le_of_le h1
    rw [hUc, Subgroup.card_bot] at this
    omega
  have hu₁3 : u₁ ^ 3 = 1 := hU.2 u₁ hu₁U
  have hu₁A : u₁ ∉ A := fun h => hu₁1 (by
    have : u₁ ∈ U ⊓ A := ⟨hu₁U, h⟩
    rw [hUA, Subgroup.mem_bot] at this
    exact this)
  have hAu : ∀ a ∈ A, a * u₁ = u₁ * a := fun a ha =>
    hcomm a ((le_sup_left : A ≤ E) ha) u₁ (hUE hu₁U)
  have hE' := CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three A hu₁3 hu₁A hAu
  have hle : A ⊔ zpowers u₁ ≤ E := sup_le le_sup_left (zpowers_le.mpr (hUE hu₁U))
  have hEeq : A ⊔ zpowers u₁ = E := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hE', hcardA, hEcard]
    norm_num
  obtain ⟨u₂, hu₂U, hu₂⟩ : ∃ u ∈ U, u ∉ zpowers u₁ := by
    by_contra hno
    push Not at hno
    have h1 : U ≤ zpowers u₁ := fun u hu => hno u hu
    have := Subgroup.card_le_of_le h1
    rw [hUc, Nat.card_zpowers, orderOf_eq_prime hu₁3 hu₁1] at this
    omega
  have hu₂E : u₂ ∈ ((A ⊔ zpowers u₁ : Subgroup G) : Set G) := hEeq ▸ hUE hu₂U
  have hAN : A ≤ normalizer ((zpowers u₁ : Subgroup G) : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer ((zpowers u₁ : Subgroup G) : Set G) (by
      rw [p34_centralizer_zpowers u₁]
      exact mem_centralizer_singleton_iff.mpr (hAu a ha))
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A (zpowers u₁) hAN] at hu₂E
  obtain ⟨a, ha, v, hv, hav'⟩ := hu₂E
  have hav : a * v = u₂ := hav'
  have haU : a ∈ U := by
    have hvU : v ∈ U := zpowers_le.mpr hu₁U hv
    have : a = u₂ * v⁻¹ := by rw [← hav]; group
    rw [this]
    exact Subgroup.mul_mem _ hu₂U (Subgroup.inv_mem _ hvU)
  have ha1 : a = 1 := by
    have : a ∈ U ⊓ A := ⟨haU, ha⟩
    rw [hUA, Subgroup.mem_bot] at this
    exact this
  rw [ha1, one_mul] at hav
  exact hu₂ (hav ▸ hv)

theorem l34_reducedCentralizer_normal {M : Subgroup G} {x : G} {J : Subgroup G}
    (hJ : IsL34Normal M x J) : (reducedCentralizerOfJ x J).Normal := by
  have := r1sBar_normal_l34 hJ
  rw [r1s_reducedCentralizerOfJ_eq]
  infer_instance

theorem l34Img_J_eq (x : G) (J : Subgroup G) :
    l34Img x J J =
      (r1sBar x J).map (QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore) := by
  unfold l34Img l34Hom r1sBar
  rw [Subgroup.map_map]

theorem l34_phi_injective (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) {M : Subgroup G}
    {x : G} {J : Subgroup G} (hJ : IsL34Normal M x J) :
    Function.Injective ((QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore).comp
      (r1sBar x J).subtype) := by
  have hDn := l34_reducedCentralizer_normal hJ
  have hbot := l34_bar_inf_reducedCentralizer_eq_bot hK1 hK2 hJ
  rw [injective_iff_map_eq_one]
  intro j hj
  have hjD : (j : GenericReduced 3 x) ∈ reducedCentralizerOfJ x J := by
    have h : (j : GenericReduced 3 x) ∈
        (QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore).ker := hj
    rwa [QuotientGroup.ker_mk', Subgroup.normalCore_eq_self] at h
  have : (j : GenericReduced 3 x) ∈ r1sBar x J ⊓ reducedCentralizerOfJ x J := ⟨j.2, hjD⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact Subtype.ext this

theorem l34_phi_range (x : G) (J : Subgroup G) :
    ((QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore).comp (r1sBar x J).subtype).range =
      l34Img x J J := by
  rw [l34Img_J_eq, MonoidHom.range_comp, Subgroup.range_subtype]

theorem l34_quot_data (_hS : Setting G) (_hU0 : FullCoreLocal G) (hK1 : KFactL34TwoSignalizer)
    (hK2 : KFactL34Three) (_hp : 3 ∈ rankThreeSigmaA G) {_P : Sylow 3 G} {M : Subgroup G}
    (_hM : IsCoreMaxLocal 3 _P M) {x : G} (_hgen : IsGenericPoint 3 _P M x) {J : Subgroup G}
    (hJ : IsL34Normal M x J) :
    (l34Img x J J).Normal ∧
      centralizer ((l34Img x J J : Subgroup (L34Quot x J)) : Set (L34Quot x J)) = ⊥ ∧
      IsRankThreeL34 ↥(l34Img x J J) := by
  have hJbn := r1sBar_normal_l34 hJ
  have hDn := l34_reducedCentralizer_normal hJ
  set D := reducedCentralizerOfJ x J with hD
  have hcore : D.normalCore = D := Subgroup.normalCore_eq_self D
  have hbot := l34_bar_inf_reducedCentralizer_eq_bot hK1 hK2 hJ
  set q : GenericReduced 3 x →* L34Quot x J := QuotientGroup.mk' D.normalCore with hq
  have hker : q.ker = D := by rw [hq, QuotientGroup.ker_mk', hcore]
  rw [l34Img_J_eq]
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
  · have hinj := l34_phi_injective hK1 hK2 hJ
    have hr : (q.comp (r1sBar x J).subtype).range = (r1sBar x J).map q := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact isL34_of_mulEquiv
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hr)).symm (r1sBar_isL34 hJ)

theorem l34_T_data (_hS : Setting G) (_hU0 : FullCoreLocal G) (hK1 : KFactL34TwoSignalizer)
    (hK2 : KFactL34Three) (_hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (_hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsL34Normal M x J) :
    IsElemAbelian 3 (l34Img x J ((P : Subgroup G) ⊓ J)) ∧
      Nat.card (l34Img x J ((P : Subgroup G) ⊓ J)) = 3 ^ 2 ∧
      l34Img x J ((P : Subgroup G) ⊓ J) ≤ l34Img x J J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJC := hJ.le_centralizer
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hSylJ : IsSylowOf 3 (((P : Subgroup G) ⊓ C) ⊓ J) J :=
    hgen.2.2.1.inf_of_le_normalizer hJC hJ.centralizer_le
  have hPJ : ((P : Subgroup G) ⊓ C) ⊓ J = (P : Subgroup G) ⊓ J := by
    rw [inf_assoc, inf_eq_right.mpr hJC]
  rw [hPJ] at hSylJ
  obtain ⟨T, hT⟩ := hSylJ
  set T' : Sylow 3 ↥(r1sBar x J) := T.mapSurjective (r1sHom_surjective x hJC) with hT'
  obtain ⟨hTe, hTc, -⟩ := r1sBar_sylow_facts_l34 hK1 hK2 hJ T'
  set φ := (QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore).comp
    (r1sBar x J).subtype with hφ
  have hinj := l34_phi_injective hK1 hK2 hJ
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
  rw [hLHS]
  refine ⟨CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hTe φ, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hinj]
    exact hTc
  · rw [← l34_phi_range x J]
    exact Subgroup.map_le_range _ _

end CFSG.LocalAnalysis.RankThreeTheoremC
