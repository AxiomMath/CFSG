module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34R1Omega
public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerNoncentral2_7KFact
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f
import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerSubgroupIndices

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem l34cm_isSimpleGroup {M : Subgroup G} {x : G} {J : Subgroup G} (hJ : IsL34Normal M x J) :
    IsSimpleGroup ↥(r1sBar x J) := by
  have hJC := hJ.le_centralizer
  set φ : ↥J →* ↥(r1sBar x J) := r1sHom x hJC with hφ
  have hsurj : Function.Surjective φ := r1sHom_surjective x hJC
  have hker : φ.ker = (rankThreePrimeCore 3 J).subgroupOf J := ker_r1sHom_l34 hJ
  have hOJ : rankThreePrimeCore 3 J ≤ J := sSup_le fun _ hN => hN.1
  have : Nontrivial ↥(r1sBar x J) := by
    obtain ⟨j, hjJ, hjO⟩ := IsConcreteLE.exists_of_lt hJ.lt_core
    refine ⟨⟨φ ⟨j, hjJ⟩, 1, fun h => ?_⟩⟩
    have : (⟨j, hjJ⟩ : ↥J) ∈ φ.ker := h
    rw [hker] at this
    exact hjO (Subgroup.mem_subgroupOf.mp this)
  refine ⟨fun N hN => ?_⟩
  set N' : Subgroup ↥J := N.comap φ with hN'
  set NG : Subgroup G := N'.map J.subtype with hNG
  have hNGJ : NG ≤ J := Subgroup.map_subtype_le N'
  have hNGsub : NG.subgroupOf J = N' :=
    Subgroup.comap_map_eq_self_of_injective J.subtype_injective N'
  have hNn : (NG.subgroupOf J).Normal := by rw [hNGsub]; exact Subgroup.normal_comap φ
  have hON : rankThreePrimeCore 3 J ≤ NG := by
    intro o ho
    have hoJ : o ∈ J := hOJ ho
    have h1 : (⟨o, hoJ⟩ : ↥J) ∈ φ.ker := by rw [hker]; exact Subgroup.mem_subgroupOf.mpr ho
    refine ⟨⟨o, hoJ⟩, ?_, rfl⟩
    show φ ⟨o, hoJ⟩ ∈ N
    rw [MonoidHom.mem_ker.mp h1]
    exact N.one_mem
  rcases hJ.minimal NG hNGJ hNn hON with h | h
  · left
    refine eq_bot_iff.mpr fun n hn => ?_
    obtain ⟨j, rfl⟩ := hsurj n
    have hj : j ∈ N' := hn
    have h2 : N' = φ.ker := by rw [← hNGsub, h, hker]
    rw [h2] at hj
    exact Subgroup.mem_bot.mpr hj
  · right
    refine eq_top_iff.mpr fun n _ => ?_
    obtain ⟨j, rfl⟩ := hsurj n
    have h2 : N' = ⊤ := by rw [← hNGsub, h, Subgroup.subgroupOf_self]
    have hj : j ∈ N' := by rw [h2]; exact Subgroup.mem_top j
    exact hj

theorem l34cm_quot_simple (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) {M : Subgroup G}
    {x : G} {J : Subgroup G} (hJ : IsL34Normal M x J) :
    IsSimpleGroup ↥(l34Img x J J) ∧ (∃ a b : ↥(l34Img x J J), a * b ≠ b * a) ∧
      IsCatalogGroup ↥(l34Img x J J) ∧ IsRankThreeL34 ↥(l34Img x J J) := by
  have hsimple := l34cm_isSimpleGroup hJ
  have hperf := r1sBar_perfect_l34 hJ
  have e : ↥(r1sBar x J) ≃* ↥(l34Img x J J) :=
    (MonoidHom.ofInjective (l34_phi_injective hK1 hK2 hJ)).trans
      (MulEquiv.subgroupCongr (l34_phi_range x J))
  have hKs : IsSimpleGroup ↥(l34Img x J J) := e.symm.isSimpleGroup
  have hKp : Group.IsPerfect ↥(l34Img x J J) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hL34 : IsRankThreeL34 ↥(l34Img x J J) := isL34_of_mulEquiv e.symm (r1sBar_isL34 hJ)
  refine ⟨hKs, ?_, ?_, hL34⟩
  · by_contra hab
    push Not at hab
    exact Group.IsPerfect.not_isMulCommutative ↥(l34Img x J J) ⟨⟨fun a b => hab a b⟩⟩
  · obtain ⟨q, -, -, hv, ⟨f⟩⟩ := hL34
    exact ⟨_, ⟨f⟩⟩

theorem l34cm_card_img (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) {M : Subgroup G}
    {x : G} {J : Subgroup G} (hJ : IsL34Normal M x J) {A : Subgroup G} (hAJ : A ≤ J)
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) : Nat.card (l34Img x J A) = Nat.card A := by
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hAC : A ≤ C := hAJ.trans hJ.le_centralizer
  set ψ : ↥A →* L34Quot x J := (l34Hom x J).comp (inclusion hAC)
  have hψi : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hO := l34_mem_of_ker_of_mem_J hK1 hK2 hJ (inclusion hAC a) (hAJ a.2) ha
    have h1 : orderOf (inclusion hAC a) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (hA3 a a.2))
    have h2 : orderOf (inclusion hAC a) ∣ Nat.card (primeComplementCore (G := C) 3) :=
      Subgroup.orderOf_dvd_natCard _ hO
    have h3 := Nat.eq_one_of_dvd_coprimes (primeComplementCore_coprime 3) h1 h2
    have h4 : ((inclusion hAC a : C) : G) = 1 := congrArg Subtype.val (orderOf_eq_one_iff.mp h3)
    exact Subtype.ext h4
  have hr : ψ.range = l34Img x J A := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨inclusion hAC a, mem_subgroupOf.mpr a.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, mem_subgroupOf.mp hc⟩, rfl⟩
  rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hψi).toEquiv]

theorem l34_commutator_mem (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : KFactL34TwoSignalizer)
    (hK2 : KFactL34Three) (hK10 : KFactL34OuterCentralizer) (hSig : SignalizerTwoGroupKFact)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J)
    {R₁ T₁ : Subgroup G} (hR₁C : R₁ ≤ centralizer ({x} : Set G)) (hR₁el : IsElemAbelian 3 R₁)
    (hR₁card : Nat.card R₁ = 3 ^ 3) (hT₁C : T₁ ≤ centralizer ({x} : Set G))
    (hT₁ : IsPGroup 2 T₁) (hn : R₁ ≤ normalizer (T₁ : Set G)) :
    ∀ t ∈ T₁, ∀ r ∈ R₁, ⁅t, r⁆ ∈ GLBPrimeCore 3 (centralizer ({x} : Set G)) := by
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  obtain ⟨hxR, -, hReq⟩ := l34_elem27 hS hU0 hK1 hK2 hK10 hp hM hgen hJ hR₁C hR₁el hR₁card
  have hJC := hJ.le_centralizer
  have hBJ : R₁ ⊓ J ≤ J := inf_le_right
  have hBC : R₁ ⊓ J ≤ C := hBJ.trans hJC
  have hB3 : ∀ b ∈ R₁ ⊓ J, b ^ 3 = 1 := fun b hb => hR₁el.2 b hb.1
  have hx3 : x ^ 3 = 1 := hR₁el.2 x hxR
  have hxB : x ∉ R₁ ⊓ J := fun h => l34_x_not_mem_J hS hU0 hK1 hK2 hp hM hgen hJ h.2
  have hBx : ∀ b ∈ R₁ ⊓ J, b * x = x * b := fun b hb =>
    (mem_centralizer_iff.mp (hBC hb) x rfl).symm
  have hBcard : Nat.card ↥(R₁ ⊓ J) = 3 ^ 2 := by
    have h := CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (R₁ ⊓ J) hx3 hxB
      hBx
    rw [← hReq, hR₁card] at h
    omega
  obtain ⟨hKn, hKD, -⟩ := l34_quot_data hS hU0 hK1 hK2 hp hM hgen hJ
  obtain ⟨hKs, hKab, hKcat, hL34⟩ := l34cm_quot_simple hK1 hK2 hJ
  have hSE : IsRankTwoSEGroup 3 ↥(l34Img x J J) :=
    Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl hL34⟩)))
  have hBel : IsElemAbelian 3 (l34Img x J (R₁ ⊓ J)) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3
      (CFSG.SignalizerFunctor.Helpers.elementary_abelian_subgroupOf 3 (R₁ ⊓ J) C
        (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 3 hR₁el inf_le_left))
      (l34Hom x J)
  have hBtcard : Nat.card (l34Img x J (R₁ ⊓ J)) = 3 ^ 2 := by
    rw [l34cm_card_img hK1 hK2 hJ hBJ hB3, hBcard]
  have hBK : l34Img x J (R₁ ⊓ J) ≤ l34Img x J J := Subgroup.map_mono (subgroupOf_mono _ hBJ)
  have hBD : l34Img x J (R₁ ⊓ J) ⊓
      centralizer ((l34Img x J J : Subgroup (L34Quot x J)) : Set (L34Quot x J)) = ⊥ := by
    rw [hKD, inf_bot_eq]
  have hT2 : IsPGroup 2 (l34Img x J T₁) := (hT₁.comap_subtype).map _
  have hBT : l34Img x J (R₁ ⊓ J) ≤
      normalizer ((l34Img x J T₁ : Subgroup (L34Quot x J)) : Set (L34Quot x J)) := by
    rintro _ ⟨c, hc, rfl⟩
    have hcR : (c : G) ∈ R₁ := (mem_subgroupOf.mp hc).1
    have hcN : c ∈ normalizer ((T₁.subgroupOf C : Subgroup C) : Set C) := by
      rw [mem_normalizer_iff]
      intro f
      rw [mem_subgroupOf, mem_subgroupOf]
      have := mem_normalizer_iff.mp (hn hcR) (f : G)
      simpa using this
    exact Subgroup.le_normalizer_map (l34Hom x J) ⟨c, hcN, rfl⟩
  have hcomm := hSig (L34Quot x J) (l34Img x J J) hKn hKs hKab hKcat 3 Nat.prime_three
    (by norm_num) (l34Img x J (R₁ ⊓ J)) hBel hBtcard hBD (Or.inl ⟨hSE, hBK⟩) (l34Img x J T₁) hT2
    hBT
  rw [hKD] at hcomm
  have hkey : ∀ t ∈ T₁, ∀ b ∈ R₁ ⊓ J, ⁅t, b⁆ ∈ GLBPrimeCore 3 C := by
    intro t ht b hb
    set tc : C := ⟨t, hT₁C ht⟩
    set bc : C := ⟨b, hBC hb⟩
    have h1 : l34Hom x J ⁅tc, bc⁆ = 1 := by
      rw [map_commutatorElement]
      have : ⁅l34Hom x J tc, l34Hom x J bc⁆ ∈ ⁅l34Img x J (R₁ ⊓ J), l34Img x J T₁⁆ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator ⟨tc, ht, rfl⟩ ⟨bc, hb, rfl⟩
      exact Subgroup.mem_bot.mp (hcomm this)
    have hJmem : ((⁅tc, bc⁆ : C) : G) ∈ J := by
      have h2 : t * b * t⁻¹ ∈ J := (mem_normalizer_iff.mp (hJ.centralizer_le (hT₁C ht)) b).mp hb.2
      exact J.mul_mem h2 (J.inv_mem hb.2)
    exact (CFSG.AGLEmbedding.mem_primeComplementCore_iff_mem_glbPrimeCore 3 _).mp
      (l34_mem_of_ker_of_mem_J hK1 hK2 hJ ⁅tc, bc⁆ hJmem h1)
  intro t ht r hr
  have hCz := p34_centralizer_zpowers x
  have hBN : R₁ ⊓ J ≤ normalizer ((zpowers x : Subgroup G) : Set G) := fun b hb =>
    centralizer_le_normalizer _ (by rw [hCz]; exact hBC hb)
  have hr' : r ∈ ((R₁ ⊓ J ⊔ zpowers x : Subgroup G) : Set G) := by
    rw [← hReq]; exact hr
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hBN] at hr'
  obtain ⟨b, hb, u, hu, rfl⟩ := hr'
  have htu : Commute t u :=
    (mem_centralizer_iff.mp (show t ∈ centralizer ((zpowers x : Subgroup G) : Set G) by
      rw [hCz]; exact hT₁C ht) u hu).symm
  have hbu : ⁅t, b * u⁆ = ⁅t, b⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc t * (b * u) * t⁻¹ * (b * u)⁻¹ = t * b * (u * t⁻¹) * u⁻¹ * b⁻¹ := by group
      _ = t * b * (t⁻¹ * u) * u⁻¹ * b⁻¹ := by rw [← htu.inv_left.eq]
      _ = t * b * t⁻¹ * b⁻¹ := by group
  rw [hbu]
  exact hkey t ht b hb

end CFSG.LocalAnalysis.RankThreeTheoremC
