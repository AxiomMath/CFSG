module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11P34SDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11P34Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerNoncentral2_7KFact
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34c
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem mem_of_mul_core {C : Type*} [Group C] [Finite C] {J O : Subgroup C} [J.Normal]
    (hO : Nat.Coprime 3 (Nat.card O)) {k j o : C} (hj : j ∈ J) (ho : o ∈ O) (hko : k = j * o)
    (hk : ∃ a : ℕ, orderOf k = 3 ^ a) : k ∈ J := by
  obtain ⟨a, ha⟩ := hk
  have hj1 : QuotientGroup.mk' J j = 1 := (QuotientGroup.eq_one_iff j).mpr hj
  have h1 : QuotientGroup.mk' J k = QuotientGroup.mk' J o := by
    rw [hko, map_mul, hj1, one_mul]
  have h2 : orderOf (QuotientGroup.mk' J k) ∣ 3 ^ a := ha ▸ orderOf_map_dvd _ k
  have h3 : orderOf (QuotientGroup.mk' J k) ∣ Nat.card O := by
    rw [h1]
    exact (orderOf_map_dvd _ o).trans (Subgroup.orderOf_dvd_natCard O ho)
  have h4 : orderOf (QuotientGroup.mk' J k) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left a hO) h2 h3
  exact (QuotientGroup.eq_one_iff k).mp (orderOf_eq_one_iff.mp h4)

theorem p34_inf_data (hS : Setting G) (hU0 : FullCoreLocal G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsM11Normal M x J) :
    IsElemAbelian 3 ((P : Subgroup G) ⊓ J) ∧ Nat.card ↥((P : Subgroup G) ⊓ J) = 3 ^ 2 ∧
      x ∉ (P : Subgroup G) ⊓ J := by
  have hY := p34_yData hS hU0 hKM hKA hp hM hgen hJ
  obtain ⟨Sbar, hSbar, hsh⟩ := exists_genericShadow3 hS hU0 hp rfl hM hgen
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hJC : J ≤ C := hJ.le_centralizer
  set O : Subgroup C := primeComplementCore (G := C) 3 with hO
  have hOcop : Nat.Coprime 3 (Nat.card O) := primeComplementCore_coprime 3
  set π : C →* C ⧸ O := QuotientGroup.mk' O with hπ
  set Q' : Subgroup C := ((P : Subgroup G) ⊓ C).subgroupOf C with hQ'
  have hQ'p : IsPGroup 3 Q' := (P.isPGroup'.to_le inf_le_left).comap_subtype
  set L : Subgroup (C ⧸ O) := r1sBar x J with hL
  set SL : Subgroup (C ⧸ O) := (Sbar : Subgroup (C ⧸ O)) ⊓ L with hSL
  obtain ⟨hSLe, hSLc⟩ := hY.inf_elemAbelian hKM hKA Sbar
  have hJn : (J.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJC).mpr hJ.centralizer_le
  set D' : Subgroup C := ((P : Subgroup G) ⊓ J).subgroupOf C with hD'
  have hD'Q : D' ≤ Q' := fun a ha =>
    Subgroup.mem_subgroupOf.mpr ⟨(Subgroup.mem_subgroupOf.mp ha).1, a.2⟩
  have hD'p : IsPGroup 3 D' := hQ'p.to_le hD'Q
  have hπQ : Q'.map π = (Sbar : Subgroup (C ⧸ O)) := hSbar.symm
  have hmapD : D'.map π = SL := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hπQ]
        exact Subgroup.mem_map_of_mem _ (hD'Q ha)
      · exact ⟨a, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp ha).2, rfl⟩
    · intro s hs
      obtain ⟨k, hkQ, rfl⟩ : s ∈ Q'.map π := by
        rw [hπQ]
        exact hs.1
      obtain ⟨j, hj, hjk⟩ := hs.2
      have hjo : j⁻¹ * k ∈ O := QuotientGroup.eq.mp hjk
      obtain ⟨a, ha⟩ := IsPGroup.iff_orderOf.mp hQ'p ⟨k, hkQ⟩
      have hka : orderOf k = 3 ^ a := by
        rw [← Subgroup.orderOf_mk k hkQ]
        exact ha
      have hkJ : k ∈ J.subgroupOf C :=
        mem_of_mul_core (J := J.subgroupOf C) hOcop hj hjo (by group) ⟨a, hka⟩
      exact ⟨k, Subgroup.mem_subgroupOf.mpr
        ⟨(Subgroup.mem_subgroupOf.mp hkQ).1, Subgroup.mem_subgroupOf.mp hkJ⟩, rfl⟩
  have hDcard : Nat.card D' = 3 ^ 2 := by
    rw [← CFSG.AGLEmbedding.card_map_mk_of_isPGroup Nat.prime_three O hOcop hD'p]
    exact hmapD ▸ hSLc
  have hπD : ∀ a ∈ D', π a ∈ SL := fun a ha => hmapD ▸ Subgroup.mem_map_of_mem _ ha
  have hDel : IsElemAbelian 3 D' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · apply Subtype.ext
      change (a : C) * b = b * a
      refine p34_mk_inj hOcop hQ'p (Q'.mul_mem (hD'Q a.2) (hD'Q b.2))
        (Q'.mul_mem (hD'Q b.2) (hD'Q a.2)) ?_
      rw [map_mul, map_mul]
      exact p34_comm_of_isMulCommutative hSLe.1 (hπD a a.2) (hπD b b.2)
    · refine p34_mk_inj hOcop hQ'p (Q'.pow_mem (hD'Q ha) 3) Q'.one_mem ?_
      rw [map_pow, map_one]
      exact hSLe.2 _ (hπD a ha)
  have hmapG : D'.map C.subtype = (P : Subgroup G) ⊓ J :=
    Subgroup.map_subgroupOf_eq_of_le (inf_le_right.trans hJC)
  refine ⟨?_, ?_, ?_⟩
  · rw [← hmapG]
    exact CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hDel C.subtype
  · rw [← hmapG, Subgroup.card_map_of_injective C.subtype_injective]
    exact hDcard
  · intro hxPJ
    have hxD : (⟨x, mem_centralizer_singleton_iff.mpr rfl⟩ : C) ∈ D' :=
      Subgroup.mem_subgroupOf.mpr hxPJ
    have hz : π ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩ ∈ center (C ⧸ O) := hsh.mem_center
    have h1 : π ⟨x, mem_centralizer_singleton_iff.mpr rfl⟩ ∈ L ⊓ center (C ⧸ O) :=
      ⟨(hπD _ hxD).2, hz⟩
    rw [hY.inf_center_eq_bot, Subgroup.mem_bot] at h1
    have h2 := hsh.orderOf_eq
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)

theorem m11_prop34S (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hKT : KFactM11SylowTransitive) (hSig : SignalizerTwoGroupKFact)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsM11Normal M x J) :
    M11Prop34S 3 P J x := by
  have h34 := m11_prop34 hS hU0 hD1 hKM hKA hKT hSig hp hM hgen hJ
  obtain ⟨hKel, hKcard, hxK⟩ := p34_inf_data hS hU0 hKM hKA hp hM hgen hJ
  refine ⟨h34, ?_⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set K₀ : Subgroup G := (P : Subgroup G) ⊓ J with hK₀
  have hJC : J ≤ C := hJ.le_centralizer
  have hPab : IsMulCommutative (P : Subgroup G) := h34.1
  have hPc : ∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a := fun a ha b hb =>
    p34_comm_of_isMulCommutative hPab ha hb
  have hrank : CFSG.Open.pRank 3 (P : Subgroup G) = 3 := by
    obtain ⟨hxP, -, -, hr⟩ := hgen
    have hPC : (P : Subgroup G) ≤ C := fun y hy => mem_centralizer_singleton_iff.mpr
      (hPc y hy x hxP)
    rwa [inf_eq_left.mpr hPC] at hr
  obtain ⟨hxP, hlo, -, -⟩ := hgen
  obtain ⟨-, hx1, hx3, -, -⟩ := hlo
  have hK₀P : K₀ ≤ (P : Subgroup G) := inf_le_left
  have hK₀x : ∀ k ∈ K₀, ∀ c ∈ zpowers x, k * c = c * k := fun k hk c hc => by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
    exact (Commute.zpow_right (show Commute k x from
      mem_centralizer_singleton_iff.mp (hJC hk.2)) j).eq
  have hK₀cent : K₀ ≤ centralizer ((zpowers x : Subgroup G) : Set G) := fun k hk => by
    rw [p34_centralizer_zpowers x]
    exact hJC hk.2
  set E : Subgroup G := K₀ ⊔ zpowers x with hE
  have hEP : E ≤ (P : Subgroup G) := sup_le hK₀P (zpowers_le.mpr hxP)
  have hEel : IsElemAbelian 3 E :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3 hKel
      (CFSG.AGLEmbedding.isElemAbelian_zpowers hx3) hK₀cent
  have hEcard : Nat.card E = 3 ^ 3 := by
    rw [hE, CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three K₀ hx3 hxK
      (fun e he => hK₀x e he x (mem_zpowers x)), hKcard]
    norm_num
  refine ⟨hEel, by simpa using hEcard, fun y hyP hy3 => ?_⟩
  by_contra hyE
  have hcomm : ∀ e ∈ E, e * y = y * e := fun e he => hPc e (hEP he) y hyP
  have hcard := CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three E hy3 hyE hcomm
  have hcent : E ≤ centralizer ((zpowers y : Subgroup G) : Set G) := fun e he => by
    rw [p34_centralizer_zpowers y]
    exact mem_centralizer_singleton_iff.mpr (hcomm e he)
  have hel := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3 hEel
    (CFSG.AGLEmbedding.isElemAbelian_zpowers hy3) hcent
  have hle : E ⊔ zpowers y ≤ (P : Subgroup G) := sup_le hEP (zpowers_le.mpr hyP)
  have h4 := le_pRank_of_elemAbelian_card (p := 3) hle hel (k := 4)
    (by rw [hcard, hEcard]; norm_num)
  omega

theorem GL83GenericPrimeThreeM11Shape.of_kfacts (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hKT : KFactM11SylowTransitive) (hSig : SignalizerTwoGroupKFact) :
    GL83GenericPrimeThreeM11Shape G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ _
  subst hp3
  exact m11_prop34S hS hU0 hD1 hKM hKA hKT hSig hp hM hgen
    ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
