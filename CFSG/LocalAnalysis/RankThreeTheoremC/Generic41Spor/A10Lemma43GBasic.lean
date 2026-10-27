module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GPData
public import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

private theorem a10t1_Y_inj {A : Subgroup G} (hA : IsPGroup 5 A) {m n : ↥M} (hm : (m : G) ∈ A)
    (hn : (n : G) ∈ A) (h : a10π M m = a10π M n) : m = n := by
  have hAp : IsPGroup 5 (A.subgroupOf M) := hA.comap_subtype
  have h1 : m⁻¹ * n ∈ primeComplementCore (G := ↥M) 5 := QuotientGroup.eq.mp h
  have h2 : m⁻¹ * n ∈ A.subgroupOf M ⊓ primeComplementCore (G := ↥M) 5 :=
    ⟨(A.subgroupOf M).mul_mem ((A.subgroupOf M).inv_mem hm) hn, h1⟩
  rw [CFSG.AGLEmbedding.inf_eq_bot_of_isPGroup Nat.prime_five hAp (primeComplementCore_coprime 5),
    Subgroup.mem_bot, inv_mul_eq_one] at h2
  exact h2

private theorem a10t1_Y_orderOf {A : Subgroup G} (hA : IsPGroup 5 A) {a : G} (haM : a ∈ M)
    (haA : a ∈ A) (ho : orderOf a = 5) : orderOf (a10π M ⟨a, haM⟩) = 5 := by
  have hdvd : orderOf (a10π M ⟨a, haM⟩) ∣ 5 := by
    have h := orderOf_map_dvd (a10π M) (⟨a, haM⟩ : ↥M)
    rwa [Subgroup.orderOf_mk, ho] at h
  rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h1
  · exfalso
    have h1' : a10π M ⟨a, haM⟩ = 1 := orderOf_eq_one_iff.mp h1
    have h2 : (⟨a, haM⟩ : ↥M) = 1 :=
      a10t1_Y_inj hA (m := ⟨a, haM⟩) (n := 1) haA (one_mem A) (by rw [h1', map_one])
    have h3 : a = 1 := congrArg Subtype.val h2
    have h4 : orderOf a = 1 := orderOf_eq_one_iff.mpr h3
    rw [ho] at h4
    omega
  · exact h1

private theorem a10t1_Y_zpowers_subgroupOf {a : G} (ha : a ∈ M) :
    (Subgroup.zpowers a).subgroupOf M = Subgroup.zpowers (⟨a, ha⟩ : ↥M) := by
  ext m
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp⟩

private theorem a10t1_Y_img_zpowers {a : G} (ha : a ∈ M) :
    a10Img M (Subgroup.zpowers a) = Subgroup.zpowers (a10π M ⟨a, ha⟩) := by
  unfold a10Img
  rw [a10t1_Y_zpowers_subgroupOf ha, MonoidHom.map_zpowers]

private theorem a10t1_Y_img_sup {A B : Subgroup G} (hA : A ≤ M) (hB : B ≤ M) :
    a10Img M (A ⊔ B) = a10Img M A ⊔ a10Img M B := by
  unfold a10Img
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

private theorem a10t1_Y_comm {A : Subgroup G} (hA : IsMulCommutative A) :
    IsMulCommutative (a10Img M A) := by
  rw [isMulCommutative_iff_of_setLike]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (isMulCommutative_iff_of_setLike.mp hA (a : G) ha (b : G) hb)

private theorem a10t1_Y_sylow_subgroupOf (P : Sylow 5 G) {M : Subgroup G}
    (hPM : (P : Subgroup G) ≤ M) :
    ∃ T : Sylow 5 M, (T : Subgroup M) = (P : Subgroup G).subgroupOf M := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h : CFSG.ABGLocalTools.IsSylowOf 5 (P : Subgroup G) M := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨hPM, P.isPGroup', fun h =>
      P.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hPM))⟩
  exact h.exists_sylow_eq_subgroupOf

private theorem a10t1_Y_rank (M : Subgroup G) (hrank : CFSG.Open.pRank 5 M ≤ 3) :
    CFSG.Open.pRank 5 (⊤ : Subgroup (A10Y M)) ≤ 3 := by
  have h1 := CFSG.AGLEmbedding.pRank_map_mk_eq_pRank_map_subtype Nat.prime_five
    (primeComplementCore (G := ↥M) 5) (primeComplementCore_coprime 5) ⊤
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
  rw [h1, Subgroup.map_top, Subgroup.range_subtype]
  exact hrank

theorem a10_Y_basic (hS : Setting G) (hX : A10Facts) (hc : PointConfig IsA10Type G 5 P M x J)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) (hxM : x ∈ M) :
    CFSG.AGLEmbedding.CatalogSimpleSections (A10Y M) ∧ primeComplementCore (G := A10Y M) 5 = ⊥ ∧
      (∃ S : Sylow 5 (A10Y M), (S : Subgroup (A10Y M)) = a10Img M (P : Subgroup G)) ∧
      CFSG.Open.pRank 5 (⊤ : Subgroup (A10Y M)) ≤ 3 ∧ IsMulCommutative (a10Img M (P : Subgroup G)) ∧
      a10π M ⟨x, hxM⟩ ∈ a10Img M (P : Subgroup G) ∧ orderOf (a10π M ⟨x, hxM⟩) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hMtop : M ≠ ⊤ := fun h => hc.not_le (h ▸ le_top)
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hrank : CFSG.Open.pRank 5 M ≤ 3 := by
    have h1 := local_pRank_le_evenRank 5 (sigmaA_prime 5 hc.sigma) (sigmaA_odd 5 hc.sigma) M
      hc.core.1.1
    rw [hS.rank] at h1
    exact h1
  have hpd := a10_pdata hX hc hP
  have hxP : x ∈ (P : Subgroup G) := hpd.D_le hpd.x_mem
  refine ⟨(CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper M hMtop).quotient _,
    primeComplementCore_quotient_eq_bot 5, ?_, a10t1_Y_rank M hrank,
    a10t1_Y_comm (a10_P_comm hX hc hP), Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxP),
    a10t1_Y_orderOf P.isPGroup' hxM hxP hpd.x_ord⟩
  obtain ⟨T', hT'⟩ := a10t1_Y_sylow_subgroupOf P hPM
  exact ⟨T'.mapSurjective (QuotientGroup.mk'_surjective _), by
    rw [Sylow.coe_mapSurjective, hT']
    rfl⟩

theorem a10_Y_points (hX : A10Facts) (hc : PointConfig IsA10Type G 5 P M x J)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) (hxM : x ∈ M) {a₁ a₂ : G}
    (ha₁M : a₁ ∈ M) (ha₂M : a₂ ∈ M) (ho₁ : orderOf a₁ = 5) (ho₂ : orderOf a₂ = 5)
    (hT : u3T P x J = Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂) (hne : a₁ ∉ Subgroup.zpowers a₂) :
    orderOf (a10π M ⟨a₁, ha₁M⟩) = 5 ∧ orderOf (a10π M ⟨a₂, ha₂M⟩) = 5 ∧
      a10π M ⟨x, hxM⟩ ∉ Subgroup.zpowers (a10π M ⟨a₁, ha₁M⟩) ⊔ Subgroup.zpowers (a10π M ⟨a₂, ha₂M⟩) ∧
      a10π M ⟨a₁, ha₁M⟩ ∉ Subgroup.zpowers (a10π M ⟨a₂, ha₂M⟩) ∧
      a10Img M (u3T P x J) =
        Subgroup.zpowers (a10π M ⟨a₁, ha₁M⟩) ⊔ Subgroup.zpowers (a10π M ⟨a₂, ha₂M⟩) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hpd := a10_pdata hX hc hP
  have hxP : x ∈ (P : Subgroup G) := hpd.D_le hpd.x_mem
  have hTP : u3T P x J ≤ (P : Subgroup G) := hpd.T_le
  have hxJ : x ∉ J := (plane_T_structure hX.sylow hc).2.2
  have hxT : x ∉ u3T P x J := fun h => hxJ (Subgroup.mem_inf.mp h).2
  have hPp : IsPGroup 5 (P : Subgroup G) := P.isPGroup'
  have ha₁T : a₁ ∈ u3T P x J := hT ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers a₁)
  have ha₂T : a₂ ∈ u3T P x J := hT ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers a₂)
  have hz₁ : Subgroup.zpowers a₁ ≤ M := (Subgroup.zpowers_le).mpr ha₁M
  have hz₂ : Subgroup.zpowers a₂ ≤ M := (Subgroup.zpowers_le).mpr ha₂M
  have hTbar : a10Img M (u3T P x J) =
      Subgroup.zpowers (a10π M ⟨a₁, ha₁M⟩) ⊔ Subgroup.zpowers (a10π M ⟨a₂, ha₂M⟩) := by
    rw [hT, a10t1_Y_img_sup hz₁ hz₂, a10t1_Y_img_zpowers ha₁M, a10t1_Y_img_zpowers ha₂M]
  refine ⟨a10t1_Y_orderOf hPp ha₁M (hTP ha₁T) ho₁, a10t1_Y_orderOf hPp ha₂M (hTP ha₂T) ho₂,
    ?_, ?_, hTbar⟩
  · rw [← hTbar]
    rintro ⟨t, ht, hteq⟩
    have h1 : t = ⟨x, hxM⟩ :=
      a10t1_Y_inj hPp (hTP (show (t : G) ∈ u3T P x J from ht)) hxP hteq
    exact hxT (by simpa [h1] using (show (t : G) ∈ u3T P x J from ht))
  · rw [← a10t1_Y_img_zpowers ha₂M]
    rintro ⟨t, ht, hteq⟩
    have ht' : (t : G) ∈ Subgroup.zpowers a₂ := ht
    have h1 : t = ⟨a₁, ha₁M⟩ :=
      a10t1_Y_inj hPp (hTP (hT ▸ Subgroup.mem_sup_right ht')) (hTP ha₁T) hteq
    exact hne (by simpa [h1] using ht')

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
