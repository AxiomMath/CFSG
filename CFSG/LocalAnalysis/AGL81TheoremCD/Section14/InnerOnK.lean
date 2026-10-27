module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFifteenOne
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFactL34FixedPoints
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34Lift

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_commute_of_conj_mem_pPrimeCore {K : Subgroup G} {e k : G}
    (he : e ∈ Subgroup.normalizer (K : Set G)) (he3 : IsPGroup 3 (Subgroup.zpowers e))
    (hk : k ∈ K) (hek : k⁻¹ * (e * k * e⁻¹) ∈ (CFSG.pPrimeCore 3 ↥K).map K.subtype) :
    ∃ c ∈ K, e * c = c * e ∧ c⁻¹ * k ∈ (CFSG.pPrimeCore 3 ↥K).map K.subtype := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X : Subgroup G := Subgroup.normalizer (K : Set G)
  set OK : Subgroup G := (CFSG.pPrimeCore 3 ↥K).map K.subtype
  set N : Subgroup ↥X := OK.subgroupOf X
  have hOKleK : OK ≤ K := Subgroup.map_subtype_le _
  have hOKleX : OK ≤ X := hOKleK.trans Subgroup.le_normalizer
  have hXnormOK : X ≤ Subgroup.normalizer (OK : Set G) :=
    CFSG.section9_normalizer_le_normalizer_map_subtype_of_characteristic (G := G) K
      (CFSG.pPrimeCore 3 ↥K)
  have hNnormal : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOKleX).mpr hXnormOK
  haveI : N.Normal := hNnormal
  have hNcard : Nat.card N = Nat.card OK :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOKleX).toEquiv
  have hOKcard : Nat.card OK = Nat.card (CFSG.pPrimeCore 3 ↥K) :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hNcop : ¬ 3 ∣ Nat.card N := by
    rw [hNcard, hOKcard]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥K))
  let eX : ↥X := ⟨e, he⟩
  let kX : ↥X := ⟨k, Subgroup.le_normalizer hk⟩
  let Q : Subgroup ↥X := Subgroup.zpowers eX
  have hQp : IsPGroup 3 Q := by
    obtain ⟨n, hn⟩ := he3.exists_card_eq
    refine IsPGroup.of_card (n := n) ?_
    rw [show Nat.card Q = Nat.card (Subgroup.zpowers e) from ?_, hn]
    rw [Nat.card_zpowers, Nat.card_zpowers]
    exact (Subgroup.orderOf_coe eX).symm
  have hce : (QuotientGroup.mk' N) kX * (QuotientGroup.mk' N) eX =
      (QuotientGroup.mk' N) eX * (QuotientGroup.mk' N) kX := by
    have hyX : (⟨k⁻¹ * (e * k * e⁻¹), hOKleX hek⟩ : ↥X) ∈ N :=
      Subgroup.mem_subgroupOf.mpr hek
    have hπy : (QuotientGroup.mk' N) ⟨k⁻¹ * (e * k * e⁻¹), hOKleX hek⟩ = 1 :=
      (QuotientGroup.eq_one_iff (N := N) _).mpr hyX
    have hsplit : eX * kX * eX⁻¹ = kX * ⟨k⁻¹ * (e * k * e⁻¹), hOKleX hek⟩ := by
      apply Subtype.ext
      show e * k * e⁻¹ = k * (k⁻¹ * (e * k * e⁻¹))
      group
    have hconj : (QuotientGroup.mk' N) (eX * kX * eX⁻¹) = (QuotientGroup.mk' N) kX := by
      rw [hsplit, map_mul, hπy, mul_one]
    rw [map_mul, map_mul, map_inv] at hconj
    calc (QuotientGroup.mk' N) kX * (QuotientGroup.mk' N) eX =
        ((QuotientGroup.mk' N) eX * (QuotientGroup.mk' N) kX *
          ((QuotientGroup.mk' N) eX)⁻¹) * (QuotientGroup.mk' N) eX := by rw [hconj]
      _ = (QuotientGroup.mk' N) eX * (QuotientGroup.mk' N) kX := by group
  have hcent : (QuotientGroup.mk' N) kX ∈ Subgroup.centralizer
      ((Q.map (QuotientGroup.mk' N) : Subgroup (↥X ⧸ N)) : Set (↥X ⧸ N)) := by
    rw [show Q.map (QuotientGroup.mk' N) =
      Subgroup.zpowers ((QuotientGroup.mk' N) eX) from
        MonoidHom.map_zpowers (QuotientGroup.mk' N) eX]
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hQle : Subgroup.zpowers ((QuotientGroup.mk' N) eX) ≤
        Subgroup.centralizer ({(QuotientGroup.mk' N) kX} : Set (↥X ⧸ N)) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact hce
    exact ((Subgroup.mem_centralizer_iff.mp (hQle hz) _ rfl)).symm
  rw [CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := 3) (N := N) hNcop hQp] at hcent
  obtain ⟨cX, hcX, hcXπ⟩ := Subgroup.mem_map.mp hcent
  have hmemN : cX⁻¹ * kX ∈ N := (QuotientGroup.eq (s := N)).mp hcXπ
  have hmemOK : (cX : G)⁻¹ * k ∈ OK := Subgroup.mem_subgroupOf.mp hmemN
  have hmemK : (cX : G)⁻¹ * k ∈ K := hOKleK hmemOK
  have hcK : (cX : G) ∈ K := by
    have hc : (cX : G) = k * ((cX : G)⁻¹ * k)⁻¹ := by group
    rw [hc]
    exact K.mul_mem hk (K.inv_mem hmemK)
  refine ⟨(cX : G), hcK, ?_, ?_⟩
  · have hcommX : eX * cX = cX * eX :=
      (Subgroup.mem_centralizer_iff.mp hcX) eX (Subgroup.mem_zpowers eX)
    exact congrArg Subtype.val hcommX
  · exact hmemOK

theorem mem_map_subgroupOf_of_conj_eq {M E H : Subgroup G} (hdata : HypCGen G M 3 E H)
    (hK : KNormalAt M) {e k : G} (he : e ∈ E) (he1 : e ≠ 1) (hk : k ∈ kSub 3 M H)
    (h : k⁻¹ * (e * k * e⁻¹) ∈
      (CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype) :
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) ⟨k, hk⟩ ∈
      (M.subgroupOf (kSub 3 M H)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(kSub 3 M H))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEN : E ≤ Subgroup.normalizer ((kSub 3 M H : Subgroup G) : Set G) :=
    hdata.E_le_H.trans (hK 3 E H hdata)
  have hpow : e ^ 3 = 1 := hdata.elem.2 e he
  have he3 : IsPGroup 3 (Subgroup.zpowers e) :=
    (CFSG.Open.isElemAbelian_zpowers hpow).isPGroup
  obtain ⟨c, hcK, hce, hcO⟩ :=
    exists_commute_of_conj_mem_pPrimeCore (K := kSub 3 M H) (hEN he) he3 hk h
  have hcM : c ∈ M := by
    refine HypCGen.centralizer_le_of_mem hdata he he1 ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hce
  rw [pPrimeCore_quotient_eq_of_mem_pPrimeCore_map hcK hk hcO]
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hcM)

theorem le_of_map_subgroupOf_eq_top {K M : Subgroup G}
    (hOK : (CFSG.pPrimeCore 3 ↥K).map K.subtype ≤ M)
    (h : (M.subgroupOf K).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) = ⊤) : K ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro k hk
  have hmem : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) ⟨k, hk⟩ ∈
      (M.subgroupOf K).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)) := by
    rw [h]
    exact Subgroup.mem_top _
  obtain ⟨m, hm, hπ⟩ := Subgroup.mem_map.mp hmem
  have hmK : (m : G) ∈ K := m.2
  have hmM : (m : G) ∈ M := Subgroup.mem_subgroupOf.mp hm
  have hO : (m : G)⁻¹ * k ∈ (CFSG.pPrimeCore 3 ↥K).map K.subtype := by
    have h2 : m⁻¹ * ⟨k, hk⟩ ∈ CFSG.pPrimeCore 3 ↥K :=
      (QuotientGroup.eq (s := CFSG.pPrimeCore 3 ↥K)).mp hπ
    exact Subgroup.mem_map_of_mem K.subtype (by simpa using h2)
  have hkM : k = (m : G) * ((m : G)⁻¹ * k) := by group
  rw [hkM]
  exact M.mul_mem hmM (hOK hO)

noncomputable def actStar (J : Subgroup G) :
    ↥(Subgroup.normalizer (J : Set G)) →* MulAut (threeStar J) :=
  (CFSG.SectionRank.Ccomm.autQuotient (CFSG.pPrimeCore 3 ↥J)).comp
    (Subgroup.normalizerMonoidHom J)

theorem actStar_mk (J : Subgroup G) (n : ↥(Subgroup.normalizer (J : Set G))) (x : ↥J) :
    actStar J n (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) x) =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) ⟨(n : G) * (x : G) * (n : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp n.2 (x : G)).mp x.2⟩ := by
  simp only [actStar, MonoidHom.comp_apply, CFSG.SectionRank.Ccomm.autQuotient_mk,
    Subgroup.normalizerMonoidHom_apply_apply_coe]
  rfl

theorem actStar_eq_one_iff_mem_pPrimeCore {J : Subgroup G}
    (hZ : Subgroup.center (threeStar J) = ⊥)
    (n : ↥(Subgroup.normalizer (J : Set G))) (hn : (n : G) ∈ J) :
    actStar J n = 1 ↔ (n : G) ∈ (CFSG.pPrimeCore 3 ↥J).map J.subtype := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup G := (CFSG.pPrimeCore 3 ↥J).map J.subtype
  have hNO : Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.section9_normalizer_le_normalizer_map_subtype_of_characteristic (G := G) J
      (CFSG.pPrimeCore 3 ↥J)
  constructor
  · intro h
    have hz : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) ⟨(n : G), hn⟩ ∈
        Subgroup.center (threeStar J) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥J) z
      have h1 := actStar_mk J n w
      rw [h, MulAut.one_apply] at h1
      have h2 : (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) ⟨(n : G), hn⟩) *
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) w) *
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) ⟨(n : G), hn⟩)⁻¹ =
          QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) w := by
        rw [← map_inv, ← map_mul, ← map_mul]
        have he : (⟨(n : G), hn⟩ * w * ⟨(n : G), hn⟩⁻¹ : ↥J) =
            ⟨(n : G) * (w : G) * (n : G)⁻¹,
              (Subgroup.mem_normalizer_iff.mp n.2 (w : G)).mp w.2⟩ := Subtype.ext rfl
        rw [he]
        exact h1.symm
      have hcomm : (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) ⟨(n : G), hn⟩) *
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) w) =
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) w) *
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J) ⟨(n : G), hn⟩) := by
        have h3 := congrArg (fun t => t * (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J)
          ⟨(n : G), hn⟩)) h2
        simpa [mul_assoc] using h3
      exact hcomm.symm
    rw [hZ, Subgroup.mem_bot] at hz
    have hmem : (⟨(n : G), hn⟩ : ↥J) ∈ CFSG.pPrimeCore 3 ↥J :=
      (QuotientGroup.eq_one_iff _).mp hz
    exact Subgroup.mem_map_of_mem J.subtype hmem
  · intro hnO
    have hnJ : (n : G) ∈ J := Subgroup.map_subtype_le _ hnO
    have hJN : J ≤ Subgroup.normalizer (O : Set G) :=
      Subgroup.le_normalizer.trans hNO
    ext z
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥J) z
    rw [actStar_mk, MulAut.one_apply]
    apply QuotientGroup.eq.mpr
    have hwO : (w : G) ∈ Subgroup.normalizer (O : Set G) := hJN w.2
    have hwOinv : (w : G)⁻¹ ∈ Subgroup.normalizer (O : Set G) :=
      (Subgroup.normalizer (O : Set G)).inv_mem hwO
    have hconj : (w : G)⁻¹ * (n : G) * (w : G) ∈ O := by
      have h := (Subgroup.mem_normalizer_iff.mp hwOinv (n : G)).mp hnO
      simpa using h
    have hprod : (w : G)⁻¹ * (n : G) * (w : G) * (n : G)⁻¹ ∈ O :=
      O.mul_mem hconj (O.inv_mem hnO)
    have hgoal : ((n : G) * (w : G) * (n : G)⁻¹)⁻¹ * (w : G) ∈ O := by
      have heq : ((n : G) * (w : G) * (n : G)⁻¹)⁻¹ * (w : G) =
          ((w : G)⁻¹ * (n : G) * (w : G) * (n : G)⁻¹)⁻¹ := by group
      rw [heq]
      exact O.inv_mem hprod
    have hsubeq : O.subgroupOf J = CFSG.pPrimeCore 3 ↥J := by
      change ((CFSG.pPrimeCore 3 ↥J).map J.subtype).comap J.subtype = _
      exact Subgroup.comap_map_eq_self_of_injective
        (H := CFSG.pPrimeCore 3 ↥J) (f := J.subtype) J.subtype_injective
    rw [← hsubeq]
    exact Subgroup.mem_subgroupOf.mpr hgoal

theorem commutator_mem_pPrimeCore_of_actStar_eq_one {J : Subgroup G}
    (n : ↥(Subgroup.normalizer (J : Set G))) (x : ↥J)
    (h : actStar J n = 1) :
    ⁅(x : G), (n : G)⁆ ∈ (CFSG.pPrimeCore 3 ↥J).map J.subtype := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup G := (CFSG.pPrimeCore 3 ↥J).map J.subtype
  have hNO : Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.section9_normalizer_le_normalizer_map_subtype_of_characteristic (G := G) J
      (CFSG.pPrimeCore 3 ↥J)
  have h1 := actStar_mk J n x
  rw [h, MulAut.one_apply] at h1
  have hmem : ((⟨(n : G) * (x : G) * (n : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp n.2 (x : G)).mp x.2⟩ : ↥J))⁻¹ * x ∈
      CFSG.pPrimeCore 3 ↥J := (QuotientGroup.eq (s := CFSG.pPrimeCore 3 ↥J)).mp h1.symm
  have hmemO : ((n : G) * (x : G) * (n : G)⁻¹)⁻¹ * (x : G) ∈ O :=
    Subgroup.mem_map_of_mem J.subtype hmem
  have hJN : J ≤ Subgroup.normalizer (O : Set G) :=
    Subgroup.le_normalizer.trans hNO
  have hxN : (x : G) ∈ Subgroup.normalizer (O : Set G) := hJN x.2
  have hconj : (x : G) * (((n : G) * (x : G) * (n : G)⁻¹)⁻¹ * (x : G)) * (x : G)⁻¹ ∈ O :=
    (Subgroup.mem_normalizer_iff.mp hxN
      (((n : G) * (x : G) * (n : G)⁻¹)⁻¹ * (x : G))).mp hmemO
  have heq : (x : G) * (((n : G) * (x : G) * (n : G)⁻¹)⁻¹ * (x : G)) * (x : G)⁻¹ =
      ⁅(x : G), (n : G)⁆ := by
    rw [commutatorElement_def]
    group
  rwa [heq] at hconj

theorem innerOnKAt_of {M : Subgroup G} (hK : KNormalAt M) (hL : PLayerNotLeAt M)
    (hF : KFactL34FixedPointsGen) : InnerOnKAt M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro E H hdata hC3 e he
  let K : Subgroup G := kSub 3 M H
  let OK : Subgroup G := (CFSG.pPrimeCore 3 ↥K).map K.subtype
  let π : ↥K →* threeStar K := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)
  have hEN : E ≤ Subgroup.normalizer (K : Set G) := hdata.E_le_H.trans (hK 3 E H hdata)
  have hOK : OK ≤ M := HypCGen.pPrimeCore_map_le hdata hK
  have hKM : ¬ K ≤ M := not_kSub_le_of_not_pLayerIn_le (hL 3 E H hdata)
  let ρ : ↥E →* MulAut (threeStar K) :=
    (actStar K).comp (Subgroup.inclusion hEN)
  have hρ : ∀ (e' : ↥E) (x : ↥K),
      ρ e' (π x) = π ⟨(e' : G) * (x : G) * (e' : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hEN e'.2) (x : G)).mp x.2⟩ := by
    intro e' x
    exact actStar_mk K ⟨(e' : G), hEN e'.2⟩ x
  let Y : Subgroup (threeStar K) := (M.subgroupOf K).map π
  have hYne : Y ≠ ⊤ := fun htop => hKM (le_of_map_subgroupOf_eq_top (K := K) hOK htop)
  have hstep1 : ∀ (e' : ↥E), e' ≠ 1 → ∀ x : threeStar K, ρ e' x = x → x ∈ Y := by
    intro e' he' x hx
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥K) x
    rw [hρ e' k] at hx
    have hmem : (k : G)⁻¹ * ((e' : G) * (k : G) * (e' : G)⁻¹) ∈ OK := by
      have h2 : (⟨k, k.2⟩ : ↥K)⁻¹ * ⟨(e' : G) * (k : G) * (e' : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hEN e'.2) (k : G)).mp k.2⟩ ∈
          CFSG.pPrimeCore 3 ↥K :=
        (QuotientGroup.eq (s := CFSG.pPrimeCore 3 ↥K)).mp hx.symm
      exact Subgroup.mem_map_of_mem K.subtype (by simpa using h2)
    exact mem_map_subgroupOf_of_conj_eq hdata hK e'.2 (fun h1 => he' (Subtype.ext h1)) k.2 hmem
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro e' he'
    by_contra he1
    refine hYne (eq_top_iff.mpr fun x _ => ?_)
    exact hstep1 e' he1 x (by rw [he']; simp)
  let F : Subgroup (MulAut (threeStar K)) := ρ.range
  have hFmap : F = (⊤ : Subgroup ↥E).map ρ := MonoidHom.range_eq_map ρ
  have hFelem : CFSG.Open.IsElemAbelian 3 F := by
    have htop : CFSG.Open.IsElemAbelian 3 (⊤ : Subgroup ↥E) := by
      haveI := hdata.elem.1
      refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x _ => Subtype.ext ?_⟩
      · simpa using congrArg Subtype.val (mul_comm' a.1 b.1)
      · exact hdata.elem.2 (x : G) x.2
    rw [hFmap]
    exact htop.map ρ
  have hFcard : Nat.card F = 9 := by
    rw [hFmap, Subgroup.card_map_of_injective hinj, Subgroup.card_top]
    simpa using hdata.card
  have hfixed : ∀ f ∈ F, f ≠ 1 → ∀ x : threeStar K, f x = x → x ∈ Y := by
    intro f hf hf1 x hfx
    obtain ⟨e', rfl⟩ := MonoidHom.mem_range.mp hf
    have he' : e' ≠ 1 := by
      intro h1
      apply hf1
      rw [h1, map_one]
    exact hstep1 e' he' x hfx
  have hKiso : Nonempty (threeStar K ≃* CFSG.PGLModel.projSL 3 (GaloisField 2 2)) :=
    HypCGen.nonempty_mulEquiv_threeStar hC3
  have hinn : F ≤ (MulAut.conj : threeStar K →* MulAut (threeStar K)).range := by
    by_contra hnot
    exact hYne (hF (threeStar K) hKiso F hFelem hFcard hnot Y hfixed)
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp
    (hinn (MonoidHom.mem_range.mpr ⟨⟨e, he⟩, rfl⟩))
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥K) y
  refine ⟨(k : G), k.2, fun x hx => ?_⟩
  have hm1 : (e * x * e⁻¹) ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (hEN he) x).mp hx
  have hm2 : ((k : G) * x * (k : G)⁻¹) ∈ K :=
    K.mul_mem (K.mul_mem k.2 hx) (K.inv_mem k.2)
  have h1 : ρ ⟨e, he⟩ (π ⟨x, hx⟩) = π ⟨e * x * e⁻¹, hm1⟩ := hρ ⟨e, he⟩ ⟨x, hx⟩
  have h2 : (MulAut.conj y) (π ⟨x, hx⟩) = π ⟨(k : G) * x * (k : G)⁻¹, hm2⟩ := by
    rw [MulAut.conj_apply, ← hk, ← map_mul, ← map_inv, ← map_mul]
    rfl
  have heq : π ⟨e * x * e⁻¹, hm1⟩ = π ⟨(k : G) * x * (k : G)⁻¹, hm2⟩ := by
    rw [← h1, ← hy, h2]
  have hO : ((⟨(k : G) * x * (k : G)⁻¹, hm2⟩ : ↥K)⁻¹ * ⟨e * x * e⁻¹, hm1⟩ : ↥K) ∈
      CFSG.pPrimeCore 3 ↥K := (QuotientGroup.eq (s := CFSG.pPrimeCore 3 ↥K)).mp heq.symm
  exact Subgroup.mem_map_of_mem K.subtype (by simpa using hO)


theorem agl81FourteenFifteen_of_kFact (hF : KFactL34FixedPointsGen)
    (h : ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
      CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty →
        PreambleTypes M ∧ ChoiceExists M ∧ CaseOneFalse M ∧ CaseTwoFalse M ∧
        FourteenFifteenNormAt M ∧ KNormalAt M ∧ PLayerNotLeAt M ∧ NineNineOneAt M) :
    AGL81FourteenFifteen := by
  refine agl81FourteenFifteen_of_print_inputs ?_
  intro G _ _ hC M hM hσ
  obtain ⟨hpre, hch, h1, h2, hN, hK, hL, hU⟩ := h G hC M hM hσ
  exact ⟨hpre, hch, h1, h2, hN, hK, hL, hU, innerOnKAt_of hK hL hF⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
