module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddCtrl
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdNormal
public import CFSG.GroupTheory.SteinbergCBFTSCNRank
public import CFSG.LocalAnalysis.SectionRank.GroupRankTransport

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G] {A V K : Subgroup G} {t y : G}

private theorem le_centralizer_mul_of_l34SuzOddData (hS : L34SuzOddSetting A t)
    (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V) :
    K ≤ centralizer ({t * u} : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  have htk : t * k = k * t :=
    (Subgroup.mem_centralizer_iff.mp hS.t_mem k (le_A_of_l34SuzOddData hD hk)).symm
  have huk : u * k = k * u :=
    (Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_l34SuzOddData hD hu hk)).symm
  calc k * (t * u) = (k * t) * u := by group
    _ = (t * k) * u := by rw [← htk]
    _ = t * (k * u) := by group
    _ = t * (u * k) := by rw [← huk]
    _ = (t * u) * k := by group

private theorem exists_isElementaryAbelian_eight_of_l34SuzOddData
    (hD : L34SuzOddData A V K y)
    (hKq : IsQuasisimple ↥K) :
    ∃ F : Subgroup G, F ≤ K ∧ IsElementaryAbelian 2 F ∧ 8 ≤ Nat.card F := by
  have hKcard : Nat.card (↥K ⧸ center ↥K) = 20160 :=
    CFSG.ComponentClassification.CatLeaf.card_of_isL34Type hD.l34
  have h2K : 2 ∣ Nat.card ↥K :=
    (by norm_num : 2 ∣ 20160).trans
      (hKcard ▸ Subgroup.card_quotient_dvd_card (center ↥K))
  have hO : pPrimeCore 2 ↥K ≠ ⊤ := by
    intro htop
    have hc := CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥K)
    rw [htop, Subgroup.card_top] at hc
    exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h2K hc
  have hZ : Open.fusionZStar ↥K = center ↥K :=
    CFSG.ComponentClassification.CatLeaf.fusionZStar_eq_center_of_quasisimple hKq hO
  have hL34 : IsL34Type (↥K ⧸ Open.fusionZStar ↥K) :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq hZ).symm hD.l34
  have h3 : 3 ≤ pRank 2 ↥K :=
    CFSG.ComponentClassification.GrSLit.GrS5.three_le_pRank_of_l34 hL34
  have h3top : 3 ≤ CFSG.pRank 2 ↥(⊤ : Subgroup ↥K) := by
    rw [CFSG.pRank_congr_of_mulEquiv (Subgroup.topEquiv (G := ↥K)) 2]
    exact h3
  obtain ⟨E, hE, hE8⟩ :=
    CFSG.GroupTheory.FT63ChII.exists_isElementaryAbelian_of_three_le_pRank
      (P := ↥K) (p := 2) (B := ⊤) h3top
  let E' : Subgroup ↥K := E.map (⊤ : Subgroup ↥K).subtype
  have hE' : IsElementaryAbelian 2 E' := hE.map (⊤ : Subgroup ↥K).subtype
  have hE'card : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective (⊤ : Subgroup ↥K))
  have hE'8 : 2 ^ 3 ≤ Nat.card E' := by rwa [hE'card]
  let F : Subgroup G := E'.map K.subtype
  have hFK : F ≤ K := Subgroup.map_subtype_le E'
  have hF : IsElementaryAbelian 2 F := hE'.map_subtype
  have hFcard : Nat.card F = Nat.card E' :=
    Subgroup.card_map_of_injective K.subtype_injective
  exact ⟨F, hFK, hF, by rw [hFcard]; exact hE'8⟩

private theorem false_of_eight_le_centralizer_conj_of_l34SuzOdd
    (hS : L34SuzOddSetting A t) {F : Subgroup G} {h : G}
    (hF : IsElementaryAbelian 2 F) (hF8 : 8 ≤ Nat.card F)
    (hFC : F ≤ centralizer ((A.map (MulAut.conj h).toMonoidHom) : Set G)) : False := by
  have hF2 : IsPGroup 2 F := hF.isPGroup 2
  have hF'C : F.map (MulAut.conj h⁻¹).toMonoidHom ≤ centralizer (A : Set G) := by
    rintro _ ⟨y, hyF, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hy : (MulAut.conj h) a ∈ A.map (MulAut.conj h).toMonoidHom := ⟨a, ha, rfl⟩
    have hcomm := (Subgroup.mem_centralizer_iff.mp (hFC hyF)) ((MulAut.conj h) a) hy
    calc a * (MulAut.conj h⁻¹) y
        = (MulAut.conj h⁻¹) ((MulAut.conj h) a * y) := by simp [MulAut.conj_apply]; group
      _ = (MulAut.conj h⁻¹) (y * (MulAut.conj h) a) := by rw [hcomm]
      _ = (MulAut.conj h⁻¹) y * a := by simp [MulAut.conj_apply]; group
  have hF'2 : IsPGroup 2 (F.map (MulAut.conj h⁻¹).toMonoidHom) := hF2.map _
  have hF'2C : IsPGroup 2 ((F.map (MulAut.conj h⁻¹).toMonoidHom).subgroupOf
      (centralizer (A : Set G))) :=
    hF'2.of_equiv (Subgroup.subgroupOfEquivOfLe hF'C).symm
  obtain ⟨S, hSle⟩ := hF'2C.exists_le_sylow
  have hcardS : Nat.card S = 2 := hS.card_sylow S
  have hcardSub : Nat.card ↥((F.map (MulAut.conj h⁻¹).toMonoidHom).subgroupOf
      (centralizer (A : Set G))) = Nat.card ↥(F.map (MulAut.conj h⁻¹).toMonoidHom) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF'C).toEquiv
  have hcardMap : Nat.card ↥(F.map (MulAut.conj h⁻¹).toMonoidHom) = Nat.card F :=
    Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective
  have hle : Nat.card F ≤ Nat.card S := by
    calc Nat.card F = Nat.card ↥((F.map (MulAut.conj h⁻¹).toMonoidHom).subgroupOf
        (centralizer (A : Set G))) := hcardMap.symm.trans hcardSub.symm
      _ ≤ Nat.card S := by simpa using Subgroup.card_le_of_le hSle
  rw [hcardS] at hle
  omega

private theorem le_centralizer_of_isComponent_mul_conj_of_l34SuzOdd
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y)
    {u : G}
    (hKVu : K ≤ centralizer ({t * u} : Set G))
    (hK : IsComponent (K.subgroupOf (centralizer ({t * u} : Set G))))
    {h : G} (hh : h * t * h⁻¹ = t * u) :
    K ≤ centralizer ((A.map (MulAut.conj h).toMonoidHom) : Set G) := by
  have hth2 : orderOf (h * t * h⁻¹) = 2 := by
    rw [show h * t * h⁻¹ = (MulAut.conj h).toMonoidHom t by simp [MulAut.conj_apply]]
    rw [orderOf_injective _ (MulAut.conj h).injective, hS.orderOf_t]
  have hstAh : IsStandardSubgroup (A.map (MulAut.conj h).toMonoidHom) :=
    hS.standard.map_mulEquiv (MulAut.conj h)
  have hth_mem : h * t * h⁻¹ ∈ centralizer
      ((A.map (MulAut.conj h).toMonoidHom) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    have hta : a₀ * t = t * a₀ := Subgroup.mem_centralizer_iff.mp hS.t_mem a₀ ha₀
    calc (h * a₀ * h⁻¹) * (h * t * h⁻¹) = h * (a₀ * t) * h⁻¹ := by group
      _ = h * (t * a₀) * h⁻¹ := by rw [hta]
      _ = (h * t * h⁻¹) * (h * a₀ * h⁻¹) := by group
  obtain ⟨hAle, -, hAnorm⟩ :=
    le_centralizer_isPComponent_normal_of_isStandardSubgroup hstAh hth2 hth_mem
  have hAcomp : IsComponent ((A.map (MulAut.conj h).toMonoidHom).subgroupOf
      (centralizer ({h * t * h⁻¹} : Set G))) :=
    ⟨(IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hAle)).mpr hstAh.1,
      hAnorm.isSubnormal⟩
  have hKle : K ≤ centralizer ({h * t * h⁻¹} : Set G) := by
    rw [hh]; exact hKVu
  rw [← hh] at hK
  have hne : K.subgroupOf (centralizer ({h * t * h⁻¹} : Set G)) ≠
      (A.map (MulAut.conj h).toMonoidHom).subgroupOf
        (centralizer ({h * t * h⁻¹} : Set G)) := by
    intro heq
    have hKA : K = A.map (MulAut.conj h).toMonoidHom := by
      have h1 := congrArg (Subgroup.map (centralizer ({h * t * h⁻¹} : Set G)).subtype) heq
      rwa [Subgroup.map_subgroupOf_eq_of_le hKle,
        Subgroup.map_subgroupOf_eq_of_le hAle] at h1
    have hKcard : Nat.card (↥K ⧸ center ↥K) = 20160 :=
      CFSG.ComponentClassification.CatLeaf.card_of_isL34Type hD.l34
    have hAcard : Nat.card (↥(A.map (MulAut.conj h).toMonoidHom) ⧸
        center ↥(A.map (MulAut.conj h).toMonoidHom)) = 448345497600 := by
      let eA : ↥A ≃* ↥(A.map (MulAut.conj h).toMonoidHom) :=
        A.equivMapOfInjective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective
      rw [← CFSG.Sporadic.SuzOddCore.card_quotient_center_equiv eA]
      obtain ⟨e⟩ := hS.suz
      exact (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Suz.card_Suz
    rw [hKA] at hKcard
    omega
  have hcomm : ⁅K.subgroupOf (centralizer ({h * t * h⁻¹} : Set G)),
      (A.map (MulAut.conj h).toMonoidHom).subgroupOf
        (centralizer ({h * t * h⁻¹} : Set G))⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hK hAcomp).resolve_left hne
  have hcommG : ⁅K, A.map (MulAut.conj h).toMonoidHom⁆ = ⊥ := by
    have h1 := congrArg (Subgroup.map (centralizer ({h * t * h⁻¹} : Set G)).subtype) hcomm
    rwa [Subgroup.map_bot, Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hKle,
      Subgroup.map_subgroupOf_eq_of_le hAle] at h1
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommG

private theorem false_of_isComponent_mul_of_conj_of_l34SuzOdd
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y)
    {u : G} (hu : u ∈ V)
    (hK : IsComponent (K.subgroupOf (centralizer ({t * u} : Set G))))
    {h : G} (hh : h * t * h⁻¹ = t * u) : False := by
  have hKVu : K ≤ centralizer ({t * u} : Set G) := le_centralizer_mul_of_l34SuzOddData hS hD hu
  have hKq : IsQuasisimple ↥K :=
    (IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hKVu)).mp hK.1
  obtain ⟨F, hFK, hF, hF8⟩ := exists_isElementaryAbelian_eight_of_l34SuzOddData hD hKq
  have hFC : F ≤ centralizer ((A.map (MulAut.conj h).toMonoidHom) : Set G) :=
    hFK.trans (le_centralizer_of_isComponent_mul_conj_of_l34SuzOdd hS hD hKVu hK hh)
  exact false_of_eight_le_centralizer_conj_of_l34SuzOdd hS hF hF8 hFC

theorem false_of_isComponent_mul_of_l34SuzOdd
    (hSG : SuzTwoBFusionGeneration) (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y)
    {u : G} (hu : u ∈ V) (hu1 : u ≠ 1)
    (hK : IsComponent (K.subgroupOf (centralizer ({t * u} : Set G)))) : False := by
  by_cases hconj : ∃ h : G, h * t * h⁻¹ = t * u
  · obtain ⟨h, hh⟩ := hconj
    exact false_of_isComponent_mul_of_conj_of_l34SuzOdd hS hD hu hK hh
  · push Not at hconj
    have hKVu : K ≤ centralizer ({t * u} : Set G) := le_centralizer_mul_of_l34SuzOddData hS hD hu
    have htC : t ∈ centralizer ({t * u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : t * (t * u) = u := by rw [← mul_assoc, ← pow_two, ← hS.orderOf_t,
        pow_orderOf_eq_one, one_mul]
      have h2 : (t * u) * t = u := by
        rw [mul_assoc]
        have htu : t * u = u * t :=
          (Subgroup.mem_centralizer_iff.mp hS.t_mem u (hD.le_A hu)).symm
        rw [← htu, ← mul_assoc, ← pow_two, ← hS.orderOf_t, pow_orderOf_eq_one, one_mul]
      rw [h1, h2]
    have hNK : centralizer ({t * u} : Set G) ≤ normalizer (K : Set G) :=
      le_normalizer_of_isComponent_of_l34SuzOdd hS hD htC hKVu hK
    have h2K : 2 ∣ Nat.card ↥K := by
      have hKcard : Nat.card (↥K ⧸ center ↥K) = 20160 :=
        CFSG.ComponentClassification.CatLeaf.card_of_isL34Type hD.l34
      exact (by norm_num : 2 ∣ 20160).trans
        (hKcard ▸ Subgroup.card_quotient_dvd_card (center ↥K))
    have hv0 : ∃ v : G, v ∈ K ∧ v * v = 1 ∧ v ≠ 1 := by
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 h2K
      have hx2 : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe, hx]
      refine ⟨(x : G), x.2, ?_, ?_⟩
      · have h := pow_orderOf_eq_one (x : G)
        rwa [hx2, pow_two] at h
      · intro h1
        rw [h1, orderOf_one] at hx2
        omega
    have hgen : ∀ v ∈ K, v * v = 1 → v ≠ 1 →
        ∃ a : G, a * (t * u) * a⁻¹ = (t * u) * v ∧
          K ⊔ K.map (MulAut.conj a).toMonoidHom = A := by
      intro v hvK hv2 hv1
      obtain ⟨a, haA, hau, hsup⟩ :=
        exists_conj_mul_sup_eq_of_l34SuzOddData hSG hS.standard.1.1 hS.suz hS.odd_card_center
          hD hu hu1 hvK hv2 hv1
      refine ⟨a, ?_, hsup⟩
      have hat : a * t = t * a := Subgroup.mem_centralizer_iff.mp hS.t_mem a haA
      calc a * (t * u) * a⁻¹ = (a * t * a⁻¹) * (a * u * a⁻¹) := by group
        _ = t * (u * v) := by
          rw [show a * t * a⁻¹ = t by rw [hat]; group, hau]
        _ = (t * u) * v := by group
    have hNA : centralizer ({t * u} : Set G) ≤ normalizer (A : Set G) :=
      centralizer_le_normalizer_of_conj_sup_eq hNK hv0 hgen
    exact not_centralizer_mul_le_normalizer_of_l34SuzOdd hS hD hu hu1 hconj hNA

end CFSG.ComponentClassification.GrSLit.L34Sec5S
