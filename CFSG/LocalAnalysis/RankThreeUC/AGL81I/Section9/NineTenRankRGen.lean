module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenRankR
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.Base
import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GrpA
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenLayer

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

namespace NineSettingGen

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G}

theorem not_starImg_le_of_normal (h : NineSettingGen G M p Q H E 2) (hU : NineNineOne M p)
    (hQ : CFSG.ABGLocalTools.IsSylowOf p Q H)
    (hY : ¬ centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)) ≤ starImg p H M)
    {U : Subgroup (StarGroup p H)}
    (hUB : U ≤ starImg p H E ⊔ centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)))
    (hUn : (U.subgroupOf (starImg p H E ⊔
      centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)))).Normal)
    (hUp : IsPGroup p U) : ¬ starImg p H E ≤ U := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  intro hle
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' (primeComplementCore (G := ↥H) p)
  let Y : Subgroup (StarGroup p H) :=
    centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H))
  let pre : Subgroup (StarGroup p H) → Subgroup G := fun K => (K.comap π).map H.subtype
  haveI hYnorm : Y.Normal := by
    haveI hchar : (CFSG.layer (StarGroup p H)).Characteristic :=
      CFSG.LocalCores.layer_characteristic
    haveI hnorm : (CFSG.layer (StarGroup p H)).Normal := inferInstance
    dsimp only [Y]
    infer_instance
  have hpre_sub : ∀ K : Subgroup (StarGroup p H), (pre K).subgroupOf H = K.comap π := by
    intro K
    dsimp only [pre]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hpre_le : ∀ K : Subgroup (StarGroup p H), pre K ≤ H :=
    fun K => Subgroup.map_subtype_le _
  have hstar_pre : ∀ K : Subgroup (StarGroup p H), starImg p H (pre K) = K := by
    intro K
    change ((pre K).subgroupOf H).map π = K
    rw [hpre_sub K]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) K
  have hmem_pre_iff : ∀ {K : Subgroup (StarGroup p H)} {x : G} (hxH : x ∈ H),
      x ∈ pre K ↔ π ⟨x, hxH⟩ ∈ K := by
    intro K x hxH
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have hyx' : (⟨x, hxH⟩ : ↥H) = y := Subtype.ext hyx.symm
      rw [hyx']
      exact hy
    · intro hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, hx, rfl⟩
  have hmem_pre : ∀ {K : Subgroup (StarGroup p H)} {A : Subgroup G} (hAH : A ≤ H),
      A ≤ pre K ↔ starImg p H A ≤ K := by
    intro K A hAH
    constructor
    · intro hAK
      have h1 : (A.subgroupOf H).map H.subtype ≤ (K.comap π).map H.subtype := by
        rw [Subgroup.map_subgroupOf_eq_of_le hAH]
        exact hAK
      have h2 : A.subgroupOf H ≤ K.comap π :=
        Subgroup.map_subtype_le_map_subtype.mp h1
      calc starImg p H A = (A.subgroupOf H).map π := rfl
        _ ≤ K := Subgroup.map_le_iff_le_comap.mpr h2
    · intro hAK
      have h1 : A.subgroupOf H ≤ K.comap π := Subgroup.map_le_iff_le_comap.mp hAK
      calc A = (A.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hAH).symm
        _ ≤ (K.comap π).map H.subtype := Subgroup.map_mono h1
        _ = pre K := rfl
  have hstar_mono : ∀ {A B : Subgroup G}, A ≤ B → starImg p H A ≤ starImg p H B :=
    fun hAB => Subgroup.map_mono (Subgroup.comap_mono hAB)
  let B : Subgroup G := pre (starImg p H E ⊔ Y)
  let U₀ : Subgroup G := pre U
  let Ŷ : Subgroup G := pre Y
  have hBH : B ≤ H := hpre_le _
  have hU₀H : U₀ ≤ H := hpre_le _
  have hŶH : Ŷ ≤ H := hpre_le _
  have hEH : E ≤ H := h.stdE.2.1.trans h.Q_le_H
  have hnormU : starImg p H E ⊔ Y ≤ normalizer (U : Set (StarGroup p H)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).mp hUn
  have hU₀B : U₀ ≤ B := by
    dsimp only [U₀, B, pre]
    exact Subgroup.map_mono (Subgroup.comap_mono hUB)
  have hconjU₀ : ∀ b ∈ B, ∀ u ∈ U₀, b * u * b⁻¹ ∈ U₀ := by
    intro b hb u hu
    have hbH : b ∈ H := hBH hb
    have huH : u ∈ H := hU₀H hu
    have hπb : π ⟨b, hbH⟩ ∈ starImg p H E ⊔ Y := (hmem_pre_iff hbH).mp hb
    have hπu : π ⟨u, huH⟩ ∈ U := (hmem_pre_iff huH).mp hu
    have hbU : π ⟨b, hbH⟩ ∈ normalizer (U : Set (StarGroup p H)) := hnormU hπb
    have hconj : π ⟨b, hbH⟩ * π ⟨u, huH⟩ * (π ⟨b, hbH⟩)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp hbU (π ⟨u, huH⟩)).mp hπu
    have hbuH : b * u * b⁻¹ ∈ H := H.mul_mem (H.mul_mem hbH huH) (H.inv_mem hbH)
    refine (hmem_pre_iff hbuH).mpr ?_
    have heq : (⟨b * u * b⁻¹, hbuH⟩ : ↥H) =
        ⟨b, hbH⟩ * ⟨u, huH⟩ * ⟨b, hbH⟩⁻¹ := Subtype.ext rfl
    rw [heq, map_mul, map_mul, map_inv]
    exact hconj
  have hU₀norm : (U₀.subgroupOf B).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hU₀B]
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      exact hconjU₀ b hb u hu
    · intro hu'
      have h := hconjU₀ b⁻¹ (B.inv_mem hb) (b * u * b⁻¹) hu'
      have heq : b⁻¹ * (b * u * b⁻¹) * (b⁻¹)⁻¹ = u := by group
      rwa [heq] at h
  have hOleU₀ : relPPrimeCore p H ≤ U₀ := by
    change sSup {N : Subgroup G | N ≤ H ∧ (N.subgroupOf H).Normal ∧
      Nat.Coprime p (Nat.card N)} ≤ U₀
    refine sSup_le fun N hN => ?_
    obtain ⟨hNH, hNnorm, hNcop⟩ := hN
    have h1 : N.subgroupOf H ≤ primeComplementCore (G := ↥H) p := by
      refine le_sSup ⟨hNnorm, ?_⟩
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
    have h2 : N ≤ (primeComplementCore (G := ↥H) p).map H.subtype := by
      calc N = (N.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hNH).symm
        _ ≤ (primeComplementCore (G := ↥H) p).map H.subtype := Subgroup.map_mono h1
    refine h2.trans ?_
    refine (hmem_pre (K := U) (A := (primeComplementCore (G := ↥H) p).map H.subtype)
      (Subgroup.map_subtype_le _)).mpr ?_
    have hstar_ker : starImg p H ((primeComplementCore (G := ↥H) p).map H.subtype) = ⊥ := by
      dsimp only [starImg]
      rw [show (((primeComplementCore (G := ↥H) p).map H.subtype).subgroupOf H) =
          primeComplementCore (G := ↥H) p from
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective _]
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hstar_ker]
    exact bot_le
  have hEB : E ≤ B :=
    (hmem_pre (K := starImg p H E ⊔ Y) (A := E) hEH).mpr le_sup_left
  have hŶB : Ŷ ≤ B := by
    refine (hmem_pre (K := starImg p H E ⊔ Y) (A := Ŷ) hŶH).mpr ?_
    rw [hstar_pre Y]
    exact le_sup_right
  have hB_le : B ≤ E ⊔ Ŷ := by
    intro b hb
    have hbH : b ∈ H := hBH hb
    have hπb : π ⟨b, hbH⟩ ∈ starImg p H E ⊔ Y := (hmem_pre_iff hbH).mp hb
    obtain ⟨a, ha, y, hy, hay⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := starImg p H E) (t := Y)).mp hπb
    obtain ⟨e, he, hea⟩ := Subgroup.mem_map.mp ha
    have heE : (e : G) ∈ E := Subgroup.mem_subgroupOf.mp he
    have heH : (e : G) ∈ H := hEH heE
    let bH : ↥H := ⟨b, hbH⟩
    have hπ_e : π (e⁻¹ * bH) = y := by
      rw [map_mul, map_inv, hea, show π bH = a * y from hay.symm]
      group
    have hmem : (e : G)⁻¹ * b ∈ Ŷ := by
      have h1 : H.subtype (e⁻¹ * bH) ∈ pre Y :=
        Subgroup.mem_map_of_mem H.subtype (Subgroup.mem_comap.mpr (by rw [hπ_e]; exact hy))
      simpa [bH] using h1
    have hb_eq : b = (e : G) * ((e : G)⁻¹ * b) := by group
    rw [hb_eq]
    exact (E ⊔ Ŷ).mul_mem (Subgroup.mem_sup_left heE) (Subgroup.mem_sup_right hmem)
  have hB_eq : B = E ⊔ Ŷ := le_antisymm hB_le (sup_le hEB hŶB)
  have hŶnorm : (Ŷ.subgroupOf H).Normal := by
    dsimp only [Ŷ]
    rw [hpre_sub Y]
    infer_instance
  have hUp₀ : IsPGroup p ↥(starImg p H U₀) := by
    dsimp only [U₀]
    rw [hstar_pre U]
    exact hUp
  have hEQ : E ≤ Q := h.stdE.2.1
  have hS : CFSG.ABGLocalTools.IsSylowOf p (Q ⊓ B) B := by
    rw [hB_eq]
    exact isSylowOf_inf_sup hQ hŶH hŶnorm hEQ
  have hES : E ≤ Q ⊓ B := le_inf hEQ hEB
  have hEU₀ : E ≤ U₀ := (hmem_pre (K := U) (A := E) hEH).mpr hle
  have hSM : Q ⊓ B ≤ M := inf_le_left.trans h.Q_le_M
  have hBM : B ≤ M :=
    h.le_of_frattini (B := B) (U := U₀) (S := Q ⊓ B) hU hBH hU₀B hU₀norm hOleU₀
      hUp₀ hS hSM hES hEU₀
  have hYle : Y ≤ starImg p H M := by
    calc Y = starImg p H Ŷ := (hstar_pre Y).symm
      _ ≤ starImg p H B := hstar_mono hŶB
      _ ≤ starImg p H M := hstar_mono hBM
  exact hY hYle

theorem two_le_pRank_pCore (h : NineSettingGen G M p Q H E 2) (hU : NineNineOne M p)
    (hQ : CFSG.ABGLocalTools.IsSylowOf p Q H)
    (hY : ¬ centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H)) ≤ starImg p H M) :
    2 ≤ CFSG.Open.pRank p (CFSG.pCore p (StarGroup p H)) := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  let Rstar : Subgroup (StarGroup p H) := CFSG.pCore p (StarGroup p H)
  let Y : Subgroup (StarGroup p H) :=
    centralizer (CFSG.layer (StarGroup p H) : Set (StarGroup p H))
  change 2 ≤ CFSG.Open.pRank p Rstar
  by_contra hlt
  have hlt1 : CFSG.Open.pRank p Rstar ≤ 1 := by
    have := Nat.not_le.mp hlt
    omega
  haveI hRnorm : Rstar.Normal := CFSG.pCore_normal (p := p) (G := StarGroup p H)
  haveI hRp : IsPGroup p Rstar := CFSG.pCore_isPGroup (p := p) (G := StarGroup p H)
  haveI hCnorm : (centralizer (Rstar : Set (StarGroup p H))).Normal := inferInstance
  haveI hYnorm : Y.Normal := by
    haveI hchar : (CFSG.layer (StarGroup p H)).Characteristic :=
      CFSG.LocalCores.layer_characteristic
    haveI hnorm : (CFSG.layer (StarGroup p H)).Normal := inferInstance
    dsimp only [Y]
    infer_instance
  have hnorm_of_normal : ∀ g : StarGroup p H, g ∈ normalizer (Rstar : Set (StarGroup p H)) := by
    intro g
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top g
  have hRcyc : IsCyclic ↥Rstar := by
    by_contra hnc
    haveI : Fact (IsPGroup p ↥Rstar) := ⟨hRp⟩
    obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a (R := ↥Rstar) h.ne_two hnc
    have hSab : IsElemAbelian p (S.map Rstar.subtype) :=
      (CFSG.Open.isElemAbelian_iff_isElementaryAbelian).mpr
        (CFSG.IsElementaryAbelian.subgroup_map hSel Rstar.subtype)
    have hSR : S.map Rstar.subtype ≤ Rstar := Subgroup.map_subtype_le _
    have hcard : Nat.card (S.map Rstar.subtype) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective Rstar.subtype_injective, hScard]
    have h2 := CFSG.SectionRank.le_pRank h.prime.one_lt hSR hSab hcard
    omega
  have hEp : ∀ e ∈ starImg p H E, e ^ p = 1 := by
    intro e he
    obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp he
    have he'E : (e' : G) ∈ E := Subgroup.mem_subgroupOf.mp he'
    have he'p : (e' : ↥H) ^ p = 1 := by
      apply Subtype.ext
      simpa using h.stdE.2.2.1.2 (e' : G) he'E
    rw [← map_pow, he'p, map_one]
  have hEpgroup : IsPGroup p (starImg p H E) :=
    ((h.stdE.2.2.1.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))).isPGroup
  let B : Subgroup (StarGroup p H) := starImg p H E ⊔ Y
  let K₀ : Subgroup (StarGroup p H) := B ⊓ centralizer (Rstar : Set (StarGroup p H))
  let U : Subgroup (StarGroup p H) := starImg p H E ⊔ K₀
  have hE_B : starImg p H E ≤ B := le_sup_left
  have hK₀_B : K₀ ≤ B := inf_le_left
  have hK₀_normB : (K₀.subgroupOf B).Normal := by
    rw [show K₀ = B ⊓ centralizer (Rstar : Set (StarGroup p H)) from rfl]
    rw [Subgroup.inf_subgroupOf_left (centralizer (Rstar : Set (StarGroup p H))) B]
    infer_instance
  have hK₀p : IsPGroup p K₀ := by
    rw [IsPGroup.iff_orderOf]
    intro x
    have hxB : (x : StarGroup p H) ∈ B := x.2.1
    have hxcent : (x : StarGroup p H) ∈ centralizer (Rstar : Set (StarGroup p H)) := x.2.2
    obtain ⟨e, he, y, hy, hxy⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := starImg p H E) (t := Y)).mp hxB
    have hep : e ^ p = 1 := hEp e he
    have hxpY : (x : StarGroup p H) ^ p ∈ Y := by
      have h1 : QuotientGroup.mk' Y ((x : StarGroup p H) ^ p) = 1 := by
        rw [map_pow]
        have hxq : QuotientGroup.mk' Y (x : StarGroup p H) = QuotientGroup.mk' Y e := by
          rw [← hxy, map_mul, show QuotientGroup.mk' Y y = 1 from
            (QuotientGroup.eq_one_iff y).mpr hy, mul_one]
        rw [hxq, ← map_pow, hep, map_one]
      rw [← QuotientGroup.ker_mk' Y, MonoidHom.mem_ker]
      exact h1
    have hxpcent : (x : StarGroup p H) ^ p ∈
        centralizer (Rstar : Set (StarGroup p H)) :=
      (Subgroup.centralizer (Rstar : Set (StarGroup p H))).pow_mem hxcent p
    have hxpR : (x : StarGroup p H) ^ p ∈ Rstar := by
      have hle := cStarL_inf_centralizer_le_pCore h.prime H
      rw [cStarL_eq_centralizer_layer h.prime H] at hle
      exact hle ⟨hxpY, hxpcent⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hRp) ⟨(x : StarGroup p H) ^ p, hxpR⟩
    have hn' : orderOf ((x : StarGroup p H) ^ p) = p ^ n := by
      rw [← Subgroup.orderOf_mk ((x : StarGroup p H) ^ p) hxpR]
      exact hn
    have hxpow : (x : StarGroup p H) ^ (p ^ (n + 1)) = 1 := by
      have h1 : ((x : StarGroup p H) ^ p) ^ (p ^ n) = 1 := by
        rw [← hn']
        exact pow_orderOf_eq_one _
      rwa [← pow_mul, ← pow_succ'] at h1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow h.prime).mp (orderOf_dvd_of_pow_eq_one hxpow)
    refine ⟨k, ?_⟩
    rw [← Subgroup.orderOf_coe x]
    exact hk
  have hE_normK₀ : starImg p H E ≤ normalizer (K₀ : Set (StarGroup p H)) := by
    have h1 : starImg p H E ≤ normalizer (B : Set (StarGroup p H)) :=
      hE_B.trans B.le_normalizer
    have h2 : starImg p H E ≤
        normalizer (centralizer (Rstar : Set (StarGroup p H)) : Set (StarGroup p H)) :=
      Subgroup.le_normalizer_of_normal
    have h3 : normalizer (B : Set (StarGroup p H)) ⊓
        normalizer (centralizer (Rstar : Set (StarGroup p H)) : Set (StarGroup p H)) ≤
        normalizer (K₀ : Set (StarGroup p H)) := by
      rw [show K₀ = B ⊓ centralizer (Rstar : Set (StarGroup p H)) from rfl]
      exact Subgroup.inf_normalizer_le_normalizer_inf
    exact (le_inf h1 h2).trans h3
  have hUp : IsPGroup p U := by
    rw [show U = starImg p H E ⊔ K₀ from rfl]
    exact hEpgroup.to_sup_of_normal_right' hK₀p hE_normK₀
  have hUB : U ≤ B := by
    rw [show U = starImg p H E ⊔ K₀ from rfl]
    exact sup_le hE_B hK₀_B
  have hUnormB : (U.subgroupOf B).Normal := by
    have hconjU : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U := by
      intro b hb u hu
      have hnormK₀ : b ∈ normalizer (K₀ : Set (StarGroup p H)) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hK₀_B).mp hK₀_normB hb
      obtain ⟨e, he, k, hk, huk⟩ :=
        CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.mem_sup_of_le_normalizer hE_normK₀ hu
      rw [huk]
      have hbkb : b * k * b⁻¹ ∈ K₀ := (Subgroup.mem_normalizer_iff.mp hnormK₀ k).mp hk
      have hbeb : b * e * b⁻¹ ∈ U := by
        have hce : b * e * b⁻¹ * e⁻¹ ∈ K₀ := by
          refine ⟨?_, ?_⟩
          · exact B.mul_mem (B.mul_mem (B.mul_mem hb (hE_B he)) (B.inv_mem hb))
              (B.inv_mem (hE_B he))
          · exact commutator_mem_centralizer_of_isCyclic hRcyc
              (hnorm_of_normal b) (hnorm_of_normal e)
        have heq : b * e * b⁻¹ = (b * e * b⁻¹ * e⁻¹) * e := by group
        rw [heq]
        exact U.mul_mem (Subgroup.mem_sup_right hce) (Subgroup.mem_sup_left he)
      have heq : b * (e * k) * b⁻¹ = (b * e * b⁻¹) * (b * k * b⁻¹) := by group
      rw [heq]
      exact U.mul_mem hbeb (Subgroup.mem_sup_right hbkb)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hUB]
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      exact hconjU b hb u hu
    · intro hu'
      have h := hconjU b⁻¹ (B.inv_mem hb) (b * u * b⁻¹) hu'
      have heq : b⁻¹ * (b * u * b⁻¹) * (b⁻¹)⁻¹ = u := by group
      rwa [heq] at h
  exact h.not_starImg_le_of_normal hU hQ hY hUB hUnormB hUp le_sup_left

end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
