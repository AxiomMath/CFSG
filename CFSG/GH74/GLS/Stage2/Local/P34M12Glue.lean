module

public import CFSG.GH74.GLS.Stage2.Local.P34Step1
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Transport
public import CFSG.GH74.GLS.Stage2.Local.Bar
public import CFSG.GH74.GLS.Stage2.Local.P34M12Bar

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34M12

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.GH74.GLS.Stage1.Thm6.Prod
open scoped commutatorElement

section Glue

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {H : Subgroup G}

open scoped Classical in
noncomputable def piFun (H : Subgroup G) (hCH : Cen z ≤ H) : HBar H → CentralizerBar z :=
  fun x => if hx : x ∈ barIn H (Cen z) then cenToBar H hCH ⟨x, hx⟩ else 1

theorem piFun_of_mem (hCH : Cen z ≤ H) {x : HBar H} (hx : x ∈ barIn H (Cen z)) :
    piFun H hCH x = cenToBar H hCH ⟨x, hx⟩ := by
  simp [piFun, hx]

theorem sq_eq_one_of_orderOf_eq_two {M : Type*} [Group M] {g : M} (h : orderOf g = 2) : g * g = 1 := by
  have := pow_orderOf_eq_one g
  rw [h] at this
  simpa [pow_two] using this

theorem setup_of (hz2 : orderOf z = 2) (hzH : z ∈ H) (hCH : Cen z ≤ H) {a : CentralizerBar z}
    (hB : BarFacts (WBar z) (toBar z ⟨z, mem_Cen_self z⟩) a) :
    Setup (WBar z) (toBar z ⟨z, mem_Cen_self z⟩) a (barIn H (Cen z)) (piFun H hCH)
      (mkH H ⟨z, hzH⟩) := by
  have hzH2 : orderOf (⟨z, hzH⟩ : ↥H) = 2 := by
    rw [← hz2]
    exact (Subgroup.orderOf_coe (⟨z, hzH⟩ : ↥H)).symm
  have hzb2 : orderOf (mkH H ⟨z, hzH⟩) = 2 := orderOf_mk_eq_two H hzH2
  have hCen : centralizer ({mkH H ⟨z, hzH⟩} : Set (HBar H)) = barIn H (Cen z) :=
    centralizer_mk_eq H hz2 hzH
  have hzbC : mkH H ⟨z, hzH⟩ ∈ barIn H (Cen z) := by
    rw [← hCen]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  refine ⟨hB, ?_, ?_, ?_, ?_, sq_eq_one_of_orderOf_eq_two hzb2, ?_, ?_⟩
  · intro x hx y hy
    rw [piFun_of_mem hCH hx, piFun_of_mem hCH hy, piFun_of_mem hCH ((barIn H (Cen z)).mul_mem hx hy)]
    exact map_mul (cenToBar H hCH) ⟨x, hx⟩ ⟨y, hy⟩
  · rw [piFun_of_mem hCH (one_mem _)]
    exact map_one (cenToBar H hCH)
  · intro y
    obtain ⟨x, rfl⟩ := cenToBar_surjective H hCH y
    exact ⟨x, x.2, piFun_of_mem hCH x.2⟩
  · intro x hx h1 h2
    rw [piFun_of_mem hCH hx] at h1
    have h3 : (⟨x, hx⟩ : ↥(barIn H (Cen z))) * ⟨x, hx⟩ = 1 := Subtype.ext h2
    exact congrArg Subtype.val
      (eq_one_of_odd_of_sq (odd_orderOf_of_cenToBar_eq_one H hCH ⟨x, hx⟩ h1) h3)
  · intro x
    rw [← hCen, Subgroup.mem_centralizer_singleton_iff]
  · rw [piFun_of_mem hCH hzbC]
    exact cenToBar_cenMk H hCH ⟨z, mem_Cen_self z⟩

theorem exists_conj_into_bar (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) (hSC : S ≤ Cen z)
    (hCH : Cen z ≤ H) {u : HBar H} (hu : u ∈ barIn H (Cen z)) (hu2 : u * u = 1) :
    ∃ c ∈ barIn H (Cen z), c * u * c⁻¹ ∈ barIn H S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := barIn_sylow H hS (hSC.trans hCH)
  have hle : barIn H S ≤ barIn H (Cen z) := Subgroup.map_mono (Subgroup.comap_mono hSC)
  have hPb : IsPGroup 2 ↥(barIn H S) := by
    rw [← hT]
    exact T.isPGroup'
  have hP : IsPGroup 2 ↥((barIn H S).subgroupOf (barIn H (Cen z))) :=
    hPb.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  have hidx : ¬ 2 ∣ ((barIn H S).subgroupOf (barIn H (Cen z))).index := by
    intro hd
    apply T.not_dvd_index
    rw [hT]
    exact hd.trans (Subgroup.relIndex_dvd_index_of_le hle)
  let Q : Sylow 2 ↥(barIn H (Cen z)) := hP.toSylow hidx
  by_cases hu1 : u = 1
  · exact ⟨1, one_mem _, by simp [hu1]⟩
  have hsq : (⟨u, hu⟩ : ↥(barIn H (Cen z))) ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hu2
  have hne : (⟨u, hu⟩ : ↥(barIn H (Cen z))) ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  have hpu : IsPGroup 2 ↥(zpowers (⟨u, hu⟩ : ↥(barIn H (Cen z)))) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, orderOf_eq_prime hsq hne]
    norm_num
  obtain ⟨Q', hQ'⟩ := hpu.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥(barIn H (Cen z)) Q' Q
  have hmem : c * (⟨u, hu⟩ : ↥(barIn H (Cen z))) * c⁻¹ ∈
      ((c • Q' : Sylow 2 ↥(barIn H (Cen z))) : Subgroup ↥(barIn H (Cen z))) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) _ (hQ' (mem_zpowers _))
  rw [hc] at hmem
  exact ⟨(c : HBar H), c.2, Subgroup.mem_subgroupOf.1 hmem⟩

theorem normal_le_bar (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) (hSH : S ≤ H) {E : Subgroup (HBar H)}
    (hEn : E.Normal) (hE2 : ∀ e ∈ E, e * e = 1) : E ≤ barIn H S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := barIn_sylow H hS hSH
  have hEp : IsPGroup 2 ↥E := fun g => ⟨1, by
    apply Subtype.ext
    simpa [pow_two] using hE2 g g.2⟩
  rw [← hT]
  exact hEp.le_sylow_of_normal T

def ZCls (H : Subgroup G) (z : G) (x : HBar H) : Prop :=
  ∃ s : ↥H, mkH H s = x ∧ IsConj z (s : G)

omit [Finite G] in
theorem ZCls.conj {x y : HBar H} (hx : ZCls H z x) (h : ∃ g : HBar H, g * x * g⁻¹ = y) :
    ZCls H z y := by
  obtain ⟨s, rfl, hs⟩ := hx
  obtain ⟨g, rfl⟩ := h
  obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥H) g
  refine ⟨g' * s * g'⁻¹, by rw [map_mul, map_mul, map_inv], ?_⟩
  have : IsConj (s : G) ((g' * s * g'⁻¹ : ↥H) : G) := isConj_iff.2 ⟨(g' : G), by simp⟩
  exact hs.trans this

omit [Finite G] in
theorem zCls_self (hzH : z ∈ H) : ZCls H z (mkH H ⟨z, hzH⟩) := ⟨⟨z, hzH⟩, rfl, IsConj.refl z⟩

theorem fuse_out_data (hCH : Cen z ≤ H) (hSC : S ≤ Cen z) {t : G} (htS : t ∈ S) (htW : t ∉ WC z)
    (ht2 : orderOf t = 2) (htc : IsConj z t) :
    ∃ tb : HBar H, tb ∈ barIn H (Cen z) ∧ tb * tb = 1 ∧ piFun H hCH tb ∉ WBar z ∧ ZCls H z tb := by
  have htC : t ∈ Cen z := hSC htS
  have htH : t ∈ H := hCH htC
  have htH2 : orderOf (⟨t, htH⟩ : ↥H) = 2 := by
    rw [← ht2]
    exact (Subgroup.orderOf_coe (⟨t, htH⟩ : ↥H)).symm
  have htb : mkH H ⟨t, htH⟩ ∈ barIn H (Cen z) := cenMk_mem H hCH ⟨t, htC⟩
  refine ⟨mkH H ⟨t, htH⟩, htb, sq_eq_one_of_orderOf_eq_two (orderOf_mk_eq_two H htH2), ?_,
    ⟨⟨t, htH⟩, rfl, htc⟩⟩
  rw [piFun_of_mem hCH htb]
  intro hW
  apply htW
  refine (mem_WC_iff z ⟨t, htC⟩).2 ?_
  have := cenToBar_cenMk H hCH ⟨t, htC⟩
  exact this ▸ hW

theorem ncard_le_seven (hS2 : IsPGroup 2 ↥S) (hSC : S ≤ Cen z) (hCH : Cen z ≤ H) (hz2 : orderOf z = 2)
    (hcard : Nat.card {u : G // u ∈ S ∧ u ∈ WC z ∧ orderOf u = 2 ∧ IsConj z u} = 7) :
    {u : HBar H | u ∈ barIn H S ∧ u * u = 1 ∧ u ≠ 1 ∧ piFun H hCH u ∈ WBar z ∧ ZCls H z u}.ncard
      ≤ 7 := by
  classical
  obtain ⟨Z, hZ⟩ : ∃ Z : Set G, Z = {s | s ∈ S ∧ s ∈ WC z ∧ orderOf s = 2 ∧ IsConj z s} :=
    ⟨_, rfl⟩
  have h7 : Z.ncard = 7 := by
    rw [← Nat.card_coe_set_eq, hZ]
    exact hcard
  let f : G → HBar H := fun g => if hg : g ∈ H then mkH H ⟨g, hg⟩ else 1
  have hsub : {u : HBar H | u ∈ barIn H S ∧ u * u = 1 ∧ u ≠ 1 ∧ piFun H hCH u ∈ WBar z ∧
      ZCls H z u} ⊆ f '' Z := by
    rintro u ⟨huS, hu2, hu1, huW, hcls⟩
    obtain ⟨h₀, hh₀S, rfl⟩ := Subgroup.mem_map.1 huS
    rw [Subgroup.mem_subgroupOf] at hh₀S
    have hgC : (h₀ : G) ∈ Cen z := hSC hh₀S
    have hne : (h₀ : G) ≠ 1 := by
      intro h1
      apply hu1
      have : h₀ = 1 := Subtype.ext h1
      show mkH H h₀ = 1
      rw [this, map_one]
    have hsqmem : h₀ * h₀ ∈ pPrimeCore 2 ↥H := by
      rw [← mkH_eq_one_iff, map_mul]
      exact hu2
    have hodd : Odd (orderOf (h₀ * h₀)) := odd_orderOf_of_mem_core H hsqmem
    obtain ⟨k, hk⟩ := hS2 ⟨(h₀ : G), hh₀S⟩
    have hk' : (h₀ : G) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have hpow : ((h₀ * h₀ : ↥H) : G) ^ (2 ^ k) = 1 := by
      calc ((h₀ * h₀ : ↥H) : G) ^ (2 ^ k) = ((h₀ : G) ^ (2 ^ k)) ^ 2 := by
            rw [Subgroup.coe_mul, ← pow_two, ← pow_mul, ← pow_mul, mul_comm]
        _ = 1 := by rw [hk']; simp
    have hdvd : orderOf (h₀ * h₀) ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hpow
    have hone : orderOf (h₀ * h₀) = 1 :=
      Nat.Coprime.eq_one_of_dvd ((Nat.coprime_two_right.2 hodd).pow_right k) hdvd
    have hsq1 : h₀ * h₀ = 1 := orderOf_eq_one_iff.1 hone
    have hsq1G : (h₀ : G) * (h₀ : G) = 1 := congrArg Subtype.val hsq1
    have hh₀2 : orderOf (h₀ : G) = 2 := orderOf_eq_prime (by rwa [pow_two]) hne
    have hh₀2H : orderOf h₀ = 2 := by rw [← hh₀2]; exact (Subgroup.orderOf_coe h₀).symm
    obtain ⟨s, hsu, hsconj⟩ := hcls
    have hs2 : orderOf (s : G) = 2 := (orderOf_eq_of_isConj' hsconj).symm.trans hz2
    have hs2H : orderOf s = 2 := by rw [← hs2]; exact (Subgroup.orderOf_coe s).symm
    obtain ⟨p, -, hp⟩ := exists_mem_core_conj H hs2H hh₀2H hsu.symm
    have hconj : IsConj (s : G) (h₀ : G) := by
      refine isConj_iff.2 ⟨((p⁻¹ : ↥H) : G), ?_⟩
      calc ((p⁻¹ : ↥H) : G) * (s : G) * ((p⁻¹ : ↥H) : G)⁻¹ = ((p⁻¹ * s * (p⁻¹)⁻¹ : ↥H) : G) := rfl
        _ = ((p⁻¹ * s * p : ↥H) : G) := by rw [inv_inv]
        _ = (h₀ : G) := by rw [← hp]
    refine ⟨(h₀ : G), ?_, ?_⟩
    · rw [hZ]
      refine ⟨hh₀S, ?_, hh₀2, hsconj.trans hconj⟩
      refine (mem_WC_iff z ⟨(h₀ : G), hgC⟩).2 ?_
      have hmemb : mkH H h₀ ∈ barIn H (Cen z) := cenMk_mem H hCH ⟨(h₀ : G), hgC⟩
      rw [piFun_of_mem hCH hmemb] at huW
      have := cenToBar_cenMk H hCH ⟨(h₀ : G), hgC⟩
      exact this ▸ huW
    · simp [f]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_image_le (f := f) (s := Z) (Set.toFinite _)
  omega

theorem conclA_of_center (hz2 : orderOf z = 2) (hzH : z ∈ H)
    (hcen : mkH H ⟨z, hzH⟩ ∈ center (HBar H)) : ConclA z H := by
  have hCen : centralizer ({mkH H ⟨z, hzH⟩} : Set (HBar H)) = barIn H (Cen z) :=
    centralizer_mk_eq H hz2 hzH
  intro h hh
  have hmem : mkH H ⟨h, hh⟩ ∈ centralizer ({mkH H ⟨z, hzH⟩} : Set (HBar H)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_center_iff.1 hcen _
  rw [hCen] at hmem
  obtain ⟨c', hc', hcc⟩ := Subgroup.mem_map.1 hmem
  rw [Subgroup.mem_subgroupOf] at hc'
  have hq : c'⁻¹ * ⟨h, hh⟩ ∈ pPrimeCore 2 ↥H := QuotientGroup.eq.1 hcc
  refine ⟨(c' : G), hc', ((c'⁻¹ * ⟨h, hh⟩ : ↥H) : G), Subgroup.mem_map.2 ⟨_, hq, rfl⟩, ?_⟩
  simp

end Glue

end CFSG.GH74.GLS.Stage2.Local.P34M12
