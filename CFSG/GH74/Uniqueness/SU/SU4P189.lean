module

public import CFSG.GH74.Uniqueness.SU.SU4P189a
public import CFSG.GH74.Uniqueness.SU.SU4L187
public import CFSG.GH74.Uniqueness.SU.SU5Facts

public section

namespace CFSG.GH74.Uniqueness.SU.SU4

open Subgroup CFSG.Blueprint

section Ident

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ZP_eq_Zc {H : Type} [Group H] (T : Sylow 2 H) :
    K.ZP H T = SU5.Zc (K.Psub H T) := by
  ext y
  unfold K.ZP SU5.Zc
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p.2, Subgroup.mem_centralizer_iff.mpr (fun q hq => ?_)⟩
    have := Subgroup.mem_center_iff.mp hp ⟨q, hq⟩
    exact congrArg Subtype.val this
  · rintro ⟨hy, hyc⟩
    refine ⟨⟨y, hy⟩, Subgroup.mem_center_iff.mpr (fun q => ?_), rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyc q q.2)

omit [Finite G] in
theorem Conf18H.x_mem_S {S : Sylow 2 G} {M V : Subgroup G} {x z : G} (hc : Conf18H S M V x z) :
    x ∈ (S : Subgroup G) := by
  obtain ⟨K', -, -, hK, -, -⟩ := hc.K_ex
  have : x ∈ zpowers x ⊔ K' := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  rw [hK] at this
  exact (Subgroup.mem_inf.mp this).2

theorem concl189_of_J2 {S : Sylow 2 G} {U M V : Subgroup G} {x z : G} (h : Hyp184Core S U M)
    (hc : Conf18H S M V x z) (T : Sylow 2 (Mbar M))
    (hT : (T : Subgroup (Mbar M)) = barImage M S)
    (hxb2 : orderOf (xbar M x hc.x_mem) = 2)
    (hrk2 : Open.pRank 2 (centralizer ({xbar M x hc.x_mem} : Set (Mbar M))) = 2)
    (hJ : K.J2Structure (Mbar M) T)
    (hcase : (LieModel ↥(generalizedFitting (Mbar M)) .PSL 3 2 2 ∧
        GLS.oPrimeResidual 2 (Mbar M) =
          generalizedFitting (Mbar M) ⊔ zpowers (xbar M x hc.x_mem) ∧
        9 ∣ Nat.card ↥(centralizer ({xbar M x hc.x_mem} : Set (Mbar M)) ⊓
          generalizedFitting (Mbar M))) ∨
      K.Psub (Mbar M) T = generalizedFitting (Mbar M)) :
    Concl189 S U M x hc.x_mem := by
  have hSM : (S : Subgroup G) ≤ M := h.S_le
  have hSp : IsPGroup 2 (S : Subgroup G) := S.isPGroup'
  obtain ⟨hSJ2, hPL, E, hE⟩ := hJ
  set Pb : Subgroup (Mbar M) := K.Psub (Mbar M) T with hPb
  have hPleT : Pb ≤ (T : Subgroup (Mbar M)) := inf_le_left
  have hxS : x ∈ (S : Subgroup G) := hc.x_mem_S
  set xb := xbar M x hc.x_mem with hxbdef
  have hxbS : xb ∈ (T : Subgroup (Mbar M)) := by
    rw [hT]; exact (mem_barImage M).mpr ⟨⟨x, hc.x_mem⟩, hxS, rfl⟩
  have hxb2' : xb ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one xb
    rwa [hxb2] at h1
  have hxb1 : xb ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hxb2
    omega
  have hxbP : xb ∉ Pb := by
    intro hxP
    obtain ⟨A, B, hAB⟩ := hPL.facts
    rcases hAB.invol xb hxP hxb1 hxb2' with hA | hB
    · have hle : A ≤ centralizer ({xb} : Set (Mbar M)) := fun a ha =>
        Subgroup.mem_centralizer_singleton_iff.mpr
          ((SU1.isElemAbelian_iff.mp hAB.A_E.1).1 a ha xb hA)
      have := SU1.le_pRank (p := 2) (by norm_num) hle hAB.A_E.1 hAB.A_E.2
      omega
    · have hle : B ≤ centralizer ({xb} : Set (Mbar M)) := fun a ha =>
        Subgroup.mem_centralizer_singleton_iff.mpr
          ((SU1.isElemAbelian_iff.mp hAB.B_E.1).1 a ha xb hB)
      have := SU1.le_pRank (p := 2) (by norm_num) hle hAB.B_E.1 hAB.B_E.2
      omega
  have hemb := SU5.J2Emb.of_types hSJ2 hPleT hPL hxbS hxbP hxb2'
  obtain ⟨zh, hzh⟩ := hemb.exists_zgen
  have hfacts := hemb.facts hzh
  have hUS : U ≤ (S : Subgroup G) := h.four.1
  have hUM : U ≤ M := hUS.trans hSM
  have hUp : IsPGroup 2 U := IsPGroup.of_card h.four.2.2
  obtain ⟨hUel, hUcard⟩ := isElemAbelian_barImage M hUp hUM h.four.2.1
  have hUT : barImage M U ≤ (T : Subgroup (Mbar M)) := by
    rw [hT]
    intro y hy
    obtain ⟨m, hmU, rfl⟩ := (mem_barImage M).mp hy
    exact (mem_barImage M).mpr ⟨m, hUS hmU, rfl⟩
  have hUn : ∀ s ∈ (T : Subgroup (Mbar M)), ∀ n ∈ barImage M U,
      s * n * s⁻¹ ∈ barImage M U := by
    intro sb hsb nb hnb
    rw [hT] at hsb
    obtain ⟨s, hsS, rfl⟩ := (mem_barImage M).mp hsb
    obtain ⟨u, huU, rfl⟩ := (mem_barImage M).mp hnb
    refine (mem_barImage M).mpr ⟨s * u * s⁻¹, ?_, by simp [map_mul]⟩
    exact SU1.conj_mem_of_le_normalizer h.normal _ hsS _ huU
  have hZcPb : barImage M U = SU5.Zc Pb :=
    hfacts.U_unique (barImage M U) hUT hUn ⟨hUel, hUcard.trans h.four.2.2⟩
  have hZ4 : Nat.card (barImage M U) = 4 := by rw [hUcard, h.four.2.2]; norm_num
  have hcentPb : ∀ sb ∈ (T : Subgroup (Mbar M)),
      (∀ ub ∈ barImage M U, sb * ub = ub * sb) ↔ sb ∈ Pb := by
    intro sb hsb
    constructor
    · intro hcomm
      by_contra hsbP
      have hxs : xb * sb ∈ Pb := (hfacts.S_cover sb hsb).resolve_left hsbP
      have hxcomm : ∀ ub ∈ barImage M U, xb * ub = ub * xb := by
        intro ub hub
        have hubZ := hZcPb ▸ hub
        have h1 : Commute (xb * sb) ub :=
          ((SU5.mem_Zc.mp hubZ).2 (xb * sb) hxs).symm
        have h2 : Commute sb ub := hcomm ub hub
        have h3 : Commute xb ub := by simpa using Commute.mul_left h1 h2.inv_left
        exact h3
      have hzs := hfacts.Q
      have hUz : barImage M U ≤ zpowers zh := by
        intro ub hub
        have hubZ := hZcPb ▸ hub
        obtain ⟨hubP, hubc⟩ := SU5.mem_Zc.mp hubZ
        have hmem : ub ∈ Pb ⊓ centralizer ({xb} : Set (Mbar M)) :=
          Subgroup.mem_inf.mpr ⟨hubP, Subgroup.mem_centralizer_singleton_iff.mpr
            (hxcomm ub hub).symm⟩
        have := (hzs.2.2.1 ub hmem).mp (fun q' hq' => hubc q' (Subgroup.mem_inf.mp hq').1)
        rcases this with h0 | h0
        · rw [h0]; exact one_mem _
        · rw [h0]; exact Subgroup.mem_zpowers zh
      have hcardle := Subgroup.card_le_of_le hUz
      have hord : Nat.card (zpowers zh) ≤ 2 := by
        rw [Nat.card_zpowers]
        exact Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one hfacts.z_sq)
      omega
    · intro hsbP ub hub
      have hubZ := hZcPb ▸ hub
      exact ((SU5.mem_Zc.mp hubZ).2 sb hsbP).symm
  have hTP : barImage M (Tsub S U) = Pb := by
    ext y
    constructor
    · intro hy
      obtain ⟨t, htT, rfl⟩ := (mem_barImage M).mp hy
      have htS : (t : G) ∈ (S : Subgroup G) := (Subgroup.mem_inf.mp htT).2
      have htU : (t : G) ∈ centralizer (U : Set G) := (Subgroup.mem_inf.mp htT).1
      refine (hcentPb _ (by rw [hT]; exact (mem_barImage M).mpr ⟨t, htS, rfl⟩)).mp ?_
      intro ub hub
      obtain ⟨u, huU, rfl⟩ := (mem_barImage M).mp hub
      have := Subgroup.mem_centralizer_iff.mp htU u huU
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext this.symm
    · intro hy
      have hyT : y ∈ (T : Subgroup (Mbar M)) := hPleT hy
      have hyT' := hyT
      rw [hT] at hyT'
      obtain ⟨s, hsS, rfl⟩ := (mem_barImage M).mp hyT'
      have hcomm := (hcentPb _ hyT).mpr hy
      refine (mem_barImage M).mpr ⟨s, Subgroup.mem_inf.mpr ⟨?_, hsS⟩, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro u huU
      have h1 := hcomm (proj M ⟨u, hUM huU⟩) ((mem_barImage M).mpr ⟨⟨u, hUM huU⟩, huU, rfl⟩)
      have h2 : proj M (s * ⟨u, hUM huU⟩) = proj M (⟨u, hUM huU⟩ * s) := by
        rw [map_mul, map_mul]; exact h1
      have := eq_of_proj_eq_of_isPGroup M hSp hSM (a := s * ⟨u, hUM huU⟩)
        (b := ⟨u, hUM huU⟩ * s) (S.mul_mem hsS (hUS huU)) (S.mul_mem (hUS huU) hsS) h2
      exact (congrArg Subtype.val this).symm
  have hTsubS : Tsub S U ≤ (S : Subgroup G) := inf_le_right
  have hTsubp : IsPGroup 2 (Tsub S U) := hSp.to_le hTsubS
  have typeT : SU5.IsL34Type ↥(Tsub S U) := by
    obtain ⟨eP⟩ := hPL
    exact ⟨(mulEquivBarImage M hTsubp (hTsubS.trans hSM)).trans
      ((MulEquiv.subgroupCongr hTP).trans eP)⟩
  have typeS : SU5.IsJ2Type ↥(S : Subgroup G) := by
    obtain ⟨eS⟩ := hSJ2
    exact ⟨(mulEquivBarImage M hSp hSM).trans ((MulEquiv.subgroupCongr hT.symm).trans eS)⟩
  have hUZ : barImage M U = K.ZP (Mbar M) T := hZcPb.trans (ZP_eq_Zc T).symm
  obtain ⟨hN, hEP, hE3, E₀, hE₀E, hE₀3, hEsup, hEinf, hcomm', hfpf, hcard'⟩ := hE
  refine ⟨hcase.imp id (fun h' => hTP.trans h'), ?_, typeT, typeS, ?_⟩
  · rw [hTP]
    exact inf_le_right
  · refine ⟨E, E₀, ?_⟩
    rw [hTP, hUZ]
    exact ⟨hN, hEP, hE₀E, hE₀3, hEsup, hEinf, hcomm', hfpf, hcard'⟩

end Ident

section Final

variable {G : Type} [Group G] [Finite G]

theorem prop189 (hKI1 : K.KI1) (hKI2 : K.KI2) : Prop189Stmt := by
  intro G _ _ S U M V x z hc h
  have hSM : (S : Subgroup G) ≤ M := h.S_le
  have hSyl : IsSylowIn M (S : Subgroup G) := h.isSylowIn_M
  have hSp : IsPGroup 2 (S : Subgroup G) := S.isPGroup'
  have hxM : x ∈ M := hc.x_mem
  have hxS : x ∈ (S : Subgroup G) := hc.x_mem_S
  have hzS : z ∈ (S : Subgroup G) := hc.z_mem_S
  have hx2 : x * x = 1 := by rw [← pow_two]; exact hc.hx ▸ pow_orderOf_eq_one x
  have hGH : SU0.GHGroup (Mbar M) :=
    SU0.GHGroup.of_kgh_quotient h.kgh h.maximal.1 (pPrimeCore 2 ↥M)
  have hO : pPrimeCore 2 (Mbar M) = ⊥ := GLS.pPrimeCore_quotient_eq_bot (↥M)
  obtain ⟨T, hT⟩ := exists_sylow_barImage M hSyl
  have hrank : 3 ≤ Open.twoRank (Mbar M) := by
    unfold Open.twoRank
    have h1 := SU1.pRank_mono (p := 2) (by norm_num) (le_top : barImage M S ≤ ⊤)
    rw [pRank_barImage M hSM] at h1
    exact h.rank.trans h1
  have hmov : ∃ u ∈ M, u⁻¹ * z * u ∈ (S : Subgroup G) ∧ u⁻¹ * z * u ≠ z := by
    by_contra hcon
    push Not at hcon
    exact lemma188 G S U M V x z h hc ⟨hzS, fun u hu hu' => hcon u hu hu'⟩
  have hcenter : center (Mbar M) = ⊥ :=
    center_Mbar_eq_bot M hSyl hzS hc.z_unique hmov
  set xb := xbar M x hxM with hxbdef
  have hxbT : xb ∈ (T : Subgroup (Mbar M)) := by
    rw [hT]; exact (mem_barImage M).mpr ⟨⟨x, hxM⟩, hxS, rfl⟩
  have hxb1 : xb ≠ 1 := by
    intro h1
    have h0 : proj M ⟨x, hxM⟩ = proj M 1 := by rw [map_one]; exact h1
    have h2 := eq_of_proj_eq_of_isPGroup M hSp hSM (a := ⟨x, hxM⟩) (b := 1) hxS S.one_mem h0
    have h3 : x = 1 := congrArg Subtype.val h2
    have := hc.hx
    rw [h3, orderOf_one] at this
    omega
  have hxb2 : orderOf xb = 2 := by
    refine orderOf_eq_prime ?_ hxb1
    show (proj M ⟨x, hxM⟩) ^ 2 = 1
    rw [← map_pow]
    have : (⟨x, hxM⟩ : ↥M) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, pow_two]; exact hx2)
    rw [this, map_one]
  obtain ⟨K', hK1, hK2, hK3, hK4, hK5⟩ := hc.K_ex
  have hV4 : IsFour M V := hc.iso.isFour
  have hVgen : V = zpowers x ⊔ zpowers z := by rw [hc.gen, closure_pair_eq]
  have hrk2 : Open.pRank 2 (centralizer ({xb} : Set (Mbar M))) = 2 :=
    pRank_centralizer_xbar M hxM hx2 hc.syl_c hV4 hVgen hK1 hK3 hK4 hK5
  rcases hKI1 (Mbar M) hGH hO hrank hcenter T xb hxbT hxb2 hrk2 with
    ⟨⟨hA1, hA2, hA3⟩, hJ⟩ | ⟨p, f, hp, hp2, hL, hPGL⟩ | ⟨hFle, hJ⟩
  · exact concl189_of_J2 h.toHyp184Core hc T hT hxb2 hrk2 hJ (Or.inl ⟨hA2, hA1, hA3⟩)
  · exact (caseB_false M hKI2 h hp hp2 hL hxb2 hPGL).elim
  · exact concl189_of_J2 h.toHyp184Core hc T hT hxb2 hrk2 hJ (Or.inr (inf_eq_right.mpr hFle))

end Final

end CFSG.GH74.Uniqueness.SU.SU4
