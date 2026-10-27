module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P310
public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelBase
public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelLeaves
public import CFSG.GH74.GLS.C3.Layer1.Thm1GlueJ

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Thm1

theorem b_thm1_L310_V0_rel_proved
    (h2hb : IVK.IVK_1_2h_b) (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem)
    (hP31s : B_thm1_P31s_rel) (hP31c : B_thm1_P31c_rel) (hL32 : B_thm1_L32'_rel) :
    B_thm1_L310_V0_rel := by
  intro G _ _ hG hNo x y K T V f z cfg hsup hPV h5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJc, hJn, r, hrodd, hr5, hI, hKshape, -, -⟩ := hL32 G hG hNo x y K f cfg.fmax h5
  have hshape := Thm1.kBar_model_of_U2 hG h102 hL34 cfg.hu2
  obtain ⟨hKN, -, -, hTdata⟩ := hP31s G hG hNo x y K cfg.hu2 hshape h5
  obtain ⟨-, ⟨n, hn3, hdih⟩, z₁, hz₁P, hz₁2, hz₁c, hz₁u⟩ := hTdata T cfg.setup
  have hKC : K ≤ centralizer ({x} : Set G) := cfg.hKx
  have hCN : centralizer ({x} : Set G) ≤ normalizer (K : Set G) := fun c hc =>
    U1a.mem_normalizer_of_norm hKN hc
  have hPK : IsSylowOf 2 (T ⊓ K) K := cfg.setup.sylowT.inf_of_le_normalizer hKC hCN
  have hfP : ∀ p ∈ T ⊓ K, f * p = p * f := cfg.mem.2.2.1
  have hzP : z ∈ T ⊓ K := cfg.z_mem.1
  have hz2 : orderOf z = 2 := cfg.z_mem.2.1
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  have hzu : ∀ w ∈ T ⊓ K, (∀ p ∈ T ⊓ K, w * p = p * w) → w = 1 ∨ w = z := by
    have hzz₁ : z = z₁ := by
      rcases hz₁u z hzP (fun p hp => (cfg.z_mem.2.2 p hp.1).symm) with h | h
      · exact absurd h hz1
      · exact h
    intro w hw hwc
    rcases hz₁u w hw hwc with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hzz₁.symm)
  have hfC : f ∈ centralizer ({x} : Set G) := cfg.setup.sylowT.le cfg.mem.1
  have hfout : Back.actHom hKN ⟨f, hfC⟩ ∉ innAut (kBar K) := by
    obtain ⟨hfN, hF⟩ := thm1_FmemberF_of_rel h2hb G hG hNo x y K cfg.hu2 hshape hKN T cfg.setup f cfg.mem h5
    exact not_mem_innAut_of_isFAutL2A7 hF
  obtain ⟨hcen, -⟩ := kBar_autData_rel h2hb hNo cfg.hu2 hshape h5
  have hAutC : AutLevelC (kBar K) := autLevelC_of_shape hshape
  have hxS : IsSylowOf 2 (zpowers x) (CxK x K) := hP31c G hG hNo x y K cfg.hu2 h5
  have hVC : V ≤ centralizer ({f} : Set G) := cfg.sylowV.le
  have hV2 : IsPGroup 2 ↥V := cfg.sylowV.isPGroup
  obtain ⟨eIJ⟩ := kBar_pumpJ_equiv hsup
  have hJmodel : HasL2Model (kBar (pumpJ K f)) (fun q => q = r) :=
    TwoThin.hasL2Model_of_mulEquiv eIJ hI
  obtain ⟨F₀, _, _, hF₀card, hF₀, ⟨e₀⟩⟩ := exists_l2_model_card hrodd hr5 hJmodel
  have hcenJ : Function.Injective
      (MulAut.conj : kBar (pumpJ K f) →* MulAut (kBar (pumpJ K f))) :=
    IVK.conj_injective_of_L2 e₀
  have hzI : z ∈ layerI K f := z_mem_layerI hPK hfP hI hrodd hzu
  have hzD : z ∉ secD K f V := z_not_mem_secD hsup hJn hcenJ hzI hz2
  have hPVle : T ⊓ K ≤ V := fun p hp => cfg.CTf_le p hp.1 (hfP p hp)
  have hDV : secD K f V ≤ V := inf_le_left
  have hDeq := secD_eq_inf_cmk hsup hVC
  have hDn : ∀ v ∈ V, ∀ d ∈ secD K f V, v * d * v⁻¹ ∈ secD K f V := by
    intro v hv d hd
    rw [hDeq] at hd ⊢
    exact ⟨V.mul_mem (V.mul_mem hv hd.1) (V.inv_mem hv), P34Real.CMK_conj hJn (hVC hv) hd.2⟩
  have hPD : (T ⊓ K) ⊓ secD K f V = ⊥ := inf_eq_bot_of_normal hV2 hPVle hPV hDn hzD hzu
  have hcomm := commute_of_inf_eq_bot hPVle hDV hPV hDn hPD
  have hxD : x ∈ secD K f V := cfg.x_mem_secD hsup hJn
  have hfD : f ∈ secD K f V := cfg.f_mem_secD hsup hJn
  have hxf : x * f = f * x := cfg.hxf
  have hne : x ≠ f := Ne.symm cfg.mem.2.2.2.1
  have hVf : ∀ v ∈ V, v * f = f * v := fun v hv => mem_centralizer_singleton_iff.1 (hVC hv)
  have hCx := cent_le_of_secD hKC hKN hPK hcen hAutC ⟨n, hn3, hdih⟩ hfC cfg.hf2 hfP hfout hxS hV2
    hVf hDV hxD hfD hPD hcomm
  have hxsq : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [cfg.hx2, sq] at this
  have hfsq : f * f = 1 := by
    have := pow_orderOf_eq_one f
    rwa [cfg.hf2, sq] at this
  have hx1 : x ≠ 1 := fun h => by have := cfg.hx2; rw [h, orderOf_one] at this; omega
  have hf1 : f ≠ 1 := fun h => by have := cfg.hf2; rw [h, orderOf_one] at this; omega
  have hD2 : IsPGroup 2 ↥(secD K f V) := hV2.to_le hDV
  obtain ⟨hDmax, hDshape⟩ := secD_shape hD2 hDn hxD cfg.hx2 hfD cfg.hf2 hxf hne hCx
    (fun d hd => hVf d (hDV hd))
  have hVtop : ¬ 2 ∣ V.index := by
    have := (isSylowOf_iff.1 cfg.sylowW).2.2
    rwa [Subgroup.relIndex_top_right] at this
  have hSV : ((hV2.toSylow hVtop : Sylow 2 G) : Subgroup G) = V := IsPGroup.toSylow_coe hV2 hVtop
  have hCMKn : centralizer ({f} : Set G) ≤
      normalizer ((CMK (centralizer ({f} : Set G)) (pumpJ K f) : Subgroup G) : Set G) := fun g hg =>
    Thm1L3.mem_normalizer_of_conj_le (fun a ha => P34Real.CMK_conj hJn hg ha)
  have hDsyl : IsSylowOf 2 (secD K f V) (CMK (centralizer ({f} : Set G)) (pumpJ K f)) := by
    rw [hDeq]
    exact cfg.sylowV.inf_of_le_normalizer inf_le_left hCMKn
  have hyp : Bk.Prop34HypN G f (pumpJ K f) :=
    { simple := hG.kproper.1
      nonab := hG.kproper.2.1
      central := ⟨cfg.hf2, hV2.toSylow hVtop, by rw [hSV]; exact cfg.f_mem_V,
        fun s hs => hVf s (by rw [hSV] at hs; exact hs)⟩
      comp := hJc
      normal := hJn
      shape := Or.inl (Back.hasL2Model_mono (fun q hq => by subst hq; exact hrodd) hJmodel)
      sylowQ := ⟨secD K f V, hDsyl, Or.inr hDmax⟩ }
  have hinvE := involution_act_mem_innDiag hF₀.1 e₀ hyp hJn hVC
  let ρ : ↥V →* MulAut (kBar (pumpJ K f)) :=
    (Back.actHom hJn).comp (Subgroup.inclusion hVC)
  have hρker : ∀ w : ↥V, ρ w = 1 ↔ (w : G) ∈ secD K f V := by
    intro w
    have h1 : ρ w = Back.actHom hJn ⟨(w : G), hVC w.2⟩ := rfl
    rw [h1, ← MonoidHom.mem_ker, Back.actHom_ker hJn, Subgroup.mem_subgroupOf, hDeq]
    exact ⟨fun h => ⟨w.2, h⟩, fun h => h.2⟩
  set E := innDiagSub e₀ with hEdef
  set P' : Subgroup ↥V := (T ⊓ K).subgroupOf V with hP'
  have hker' : ∀ p ∈ P', ρ p = 1 → p = 1 := by
    intro p hp hρp
    have hpP : (p : G) ∈ T ⊓ K := hp
    have hpD : (p : G) ∈ secD K f V := (hρker p).1 hρp
    have : (p : G) ∈ (T ⊓ K) ⊓ secD K f V := ⟨hpP, hpD⟩
    rw [hPD, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hPE : ∀ p ∈ P', ρ p ∈ E := by
    intro p hp
    obtain ⟨u, hu, w, hw, huu, hww, hpuw⟩ := exists_mul_involutions_of_dihedral hdih (p : G) hp
    have hpeq : p = ⟨u, hPVle hu⟩ * ⟨w, hPVle hw⟩ := Subtype.ext hpuw
    rw [hpeq, map_mul]
    exact E.mul_mem (hinvE u (hPVle hu) huu) (hinvE w (hPVle hw) hww)
  have hEcard : Nat.card E = r * (r ^ 2 - 1) := by
    rw [hEdef, IVK.card_innDiagSub e₀ hF₀, Thm1L34.card_kBar_of_hasL2Model hJmodel]
    obtain ⟨k, rfl⟩ := hrodd
    rw [PumpClass.ordA_one_odd]
    have h2 : (2 * k + 1) ^ 2 - 1 = 4 * k * (k + 1) := by
      have : (2 * k + 1) ^ 2 = 4 * k * (k + 1) + 1 := by ring
      omega
    rw [h2]; ring
  have hdvdK : r ^ 2 - 1 ∣ Nat.card (kBar K) := by
    rcases hKshape with hK2 | ⟨hr5', hKA7⟩
    · rw [Thm1L34.card_kBar_of_hasL2Model hK2]
      obtain ⟨k, hk⟩ := hrodd
      have hr2 : r ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by rw [hk]; ring
      rw [hr2, PumpClass.ordA_one_odd, Nat.add_sub_cancel]
      exact ⟨(2 * k * (k + 1) + 1) * (2 * (2 * k * (k + 1)) + 1), by ring⟩
    · rw [Thm1L34.card_kBar_of_alt7 hKA7, hr5']
      norm_num
  have hcard : ∀ j : ℕ, 2 ^ j ∣ Nat.card E → 2 ^ j ≤ Nat.card P' := by
    intro j hj
    rw [hEcard] at hj
    have h1 := two_pow_le_card_of_dvd hPK hrodd hdvdK hj
    have h2 : Nat.card P' = Nat.card ↥(T ⊓ K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPVle).toEquiv
    rw [h2]
    exact h1
  have himg := image_inf_eq_image hV2 ρ E P' hker' hPE hcard
  have hPDmem : ∀ w : ↥V, ρ w ∈ E → (w : G) ∈ (T ⊓ K) ⊔ secD K f V := by
    intro w hw
    obtain ⟨p, hp, hpw⟩ := himg w hw
    have hq : ρ (p⁻¹ * w) = 1 := by rw [map_mul, map_inv, hpw]; group
    have hqD : ((p⁻¹ * w : ↥V) : G) ∈ secD K f V := (hρker _).1 hq
    have hpP : (p : G) ∈ T ⊓ K := hp
    have hw' : (w : G) = (p : G) * ((p⁻¹ * w : ↥V) : G) := by simp
    rw [hw']
    exact Subgroup.mul_mem_sup hpP hqD
  have hinv : ∀ u ∈ V, u * u = 1 → u ∈ (T ⊓ K) ⊔ secD K f V := fun u hu huu =>
    hPDmem ⟨u, hu⟩ (hinvE u hu huu)
  have hcyc : ∃ b ∈ V, ∀ v ∈ V, ∃ k : ℤ, (b ^ k) ⁻¹ * v ∈ (T ⊓ K) ⊔ secD K f V := by
    have := IVK.ringAut_isCyclic F₀
    obtain ⟨b, hb⟩ := exists_gen_of_cyclic ((fieldProj e₀).comp ρ)
    refine ⟨(b : G), b.2, fun v hv => ?_⟩
    obtain ⟨k, hk⟩ := hb ⟨v, hv⟩
    refine ⟨k, ?_⟩
    have hmem : ρ ((b ^ k)⁻¹ * ⟨v, hv⟩) ∈ E := by
      rw [hEdef, mem_innDiagSub_iff]
      exact hk
    have := hPDmem _ hmem
    simpa using this
  rcases hDshape with ⟨-, hDeq4⟩ | ⟨a, haD, hVa, h4, hxa, hDx, hfa⟩
  · exact Thm1P310.exists_V0_of_four hDV hPVle hPV hDn hPD hcomm hDeq4 hxsq hfsq hxf hx1 hne hVf
      hinv hcyc
  · exact Thm1P310.exists_V0_of_cyclic_maximal hDV hPVle hPD hcomm haD hVa h4 hxD hDx hfa hfsq hf1
      (fun d hd hdx => mul_self_eq_one_of_mem_klein hxsq hfsq hxf (hCx d hd hdx)) hinv

end CFSG.GH74.GLS
