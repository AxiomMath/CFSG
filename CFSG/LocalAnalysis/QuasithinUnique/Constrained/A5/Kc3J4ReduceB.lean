module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4D4Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Inv
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Parts
public import CFSG.Sporadic.J4.QT2LocHBasic

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2

theorem card_Omega_eq_b
    (hF : J4Basic)
    {z : J} (hz : z ∈ Zl) : (Omega z).ncard = 77 := by
  have hM := hF.mat
  have hKM := card_eq_orbit_mul_inf (Subgroup.centralizer ({z} : Set J)) Hj w₀
    (fun g => ⟨hF.stab g, smul_root_of_mem_Hj hM⟩)
  have hHM := card_eq_card_mul_centralizer Hj z Zl hz
    (fun h hh x hx => (Zl_conj hM h hh).1 x hx) (fun x hx => Zl_trans hM z hz x hx)
  rw [hF.cardHj, card_Zl hM] at hHM
  have hMval : Nat.card ↥(Subgroup.centralizer ({z} : Set J) ⊓ Hj) = 283115520 := by omega
  have hC := card_centralizer_of_mem_Zl_b hF hz
  have horb : Nat.card ↥(MulAction.orbit (Subgroup.centralizer ({z} : Set J)) w₀) = 77 := by
    rw [hC, hMval] at hKM
    omega
  have hsub : MulAction.orbit (Subgroup.centralizer ({z} : Set J)) w₀ ⊆ Omega z := by
    refine orbit_subset_of _ w₀ _ fun q hq => ?_
    refine ⟨q, rfl, ?_⟩
    have hc := comm_of_mem_centralizer hq
    have : q⁻¹ * z * q = z := by
      rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]
    exact mem_Eg_of_mem_Zl hz
  have h1 : 77 ≤ (Omega z).ncard := by
    rw [← horb, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  exact le_antisymm (card_Omega_le_b hF hz) h1

theorem card_Omega_eq_of_isConj_b
    (hF : J4Basic)
    {u : J} (hu : IsConj (eta uJ 11 3) u) : (Omega u).ncard = 77 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hu
  have h3 : eta uJ 11 3 ∈ Zl := mem_Zl.2 ⟨3, three_mem_zMasks, rfl⟩
  have e : Omega u = (fun p : Row => c • p) '' Omega (eta uJ 11 3) := by
    ext w
    constructor
    · intro hw
      refine ⟨c⁻¹ • w, ?_, smul_inv_smul c w⟩
      have := (RIn_conj c (c⁻¹ • w) (eta uJ 11 3)).1
      rw [smul_inv_smul, hc] at this
      exact this hw
    · rintro ⟨p, hp, rfl⟩
      have := (RIn_conj c p (eta uJ 11 3)).2 hp
      rw [hc] at this
      exact this
  rw [e, Set.ncard_image_of_injective _ (MulAction.injective c), card_Omega_eq_b hF h3]

theorem exists_fixed_point_Omega_b
    (hF : J4Basic)
    {u : J} (hu : IsConj (eta uJ 11 3) u) (V : Subgroup J)
    (hV : IsPGroup 2 V) (hcomm : ∀ v ∈ V, v * u = u * v) :
    ∃ p, RIn p u ∧ ∀ v ∈ V, v • p = p := by
  have hmap : ∀ v ∈ V, ∀ p ∈ Omega u, v • p ∈ Omega u := by
    intro v hv p hp
    have h := (RIn_conj v p u).2 hp
    rwa [show v * u * v⁻¹ = u by rw [hcomm v hv]; group] at h
  have hodd : ¬ 2 ∣ (Omega u).ncard := by
    rw [card_Omega_eq_of_isConj_b hF hu]
    norm_num
  obtain ⟨p, hp, hfix⟩ := exists_fixed_of_pgroup_odd V hV (Omega u) (Set.toFinite _) hmap hodd
  exact ⟨p, hp, hfix⟩

theorem exists_conj_fiveElt_b
    (hF : J4Basic)
    {y : ↥J} (hy : orderOf y = 5) : ∃ g : ↥J, g * y * g⁻¹ = fiveElt := by
  obtain ⟨n, hn⟩ := exists_conj_fiveElt_sq hF.mat
  exact exists_conj_five (Dec2.five_sq_not_dvd_card_J_b hF) (orderOf_fiveElt hF.mat) hn hy

theorem fpfV_exists_fpfX0_b
    (hF : J4Basic)
    {V : Subgroup ↥J} (hV : FpfV V) : ∃ c : ↥J, FpfX0 (V.map (cm c)) := by
  obtain ⟨hc, hab, hsq, y, hy, hy5, hfpf⟩ := hV
  obtain ⟨g, hg⟩ := exists_conj_fiveElt_b hF hy5
  have h : FpfAt V y := ⟨hc, hab, hsq, hy, hy5, hfpf⟩
  have h1 := fpfAt_map_cm g h
  rw [cm_apply, hg] at h1
  exact ⟨g, h1⟩

theorem exists_pt_fixed_inE_b
    (hF : J4Basic)
    {V : Subgroup ↥J} (hc : Nat.card V = 16)
    (hab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hsq : ∀ a ∈ V, a * a = 1) :
    ∃ p : Row, p ∈ Pts ∧ (∀ u ∈ V, u • p = p) ∧ ∃ v ∈ V, v ≠ 1 ∧ RIn p v := by
  obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : V = ⊥ := (Subgroup.eq_bot_iff_forall V).2 hcon
    rw [hbot] at hc
    simp at hc
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (p := 2) (n := 4) (by rw [hc]; norm_num)
  rcases inv_conj_root_b hF (hsq v hv) hv1 with h1 | h3
  · obtain ⟨c, hcv⟩ := isConj_iff.1 h1
    have e : c⁻¹ * v * c = eta uJ 11 1 := by rw [← hcv]; group
    refine ⟨c • w₀, ⟨c, rfl⟩, ?_, v, hv, hv1, c, rfl, ?_⟩
    · intro u hu
      have hcomm : (c⁻¹ * u * c) * eta uJ 11 1 = eta uJ 11 1 * (c⁻¹ * u * c) := by
        have h := hab u hu v hv
        rw [← hcv] at h
        calc (c⁻¹ * u * c) * eta uJ 11 1 = c⁻¹ * (u * (c * eta uJ 11 1 * c⁻¹)) * c := by group
          _ = c⁻¹ * ((c * eta uJ 11 1 * c⁻¹) * u) * c := by rw [h]
          _ = eta uJ 11 1 * (c⁻¹ * u * c) := by group
      have hfix := smul_root_of_mem_Hj hF.mat (centralizer_eta_one_le_Hj_b hF hcomm)
      calc u • (c • w₀) = (u * c) • w₀ := (mul_smul u c w₀).symm
        _ = (c * (c⁻¹ * u * c)) • w₀ := by rw [show u * c = c * (c⁻¹ * u * c) by group]
        _ = c • ((c⁻¹ * u * c) • w₀) := mul_smul _ _ _
        _ = c • w₀ := by rw [hfix]
    · rw [e]
      exact eta_mem_Eg 11 le_rfl 1
  · obtain ⟨p, hp, hfix⟩ := exists_fixed_point_Omega_b hF h3 V hV2 (fun w hw => hab w hw v hv)
    have hpts : p ∈ Pts := by
      obtain ⟨g, hg, -⟩ := hp
      exact ⟨g, hg⟩
    exact ⟨p, hpts, hfix, v, hv, hv1, hp⟩

theorem noCommon_pentagon_x0_b
    (hF : J4Basic)
    {W : Subgroup ↥J} (hW : FpfX0 W) (hnc : ¬ HasCommonFixedPt W) :
    ∃ (p : Row) (v : ↥J), PentCand p v ∧ W = pentSub v := by
  obtain ⟨hc, hab, hsq, hx, hx5, hfpf⟩ := hW
  obtain ⟨p, hp, hfix, v, hv, hv1, hvp⟩ := exists_pt_fixed_inE_b hF hc hab hsq
  refine ⟨p, v, ⟨hp, hv1, hsq v hv, hvp, ?_, ?_⟩, ?_⟩
  · intro hxp
    exact hnc ((hasCommonFixedPt_iff_b hF.mat hF.stab W).2
      ⟨fiveElt, hx, hx5, hfpf, p, ⟨hp, hfix⟩, hxp⟩)
  · intro k
    have hxk : fiveElt ^ k ∈ Subgroup.normalizer (W : Set ↥J) := Subgroup.pow_mem _ hx k
    exact (smul_mem_omV hxk ⟨hp, hfix⟩).2 v hv
  · exact (fpfV_closure_pentagon hc hab hx hx5 hfpf hv hv1).symm

theorem noCommon_pentagon_b
    (hF : J4Basic)
    {V : Subgroup ↥J} (hV : FpfV V) (hnc : ¬ HasCommonFixedPt V) :
    ∃ (c : ↥J) (p : Row) (v : ↥J), PentCand p v ∧ V.map (cm c) = pentSub v ∧
      FpfX0 (pentSub v) ∧ ¬ HasCommonFixedPt (pentSub v) := by
  obtain ⟨c, hc⟩ := fpfV_exists_fpfX0_b hF hV
  have hnc' : ¬ HasCommonFixedPt (V.map (cm c)) := by
    intro h
    apply hnc
    have := hasCommonFixedPt_map_cm c⁻¹ h
    rwa [map_cm_inv_map_cm] at this
  obtain ⟨p, v, hpv, hW⟩ := noCommon_pentagon_x0_b hF hc hnc'
  refine ⟨c, p, v, hpv, hW, ?_, ?_⟩
  · rw [← hW]
    exact hc
  · rw [← hW]
    exact hnc'

theorem complete_of_pentagon_cover_b
    (hF : J4Basic)
    (L : List (Subgroup ↥J)) (cands : Set Row)
    (hcov : ∀ (p : Row) (v : ↥J), PentCand p v → ∃ k ∈ X0Sub, ∃ q ∈ cands, p = k • q)
    (hD4 : ∀ (q : Row) (v : ↥J), q ∈ cands → PentCand q v → FpfX0 (pentSub v) →
      ¬ HasCommonFixedPt (pentSub v) → ∃ V' ∈ L, ∃ g : ↥J, pentSub v = V'.map (cm g)) :
    ∀ V : Subgroup ↥J, FpfV V → ¬ HasCommonFixedPt V →
      ∃ V' ∈ L, ∃ g : ↥J, V = V'.map (cm g) := by
  intro V hV hnc
  obtain ⟨c, p, v, hpv, hVc, hF', hN⟩ := noCommon_pentagon_b hF hV hnc
  obtain ⟨k, hkX, q, hq, hpq⟩ := hcov p v hpv
  have hk : k * fiveElt = fiveElt * k :=
    (Subgroup.mem_centralizer_singleton_iff (G := ↥J) (g := fiveElt) (k := k)).1
      (X0Sub_le_centralizer hF.mat hkX)
  have hpv' := pentCand_conj hk hpq hpv
  have hv'k : k * (k⁻¹ * v * k) * k⁻¹ = v := by group
  have hsub : pentSub v = (pentSub (k⁻¹ * v * k)).map (cm k) := by
    rw [map_cm_pentSub hk, hv'k]
  have hF'' : FpfX0 (pentSub (k⁻¹ * v * k)) := by
    have h1 := fpfAt_map_cm k⁻¹ hF'
    rw [hsub, map_cm_inv_map_cm, cm_apply] at h1
    have e : k⁻¹ * fiveElt * k⁻¹⁻¹ = fiveElt := by
      rw [inv_inv]
      calc k⁻¹ * fiveElt * k = k⁻¹ * (fiveElt * k) := mul_assoc _ _ _
        _ = k⁻¹ * (k * fiveElt) := by rw [hk]
        _ = fiveElt := inv_mul_cancel_left k fiveElt
    rw [e] at h1
    exact h1
  have hN' : ¬ HasCommonFixedPt (pentSub (k⁻¹ * v * k)) := by
    intro h
    apply hN
    rw [hsub]
    exact hasCommonFixedPt_map_cm k h
  obtain ⟨V', hV', g, hg⟩ := hD4 q (k⁻¹ * v * k) hq hpv' hF'' hN'
  refine ⟨V', hV', c⁻¹ * k * g, ?_⟩
  calc V = (V.map (cm c)).map (cm c⁻¹) := (map_cm_inv_map_cm c V).symm
    _ = (pentSub v).map (cm c⁻¹) := by rw [hVc]
    _ = ((pentSub (k⁻¹ * v * k)).map (cm k)).map (cm c⁻¹) := by rw [hsub]
    _ = (((V'.map (cm g)).map (cm k)).map (cm c⁻¹)) := by rw [hg]
    _ = V'.map (cm (c⁻¹ * k * g)) := by rw [map_cm_map_cm, map_cm_map_cm]

theorem not_sq_dvd_card_J_b (hF : J4Basic) : ¬ 5 ^ 2 ∣ Nat.card ↥J :=
  Dec2.five_sq_not_dvd_card_J_b hF

theorem j4GlobalRad_of_verdict_b (hF : J4Basic) (h : J4VVerdict) : J4GlobalRad := by
  intro L hL hLp hnH hno
  have hcore : D5Core L := by
    rcases d5Core_or_central_of_d5Plus hL with hc | ⟨z, -, hz2, hzc⟩
    · exact hc
    · exact absurd ⟨z, hz2, hzc⟩ hno
  rcases h _ (fpfV_of_d5Core hcore) with hcr | hNo
  · obtain ⟨x, hxL, hx5⟩ : ∃ g ∈ L, orderOf g = 5 := by
      obtain ⟨V, Q, -, -, -, -, -, -, α, hα, -, -, -⟩ := hL
      exact exists_orderOf_five α hα
    have hxN : x ∈ Subgroup.normalizer ((pCoreOf 2 L : Subgroup ↥J) : Set ↥J) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hxL
    have hR := radV_of_classRad (not_sq_dvd_card_J_b hF) hcr hxN hx5
    exact ⟨hR.1, x, hxL, hx5, hR.2⟩
  · exfalso
    rcases hNo L hL hLp rfl with ⟨g, hg⟩ | ⟨y, hy2, hyc⟩
    · exact hnH g hg
    · exact hno ⟨y, hy2, hyc⟩

theorem j4HPart_b
    (hF : J4Basic) : J4HPart := by
  intro L hL hD hp
  rcases d5Plus_core_or_central hD hp with hcore | ⟨z, -, hz2, hzc⟩
  · obtain ⟨V, x, d, hVL, hxL, hdL, hcard, hab, hV2, hx5, hd2, hVx, hVd, hfpf, hxd, hfix, hgen⟩ :=
      d5Core_config hcore
    have hcfg : HCfg V x d :=
      ⟨fun v hv => hL (hVL hv), hL hxL, hL hdL, hcard, hab, hV2, hx5, hd2, hVx, hVd, hfpf, hxd,
        hfix⟩
    have hcon := hpart_core_b hF hcfg
    unfold HConcl at hcon
    obtain ⟨y, hyE, hy1, hxy, hdy, hVy⟩ := hcon
    refine ⟨y, ?_, hgen y hxy hdy hVy⟩
    obtain ⟨c, -, rfl⟩ := (mem_Eg_iff (elem_uJ hF.mat)).1 hyE
    have hsq : eta uJ 11 c ^ 2 = 1 := by
      rw [sq]
      exact eta_sq (elem_uJ hF.mat) c
    have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hsq hy1
  · exact ⟨z, hz2, hzc⟩

theorem j4BlockRad_of_globalRad_b
    (hF : J4Basic)
    (hG : J4GlobalRad) : J4BlockRad := by
  intro L hL hLp hno
  by_cases hconj : ∃ g : ↥J, L ≤ Hj.map (MulAut.conj g).toMonoidHom
  · obtain ⟨g, hg⟩ := hconj
    exact absurd (exists_involution_of_conj_le (Y := ↥J) Hj (j4HPart_b hF) hL hLp hg) hno
  · exact hG L hL hLp (fun g hg => hconj ⟨g, hg⟩) hno

theorem j4InvRadical_b
    (hF : J4Basic) :
    InvRadical ↥CFSG.Sporadic.J4.J :=
  fun y hy hne => j4_involution_radical_b hF y hy hne

theorem blockRadAbs_of_j4_b (hF : J4Basic)
    {X : Type} [Group X] (hP : Kc3Spor .J4 X) (hB : J4BlockRad) :
    BlockRadAbs X := by
  obtain ⟨e⟩ := hP
  have f : NativeSporadic.Carrier .J4 ≃* ↥CFSG.Sporadic.J4.J :=
    CFSG.Sporadic.J4.seedEquiv hF.mat
  obtain ⟨φ⟩ : Nonempty (↥CFSG.Sporadic.J4.J ≃* X) := ⟨(e.trans f).symm⟩
  exact blockRadAbs_of_equiv (X := ↥CFSG.Sporadic.J4.J) (Y := X) φ hB

theorem not_sq_dvd_card_of_j4_b (hF : J4Basic) {X : Type} [Group X] (h : Kc3Spor .J4 X) :
    ¬ 5 ^ 2 ∣ Nat.card X := by
  obtain ⟨e⟩ := h
  have h1 : Nat.card X = Nat.card ↥CFSG.Sporadic.J4.J :=
    (Nat.card_congr e.toEquiv).trans (Nat.card_congr (CFSG.Sporadic.J4.seedEquiv hF.mat).toEquiv)
  rw [h1, hF.cardJ]
  norm_num

theorem invRadical_of_j4_b (hF : J4Basic) (hIR : InvRadical ↥CFSG.Sporadic.J4.J) {X : Type}
    [Group X] (h : Kc3Spor .J4 X) : InvRadical X := by
  obtain ⟨e⟩ := h
  have h2 : InvRadical (NativeSporadic.Carrier .J4) :=
    invRadical_of_equiv (X := ↥CFSG.Sporadic.J4.J) (Y := NativeSporadic.Carrier .J4)
      (CFSG.Sporadic.J4.seedEquiv hF.mat).symm hIR
  exact invRadical_of_equiv e.symm h2

theorem kc3ForSPlus_j4_of_rad_b
    (hF : J4Basic)
    (hB : J4BlockRad) : Kc3ForSPlus (Kc3Spor .J4) := by
  intro G _ _ K L S₀ T₀ hq hP hZ hLK hL hLp hSL hS hT hST hTK hTS
  by_cases hinv : ∃ y ∈ K, orderOf y = 2 ∧ ∀ l ∈ L, l * y = y * l
  · exact kc3_core (not_sq_dvd_card_of_j4_b hF hP) hLK hL hLp hSL hS hT hST hTK hinv
      (invRadicalIn_of_invRadical (invRadical_of_j4_b hF (j4InvRadical_b hF) hP))
  · have hBK : BlockRadAbs ↥K := blockRadAbs_of_j4_b hF hP hB
    obtain ⟨hCR, hnum⟩ := blockRadIn_conditions hLK hL hLp hinv hBK
    have hSK : S₀ ≤ Subgroup.normalizer (K : Set G) := hST.trans hTK
    have hSR : S₀ ≤ Subgroup.normalizer (blockRadIn K L : Set G) := fun s hs =>
      normalizer_blockRadIn (hSK hs) (hSL hs)
    exact kc3_core_rad (not_sq_dvd_card_of_j4_b hF hP) hLK hL hLp hS hT hST hTK
      (isPGroup_blockRadIn K L) (blockRadIn_le K L) (le_normalizer_blockRadIn hLK) hSR hCR hnum

theorem kc3For_j4_of_verdict_b
    (hF : J4Basic) (h : J4VVerdict) : Kc3For (Kc3Spor .J4) :=
  kc3For_of_simplePlus (isoInv_spor .J4)
    (kc3ForSPlus_j4_of_rad_b hF (j4BlockRad_of_globalRad_b hF (j4GlobalRad_of_verdict_b hF h)))

theorem kc3For_j4_of_two_cases_b
    (hF : J4Basic) (lA lB1 lB0 : List (Subgroup ↥J))
    (hH : ∀ V : Subgroup ↥J, FpfV V → HasCommonFixedPt V →
      ∃ V' ∈ lA ++ lB1, ∃ g : ↥J, V = V'.map (cm g))
    (hN : ∀ V : Subgroup ↥J, FpfV V → ¬ HasCommonFixedPt V →
      ∃ V' ∈ lA ++ lB0, ∃ g : ↥J, V = V'.map (cm g))
    (hdA : ∀ V' ∈ lA, ClassRad V' ∨ NoNonHBlockAt Hj V')
    (hdB1 : ∀ V' ∈ lB1, ClassRad V' ∨ NoNonHBlockAt Hj V')
    (hdB0 : ∀ V' ∈ lB0, ClassRad V' ∨ NoNonHBlockAt Hj V') : Kc3For (Kc3Spor .J4) := by
  refine kc3For_j4_of_verdict_b hF (verdict_of_two_cases (lA ++ lB1) (lA ++ lB0) hH hN ?_)
  intro V' hV'
  simp only [List.mem_append] at hV'
  rcases hV' with (h | h) | (h | h)
  · exact hdA V' h
  · exact hdB1 V' h
  · exact hdA V' h
  · exact hdB0 V' h

end CFSG.QuasithinUnique.A5
