module

public import CFSG.GH74.GLS.Stage2.Local.P34Sp4Def
public import CFSG.GH74.GLS.Stage2.Local.Lemma23
public import CFSG.GH74.GLS.Stage2.Local.P34Lift
public import CFSG.GH74.GLS.Stage2.Local.P34Pair

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12

section Prelim

variable {G : Type} [Group G] [Finite G]

theorem perfect_hbar_le {H : Subgroup G} (hPerf : PerfInJ H) {Q : Subgroup (HBar H)} (hQ : ⁅Q, Q⁆ = Q) :
    Q ≤ generalizedFitting (HBar H) := by
  obtain ⟨P, hP, hmap⟩ := exists_perfect_lift (mkH H) (QuotientGroup.mk'_surjective _) hQ
  have hP' : ⁅P.map H.subtype, P.map H.subtype⁆ = P.map H.subtype := by
    rw [← Subgroup.map_commutator, hP]
  have hle : P.map H.subtype ≤ H := Subgroup.map_subtype_le P
  have h1 := hPerf (P.map H.subtype) hle (Subgroup.isPerfect_iff.2 hP')
  have hbar : barIn H (P.map H.subtype) = Q := by
    have hsub : (P.map H.subtype).subgroupOf H = P :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective P
    unfold barIn
    rw [hsub]
    exact hmap
  rwa [hbar] at h1

omit [Finite G] in
theorem barIn_zpowers (H : Subgroup G) {z : G} (hzH : z ∈ H) :
    barIn H (zpowers z) = zpowers (mkH H ⟨z, hzH⟩) := by
  have h1 : (zpowers z).subgroupOf H = zpowers (⟨z, hzH⟩ : ↥H) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  unfold barIn
  rw [h1, MonoidHom.map_zpowers]

end Prelim

section Six

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem z_mem_LC_pair (hpair : Stage1Pair G z S q L₁ L₂) (hz : orderOf z = 2) : z ∈ LC z := by
  have hc := toBar_z_mem_center z
  have h1 : toBar z ⟨z, mem_Cen_self z⟩ ∈ generalizedFitting (CentralizerBar z) := by
    refine CFSG.centralizer_generalizedFitting_le (CentralizerBar z) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro f _
    exact Subgroup.mem_center_iff.mp hc f
  rw [hpair.fitting] at h1
  exact mem_LC_of_toBar_mem z (mem_Cen_self z) ⟨1, by simpa using hz⟩ h1

theorem perfect_LBar (hpair : Stage1Pair G z S q L₁ L₂) : ⁅LBar z, LBar z⁆ = LBar z := by
  obtain ⟨hsup, hcomm, hcard⟩ := hpair.prod
  have h4 : 4 ≤ q := by
    have := hpair.gt3
    omega
  have hq₁ : IsQuasisimple ↥L₁ := CFSG.GH74.Generic.S1.isQuasisimple_of_sl2 h4 hpair.sl₁
  have hq₂ : IsQuasisimple ↥L₂ := CFSG.GH74.Generic.S1.isQuasisimple_of_sl2 h4 hpair.sl₂
  rw [← hsup]
  exact pair_perfect hq₁ hq₂

theorem exists_lift_LBar {H : Subgroup G} (hCH : Cen z ≤ H) (hPerf : PerfInJ H)
    (hpair : Stage1Pair G z S q L₁ L₂) :
    ∃ P₀ : Subgroup ↥(barIn H (Cen z)), ⁅P₀, P₀⁆ = P₀ ∧ P₀.map (cenToBar H hCH) = LBar z ∧
      P₀.map (barIn H (Cen z)).subtype ≤ generalizedFitting (HBar H) := by
  obtain ⟨P₀, hP₀, hmap⟩ := exists_perfect_lift (cenToBar H hCH) (cenToBar_surjective H hCH) (perfect_LBar hpair)
  refine ⟨P₀, hP₀, hmap, perfect_hbar_le hPerf ?_⟩
  rw [← Subgroup.map_commutator, hP₀]

theorem mkH_z_mem_fitting {H : Subgroup G} (hCH : Cen z ≤ H) (hPerf : PerfInJ H)
    (hpair : Stage1Pair G z S q L₁ L₂) (hz2 : orderOf z = 2) (hzH : z ∈ H) :
    mkH H ⟨z, hzH⟩ ∈ generalizedFitting (HBar H) := by
  obtain ⟨P₀, -, hmap, hPK⟩ := exists_lift_LBar hCH hPerf hpair
  have hzL : z ∈ LC z := z_mem_LC_pair hpair hz2
  have hzQ : toBar z ⟨z, mem_Cen_self z⟩ ∈ LBar z :=
    Subgroup.mem_map.2 ⟨⟨z, mem_Cen_self z⟩, Subgroup.mem_subgroupOf.2 hzL, rfl⟩
  rw [← hmap] at hzQ
  obtain ⟨p₀, hp₀, hpz⟩ := Subgroup.mem_map.1 hzQ
  let uc : ↥(barIn H (Cen z)) := ⟨cenMk H hCH ⟨z, mem_Cen_self z⟩, cenMk_mem H hCH ⟨z, mem_Cen_self z⟩⟩
  have hucz : cenToBar H hCH uc = toBar z ⟨z, mem_Cen_self z⟩ := cenToBar_cenMk H hCH ⟨z, mem_Cen_self z⟩
  have hzH' : orderOf (⟨z, hzH⟩ : ↥H) = 2 := by
    rw [← hz2]
    exact (Subgroup.orderOf_coe (⟨z, hzH⟩ : ↥H)).symm
  have huc2 : orderOf uc = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_mk_eq_two H hzH'
  have hcent : ∀ y : ↥(barIn H (Cen z)), uc * y = y * uc := by
    intro y
    have hy : (y : HBar H) ∈ centralizer ({mkH H ⟨z, hzH⟩} : Set (HBar H)) := by
      rw [centralizer_mk_eq H hz2 hzH]
      exact y.2
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hy (mkH H ⟨z, hzH⟩) (Set.mem_singleton _))
  set n : ↥(barIn H (Cen z)) := uc⁻¹ * p₀ with hn
  have hn1 : cenToBar H hCH n = 1 := by
    rw [hn, map_mul, map_inv, hucz, hpz, inv_mul_cancel]
  have hnodd : Odd (orderOf n) := odd_orderOf_of_cenToBar_eq_one H hCH n hn1
  have hp₀n : p₀ = uc * n := by rw [hn]; group
  have hcomm : Commute uc n := hcent n
  have hmpow : p₀ ^ orderOf n = uc := by
    rw [hp₀n, hcomm.mul_pow, pow_orderOf_eq_one, mul_one]
    obtain ⟨j, hj⟩ := hnodd
    have huc2' : uc ^ 2 = 1 := by
      have := pow_orderOf_eq_one uc
      rwa [huc2] at this
    rw [hj, pow_succ, pow_mul, huc2', one_pow, one_mul]
  have hucP : uc ∈ P₀ := by
    rw [← hmpow]
    exact P₀.pow_mem hp₀ _
  exact hPK (Subgroup.mem_map.2 ⟨uc, hucP, rfl⟩)

theorem card_LBar_ge (hpair : Stage1Pair G z S q L₁ L₂) : q * (q ^ 2 - 1) ≤ Nat.card ↥(LBar z) := by
  obtain ⟨F, _, _, hFq, ⟨e⟩⟩ := CFSG.GH74.Generic.S1.exists_sl2_equiv hpair.sl₁
  have h1 : Nat.card ↥L₁ = q * (q ^ 2 - 1) := by
    rw [← Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hFq]
  have h2 : L₁ ≤ LBar z := by
    rw [← hpair.prod.1]
    exact le_sup_left
  rw [← h1]
  exact Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective h2)

theorem fitting_cbar_le (hpair : Stage1Pair G z S q L₁ L₂) (hz : orderOf z = 2) :
    fittingSubgroup (CentralizerBar z) ≤ zpowers (toBar z ⟨z, mem_Cen_self z⟩) := by
  obtain ⟨hsup, hcomm, hcard⟩ := hpair.prod
  obtain ⟨t₁, ht₁L, ht₁2, -, hZ₁⟩ := CFSG.GH74.Generic.S1.sl2_involution_facts hpair.odd hpair.sl₁
  obtain ⟨t₂, ht₂L, ht₂2, -, hZ₂⟩ := CFSG.GH74.Generic.S1.sl2_involution_facts hpair.odd hpair.sl₂
  have ht₁sq : t₁ * t₁ = 1 := by
    have h := pow_orderOf_eq_one t₁
    rw [ht₁2] at h
    simpa [pow_two] using h
  have ht₂sq : t₂ * t₂ = 1 := by
    have h := pow_orderOf_eq_one t₂
    rw [ht₂2] at h
    simpa [pow_two] using h
  obtain ⟨c, hc₁, hc₂, hc1⟩ := exists_inf_ne_one hcard
  have hcc : c * c = 1 := inf_sq hcard ⟨hc₁, hc₂⟩
  have hct₁ : c = t₁ := (hZ₁ c hc₁ (fun w hw => (hcomm w hw c hc₂).symm)).resolve_left hc1
  have hct₂ : c = t₂ := (hZ₂ c hc₂ (fun w hw => hcomm c hc₁ w hw)).resolve_left hc1
  have ht21 : t₂ = t₁ := hct₂.symm.trans hct₁
  set zb := toBar z ⟨z, mem_Cen_self z⟩ with hzb
  have hzL : zb ∈ LBar z :=
    Subgroup.mem_map.2 ⟨⟨z, mem_Cen_self z⟩, Subgroup.mem_subgroupOf.2 (z_mem_LC_pair hpair hz), rfl⟩
  have hzcent : ∀ y : CentralizerBar z, y * zb = zb * y := fun y =>
    Subgroup.mem_center_iff.1 (toBar_z_mem_center z) y
  have hzb1 : zb ≠ 1 := by
    intro h
    have hmem : (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) ∈ pPrimeCore 2 ↥(Cen z) := (QuotientGroup.eq_one_iff _).1 h
    have hodd := odd_orderOf_of_mem_pPrimeCore hmem
    rw [Subgroup.orderOf_mk, hz] at hodd
    exact absurd hodd (by decide)
  have hZΛ : ∀ x ∈ LBar z, (∀ l ∈ LBar z, x * l = l * x) → x = 1 ∨ x = t₁ := by
    intro x hx hxc
    rw [← hsup] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute' hcomm hx
    have ha' : ∀ w ∈ L₁, a * w = w * a := by
      intro w hw
      have h1 := hxc w (hsup ▸ Subgroup.mem_sup_left hw)
      have hbw : b * w = w * b := (hcomm w hw b hb).symm
      have : (a * w) * b = (w * a) * b := by
        calc (a * w) * b = a * (w * b) := by group
          _ = a * (b * w) := by rw [hbw]
          _ = (a * b) * w := by group
          _ = w * (a * b) := h1
          _ = (w * a) * b := by group
      exact mul_right_cancel this
    have hb' : ∀ w ∈ L₂, b * w = w * b := by
      intro w hw
      have h1 := hxc w (hsup ▸ Subgroup.mem_sup_right hw)
      have haw : a * w = w * a := hcomm a ha w hw
      have : a * (b * w) = a * (w * b) := by
        calc a * (b * w) = (a * b) * w := by group
          _ = w * (a * b) := h1
          _ = (w * a) * b := by group
          _ = (a * w) * b := by rw [haw]
          _ = a * (w * b) := by group
      exact mul_left_cancel this
    rcases hZ₁ a ha ha' with rfl | rfl
    · rcases hZ₂ b hb hb' with rfl | rfl
      · left; simp
      · right; rw [one_mul, ht21]
    · rcases hZ₂ b hb hb' with rfl | rfl
      · right; rw [mul_one]
      · left; rw [ht21]; exact ht₁sq
  have hzbt : zb = t₁ := (hZΛ zb hzL (fun l _ => (hzcent l).symm)).resolve_left hzb1
  intro f hf
  have hfΛ : f ∈ LBar z := by
    have : f ∈ generalizedFitting (CentralizerBar z) := Subgroup.mem_sup_left hf
    rwa [hpair.fitting] at this
  have hlayer : layer (CentralizerBar z) = LBar z := by
    simp only [CFSG.layer.eq_sSup]
    rw [hpair.comps, sSup_pair, hsup]
  have hfc : ∀ l ∈ LBar z, f * l = l * f := by
    intro l hl
    rw [← hlayer] at hl
    have hcom := CFSG.LocalCores.fitting_layer_commute (G := CentralizerBar z)
    have hf' : f ∈ centralizer ((layer (CentralizerBar z) : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcom hf
    exact (Subgroup.mem_centralizer_iff.1 hf' l hl).symm
  rcases hZΛ f hfΛ hfc with h | h
  · rw [h]; exact one_mem _
  · rw [h, ← hzbt]; exact mem_zpowers _

theorem map_fitting_le {C R : Type} [Group C] [Group R] [Finite C] (ψ : C →* R)
    (hψ : Function.Surjective ψ) : (fittingSubgroup C).map ψ ≤ fittingSubgroup R := by
  have hn : ((fittingSubgroup C).map ψ).Normal := (fittingSubgroup_normal).map ψ hψ
  have hnil : Group.IsNilpotent ↥((fittingSubgroup C).map ψ) :=
    Group.nilpotent_of_surjective (ψ.subgroupMap (fittingSubgroup C)) (ψ.subgroupMap_surjective _)
  exact le_sSup ⟨hn, hnil⟩

theorem step6_of (hSp4 : Sp4Facts) :
    ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
      ∀ H : Subgroup G, H ≠ ⊤ → Cen z ≤ H → PerfInJ H → C0 z k S H →
        IsCoatom (barIn H (Cen z)) ∧ barIn H (LC z) ≤ generalizedFitting (HBar H) ∧
          CFSG.GH74.GLS.Bg.Fm (barIn H (Cen z)) = barIn H (zpowers z) := by
  intro G _ _ z k S hctx H hne hCH hPerf hC0
  obtain ⟨ε, q, L₁, L₂, hk, hL4, hq3, hpsp, hnS, hO2⟩ := hC0
  have hz2 := hctx.orderOf_z
  have hzH : z ∈ H := z_mem_of_cen_le hCH
  have hCu : centralizer ({mkH H ⟨z, hzH⟩} : Set (HBar H)) = barIn H (Cen z) :=
    centralizer_mk_eq H hz2 hzH
  have hzH' : orderOf (⟨z, hzH⟩ : ↥H) = 2 := by
    rw [← hz2]
    exact (Subgroup.orderOf_coe (⟨z, hzH⟩ : ↥H)).symm
  let uc : ↥(barIn H (Cen z)) :=
    ⟨cenMk H hCH ⟨z, mem_Cen_self z⟩, cenMk_mem H hCH ⟨z, mem_Cen_self z⟩⟩
  have huc2 : orderOf uc = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_mk_eq_two H hzH'
  have hucz : cenToBar H hCH uc = toBar z ⟨z, mem_Cen_self z⟩ :=
    cenToBar_cenMk H hCH ⟨z, mem_Cen_self z⟩
  have hcent : ∀ y : ↥(barIn H (Cen z)), uc * y = y * uc := by
    intro y
    have hy : (y : HBar H) ∈ centralizer ({mkH H ⟨z, hzH⟩} : Set (HBar H)) := by
      rw [hCu]
      exact y.2
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hy (mkH H ⟨z, hzH⟩) (Set.mem_singleton _))
  obtain ⟨P₀, hP₀, hmap, hPK⟩ := exists_lift_LBar hCH hPerf hL4.pair
  have hset : Sp4Setting (generalizedFitting (HBar H)) q (mkH H ⟨z, hzH⟩) := by
    refine ⟨(CFSG.LocalCores.generalized_fitting_characteristic).2, hpsp, hL4.pair.odd, hq3,
      CFSG.centralizer_generalizedFitting_le (HBar H), mkH_z_mem_fitting hCH hPerf hL4.pair hz2 hzH,
      orderOf_mk_eq_two H hzH', ?_, ?_⟩
    · obtain ⟨T, hT⟩ := barIn_sylow H hctx.sylow_top (hctx.S_le_Cen.trans hCH)
      refine ⟨T, ?_, ?_⟩
      · rw [hT]
        exact Subgroup.mem_map.2 ⟨⟨z, hzH⟩, Subgroup.mem_subgroupOf.2 hctx.z_mem, rfl⟩
      · intro s hs
        rw [hT] at hs
        obtain ⟨⟨s', hs'H⟩, hs', rfl⟩ := Subgroup.mem_map.1 hs
        have hcomm : (⟨s', hs'H⟩ : ↥H) * ⟨z, hzH⟩ = ⟨z, hzH⟩ * ⟨s', hs'H⟩ :=
          Subtype.ext (hctx.S_comm_z (Subgroup.mem_subgroupOf.1 hs'))
        change mkH H ⟨s', hs'H⟩ * mkH H ⟨z, hzH⟩ = mkH H ⟨z, hzH⟩ * mkH H ⟨s', hs'H⟩
        rw [← map_mul, ← map_mul, hcomm]
    · refine ⟨P₀.map (barIn H (Cen z)).subtype, le_inf hPK ?_, ?_, ?_⟩
      · rintro _ ⟨p, -, rfl⟩
        rw [hCu]
        exact p.2
      · rw [← Subgroup.map_commutator, hP₀]
      · have h1 : Nat.card ↥(P₀.map (barIn H (Cen z)).subtype) = Nat.card ↥P₀ :=
          Subgroup.card_map_of_injective (barIn H (Cen z)).subtype_injective
        have h2 : Nat.card ↥(LBar z) ≤ Nat.card ↥P₀ := by
          rw [← hmap]
          exact Nat.card_le_card_of_surjective _ ((cenToBar H hCH).subgroupMap_surjective P₀)
        have h3 := card_LBar_ge hL4.pair
        have hq5 : 0 < q * (q ^ 2 - 1) := by
          have h4 : 16 ≤ q ^ 2 := by nlinarith
          have h5 : 1 ≤ q ^ 2 - 1 := by omega
          have h6 : 0 < q := by omega
          positivity
        rw [h1]
        calc q * (q ^ 2 - 1) / 2 < q * (q ^ 2 - 1) := Nat.div_lt_self hq5 (by norm_num)
          _ ≤ Nat.card ↥(LBar z) := h3
          _ ≤ Nat.card ↥P₀ := h2
  have hfus := hSp4.fusion (HBar H) _ q _ hset
  have hmax := hSp4.max (HBar H) _ q _ hset
  have hodd := hSp4.oddCore (HBar H) _ q _ hset
  have hoddM : pPrimeCore 2 ↥(barIn H (Cen z)) = ⊥ := by
    rw [← hCu]
    exact hodd
  have hinj : Function.Injective (cenToBar H hCH) := by
    have hker : (cenToBar H hCH).ker = ⊥ :=
      eq_bot_of_odd_normal_of_oddCore hoddM (N := (cenToBar H hCH).ker)
        (fun n hn => odd_orderOf_of_cenToBar_eq_one H hCH n (MonoidHom.mem_ker.1 hn))
    exact (MonoidHom.ker_eq_bot_iff _).1 hker
  refine ⟨?_, ?_, ?_⟩
  · rw [← hCu]
    exact isCoatom_centralizer_of_fusion hfus hmax
  · intro l hl
    obtain ⟨⟨c, hcH⟩, hc, rfl⟩ := Subgroup.mem_map.1 hl
    have hcL : c ∈ LC z := Subgroup.mem_subgroupOf.1 hc
    have hcC : c ∈ Cen z := LC_le_Cen z hcL
    let lc : ↥(barIn H (Cen z)) := ⟨cenMk H hCH ⟨c, hcC⟩, cenMk_mem H hCH ⟨c, hcC⟩⟩
    have hlcQ : cenToBar H hCH lc ∈ LBar z := by
      change cenToBar H hCH ⟨cenMk H hCH ⟨c, hcC⟩, cenMk_mem H hCH ⟨c, hcC⟩⟩ ∈ LBar z
      rw [cenToBar_cenMk]
      exact Subgroup.mem_map.2 ⟨⟨c, hcC⟩, Subgroup.mem_subgroupOf.2 hcL, rfl⟩
    rw [← hmap] at hlcQ
    obtain ⟨p, hp, hpl⟩ := Subgroup.mem_map.1 hlcQ
    have hplc : p = lc := hinj hpl
    exact hPK (Subgroup.mem_map.2 ⟨lc, hplc ▸ hp, rfl⟩)
  · unfold CFSG.GH74.GLS.Bg.Fm inSubgroup
    rw [barIn_zpowers H hzH]
    apply le_antisymm
    · rintro y ⟨φ, hφ, rfl⟩
      have h1 : cenToBar H hCH φ ∈ fittingSubgroup (CentralizerBar z) :=
        map_fitting_le (cenToBar H hCH) (cenToBar_surjective H hCH) (Subgroup.mem_map_of_mem _ hφ)
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (fitting_cbar_le hL4.pair hz2 h1)
      have h2 : cenToBar H hCH (uc ^ n) = cenToBar H hCH φ := by
        rw [map_zpow, hucz]
        exact hn
      have h3 : uc ^ n = φ := hinj h2
      have h4 : (uc : HBar H) ^ n = (φ : HBar H) := by
        rw [← SubgroupClass.coe_zpow]
        exact congrArg Subtype.val h3
      exact Subgroup.mem_zpowers_iff.2 ⟨n, h4⟩
    · rw [Subgroup.zpowers_le]
      have hnormal : (zpowers uc).Normal := by
        refine ⟨fun x hx g => ?_⟩
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        have : g * uc ^ m * g⁻¹ = uc ^ m := by
          rw [mul_inv_eq_iff_eq_mul]
          exact ((Commute.zpow_left (hcent g) m).eq).symm
        rw [this]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers uc) _
      have hnil : Group.IsNilpotent ↥(zpowers uc) := (IsPGroup.of_card (p := 2) (n := 1) (by rw [Nat.card_zpowers, huc2, pow_one])).isNilpotent
      have hle : zpowers uc ≤ fittingSubgroup ↥(barIn H (Cen z)) := le_sSup ⟨hnormal, hnil⟩
      exact ⟨uc, hle (Subgroup.mem_zpowers uc), rfl⟩

end Six

end CFSG.GH74.GLS.Stage2.Local.P34
