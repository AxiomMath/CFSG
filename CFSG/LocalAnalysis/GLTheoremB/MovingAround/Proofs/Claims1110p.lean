module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110n2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110p

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.GLTheoremB

section UpRank

open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut)

@[expose] def InputD4UpRankBarK : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.LocalAnalysis.GLTheoremA.IsKHat K → CFSG.Open.IsKGroup K →
    GLAPPrimeCore 5 K = ⊥ →
    ∀ (D : Type) [Group D], CFSG.Models.LieModel D .POmegaPlus 4 2 1 →
    ∀ x : MulAut K, Lemma1314.PumpupVia 5 D K x →
    ∀ R : Subgroup (MulAut K), IsPGroup 5 R → x ∈ R → 4 ≤ CFSG.Open.pRank 5 R →
      ∃ T : Subgroup K, T ≤ Lemma1314.fixSub x ∧ IsElemAbelian 5 T ∧ 5 ^ 4 ≤ Nat.card T

theorem inputD4UpRank_of_barK (hres : InputD4UpRankBarK) : Claims1110i.InputD4UpRank := by
  intro G _ _ Y hY L hL x hxY hxN hx5 hnc K₁ hK₁ hs hlie R hRY hRN hRp hxR hfaith hrank
  have hp : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hq : CFSG.Open.IsQuasisimple (barOf 5 L) := Lemma1313.isQuasisimple_barOf_of_pComp hL
  have hKG : CFSG.Open.IsKGroup (barOf 5 L) := (hY.of_le hL.1).quotient _
  have hKH : CFSG.LocalAnalysis.GLTheoremA.IsKHat (barOf 5 L) :=
    ⟨hq, CFSG.LocalAnalysis.GLTheoremA.I2611.isCatalogGroup_center_quotient' hKG hq⟩
  have hcore : GLAPPrimeCore 5 (barOf 5 L) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  set xb : MulAut (barOf 5 L) := barAut 5 L ⟨x, hxN⟩ with hxbdef
  have hxb1 : xb ≠ 1 := fun h1 => hnc (Claims1110k.centMod_of_barAut_eq_one hxN h1)
  have hxb5 : xb ^ 5 = 1 := by
    rw [hxbdef, ← map_pow]
    have : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 5 = 1 := Subtype.ext (by simpa using hx5)
    rw [this, map_one]
  have hK₁L : K₁ ≤ L := hK₁.1.trans inf_le_left
  have hfix := AltFacts3.fixedSub_barAut_eq_p hp hx5 hxN
  have e1 : Lemma1314.fixSub xb = barX 5 L (L ⊓ Subgroup.centralizer ({x} : Set G)) := by
    rw [← hfix]
    rfl
  have hpump : Lemma1314.PumpupVia 5 (barOf 5 K₁) (barOf 5 L) xb := by
    refine ⟨orderOf_eq_prime hxb5 hxb1, barX 5 L K₁, ?_, ⟨(Prop115.barOfIso hK₁L).symm⟩⟩
    rw [e1]
    exact Prop115b.barX_glaPComponent_of_le hp inf_le_left hK₁
  set R' : Subgroup ↥(Subgroup.normalizer (L : Set G)) := R.subgroupOf (Subgroup.normalizer (L : Set G))
    with hR'def
  have hinjR : ∀ r ∈ R', barAut 5 L r = 1 → r = 1 := by
    intro r hr h1
    have h2 := hfaith r (Subgroup.mem_subgroupOf.1 hr) (Claims1110k.centMod_of_barAut_eq_one r.2 h1)
    exact Subtype.ext h2
  have hRb3 : IsPGroup 5 (R'.map (barAut 5 L)) :=
    (hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRN).symm).map _
  have hxRb : xb ∈ R'.map (barAut 5 L) := ⟨⟨x, hxN⟩, Subgroup.mem_subgroupOf.2 hxR, rfl⟩
  have hRb4 : 4 ≤ CFSG.Open.pRank 5 (R'.map (barAut 5 L)) :=
    hrank.trans ((Claims1110k.pRank_le_pRank_subgroupOf (by norm_num) hRN).trans
      (Claims1110k.pRank_le_pRank_map_of_injOn (by norm_num) _ hinjR))
  obtain ⟨T, hTfix, hTel, hT4⟩ :=
    hres (barOf 5 L) hKH hKG hcore (barOf 5 K₁) hlie xb hpump _ hRb3 hxRb hRb4
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.Open.IsElemAbelian.isPGroup hTel)
  set π : ↥L →* barOf 5 L := QuotientGroup.mk' (GLAPPrimeCore 5 ↥L) with hπdef
  set A : Subgroup ↥L := (L ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf L with hAdef
  have hA : ¬ 5 ∣ Nat.card ↥(A ⊓ π.ker) := by
    intro h5
    have h1 : Nat.card ↥(A ⊓ π.ker) ∣ Nat.card ↥(GLAPPrimeCore 5 ↥L) := by
      refine Subgroup.card_dvd_of_le (inf_le_right.trans ?_)
      rw [hπdef, QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd hp).1
      (CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 5 ↥L) (h5.trans h1)
  have hTA : T ≤ A.map π := hTfix.trans_eq e1
  obtain ⟨E, hEA, hEel, hEc⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.i1020_coprime_lift π A hA hTA hTel hk
  set F : Subgroup G := E.map L.subtype ⊔ Subgroup.zpowers x with hFdef
  have hEx : ∀ e ∈ E.map L.subtype, e * x = x * e := by
    rintro _ ⟨e, he, rfl⟩
    have h1 : (e : G) ∈ L ⊓ Subgroup.centralizer ({x} : Set G) := Subgroup.mem_subgroupOf.1 (hEA he)
    exact (Subgroup.mem_centralizer_singleton_iff.1 h1.2)
  refine ⟨F, sup_le (Subgroup.map_subtype_le E |>.trans hL.1) (Subgroup.zpowers_le.2 hxY), ?_,
    Subgroup.mem_sup_right (Subgroup.mem_zpowers x), ?_⟩
  · refine CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.SectionRank.isElemAbelian_map hEel _)
      (CFSG.Open.isElemAbelian_zpowers hx5) fun a ha b hb => ?_
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (hEx a ha) m).eq
  · have h1 : Nat.card ↥(E.map L.subtype) = 5 ^ k := by
      rw [Subgroup.card_map_of_injective L.subtype_injective, hEc]
    have h2 : Nat.card ↥(E.map L.subtype) ≤ Nat.card ↥F := Subgroup.card_le_of_le le_sup_left
    rw [hk] at hT4
    omega

theorem step6D4Inputs_of_upRankBarK
    (hres : InputD4UpRankBarK) (hLG : Claims1110i.InputD4LayerGen) :
    Claims1110j.Step6D4Inputs :=
  ⟨inputD4UpRank_of_barK hres, Claims1110k.inputD4ThreeRank_holds, hLG⟩

end UpRank

section Class

@[expose] def InputD4UpClassK : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.LocalAnalysis.GLTheoremA.IsKHat K → CFSG.Open.IsKGroup K →
    GLAPPrimeCore 5 K = ⊥ →
    ∀ (D : Type) [Group D], CFSG.Models.LieModel D .POmegaPlus 4 2 1 →
    ∀ x : MulAut K, Lemma1314.PumpupVia 5 D K x →
      (∃ (ε : Bool) (m : ℕ), 4 ≤ m ∧ IsOmegaTwo ε m K) ∨ CFSG.Models.LieModel K .POmegaPlus 4 2 5

theorem inputD4UpRankBarK_of_classK (h : InputD4UpClassK) : InputD4UpRankBarK := by
  intro K _ _ hKh hKG hcore D _ hD x hx R _ _ hRk
  rcases h K hKh hKG hcore D hD x hx with ⟨ε, m, hm, hΩ⟩ | hD32
  · exact Claims1110l.exists_elemAbelian_fixSub_of_isOmegaTwo hm hΩ hx.1 hRk
  · exfalso
    have hSCM : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .POmegaPlus 4 2 5 :=
      hD32.2.elim id fun h0 => absurd h0.1 (by norm_num)
    obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 5) R
    have h1 := Claims1110l.card_le_five_cube_of_D4_32 hSCM E hE
    rw [hEc] at h1
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).1 h1
    omega

@[expose] def InputD4UpClassChev2SporK : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.LocalAnalysis.GLTheoremA.IsKHat K → CFSG.Open.IsKGroup K →
    GLAPPrimeCore 5 K = ⊥ →
    ((∃ s : TauCeti.SporadicName, (s = .Co1 ∨ s = .Th ∨ s = .HN ∨ s = .B ∨ s = .M) ∧
        IsSporType s (K ⧸ Subgroup.center K)) ∨ IsLieChar (· = 2) K) →
    ∀ (D : Type) [Group D], CFSG.Models.LieModel D .POmegaPlus 4 2 1 →
    ∀ x : MulAut K, Lemma1314.PumpupVia 5 D K x →
      (∃ (ε : Bool) (m : ℕ), 4 ≤ m ∧ IsOmegaTwo ε m K) ∨ CFSG.Models.LieModel K .POmegaPlus 4 2 5

end Class

section Reduction

theorem inputD4UpClassK_of_chev2SporK (h1441 : Lemma1315b.Input14_4_1)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (h : InputD4UpClassChev2SporK) : InputD4UpClassK := by
  intro K _ _ hK hKG hO D _ hD x hx
  obtain ⟨i, ⟨e⟩⟩ := hK.2
  cases i with
  | cyclic q hq =>
    exfalso
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.1
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm (G := Multiplicative (ZMod q)) _ _
  | alternating N hN => exact (Claims1110l.not_pumpup_alt_of_lieModel_D4 hD hK.1 hO hN e x hx).elim
  | sporadic s =>
    rcases Claims1110l.spor_cases_of_lieModel_D4 hOrd hOut hD hK.1 e hx with h1 | h2 | h3 | h4 | h5 | h6
    · exact h K hK hKG hO (Or.inl ⟨s, Or.inl h1, ⟨e⟩⟩) D hD x hx
    · subst h2
      exact (Claims1110l.not_pumpup_co2_of_lieModel_D4 hOut hbr hD hK.1 e hx).elim
    · exact h K hK hKG hO (Or.inl ⟨s, Or.inr (Or.inl h3), ⟨e⟩⟩) D hD x hx
    · exact h K hK hKG hO (Or.inl ⟨s, Or.inr (Or.inr (Or.inl h4)), ⟨e⟩⟩) D hD x hx
    · exact h K hK hKG hO (Or.inl ⟨s, Or.inr (Or.inr (Or.inr (Or.inl h5))), ⟨e⟩⟩) D hD x hx
    · exact h K hK hKG hO (Or.inl ⟨s, Or.inr (Or.inr (Or.inr (Or.inr h6))), ⟨e⟩⟩) D hD x hx
  | lie d =>
    by_cases hd2 : d.1.characteristic = 2
    · exact h K hK hKG hO (Or.inr ⟨d, ⟨e⟩, hd2⟩) D hD x hx
    · exact (Claims1110l.not_pumpup_lie_odd_of_lieModel_D4 h1441 hD hK hO hx hd2 e).elim

theorem inputD4UpRankBarK_of_chev2SporK (h1441 : Lemma1315b.Input14_4_1)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (h : InputD4UpClassChev2SporK) : InputD4UpRankBarK :=
  inputD4UpRankBarK_of_classK (inputD4UpClassK_of_chev2SporK h1441 hOrd hOut hbr h)

end Reduction

section Monster

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporTables (SporTypes)
open CFSG.LocalAnalysis.GLTheoremA.Chev2Rows (CRow)

theorem inputD4UpClassChev2SporK_of_noD4UpOn
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hGA : GriessAllModelsStatement)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hCo1 : CRow .Co1 5) (hTh : CRow .Th 5) (hHN : CRow .HN 5)
    (hB5 : SporTypes 5 (fun T _ => Nat.card T = 44352000 ∨ ¬ 7 ∣ 5 * Nat.card T) .B)
    (hM5 : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group →
      SporTypes 5 (fun T _ => Nat.card T = 273030912000000) .M)
    (hC : Claims1110m.NoD4UpOn Claims1110m.D4UpChev2RestIdx) : InputD4UpClassChev2SporK := by
  intro K _ _ hK hKG hO hcase D _ hD x hx
  rcases hcase with ⟨s, hs, ⟨f⟩⟩ | ⟨d, ⟨e⟩, hd2⟩
  · exfalso
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact Claims1110m.false_of_crow_d4cls hb hOut hCo1 hD hK.1 f hx
    · exact Claims1110m.false_of_crow_d4cls hb hOut hTh hD hK.1 f hx
    · exact Claims1110m.false_of_crow_d4cls hb hOut hHN hD hK.1 f hx
    · refine Claims1110m.false_of_sporTypes_d4cls hOut hB5 (fun T _ h hc => ?_) hD hK.1 f hx
      rw [hc] at h
      rcases h with h | h
      · norm_num at h
      · exact h (by norm_num)
    ·
      have hMK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group :=
        (hKG.quotient (Subgroup.center K)).of_surjective f.toMonoidHom f.surjective
      refine Claims1110m.false_of_sporTypes_d4cls hOut (hM5 hMK) (fun T _ h hc => ?_) hD hK.1 f hx
      rw [hc] at h
      norm_num at h
  · by_cases hfree : Claims1110m.D4UpFreeIdx d.1
    · obtain ⟨d, hv⟩ := d
      cases d with
      | D r q =>
        rcases hfree with hq | ⟨rfl, hq⟩
        · obtain ⟨hr, hΩ⟩ := Claims1110m.isOmegaTwo_of_catalog_D_two_d4cls hGA hK.1 hO hv hq e
          exact Or.inl ⟨true, r, hr, hΩ⟩
        · exact Or.inr (Claims1110m.lieModel_of_catalog_D4_32_d4cls hGA hK.1 hv hq e)
      | twistedD r q =>
        obtain ⟨hr, hΩ⟩ := Claims1110m.isOmegaTwo_of_catalog_twistedD_two_d4cls hGA hK.1 hO hv hfree e
        exact Or.inl ⟨false, r, hr, hΩ⟩
      | _ => exact hfree.elim
    · exact (hC K hK hO d ⟨hd2, hfree⟩ ⟨e⟩ D hD x hx).elim

set_option linter.unusedSectionVars false

theorem inputD4UpClassChev2SporK_of_e8
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hGA : GriessAllModelsStatement)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hCo1 : CRow .Co1 5) (hTh : CRow .Th 5) (hHN : CRow .HN 5)
    (hB5 : SporTypes 5 (fun T _ => Nat.card T = 44352000 ∨ ¬ 7 ∣ 5 * Nat.card T) .B)
    (hM5 : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group →
      SporTypes 5 (fun T _ => Nat.card T = 273030912000000) .M)
    (hX : Inputs256p.ExcCompFieldIdx) (hE8 : Claims1110n.E8TwoNoD4Comp) : InputD4UpClassChev2SporK :=
  inputD4UpClassChev2SporK_of_noD4UpOn hb hGA hOut hCo1 hTh hHN hB5 hM5
    (Claims1110m.noD4UpOn_chev2Rest_of_rest_d4cls hb (Claims1110n.noD4UpOn_rest_of_exc_of_e8_d4n hX hE8))

end Monster

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110p
