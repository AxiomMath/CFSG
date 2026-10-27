module

public import CFSG.HardMathSupport.Dickson.BMRows.CensusShape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenShape

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Open CFSG.Blueprint CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Dickson.I271.TabMSeven
open CFSG.Monster.Generated (Gmat)
open CFSG.AGLEmbedding.Norton.MON5_7 (dG zG tG)

section HeP


theorem census_M_seven_shape_of_heP {G : Type} [Group G] [Finite G] {k : G}
    (hk : orderOf k = 7) {H : Subgroup G} (hHk : H ≤ Subgroup.centralizer ({k} : Set G))
    (e : ↥H ≃* ↥CFSG.Sporadic.HeldB.heP)
    (hbound : Nat.card ↥(Subgroup.centralizer ({k} : Set G)) ≤ 7 * 4030387200) :
    ShapeRkAt' 7 (fun T _ => catalogIs T (· = .sporadic .He)) (fun _ _ => True) k := by
  have hcard : Nat.card ↥H = 4030387200 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.HeldB.card_heP
  have hZ : Subgroup.center ↥H = ⊥ := center_eq_bot_of_equiv_heP e
  haveI : IsSimpleGroup ↥CFSG.Sporadic.HeldB.heP := CFSG.Sporadic.HeldB.heP_simple
  have hs : IsSimpleGroup ↥H := MulEquiv.isSimpleGroup e
  have hnab : ∃ a b : ↥H, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have htop : Subgroup.center ↥H = ⊤ :=
      eq_top_iff.2 fun z _ => Subgroup.mem_center_iff.2 fun g => hc g z
    have h1 : Nat.card ↥H = 1 := by
      rw [← Subgroup.card_top (G := ↥H), ← htop, hZ, Subgroup.card_bot]
    rw [hcard] at h1
    norm_num at h1
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have b₀ : NativeSporadic.He ≃* (TauCeti.CFSGIndex.sporadic .He).Group := b
  exact tabMSeven_shapeRkAt'_of_simple (Good := fun T _ => catalogIs T (· = .sporadic .He))
    (Rk := fun _ _ => True) (by norm_num) catalogIs_of_mulEquiv (fun _ _ _ _ _ h => h) hk hHk hs
    hnab (by rw [hcard]; norm_num) (by rw [hcard]; exact hbound)
    ⟨.sporadic .He, rfl, ⟨e.trans (CFSG.Sporadic.HeldB.heEquivP.symm.trans b₀)⟩⟩ trivial

end HeP

section NoComp

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance


theorem census_M_seven_noComp
    {z : Gmat} (hz : orderOf z = 7)
    (hzd : ∀ (g : Gmat) (m : ℕ), g * z * g⁻¹ ≠ dG ^ m)
    (htA : ∃ t : Gmat, orderOf t = 2 ∧ t * dG = dG * t ∧
      Nat.card ↥(Subgroup.centralizer ({t} : Set Gmat)) = 2 * CFSG.Open.monsterBabyOrder)
    (huB : ∃ u : Gmat, orderOf u = 2 ∧ u * dG = dG * u ∧
      Nat.card ↥(Subgroup.centralizer ({u} : Set Gmat)) =
        CFSG.Monster.Existence.twoBCentralizerOrder ∧
      35280 < Nat.card ↥(Subgroup.centralizer ({u} : Set Gmat) ⊓
        Subgroup.centralizer ({dG} : Set Gmat)))
    (hQ16 : ∃ S : Subgroup Gmat, S ≤ Subgroup.centralizer ({z} : Set Gmat) ∧
      Nonempty (↥S ≃* QuaternionGroup 4)) :
    ∀ J : Subgroup Gmat, ¬ GLAPComponent 7 (Subgroup.centralizer ({z} : Set Gmat)) J := by
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  have hO : GLAPPrimeCoreOf 7 (Subgroup.centralizer ({z} : Set Gmat)) = ⊥ :=
    gLAPPrimeCoreOf_eq_bot_of_isConj' (isConj_zG_of_not_conj hz hzd).symm gLAPPrimeCoreOf_zG
  obtain ⟨S, hSC, ⟨eS⟩⟩ := hQ16
  have h32 : ¬ 32 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set Gmat)) := by
    have h := tabMSeven_not_two_pow_five_dvd hz hzd htA huB
    norm_num at h
    exact h
  have hQ := tabMSeven_sylow_quat hSC eS h32
  have h7 : 7 ^ 5 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set Gmat)) :=
    (pow_dvd_pow 7 (by norm_num : 5 ≤ 6)).trans (seven_pow_dvd_of_not_conj hz hzd)
  exact fun J => tabMSeven_noComp hO hQ h7
    (fun v hv R hR hle => card_isPGroup_seven_le_of_involution hv hR hle) J

end NoComp

section Gmat

open CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Dickson.I271.TabMFive
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance (orderOf_dG orderOf_zG orderOf_tG
  isTwoBCentralizer_tG centralizer_pow_eq_of_prime)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus (monsterSevenClasses)


theorem census_M_seven_gmat
    :
    CentShapeRk' 7 (fun T _ => catalogIs T (· = .sporadic .He)) (fun _ _ => True) Gmat := by
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  obtain ⟨hcls, h2A, h2B, hG5⟩ := gmat_seven_bounds
  obtain ⟨hHk, ⟨e⟩⟩ := tabMSeven_he_le_cent_dG
  have hE8 : HePE8 := hePE8
  have hdG : ShapeRkAt' 7 (fun T _ => catalogIs T (· = .sporadic .He)) (fun _ _ => True) dG :=
    census_M_seven_shape_of_heP orderOf_dG hHk e
      (centSevenA_of_bounds hE8 hcls h2A h2B hG5 orderOf_dG hHk e)
  obtain ⟨hcard, htA, huB, h2Bd⟩ :=
    tabMSeven_sevenA_facts hE8 hcls h2A h2B hG5 orderOf_dG hHk e
  have hzd : ∀ (g : Gmat) (m : ℕ), g * zG * g⁻¹ ≠ dG ^ m := by
    intro g m h
    by_cases hm : dG ^ m = 1
    · rw [hm] at h
      apply CFSG.AGLEmbedding.Norton.MON5_7.zG_ne_one
      have h' := congrArg (fun x => g⁻¹ * x * g) h
      simpa [mul_assoc] using h'
    · have h1 : Nat.card ↥(Subgroup.centralizer ({zG} : Set Gmat)) = 7 * 4030387200 := by
        haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
        rw [← card_centralizer_conj g zG, h, centralizer_pow_eq_of_prime orderOf_dG hm, hcard]
      have h6 := seven_pow_dvd_card_cent_zG
      rw [h1] at h6
      norm_num at h6
  have hQ : ∃ S : Subgroup Gmat, S ≤ Subgroup.centralizer ({zG} : Set Gmat) ∧
      Nonempty (↥S ≃* QuaternionGroup 4) := by
    obtain ⟨z, f, hz, hf, hzf, hzt, hft, S, hSz, ⟨eS⟩⟩ := tabMSeven_sevenB_data
    rcases monsterSevenClasses z hz with h | h
    ·
      exfalso
      obtain ⟨c, hc⟩ := isConj_iff.1 h
      have huo : orderOf (c * tG * c⁻¹) = 2 := by rw [orderOf_conj_eq, orderOf_tG]
      have hud : c * tG * c⁻¹ * dG = dG * (c * tG * c⁻¹) := by
        rw [← hc]
        exact Commute.conj hzt.symm c
      have huc : Nat.card ↥(Subgroup.centralizer ({c * tG * c⁻¹} : Set Gmat)) =
          twoBCentralizerOrder := by
        rw [card_centralizer_conj]
        exact isTwoBCentralizer_tG.2.2.2.2.1
      have hf' : c * f * c⁻¹ ∈ Subgroup.centralizer ({c * tG * c⁻¹} : Set Gmat) ⊓
          Subgroup.centralizer ({dG} : Set Gmat) := by
        refine ⟨Subgroup.mem_centralizer_singleton_iff.2 (Commute.conj hft c),
          Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        rw [← hc]
        exact Commute.conj hzf.symm c
      have h5 := Subgroup.orderOf_dvd_natCard _ hf'
      rw [h2Bd _ huo hud huc, orderOf_conj_eq, hf] at h5
      norm_num at h5
    ·
      obtain ⟨c, hc⟩ := isConj_iff.1 h
      refine ⟨S.map (MulAut.conj c).toMonoidHom, ?_,
        ⟨(S.equivMapOfInjective _ (MulAut.conj c).injective).symm.trans eS⟩⟩
      rintro _ ⟨s, hs, rfl⟩
      have hsz := Subgroup.mem_centralizer_singleton_iff.1 (hSz hs)
      rw [Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        ← hc]
      exact Commute.conj hsz c
  have hzG : ShapeRkAt' 7 (fun T _ => catalogIs T (· = .sporadic .He)) (fun _ _ => True) zG :=
    Or.inl (census_M_seven_noComp orderOf_zG hzd htA huB hQ)
  intro k hk1 hk7
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hk : orderOf k = 7 := orderOf_eq_prime hk7 hk1
  rcases monsterSevenClasses k hk with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    have hkc : k = c⁻¹ * dG * c⁻¹⁻¹ := by rw [← hc]; group
    rw [hkc]
    exact shapeRkAt'_conj (by norm_num) catalogIs_of_mulEquiv (fun _ _ _ _ _ h => h) c⁻¹ dG hdG
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    have hkc : k = c⁻¹ * zG * c⁻¹⁻¹ := by rw [← hc]; group
    rw [hkc]
    exact shapeRkAt'_conj (by norm_num) catalogIs_of_mulEquiv (fun _ _ _ _ _ h => h) c⁻¹ zG hzG

end Gmat

section Census


theorem census_M_seven
    :
    PCompCensus 7 (NativeSporadic.Carrier .M) (· = .sporadic .He) := by
  obtain ⟨e₀⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  let e : CFSG.Monster.Existence.MGriess ≃* NativeSporadic.Carrier .M := e₀
  have φ := CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth
  let eG : Gmat ≃* NativeSporadic.Carrier .M := φ.symm.trans e
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  haveI : Finite (NativeSporadic.Carrier .M) := Finite.of_equiv Gmat eG.toEquiv
  exact pCompCensus_of_centShapeRk' (by norm_num) (CentShapeRk'.of_equiv (by norm_num)
    catalogIs_of_mulEquiv (fun _ _ _ _ _ h => h) eG census_M_seven_gmat)

end Census

end CFSG.HardMathSupport.Dickson.BMRows
