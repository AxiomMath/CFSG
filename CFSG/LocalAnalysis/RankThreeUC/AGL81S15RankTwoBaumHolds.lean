module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBaumDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517_4bOfRankTwoUnitary
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBorelTorusG2
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBaum
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBorelTorusSL3
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBorelTorusSp4
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K541EvenHolds
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoB2OffInner
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512C
import CFSG.GH74.Generic.BProg.B2.L3Cover
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoG2Ident
import CFSG.ClassicalGroups.Symplectic.ComponentCoverGriessB2

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open KFactsPair

private theorem card_center_eq_one_of_A2_odd {L : Type} [Group L] [Finite L]
    (hL : CFSG.Open.IsQuasisimple L) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    (hn2 : 2 ≤ Q.exponent) (hodd : Odd Q.exponent)
    {hv : (TauCeti.LieTypeIndex.A 2 Q).Valid}
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.A 2 Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group) :
    Nat.card (Subgroup.center L) = 1 := by
  classical
  obtain ⟨p, ex, hp, hpos⟩ := Q
  simp only at hQ
  subst p
  let Q' : TauCeti.PrimePower := ⟨2, ex, hp, hpos⟩
  set F := GaloisField 2 Q'.exponent
  haveI : Fintype F := Fintype.ofFinite F
  have hcardF : Nat.card F = Q'.card := by
    simpa only [Q', TauCeti.PrimePower.card_def] using GaloisField.card 2 ex hpos.ne'
  have hcardF' : Fintype.card F = 2 ^ Q'.exponent := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 Q'.exponent (Nat.pos_iff_ne_zero.mp Q'.exponent_pos)
  obtain ⟨ePL⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_projectiveSL_mulEquiv_lie
    (n := 2) (k := F) Q' hv hcardF
  have eC : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 F)).symm
  have hL' : CFSG.IsQuasisimple L :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native L).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open L).mpr hL)
  have hdvdZ := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hL'
    ((e.trans ePL.symm).trans eC.symm)
  have hk3 : 3 ≤ Fintype.card F := by
    rw [hcardF']
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ Q'.exponent := Nat.pow_le_pow_right (by norm_num) hn2
  have h34 : Fintype.card F ≠ 4 := by
    intro h4
    have h2 : Q'.exponent = 2 := by
      apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      change 2 ^ Q'.exponent = 2 ^ 2
      rw [← hcardF', h4]
    obtain ⟨m, hm⟩ := hodd
    simp only [Q'] at h2 hm
    omega
  have hM := CFSG.GH74.Generic.BProg.B2.L3Cover.card_hopf_psl3 (k := F) hk3 h34
  have h3 : ¬ 3 ∣ Fintype.card F - 1 := by
    rw [hcardF']
    exact CFSG.GH74.Uniqueness.Hering.three_not_dvd_two_pow_sub_one hodd
  have hgcd : Nat.gcd 3 (Fintype.card F - 1) = 1 := by
    have hle : Nat.gcd 3 (Fintype.card F - 1) ∣ 3 := Nat.gcd_dvd_left _ _
    rcases (Nat.dvd_prime Nat.prime_three).1 hle with h | h
    · exact h
    · exact absurd (h ▸ Nat.gcd_dvd_right 3 (Fintype.card F - 1)) h3
  have h1 : Nat.card (Subgroup.center L) ∣ 1 := by
    rw [hM, hgcd] at hdvdZ
    exact hdvdZ
  exact Nat.dvd_one.mp h1

theorem nonempty_mulEquiv_sl3_of_gnYComponent_A2
    {X : Type} [Group X] [Finite X]
    {T T₁ T₂ : Subgroup X} (hX : GNSetting X T) (hGood : GNGood T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} (hY : GNYComponent T T₁ T₂ Ls) {d : TauCeti.ValidLieTypeIndex}
    {Q : TauCeti.PrimePower} (hrt : IsRankTwoType d.1) (hA : d.1 = .A 2 Q)
    (e : ↥Ls ⧸ Subgroup.center ↥Ls ≃* (TauCeti.CFSGIndex.lie d).Group)
    {q : ℕ} (hq : q.Prime) (hdvd : q ∣ indexQ d.1 - 1) :
    2 ≤ Q.exponent ∧
      Nonempty (↥Ls ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 Q.exponent)) := by
  obtain ⟨d1, hv⟩ := d
  change d1 = .A 2 Q at hA
  subst d1
  have hQ : Q.p = 2 := hrt
  have hdvd' : q ∣ Q.card - 1 := by simpa only [indexQ] using hdvd
  have hn2 : 2 ≤ Q.exponent := by
    by_contra hlt
    have h1 : Q.exponent = 1 := by
      have := Q.exponent_pos
      omega
    have hcard : Q.card = 2 := by
      rw [TauCeti.PrimePower.card_def, hQ, h1]
      norm_num
    exact (Nat.Prime.not_dvd_one hq) (by rw [hcard] at hdvd'; simpa using hdvd')
  refine ⟨hn2, ?_⟩
  rcases Nat.even_or_odd Q.exponent with he | ho
  · exact K541Even_holds X T hX Ls hY.1 (hGood.shape Ls hY).1 Q.exponent he
      (isLThreeOfExp_of_A2 (d := ⟨.A 2 Q, hv⟩) hQ rfl e)
  · have hZ := card_center_eq_one_of_A2_odd hY.1.2.2 hQ hn2 ho e
    exact K541Proof.nonempty_equiv_sl3_of_catalog_A2 ⟨.A 2 Q, hv⟩ Q hQ rfl ho rfl
      (K541Proof.equiv_of_center_card_one hZ e)

private theorem hasBorelTorus_A2
    {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}
    (hX : GNSetting X T) (hGood : GNGood T T₁ T₂) {Ls : Subgroup (X ⧸ gnC T)}
    (hY : GNYComponent T T₁ T₂ Ls) {d : TauCeti.ValidLieTypeIndex}
    {Q : TauCeti.PrimePower} (hrt : IsRankTwoType d.1) (hA : d.1 = .A 2 Q)
    (e : ↥Ls ⧸ Subgroup.center ↥Ls ≃* (TauCeti.CFSGIndex.lie d).Group)
    {q : ℕ} (hq : q.Prime) (hdvd : q ∣ indexQ d.1 - 1)
    {U : Subgroup ↥Ls} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    HasBorelTorus ↥Ls q U := by
  obtain ⟨-, ⟨eLs⟩⟩ := nonempty_mulEquiv_sl3_of_gnYComponent_A2 hX hGood hY hrt hA e hq hdvd
  obtain ⟨d1, hv⟩ := d
  change d1 = .A 2 Q at hA
  subst d1
  have hQ : Q.p = 2 := hrt
  have hcardF : Nat.card (GaloisField 2 Q.exponent) = 2 ^ Q.exponent :=
    GaloisField.card 2 Q.exponent (Nat.pos_iff_ne_zero.mp Q.exponent_pos)
  have hdvdF : q ∣ Nat.card (GaloisField 2 Q.exponent) - 1 := by
    rw [hcardF]
    simpa only [indexQ, TauCeti.PrimePower.card_def, hQ] using hdvd
  obtain ⟨U₀, hU₀⟩ := CFSG.QuasithinUnique.exists_isSylowTwoOf
    (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 Q.exponent)))
  exact HasBorelTorus.of_mulEquiv eLs.symm hU₀
    (hasBorelTorus_specialLinear_three hq hdvdF hU₀) hU

private theorem hasBorelTorus_B2 {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hY : GNYComponent T T₁ T₂ Ls)
    {d : TauCeti.ValidLieTypeIndex} {Q : TauCeti.PrimePower}
    (hrt : IsRankTwoType d.1) (hB : d.1 = .B 2 Q)
    (e : ↥Ls ⧸ Subgroup.center ↥Ls ≃* (TauCeti.CFSGIndex.lie d).Group)
    {q : ℕ} (hq : q.Prime) (hdvd : q ∣ indexQ d.1 - 1)
    {U : Subgroup ↥Ls} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    HasBorelTorus ↥Ls q U := by
  obtain ⟨d1, hv⟩ := d
  change d1 = .B 2 Q at hB
  subst d1
  have hQ : Q.p = 2 := hrt
  obtain ⟨eLs⟩ :=
    CFSG.ClassicalGroups.Symplectic.exists_mulEquiv_statedSp_of_component_B2
      hY.1.2.2 (two_le_exponent_of_valid_B2 hQ hv) hQ rfl e
  have hcardF : Nat.card (GaloisField 2 Q.exponent) = 2 ^ Q.exponent :=
    GaloisField.card 2 Q.exponent (Nat.pos_iff_ne_zero.mp Q.exponent_pos)
  have hdvdF : q ∣ Nat.card (GaloisField 2 Q.exponent) - 1 := by
    rw [hcardF]
    simpa only [indexQ, TauCeti.PrimePower.card_def, hQ] using hdvd
  obtain ⟨U₀, hU₀⟩ := CFSG.QuasithinUnique.exists_isSylowTwoOf
    (⊤ : Subgroup ↥(CFSG.Open.StatedSp 2 (GaloisField 2 Q.exponent)))
  exact HasBorelTorus.of_mulEquiv eLs.symm hU₀
    (hasBorelTorus_statedSp_two hq hdvdF hU₀) hU

private theorem hasBorelTorus_G2
    {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}
    (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)} (hY : GNYComponent T T₁ T₂ Ls)
    {d : TauCeti.ValidLieTypeIndex} {Q : TauCeti.PrimePower}
    (hrt : IsRankTwoType d.1) (hG : d.1 = .G2 Q)
    (e : ↥Ls ⧸ Subgroup.center ↥Ls ≃* (TauCeti.CFSGIndex.lie d).Group)
    {q : ℕ} (hq : q.Prime) (hdvd : q ∣ indexQ d.1 - 1)
    {U : Subgroup ↥Ls} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    HasBorelTorus ↥Ls q U := by
  obtain ⟨d1, hv⟩ := d
  change d1 = .G2 Q at hG
  subst d1
  have hQ : Q.p = 2 := hrt
  obtain ⟨-, ⟨eLs⟩⟩ :=
    exists_mulEquiv_cayleyGroup_of_gn_component_G2 hX hY.1 ⟨.G2 Q, hv⟩ Q rfl hQ ⟨e⟩
  have hcardF : Nat.card (GaloisField 2 Q.exponent) = 2 ^ Q.exponent :=
    GaloisField.card 2 Q.exponent (Nat.pos_iff_ne_zero.mp Q.exponent_pos)
  have hdvdF : q ∣ Nat.card (GaloisField 2 Q.exponent) - 1 := by
    rw [hcardF]
    simpa only [indexQ, TauCeti.PrimePower.card_def, hQ] using hdvd
  obtain ⟨U₀, hU₀⟩ := CFSG.QuasithinUnique.exists_isSylowTwoOf
    (⊤ : Subgroup ↥(CFSG.Quasithin.Explicit.cayleyGroup (GaloisField 2 Q.exponent)))
  exact HasBorelTorus.of_mulEquiv eLs.symm hU₀
    (hasBorelTorus_cayleyGroup hq hdvdF hU₀) hU

theorem K517_4b_rank_two_A2B2G2_of_inputs
    (hJ : K517_4b_thompsonJ_A2B2G2) (hP : K517_4b_baumPower_A2B2G2) :
    K517_4b_rank_two_A2B2G2 := by
  intro X _ _ T T₁ T₂ hX hGood Ls hY hinv d hd hrt2 hrt ⟨e⟩ q hq hq2 hdvd
  let U : Subgroup ↥Ls := (gnImg T T ⊓ Ls).subgroupOf Ls
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf (gnImg T T ⊓ Ls) Ls :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf
      hX.sylow hY.1.2.1
  have hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
    · rw [show (U.subgroupOf (⊤ : Subgroup ↥Ls)).index = U.index from
        Subgroup.relIndex_top_right _]
      exact hS.2.2
  have hBT : HasBorelTorus ↥Ls q U := by
    rcases hd with ⟨Q, hA | hB | hG⟩
    · exact hasBorelTorus_A2 hX hGood hY hrt hA e hq hdvd hUmax
    · exact hasBorelTorus_B2 hY hrt hB e hq hdvd hUmax
    · exact hasBorelTorus_G2 hX hY hrt hG e hq hdvd hUmax
  obtain ⟨E, hELs, hEU, hE, hcard, hcomm⟩ :=
    exists_borelTorus_of_hasBorelTorus (S := gnImg T T) (L := Ls) hBT
  have hSU : gnImg T T ≤ Subgroup.normalizer
      ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) := by
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hinv hx⟩
  have hJ' : gnImg T (CFSG.Quasithin.thompsonJ T) ≤
      scalarKer (gnImg T T) (gnImg T T ⊓ Ls) E :=
    le_scalarKer_of_le_sup_centralizer hSU
      (Subgroup.map_mono (CFSG.Quasithin.thompsonJ_le_self T)) inf_le_right hELs
      (hJ X T T₁ T₂ hX hGood Ls hY hinv d hd hrt2 hrt ⟨e⟩ q hq hq2 hdvd) hcomm
  have hscal : ∀ s ∈ gnImg T (CFSG.Quasithin.baum T), ∃ j : ℕ,
      ∀ x ∈ E, s * x * s⁻¹ * (x ^ j)⁻¹ ∈ gnImg T T ⊓ Ls := by
    intro s hs
    obtain ⟨j, hj⟩ :=
      hP X T T₁ T₂ hX hGood Ls hY hinv d hd hrt2 hrt ⟨e⟩ q hq hq2 hdvd s hs
    exact ⟨j, fun x hx => hj x (Subgroup.mem_inf.mpr ⟨hELs hx, hEU hx⟩)⟩
  rcases le_gnA_of_thompsonJ_le_scalarKer hX.sylow hGood.c118 hinv hq hq2 hELs hEU hE.2 hscal hJ'
    with h | h
  · exact Or.inl (one_lt_mS_of_isElemAbelian_le_gnA hq h hE hcard)
  · exact Or.inr (one_lt_mS_of_isElemAbelian_le_gnA hq h hE hcard)

end CFSG.LocalAnalysis.RankThreeUC.S15

end
