module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8Cube
public import CFSG.HardMathSupport.Lang.TwE6Step3.Assembly
public import CFSG.HardMathSupport.Lang.TwE6Step3.SixFinal
public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.OrderSix
public import CFSG.HardMathSupport.Lang.SeitzPlane.TwistedE6Six
public import CFSG.LieType.SeitzGeneration.HyperExParabolicTw
public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.Skeleton
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Order
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJPlacement
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6RouteWStarProved
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate110
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1000
public import Certificates.Certificate1001
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1004
public import Certificates.Certificate1005
public import Certificates.Certificate1006
public import Certificates.Certificate1008
public import Certificates.Certificate1009
public import Certificates.Certificate1010
public import Certificates.Certificate1011
public import Certificates.Certificate1012
public import Certificates.Certificate1013
public import Certificates.Certificate1015
public import Certificates.Certificate1016
public import Certificates.Certificate1018
public import Certificates.Certificate1019
public import Certificates.Certificate1022
public import Certificates.Certificate1952
public import Certificates.Certificate3120
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate7023
public import Certificates.Certificate7059
public import Certificates.Certificate8046
public import Certificates.Certificate8048
public import Certificates.Certificate8049
public import Certificates.Certificate8052
public import Certificates.Certificate9704
public import Certificates.Certificate9706
public import Certificates.Certificate9707
public import Certificates.Certificate14976
public import Certificates.Certificate14977
public import Certificates.Certificate15951
public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeProved
public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeSL3Sign
public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.Radicals
public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Fixed
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSplit
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.LinCover
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.Families
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Linear
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Close
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2Case
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Lang.AnisoE6 TauCeti
  CFSG.TauCetiBridge CFSG.RankThree.PartOne.KE CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem hyperGen_map_inj {Γ Δ : Type*} [Group Γ] [Group Δ] {p : ℕ} (φ : Γ →* Δ)
    (hφ : Function.Injective φ) {K E : Subgroup Γ} (h : HyperGen p K E) :
    HyperGen p (K.map φ) (E.map φ) := by
  unfold HyperGen at h ⊢
  have key := Subgroup.map_mono (f := φ) h
  rw [MonoidHom.map_closure] at key
  refine key.trans ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨k, ⟨hkK, F, hFE, hFi, hFk⟩, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨Subgroup.mem_map_of_mem φ hkK, F.map φ, Subgroup.map_mono hFE, ?_, ?_⟩
  · rw [Subgroup.relIndex_map_map_of_injective _ _ hφ]
    exact hFi
  · rintro _ ⟨f, hf, rfl⟩
    show φ f * φ k = φ k * φ f
    rw [← map_mul, ← map_mul, hFk f hf]

theorem LeviLayer.map {Γ Δ : Type*} [Group Γ] [Group Δ] {p : ℕ} (φ : Γ →* Δ)
    (hφ : Function.Injective φ) {V L : Subgroup Γ} (h : LeviLayer Γ p V L) :
    LeviLayer Δ p (V.map φ) (L.map φ) := by
  obtain ⟨A, B, hAV, hBV, hAc, hBc, hd, hAB, hLA, hHG⟩ := h.exists_split
  refine ⟨A.map φ, B.map φ, Subgroup.map_mono hAV, Subgroup.map_mono hBV, ?_, ?_, ?_, ?_, ?_,
    hyperGen_map_inj φ hφ hHG⟩
  · rw [Subgroup.card_map_of_injective hφ]
    exact hAc
  · rw [Subgroup.card_map_of_injective hφ]
    exact hBc
  · rw [Subgroup.disjoint_def]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have hab' : a = b := hφ hab.symm
    subst hab'
    rw [Subgroup.disjoint_def.1 hd ha hb, map_one]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hAB a ha b hb]
  · rintro _ ⟨l, hl, rfl⟩ _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, hLA l hl a ha]

theorem quasisimple_of_mulEquiv_levi {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hG : CFSG.Open.IsQuasisimple G) : CFSG.Open.IsQuasisimple H := by
  refine ⟨?_, ?_⟩
  · have htop : (⊤ : Subgroup G).map (e : G →* H) = ⊤ := by
      rw [← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.2 e.surjective
    have h2 : (commutator G).map (e : G →* H) = commutator H := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator, htop]
    rw [← h2, hG.1]
    exact htop
  · haveI := hG.2
    have hz : (G ⧸ Subgroup.center G) ≃* (H ⧸ Subgroup.center H) :=
      QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e (Subgroup.map_center_eq e)
    haveI : Nontrivial (H ⧸ Subgroup.center H) := hz.symm.surjective.nontrivial
    exact IsSimpleGroup.isSimpleGroup_of_surjective hz.toMonoidHom hz.surjective

theorem e8LeviPiece_of_datum {e : ℕ}
    (hS : ∀ (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid) (p : ℕ), p.Prime → 7 ≤ p →
      p ≠ q.p → orderOf ((q.card : ℕ) : ZMod p) = e → SylowTorus (Cat ⟨.E8 q, hv⟩) p 4)
    (hD : ∀ (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid) (p : ℕ), p.Prime → 7 ≤ p →
      p ≠ q.p → orderOf ((q.card : ℕ) : ZMod p) = e →
      ∃ V₀ : Subgroup (Cat ⟨.E8 q, hv⟩), IsElemAbelian p V₀ ∧ Nat.card V₀ = p ^ 4 ∧
        ∃ P₀ : Subgroup (Cat ⟨.E8 q, hv⟩), LeviLayer _ p V₀ P₀ ∧ CFSG.Open.IsQuasisimple ↥P₀ ∧
          ordTrialityD4 q.card ^ 2 < Nat.card ↥P₀) :
    E8LeviPiece e := by
  intro q hv p hp hp7 hpq he V hV hVc
  obtain ⟨V₀, hV₀, hV₀c, P₀, hL, hQ, hb⟩ := hD q hv p hp hp7 hpq he
  obtain ⟨x, hx⟩ :=
    exists_conj_of_sylowTorus_cube hp (hS q hv p hp hp7 hpq he) hV₀ hV₀c hV hVc
  refine ⟨P₀.map (MulAut.conj x).toMonoidHom, ?_, ?_, ?_⟩
  · rw [hx]
    exact hL.map _ (MulAut.conj x).injective
  · exact quasisimple_of_mulEquiv_levi
      (P₀.equivMapOfInjective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective) hQ
  · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
    exact hb


theorem pow_le_geomSum_last (n s q : ℕ) (hn : 1 ≤ n) :
    q ^ (s * (n - 1)) ≤ CFSG.Timmesfeld.ExceptionalOrders.geomSum n s q := by
  unfold CFSG.Timmesfeld.ExceptionalOrders.geomSum
  exact Finset.single_le_sum (f := fun i => q ^ (s * i)) (fun i _ => Nat.zero_le _)
    (Finset.mem_range.2 (by omega))

theorem q36_le_prodE6 (q : ℕ) : q ^ 36 ≤ CFSG.StandardType.TableBExc.prodE6 q := by
  unfold CFSG.StandardType.TableBExc.prodE6
  have h1 : q ^ 1 ≤ CFSG.Timmesfeld.ExceptionalOrders.geomSum 2 1 q := by
    simpa using pow_le_geomSum_last 2 1 q (by norm_num)
  have h2 : q ^ 2 ≤ CFSG.Timmesfeld.ExceptionalOrders.geomSum 3 1 q := by
    simpa using pow_le_geomSum_last 3 1 q (by norm_num)
  have h3 : q ^ 3 ≤ CFSG.Timmesfeld.ExceptionalOrders.geomSum 4 1 q := by
    simpa using pow_le_geomSum_last 4 1 q (by norm_num)
  have h4 : q ^ 4 ≤ CFSG.Timmesfeld.ExceptionalOrders.geomSum 5 1 q := by
    simpa using pow_le_geomSum_last 5 1 q (by norm_num)
  have h5 : q ^ 3 ≤ CFSG.Timmesfeld.ExceptionalOrders.geomSum 2 3 q := by
    simpa using pow_le_geomSum_last 2 3 q (by norm_num)
  have h6 : q ^ 7 ≤ CFSG.Timmesfeld.ExceptionalOrders.geomSum 8 1 q := by
    simpa using pow_le_geomSum_last 8 1 q (by norm_num)
  have h7 : q ^ 8 ≤ CFSG.Timmesfeld.ExceptionalOrders.geomSum 9 1 q := by
    simpa using pow_le_geomSum_last 9 1 q (by norm_num)
  have h8 : q ^ 8 ≤ CFSG.Timmesfeld.ExceptionalOrders.geomSum 3 4 q := by
    simpa using pow_le_geomSum_last 3 4 q (by norm_num)
  calc q ^ 36 = q ^ 1 * q ^ 2 * q ^ 3 * q ^ 4 * (q ^ 3 * q ^ 7) * (q ^ 8 * q ^ 8) := by ring
    _ ≤ _ := by gcongr

theorem ordTrialityD4_sq_lt_E6 {q : ℕ} (hq : 2 ≤ q) :
    ordTrialityD4 q ^ 2 < q ^ 36 * CFSG.StandardType.TableBExc.prodE6 q := by
  have hA : ordTrialityD4 q ≤ 3 * q ^ 28 := by
    unfold ordTrialityD4
    have h8 : q ^ 8 + q ^ 4 + 1 ≤ 3 * q ^ 8 := by
      have h48 : q ^ 4 ≤ q ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
      have h18 : 1 ≤ q ^ 8 := Nat.one_le_pow _ _ (by omega)
      omega
    calc q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
        ≤ q ^ 12 * (3 * q ^ 8) * q ^ 6 * q ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ h8) (Nat.sub_le _ _))
            (Nat.sub_le _ _)
      _ = 3 * q ^ 28 := by ring
  have hB : ordTrialityD4 q ^ 2 ≤ 9 * q ^ 56 := by
    calc ordTrialityD4 q ^ 2 ≤ (3 * q ^ 28) ^ 2 := Nat.pow_le_pow_left hA 2
      _ = 9 * q ^ 56 := by ring
  have hC : q ^ 72 ≤ q ^ 36 * CFSG.StandardType.TableBExc.prodE6 q := by
    calc q ^ 72 = q ^ 36 * q ^ 36 := by ring
      _ ≤ q ^ 36 * CFSG.StandardType.TableBExc.prodE6 q := Nat.mul_le_mul_left _ (q36_le_prodE6 q)
  have hpos : 0 < q ^ 56 := by positivity
  have h16 : 2 ^ 16 ≤ q ^ 16 := Nat.pow_le_pow_left hq 16
  have hD : 9 * q ^ 56 < q ^ 72 := by
    calc 9 * q ^ 56 < 65536 * q ^ 56 := by linarith
      _ ≤ q ^ 16 * q ^ 56 := Nat.mul_le_mul_right _ (by norm_num at h16 ⊢; omega)
      _ = q ^ 72 := by ring
  omega

section E6Cube



open CFSG.HardMathSupport.Foote.Coordinator.AnisoCube
  (cube plane_spec hyperGen_of_radicals card_cube isElemAbelian_cube exists_sl3_orderOf
    e6ThreeRadicalAdj_of_d4Lines E6ThreeD4Lines)
open CFSG.HardMathSupport.Malle.SeitzCube (exists_three_sl3_E6_signed e6ThreeD4Lines_proved)


theorem e6Cube_hyperGen_three {q : PrimePower} (hv : (LieTypeIndex.E6 q).Valid) {p : ℕ}
    (hp : p.Prime) (hpq : p ≠ q.p) (he : orderOf ((q.card : ℕ) : ZMod p) = 3) :
    ∃ E : Subgroup (Cat ⟨.E6 q, hv⟩), IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      HyperGen p ⊤ E := by
  have hD : E6ThreeD4Lines := e6ThreeD4Lines_proved CFSG.Goldschmidt.topStatement
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Finite (ModGL Tag.E6 K) := CFSG.LieType.Chevalley.finite_modGL
  obtain ⟨ψ, hinj, hcomm, hψ⟩ := exists_three_sl3_E6_signed K
  have hrad := e6ThreeRadicalAdj_of_d4Lines hD K q.p ψ hψ hinj hcomm
  obtain ⟨hdvd, hp3⟩ :=
    CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.dvd_sq_add_add_one_of_orderOf_eq_three hp he
  have hdvdK : p ∣ Nat.card K ^ 2 + Nat.card K + 1 := by rw [hK]; exact hdvd
  obtain ⟨g, hg⟩ := exists_sl3_orderOf (K := K) hp hp3 hdvdK
  have hordK : orderOf ((Nat.card K : ℕ) : ZMod p) = 3 := by rw [hK]; exact he
  have hrp : q.p ≠ p := fun h' => hpq h'.symm
  obtain ⟨Q, Q', hQr, hQ'r, htop, hnQ, hnQ', hlQ, hlQ'⟩ := hrad p g hp hp3 hpq hordK hg
  obtain ⟨hA, hA1⟩ := plane_spec hinj hcomm hp hp3 hg
  have hHG : HyperGen p ⊤ (cube ψ g) :=
    hyperGen_of_radicals hA hA1 htop (CFSG.LieType.Chevalley.not_dvd_card_of_isPGroup hrp hQr)
      (CFSG.LieType.Chevalley.not_dvd_card_of_isPGroup hrp hQ'r) hnQ hnQ' hlQ hlQ'
  refine ⟨(cube ψ g).map e.symm.toMonoidHom, ?_, ?_, hyperGen_map_symm e hHG⟩
  · exact CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p
      (isElemAbelian_cube hinj hcomm hp hp3 hg) e.symm.toMonoidHom
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact card_cube hinj hcomm hp hp3 hg

end E6Cube



theorem natCard_map_of_injOn_levi {G H : Type*} [Group G] [Group H] (π : G →* H) (S : Subgroup G)
    (hS : ∀ x ∈ S, π x = 1 → x = 1) : Nat.card (S.map π) = Nat.card S := by
  have hinj : Function.Injective (π.comp S.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply Subtype.ext
    exact hS x.1 x.2 hx
  have hrange : (π.comp S.subtype).range = S.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem commute_of_central_kernel_levi {G H : Type*} [Group G] [Group H] [Finite G] (π : G →* H)
    (hcen : ∀ z : G, π z = 1 → z ∈ Subgroup.center G) {F : Subgroup G}
    (hF : Nat.Coprime (Nat.card π.ker) (Nat.card F)) (k : G)
    (hk : ∀ f ∈ F, π (k * f * k⁻¹ * f⁻¹) = 1) : ∀ f ∈ F, f * k = k * f := by
  classical
  let c : F → G := fun f => k * (f : G) * k⁻¹ * (f : G)⁻¹
  have hcmem : ∀ f : F, c f ∈ π.ker := fun f => MonoidHom.mem_ker.2 (hk f f.2)
  let ψ : F →* π.ker := MonoidHom.mk' (fun f => ⟨c f, hcmem f⟩) (by
    intro a b
    apply Subtype.ext
    have hcb : c b ∈ Subgroup.center G := hcen _ (hk b b.2)
    have hconj : (a : G) * c b * (a : G)⁻¹ = c b := by
      have h := Subgroup.mem_center_iff.1 hcb (a : G)
      rw [h, mul_assoc, mul_inv_cancel, mul_one]
    show c (a * b) = c a * c b
    have e1 : c (a * b) = (c a) * ((a : G) * c b * (a : G)⁻¹) := by
      simp only [c, Subgroup.coe_mul, mul_inv_rev]
      group
    rw [e1, hconj])
  set R := ψ.range with hR
  have hd1 : Nat.card R ∣ Nat.card F := Subgroup.card_range_dvd ψ
  have hd2 : Nat.card R ∣ Nat.card π.ker := Subgroup.card_subgroup_dvd_card R
  have hRbot : R = ⊥ := Subgroup.eq_bot_of_card_eq R (Nat.eq_one_of_dvd_coprimes hF hd2 hd1)
  intro f hf
  have hmem : ψ ⟨f, hf⟩ ∈ R := MonoidHom.mem_range.2 ⟨⟨f, hf⟩, rfl⟩
  rw [hRbot, Subgroup.mem_bot] at hmem
  have hc1 : k * f * k⁻¹ * f⁻¹ = 1 := congrArg Subtype.val hmem
  exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hc1)).symm



theorem exists_elemAbelian_central_lift {G H : Type*} [Group G] [Group H] [Finite G] {p n : ℕ}
    [Fact p.Prime] (π : G →* H) (hπ : Function.Surjective π)
    (hcop : Nat.Coprime (Nat.card π.ker) p) {E : Subgroup H} (hE : IsElemAbelian p E)
    (hEc : Nat.card E = p ^ n) :
    ∃ B : Subgroup G, IsElemAbelian p B ∧ Nat.card B = p ^ n ∧ B.map π = E ∧
      ∀ x ∈ B, π x = 1 → x = 1 := by
  classical
  have hfinH : Finite H := Finite.of_surjective π hπ
  have hcopn : Nat.Coprime (Nat.card π.ker) (p ^ n) := Nat.Coprime.pow_right n hcop
  have hEidx : E.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcomap : Nat.card (E.comap π) = Nat.card π.ker * p ^ n := by
    have h1 := Subgroup.card_mul_index (E.comap π)
    have hidx : (E.comap π).index = E.index := Subgroup.index_comap_of_surjective E hπ
    rw [hidx] at h1
    have h2 := Subgroup.card_mul_index π.ker
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hπ, Subgroup.card_top] at h2
    have h3 := Subgroup.card_mul_index E
    rw [hEc] at h3
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hEidx)
    rw [h1, ← h2, ← h3]
    ring
  obtain ⟨S₀, hS₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(E.comap π)) p
    (n := n) ⟨Nat.card π.ker, by rw [hcomap]; ring⟩
  set S : Subgroup G := S₀.map (E.comap π).subtype with hSdef
  have hSc : Nat.card S = p ^ n := by
    rw [hSdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hS₀]
  have hSle : S ≤ E.comap π := by
    rw [hSdef]
    exact Subgroup.map_subtype_le _
  have hSN : S ⊓ π.ker = ⊥ := by
    have h1 : Nat.card ↥(S ⊓ π.ker) ∣ p ^ n := by
      rw [← hSc]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(S ⊓ π.ker) ∣ Nat.card π.ker :=
      Subgroup.card_dvd_of_le inf_le_right
    exact Subgroup.eq_bot_of_card_eq _ (Nat.eq_one_of_dvd_coprimes hcopn h2 h1)
  have hinjS : ∀ x ∈ S, π x = 1 → x = 1 := by
    intro x hx hπx
    have hmem : x ∈ S ⊓ π.ker := ⟨hx, MonoidHom.mem_ker.2 hπx⟩
    rw [hSN, Subgroup.mem_bot] at hmem
    exact hmem
  have hle : S.map π ≤ E := Subgroup.map_le_iff_le_comap.2 hSle
  have hSE : S.map π = E := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [natCard_map_of_injOn_levi π S hinjS, hSc, hEc]
  have hSamb : IsElemAbelian p S := by
    have hS_inj : ∀ a ∈ S, ∀ b ∈ S, π a = π b → a = b := by
      intro a ha b hb hab
      have h1 : a⁻¹ * b = 1 := hinjS (a⁻¹ * b) (S.mul_mem (S.inv_mem ha) hb)
        (by rw [map_mul, map_inv, hab, inv_mul_cancel])
      exact inv_mul_eq_one.1 h1
    have hmemE : ∀ x ∈ S, π x ∈ E := fun x hx => hle (Subgroup.mem_map_of_mem π hx)
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hS_inj _ (S.mul_mem x.2 y.2) _ (S.mul_mem y.2 x.2)
      have hc : π (x : G) * π (y : G) = π (y : G) * π (x : G) :=
        congrArg Subtype.val (hE.1.is_comm.comm ⟨π x, hmemE _ x.2⟩ ⟨π y, hmemE _ y.2⟩)
      rw [map_mul, map_mul, hc]
    · apply hinjS _ (S.pow_mem hx p)
      rw [map_pow]
      exact hE.2 _ (hmemE x hx)
  exact ⟨S, hSamb, hSc, hSE, hinjS⟩

theorem hyperplane_lift_central {G H : Type*} [Group G] [Group H] {p : ℕ} [Fact p.Prime]
    (π : G →* H)
    {B : Subgroup G} (hBc : Nat.card B = p ^ 3) (hBinj : ∀ x ∈ B, π x = 1 → x = 1)
    {F' : Subgroup H} (hF'E : F' ≤ B.map π) (hF'i : F'.relIndex (B.map π) = p)
    (hEc : Nat.card (B.map π) = p ^ 3) :
    ∃ F : Subgroup G, F ≤ B ∧ F.relIndex B = p ∧ F.map π = F' ∧ Nat.card F = Nat.card F' := by
  classical
  set F : Subgroup G := F'.comap π ⊓ B with hFdef
  have hFB : F ≤ B := inf_le_right
  have hFmap : F.map π = F' := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.1
    · intro y hy
      obtain ⟨b, hb, rfl⟩ := hF'E hy
      exact Subgroup.mem_map_of_mem π (show b ∈ F from ⟨hy, hb⟩)
  have hFinj : ∀ x ∈ F, π x = 1 → x = 1 := fun x hx hx1 => hBinj x (hFB hx) hx1
  have hFc : Nat.card F = Nat.card F' := by
    rw [← hFmap, natCard_map_of_injOn_levi π F hFinj]
  have hF'c : p * Nat.card F' = p ^ 3 := by
    have h := Subgroup.relIndex_mul_card F' (B.map π)
    rw [inf_of_le_left hF'E, hF'i, hEc] at h
    exact h
  have hFi : F.relIndex B = p := by
    have h := Subgroup.relIndex_mul_card F B
    rw [inf_of_le_left hFB, hBc] at h
    have hF2 : Nat.card F = p ^ 2 := by
      rw [hFc]
      have hp0 : 0 < p := (Fact.out : p.Prime).pos
      have : p * Nat.card F' = p * p ^ 2 := by rw [hF'c]; ring
      exact Nat.eq_of_mul_eq_mul_left hp0 this
    rw [hF2] at h
    have hp0 : 0 < p ^ 2 := pow_pos (Fact.out : p.Prime).pos 2
    have : F.relIndex B * p ^ 2 = p * p ^ 2 := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right hp0 this
  exact ⟨F, hFB, hFi, hFmap, hFc⟩



theorem hyperGen_of_central_lift {G H : Type*} [Group G] [Group H] [Finite G] {p : ℕ}
    [Fact p.Prime] (π : G →* H) (hπ : Function.Surjective π)
    (hcop : Nat.Coprime (Nat.card π.ker) p) (hcen : ∀ z : G, π z = 1 → z ∈ Subgroup.center G)
    {B : Subgroup G} (hBc : Nat.card B = p ^ 3) (hBinj : ∀ x ∈ B, π x = 1 → x = 1)
    (hHG : HyperGen p (⊤ : Subgroup H) (B.map π)) : HyperGen p (⊤ : Subgroup G) B := by
  classical
  have hE'c : Nat.card (B.map π) = p ^ 3 := by
    rw [natCard_map_of_injOn_levi π B hBinj, hBc]
  have hex : ∃ F' : Subgroup H, F' ≤ B.map π ∧ F'.relIndex (B.map π) = p := by
    by_contra hno
    push Not at hno
    have hcl : Subgroup.closure {k : H | k ∈ (⊤ : Subgroup H) ∧ ∃ F' : Subgroup H,
        F' ≤ B.map π ∧ F'.relIndex (B.map π) = p ∧ ∀ f ∈ F', f * k = k * f} ≤ ⊥ := by
      rw [Subgroup.closure_le]
      rintro k ⟨-, F', hF'E, hF'i, -⟩
      exact absurd hF'i (hno F' hF'E)
    have htop : (⊤ : Subgroup H) ≤ ⊥ := hHG.trans hcl
    have hE'bot : B.map π ≤ ⊥ := fun x hx => htop (Subgroup.mem_top x)
    have h1 : Nat.card (B.map π) = 1 := by
      rw [le_bot_iff.1 hE'bot, Subgroup.card_bot]
    rw [hE'c] at h1
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp1
    omega
  obtain ⟨F₀', hF₀E, hF₀i⟩ := hex
  obtain ⟨F₀, hF₀B, hF₀i', -, -⟩ := hyperplane_lift_central π hBc hBinj hF₀E hF₀i hE'c
  set S : Subgroup G := Subgroup.closure {k : G | k ∈ (⊤ : Subgroup G) ∧
    ∃ F : Subgroup G, F ≤ B ∧ F.relIndex B = p ∧ ∀ f ∈ F, f * k = k * f} with hSdef
  have hA : ∀ k' : H, (k' ∈ (⊤ : Subgroup H) ∧ ∃ F' : Subgroup H,
      F' ≤ B.map π ∧ F'.relIndex (B.map π) = p ∧ ∀ f ∈ F', f * k' = k' * f) →
      k' ∈ S.map π := by
    rintro k' ⟨-, F', hF'E, hF'i, hF'k⟩
    obtain ⟨F, hFB, hFi, hFmap, hFc⟩ := hyperplane_lift_central π hBc hBinj hF'E hF'i hE'c
    obtain ⟨k, hk⟩ := hπ k'
    have hF'card : Nat.card F' = p ^ 2 := by
      have h := Subgroup.relIndex_mul_card F' (B.map π)
      rw [inf_of_le_left hF'E, hF'i, hE'c] at h
      have hp0 : 0 < p := (Fact.out : p.Prime).pos
      have : p * Nat.card F' = p * p ^ 2 := by rw [h]; ring
      exact Nat.eq_of_mul_eq_mul_left hp0 this
    have hkS : k ∈ S := by
      apply Subgroup.subset_closure
      refine ⟨Subgroup.mem_top k, F, hFB, hFi, ?_⟩
      refine commute_of_central_kernel_levi π hcen ?_ k ?_
      · rw [hFc, hF'card]
        exact Nat.Coprime.pow_right 2 hcop
      · intro f hf
        have hfF' : π f ∈ F' := by
          rw [← hFmap]
          exact Subgroup.mem_map_of_mem π hf
        have hcomm := hF'k (π f) hfF'
        simp only [map_mul, map_inv, hk]
        rw [← hcomm]
        group
    have hmem := Subgroup.mem_map_of_mem π hkS
    rw [hk] at hmem
    exact hmem
  have hB : (⊤ : Subgroup H) ≤ S.map π := by
    have hHG' := hHG
    unfold HyperGen at hHG'
    refine hHG'.trans ((Subgroup.closure_le _).2 ?_)
    intro k' hk'
    exact hA k' hk'
  have hC : π.ker ≤ S := by
    intro z hz
    have hzc : z ∈ Subgroup.center G := hcen z (MonoidHom.mem_ker.1 hz)
    apply Subgroup.subset_closure
    refine ⟨Subgroup.mem_top z, F₀, hF₀B, hF₀i', fun f _ => ?_⟩
    exact Subgroup.mem_center_iff.1 hzc f
  have hD : (⊤ : Subgroup G) ≤ S := by
    intro g _
    obtain ⟨s, hs, hsg⟩ := Subgroup.mem_map.1 (hB (Subgroup.mem_top (π g)))
    have hz : s⁻¹ * g ∈ π.ker :=
      MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hsg, inv_mul_cancel])
    have hg : g = s * (s⁻¹ * g) := by group
    rw [hg]
    exact S.mul_mem hs (hC hz)
  exact hD



@[expose] def E8E6LayerInput : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid) (p : ℕ), p.Prime → 7 ≤ p → p ≠ q.p →
    orderOf ((q.card : ℕ) : ZMod p) = 3 →
    ∃ (P A : Subgroup (Cat ⟨.E8 q, hv⟩)) (π : ↥P →* Cat ⟨.E6 q, LieTypeIndex.valid_E6 q⟩),
      Function.Surjective π ∧ Nat.card π.ker ∣ 3 ∧
      (∀ z : ↥P, π z = 1 → z ∈ Subgroup.center ↥P) ∧ CFSG.Open.IsQuasisimple ↥P ∧
      IsElemAbelian p A ∧ Nat.card A = p ∧ (∀ l ∈ P, ∀ a ∈ A, l * a = a * l) ∧ Disjoint A P

theorem levi_datum_of_layer {q : PrimePower} {hv : (LieTypeIndex.E8 q).Valid} {p : ℕ}
    [Fact p.Prime] [Finite (Cat ⟨.E8 q, hv⟩)] {H : Type*} [Group H]
    (P A : Subgroup (Cat ⟨.E8 q, hv⟩))
    (π : ↥P →* H) (hπ : Function.Surjective π) (hcop : Nat.Coprime (Nat.card π.ker) p)
    (hcen : ∀ z : ↥P, π z = 1 → z ∈ Subgroup.center ↥P) (hQ : CFSG.Open.IsQuasisimple ↥P)
    (hAel : IsElemAbelian p A) (hAc : Nat.card A = p) (hcomm : ∀ l ∈ P, ∀ a ∈ A, l * a = a * l)
    (hdisj : Disjoint A P) (E : Subgroup H) (hEel : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3)
    (hEHG : HyperGen p (⊤ : Subgroup H) E) (hbound : ordTrialityD4 q.card ^ 2 < Nat.card H) :
    ∃ V₀ : Subgroup (Cat ⟨.E8 q, hv⟩), IsElemAbelian p V₀ ∧ Nat.card V₀ = p ^ 4 ∧
      ∃ P₀ : Subgroup (Cat ⟨.E8 q, hv⟩), LeviLayer _ p V₀ P₀ ∧
        CFSG.Open.IsQuasisimple ↥P₀ ∧ ordTrialityD4 q.card ^ 2 < Nat.card ↥P₀ := by
  obtain ⟨B, hBel, hBc, hBmap, hBinj⟩ := exists_elemAbelian_central_lift π hπ hcop hEel hEc
  have hHG : HyperGen p (⊤ : Subgroup H) (B.map π) := by
    rw [hBmap]
    exact hEHG
  have hPG : HyperGen p (⊤ : Subgroup ↥P) B :=
    hyperGen_of_central_lift π hπ hcop hcen hBc hBinj hHG
  have hPtop : (⊤ : Subgroup ↥P).map P.subtype = P := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hPG8 := hyperGen_map_inj P.subtype (Subgroup.subtype_injective P) hPG
  rw [hPtop] at hPG8
  have hB'P : B.map P.subtype ≤ P := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hB'el : IsElemAbelian p (B.map P.subtype) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hBel P.subtype
  have hB'c : Nat.card (B.map P.subtype) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective P), hBc]
  have hcommAB : ∀ a ∈ A, ∀ f ∈ B.map P.subtype, a * f = f * a :=
    fun a ha f hf => (hcomm f (hB'P hf) a ha).symm
  have hdAB : Disjoint A (B.map P.subtype) := Disjoint.mono_right hB'P hdisj
  have hVel : IsElemAbelian p (A ⊔ B.map P.subtype) :=
    isElemAbelian_sup_of_commute hAel hB'el hcommAB
  have hVc : Nat.card ↥(A ⊔ B.map P.subtype) = p ^ 4 := by
    rw [card_sup_eq_mul_of_commute_disjoint hcommAB hdAB, hAc, hB'c]
    ring
  have hLev : LeviLayer _ p (A ⊔ B.map P.subtype) P :=
    ⟨⟨A, B.map P.subtype, le_sup_left, le_sup_right, hAc, hB'c, hdAB, hcommAB, hcomm, hPG8⟩⟩
  have hbP : ordTrialityD4 q.card ^ 2 < Nat.card ↥P :=
    lt_of_lt_of_le hbound (Nat.card_le_card_of_surjective π hπ)
  exact ⟨A ⊔ B.map P.subtype, hVel, hVc, P, hLev, hQ, hbP⟩

section E8Three



theorem ordTrialityD4_sq_lt_cat_E6 (q : PrimePower) :
    ordTrialityD4 q.card ^ 2 < Nat.card (Cat ⟨.E6 q, LieTypeIndex.valid_E6 q⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q
      (LieTypeIndex.valid_E6 q)
  have hfin : Finite (ModGL Tag.E6 K) := CFSG.LieType.Chevalley.finite_modGL
  have hq : 2 ≤ q.card := by
    rw [PrimePower.card_def]
    exact le_trans q.prime_p.two_le (Nat.le_self_pow q.exponent_pos.ne' _)
  have hT : 0 < Nat.card (torusGroup Tag.E6 K) := Nat.card_pos
  rw [Nat.card_congr eK.toEquiv, CFSG.StandardType.TableBExc.card_adjointGroup_E6_eq, hK]
  calc ordTrialityD4 q.card ^ 2 < q.card ^ 36 * CFSG.StandardType.TableBExc.prodE6 q.card :=
        ordTrialityD4_sq_lt_E6 hq
    _ ≤ Nat.card (torusGroup Tag.E6 K) *
          (q.card ^ 36 * CFSG.StandardType.TableBExc.prodE6 q.card) :=
        Nat.le_mul_of_pos_left _ hT

theorem e8LeviPiece_three_of_layer (hL : E8E6LayerInput) : E8LeviPiece 3 := by
  refine e8LeviPiece_of_datum
    (fun q hv p hp h7 hpq he => sylowTorus_cat_E8_three hv hp h7 hpq he) ?_
  intro q hv p hp h7 hpq he
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, A, π, hπ, hker, hcen, hQ, hAel, hAc, hcomm, hdisj⟩ := hL q hv p hp h7 hpq he
  have hp3 : Nat.Coprime 3 p := (Nat.coprime_primes (by norm_num) hp).2 (by omega)
  have hcop : Nat.Coprime (Nat.card π.ker) p := Nat.Coprime.coprime_dvd_left hker hp3
  obtain ⟨K8, _, _, -, -, ⟨e8⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hfin8 : Finite (ModGL Tag.E8 K8) := CFSG.LieType.Chevalley.finite_modGL
  haveI : Finite (Cat ⟨.E8 q, hv⟩) := Finite.of_equiv _ e8.symm.toEquiv
  obtain ⟨E, hEel, hEc, hEHG⟩ := e6Cube_hyperGen_three (LieTypeIndex.valid_E6 q) hp hpq he
  exact levi_datum_of_layer P A π hπ hcop hcen hQ hAel hAc hcomm hdisj E hEel hEc hEHG
    (ordTrialityD4_sq_lt_cat_E6 q)

end E8Three


theorem ordTrialityD4_sq_le {q : ℕ} (hq : 1 ≤ q) : ordTrialityD4 q ^ 2 ≤ 9 * q ^ 56 := by
  have hA : ordTrialityD4 q ≤ 3 * q ^ 28 := by
    unfold ordTrialityD4
    have h8 : q ^ 8 + q ^ 4 + 1 ≤ 3 * q ^ 8 := by
      have h48 : q ^ 4 ≤ q ^ 8 := Nat.pow_le_pow_right hq (by norm_num)
      have h18 : 1 ≤ q ^ 8 := Nat.one_le_pow _ _ hq
      omega
    calc q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
        ≤ q ^ 12 * (3 * q ^ 8) * q ^ 6 * q ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ h8) (Nat.sub_le _ _))
            (Nat.sub_le _ _)
      _ = 3 * q ^ 28 := by ring
  calc ordTrialityD4 q ^ 2 ≤ (3 * q ^ 28) ^ 2 := Nat.pow_le_pow_left hA 2
    _ = 9 * q ^ 56 := by ring

theorem ordTrialityD4_sq_lt_ordTwistedE6 {q : ℕ} (hq : 2 ≤ q) :
    ordTrialityD4 q ^ 2 < ordTwistedE6 q := by
  have hq1 : 1 ≤ q := by omega
  have hD : ordTrialityD4 q ^ 2 ≤ 9 * q ^ 56 := ordTrialityD4_sq_le hq1
  have hq11 : q ^ 11 ≤ q ^ 12 - 1 := by
    have h1 : q ^ 11 * 2 ≤ q ^ 12 := by
      rw [show q ^ 12 = q ^ 11 * q by ring]
      exact Nat.mul_le_mul_left _ hq
    have h2 : 1 ≤ q ^ 11 := Nat.one_le_pow _ _ hq1
    omega
  have hq7 : q ^ 7 ≤ q ^ 8 - 1 := by
    have h1 : q ^ 7 * 2 ≤ q ^ 8 := by
      rw [show q ^ 8 = q ^ 7 * q by ring]
      exact Nat.mul_le_mul_left _ hq
    have h2 : 1 ≤ q ^ 7 := Nat.one_le_pow _ _ hq1
    omega
  have hq5 : q ^ 5 ≤ q ^ 6 - 1 := by
    have h1 : q ^ 5 * 2 ≤ q ^ 6 := by
      rw [show q ^ 6 = q ^ 5 * q by ring]
      exact Nat.mul_le_mul_left _ hq
    have h2 : 1 ≤ q ^ 5 := Nat.one_le_pow _ _ hq1
    omega
  have hq1' : q ≤ q ^ 2 - 1 := by
    have h1 : q * 2 ≤ q ^ 2 := by
      rw [show q ^ 2 = q * q by ring]
      exact Nat.mul_le_mul_left _ hq
    omega
  have hX : q ^ 74 ≤ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1) := by
    calc q ^ 74 = q ^ 36 * q ^ 11 * q ^ 9 * q ^ 7 * q ^ 5 * q ^ 5 * q := by ring
      _ ≤ q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
          (q ^ 5 + 1) * (q ^ 2 - 1) := by
        gcongr
        all_goals omega
  unfold ordTwistedE6
  set X : ℕ := q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
    (q ^ 5 + 1) * (q ^ 2 - 1) with hXdef
  have hg : 0 < Nat.gcd 3 (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hgle : Nat.gcd 3 (q + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  have hdiv : X / 3 ≤ X / Nat.gcd 3 (q + 1) := Nat.div_le_div_left hgle hg
  have h18 : 2 ^ 18 ≤ q ^ 18 := Nat.pow_le_pow_left hq 18
  have hpos : 1 ≤ q ^ 56 := Nat.one_le_pow _ _ hq1
  have hbig : 9 * q ^ 56 + 1 ≤ X / 3 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have h74 : q ^ 74 = q ^ 56 * q ^ 18 := by ring
    have h3 : q ^ 56 * 2 ^ 18 ≤ q ^ 56 * q ^ 18 := Nat.mul_le_mul_left _ h18
    have h4 : (9 * q ^ 56 + 1) * 3 ≤ q ^ 56 * 2 ^ 18 := by nlinarith
    omega
  have hfin := le_trans hbig hdiv
  exact lt_of_le_of_lt hD (lt_of_lt_of_le (Nat.lt_succ_self _) hfin)

@[expose] def E8E6LayerInput6 : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid) (p : ℕ), p.Prime → 7 ≤ p → p ≠ q.p →
    orderOf ((q.card : ℕ) : ZMod p) = 6 →
    ∃ (P A : Subgroup (Cat ⟨.E8 q, hv⟩))
      (π : ↥P →* Cat ⟨.twistedE6 q, LieTypeIndex.valid_twistedE6 q⟩),
      Function.Surjective π ∧ Nat.card π.ker ∣ 3 ∧
      (∀ z : ↥P, π z = 1 → z ∈ Subgroup.center ↥P) ∧ CFSG.Open.IsQuasisimple ↥P ∧
      IsElemAbelian p A ∧ Nat.card A = p ∧ (∀ l ∈ P, ∀ a ∈ A, l * a = a * l) ∧ Disjoint A P

section TwCube

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Classical2
  CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
open CFSG.HardMathSupport.Lang.TwE6Step3 (TwE6SixLines pSubgroup_comm_twistedE6
  exists_cube_containing_plane)




theorem twE6Cube_hyperGen_six (h : TwE6SixLines) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q.p)
    (hnd : ¬ p ∣ q.card ^ 2 - 1)
    (hord : orderOf ((q.card : ℕ) : ZMod p) = 6) {E₀ : Subgroup (Cat ⟨.twistedE6 q, hv⟩)}
    (hE₀ : IsElemAbelian p E₀) (hE₀c : Nat.card E₀ = p ^ 3) :
    ∃ E : Subgroup (Cat ⟨.twistedE6 q, hv⟩), IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      HyperGen p ⊤ E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨h6, hp3⟩ :=
    CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.dvd_sq_sub_add_one_of_orderOf_eq_six hp hord
  have hp3' : 3 < p := by
    have := hp.two_le
    rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h' | h' | h' | h'
    · exact absurd h' hp2
    · exact absurd h' hp3
    · exact absurd (h' ▸ hp) (by norm_num)
    · omega
  have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hpq' : ¬ p ∣ q.card := by
    intro hd
    rw [hcard] at hd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow hd))
  have hpqZ : (p : ℤ) ∣ ((q.p ^ q.exponent : ℕ) : ℤ) ^ 2 - ((q.p ^ q.exponent : ℕ) : ℤ) + 1 := by
    rw [← hcard]
    have h1 := Int.natCast_dvd_natCast.2 h6
    have h2 : ((q.card ^ 2 - q.card + 1 : ℕ) : ℤ) = (q.card : ℤ) ^ 2 - q.card + 1 := by
      rw [Nat.cast_add, Nat.cast_sub (Nat.le_self_pow two_ne_zero q.card), Nat.cast_pow,
        Nat.cast_one]
    rwa [h2] at h1
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Finite (ModGL TwistTag.E6.tag K) := by
    have hK0 : Nat.card K ≠ 0 := by
      rw [hK]
      exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero)
    have : Finite K := Nat.finite_of_card_ne_zero hK0
    have : Fintype K := Fintype.ofFinite K
    exact finite_modGL
  have : Finite (Cat ⟨.twistedE6 q, hv⟩) :=
    Finite.of_equiv (twistedE6RootGroup K σ) e.symm.toEquiv
  have hcommCat : ∀ Q : Subgroup (Cat ⟨.twistedE6 q, hv⟩), IsPGroup p Q →
      ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    intro Q hQ a ha b hb
    have hQ' : IsPGroup p (Q.map e.toMonoidHom) := hQ.map _
    have hab := pSubgroup_comm_twistedE6 q.prime_p q.exponent_pos K hK σ hσ hp hp3' hpqZ
      (Q.map e.toMonoidHom) hQ' (e a) ⟨a, ha, rfl⟩ (e b) ⟨b, hb, rfl⟩
    exact e.injective (by simpa using hab)
  obtain ⟨E, R, hE, hEc, hRne, hRp, hEN⟩ :=
    CFSG.HardMathSupport.Lang.SeitzPlane.exists_plane_twistedE6RootGroup_six
      q.prime_p q.exponent_pos K hK σ hσ hp hp3' (by rw [← hcard]; exact hpq')
      (by rw [← hcard]; exact hord) (by rw [← hcard]; exact hnd)
  let f : twistedE6RootGroup K σ →* Cat ⟨.twistedE6 q, hv⟩ := e.symm.toMonoidHom
  have hf : Function.Injective f := e.symm.injective
  have hE₀' : IsElemAbelian p (E.map f) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE f
  have hE₀c' : Nat.card (E.map f) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hf, hEc]
  have hN : ∀ x ∈ E.map f, (R.map f).map (MulAut.conj x).toMonoidHom = R.map f := by
    rintro _ ⟨x, hx, rfl⟩
    ext z
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      have hy' : x * y * x⁻¹ ∈ R := by
        rw [← hEN x hx]
        exact ⟨y, hy, rfl⟩
      exact ⟨x * y * x⁻¹, hy', by simp [MulAut.conj_apply, f]⟩
    · rintro ⟨y, hy, rfl⟩
      have hy' : x⁻¹ * y * x ∈ R := by
        have := hEN x⁻¹ (inv_mem hx)
        rw [← this]
        exact ⟨y, hy, by simp⟩
      refine ⟨f (x⁻¹ * y * x), ⟨_, hy', rfl⟩, ?_⟩
      simp [MulAut.conj_apply, f, mul_assoc]
  have hE'1 : E.map f ≠ ⊥ := by
    intro hbot
    have := hE₀c'
    rw [hbot, Subgroup.card_bot] at this
    have h2 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  have hHy : HyperGen p ⊤ (E.map f) := by
    refine seitzExcParabolicHyperTw ⟨TauCeti.LieTypeIndex.twistedE6 q, hv⟩ p hp
      (by rw [TauCeti.LieTypeIndex.characteristic_twistedE6]; exact hpq) (Or.inr ⟨q, rfl⟩) _ hE₀'
      hE'1 ⟨R.map f, ?_, ?_, hN⟩
    · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hf]
    · rw [TauCeti.LieTypeIndex.characteristic_twistedE6]
      exact hRp.map f
  obtain ⟨E₁, hle, hE₁, hE₁c⟩ := exists_cube_containing_plane hcommCat hE₀' hE₀c' hE₀ hE₀c
  refine ⟨E₁, hE₁, hE₁c, ?_⟩
  refine CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.hyperGen_of_hyperGen_of_le hHy ?_
  intro B hB hBi k hk
  have hBne : B ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.relIndex_bot_left, hE₀c'] at hBi
    have h1 : p ^ 2 = p ^ 1 := by rw [hBi, pow_one]
    have := Nat.pow_right_injective hp.two_le h1
    omega
  obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hBne
  exact h q hv p hp hp3 hpq hord E₁ hE₁ hE₁c y (hle (hB y.2)) (fun h1 => hy (Subtype.ext h1))
    k (hk y y.2).symm

end TwCube

section E8Six

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Classical2
  CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
open CFSG.HardMathSupport.Lang.TwE6Step3 (TwE6SixLines)




theorem ordTrialityD4_sq_lt_cat_twE6 (q : PrimePower) :
    ordTrialityD4 q.card ^ 2 < Nat.card (Cat ⟨.twistedE6 q, LieTypeIndex.valid_twistedE6 q⟩) := by
  obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ :=
    exists_catEquiv_twistedE6 q (LieTypeIndex.valid_twistedE6 q)
  have hq : 2 ≤ q.card := by
    rw [PrimePower.card_def]
    exact le_trans q.prime_p.two_le (Nat.le_self_pow q.exponent_pos.ne' _)
  have hKfin : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  have hcard := CFSG.LieType.SeitzGeneration.ExcHighThree.card_twistedE6RootGroup_eq
    q.prime_p q.exponent_pos σ hK hσ
  rw [Nat.card_congr eK.toEquiv, hcard, ← PrimePower.card_def]
  exact ordTrialityD4_sq_lt_ordTwistedE6 hq

theorem e8LeviPiece_six_of_layer (hL : E8E6LayerInput6) (hTw : TwE6SixLines) :
    E8LeviPiece 6 := by
  refine e8LeviPiece_of_datum
    (fun q hv p hp h7 hpq he => sylowTorus_cat_E8_six hv hp h7 hpq he) ?_
  intro q hv p hp h7 hpq he
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, A, π, hπ, hker, hcen, hQ, hAel, hAc, hcomm, hdisj⟩ := hL q hv p hp h7 hpq he
  have hp3 : Nat.Coprime 3 p := (Nat.coprime_primes (by norm_num) hp).2 (by omega)
  have hcop : Nat.Coprime (Nat.card π.ker) p := Nat.Coprime.coprime_dvd_left hker hp3
  obtain ⟨K8, _, _, -, -, ⟨e8⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hfin8 : Finite (ModGL Tag.E8 K8) := CFSG.LieType.Chevalley.finite_modGL
  haveI : Finite (Cat ⟨.E8 q, hv⟩) := Finite.of_equiv _ e8.symm.toEquiv
  have hv6 := LieTypeIndex.valid_twistedE6 q
  obtain ⟨-, V0, -, -, -, -, hV0el, hV0c⟩ :=
    (sylowTorus_cat_twE6_six hv6 hp h7 hpq he).exists_torus
  have hq1 : 1 ≤ q.card := by
    rw [PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  have hnd : ¬ p ∣ q.card ^ 2 - 1 :=
    not_dvd_sq_sub_one_of_orderOf hp hq1 he (by norm_num)
  obtain ⟨E, hEel, hEc, hEHG⟩ :=
    twE6Cube_hyperGen_six hTw hv6 hp (by omega) hpq hnd he hV0el hV0c
  exact levi_datum_of_layer P A π hπ hcop hcen hQ hAel hAc hcomm hdisj E hEel hEc hEHG
    (ordTrialityD4_sq_lt_cat_twE6 q)

end E8Six



section E8SixProved



theorem e8LeviPiece_six_proved (hL : E8E6LayerInput6) : E8LeviPiece 6 := by
  exact e8LeviPiece_six_of_layer hL
    (CFSG.HardMathSupport.Lang.TwE6Step3.twE6SixLines_of_phi6 fun r hr =>
      CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.phiPlaneGenAt_neg_of_coreW hr
        (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.phi6CoreW_of_placementSome hr
          (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.phi6PlacementSome_holds r hr)
          (CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.phi6PlacementSomeThree_holds r hr)))

end E8SixProved


end CFSG.LieType.SeitzGeneration.ExcHigh
