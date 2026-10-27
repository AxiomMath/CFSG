module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourLTwo
public import CFSG.CGT.PushingUpLit.CGT6.SixFourStd
public import CFSG.CGT.PushingUpLit.CGT6.SixFourTen

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree CFSG.CGT.PushingUpLit.EightOneRel
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin CFSG.Quasithin.G6
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL StatedLieTag)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

@[expose, reducible] def jBar (R : Subgroup G) [R.Normal] (T : Sylow 2 G) : Subgroup (G ⧸ R) :=
  (jIn (T : Subgroup G)).map (QuotientGroup.mk' R)

@[expose, reducible] def jBarClosure (R : Subgroup G) [R.Normal] (T : Sylow 2 G) :
    Subgroup (G ⧸ R) :=
  Subgroup.normalClosure ((jBar R T : Subgroup (G ⧸ R)) : Set (G ⧸ R))

variable [Finite G]

theorem eight_sl_ident {Y R : Subgroup G} {T : Sylow 2 G} [R.Normal] (h : EightCtx Y T R) {n : ℕ}
    (hn : 1 ≤ n) (hnat : IsNaturalSLTwoModule ↥Y n)
    (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt) (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt)
    (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification) :
    2 ≤ n ∧ IsSimpleGroup (↥(jBarClosure R T) ⧸ Subgroup.center ↥(jBarClosure R T)) ∧
      CFSG.CGT.Timmesfeld75.ListGroup
        (↥(jBarClosure R T) ⧸ Subgroup.center ↥(jBarClosure R T)) ∧
      CFSG.CGT.Timmesfeld75.StdPair (↥(jBarClosure R T) ⧸ Subgroup.center ↥(jBarClosure R T))
        (((jBar R T).subgroupOf (jBarClosure R T)).map
          (QuotientGroup.mk' (Subgroup.center ↥(jBarClosure R T)))) ∧
      Nat.card (((jBar R T).subgroupOf (jBarClosure R T)).map
          (QuotientGroup.mk' (Subgroup.center ↥(jBarClosure R T)))) = 2 ^ n ∧
      commutator ↥(jBarClosure R T) = ⊤ ∧
      ∃ (ρ : ↥Y →* ↥(jBarClosure R T))
        (ι' : (↥Y ⧸ pCore 2 ↥Y) →* ↥(jBarClosure R T) ⧸ Subgroup.center ↥(jBarClosure R T)),
        (∀ z : ↥Y, ((ρ z : ↥(jBarClosure R T)) : G ⧸ R) = QuotientGroup.mk' R z) ∧
        (∀ y : ↥Y, ι' (QuotientGroup.mk y) =
          QuotientGroup.mk' (Subgroup.center ↥(jBarClosure R T)) (ρ y)) ∧
        Function.Injective ι' ∧
        CFSG.CGT.Timmesfeld75.IsWC (((jBar R T).subgroupOf (jBarClosure R T)).map
          (QuotientGroup.mk' (Subgroup.center ↥(jBarClosure R T)))) ∧
        Odd (Nat.card (Subgroup.center ↥(jBarClosure R T))) := by
  classical
  obtain ⟨A, hA, hnot, hJA, hJY, hrel, hcomm, hsq, hbot, hTI, hCom⟩ := eight_sl_nine h hn hnat
  have hn2 : 2 ≤ n := h.two_le_of_SL hn hnat
  have hq := h.quasisimple_of_SL hn hnat
  have hCB := eight_sl_corB h hn hnat
  let π : G →* G ⧸ R := QuotientGroup.mk' R
  set J : Subgroup G := jIn (T : Subgroup G) with hJ
  set Jb : Subgroup (G ⧸ R) := jBar R T with hJb
  set K : Subgroup (G ⧸ R) := jBarClosure R T with hK
  have hKn : K.Normal := Subgroup.normalClosure_normal
  have hJbK : Jb ≤ K := Subgroup.le_normalClosure
  have hWC : CFSG.CGT.Timmesfeld75.IsWC Jb := CFSG.CGT.Timmesfeld75.isWC_of_corBHyp hCB
  have hTK := CFSG.CGT.Timmesfeld75.isWC_subgroupOf_normalClosure hWC
  have hKtop := CFSG.CGT.Timmesfeld75.normalClosure_subgroupOf_eq_top hWC
  have hO2K : ∀ N : Subgroup ↥K, N.Normal → IsPGroup 2 N → N = ⊥ := fun N hN hN2 =>
    CFSG.CGT.Timmesfeld75.eq_bot_of_normal_isPGroup_of_normal K (eight_O2_quot h) N hN hN2
  have hAJ : A ≤ J := by
    rw [hJ, jIn_eq_thompsonJ]
    exact le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian (T : Subgroup G) A) => A) A hA
  have hcardJb : Nat.card Jb = 2 ^ n := by
    rw [hJb, jBar, (card_map_jIn_eq hAJ hJA).2, hrel, GaloisField.card 2 n (by omega)]
  have hcardT' : Nat.card (Jb.subgroupOf K) = 2 ^ n := by
    rw [← hcardJb]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJbK).toEquiv
  have h4 : 4 ≤ Nat.card (Jb.subgroupOf K) := by
    rw [hcardT']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨hsimple, hlist, hstd, hperf, hZodd⟩ :=
    std_of_simpleCase hS h215 hL hTK hKtop hO2K h4
  have hcardTh : Nat.card ((Jb.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))) =
      2 ^ n := by
    rw [card_map_central_odd_eq hTK.1 (Subgroup.center ↥K) hZodd, hcardT']
  have hnat' := hnat
  obtain ⟨φ, -⟩ := hnat'
  have hOY : oTwoIn Y ≤ R := h.le_R_of_le_centralizerModCore
    (ThreeFromEight.isPGroup_oTwoIn Y) (EightOneWindow.oTwoIn_le_centralizerModCore Y)
  have hYK : ∀ y ∈ Y, π y ∈ K := fun y hy => (eight_sl_Y_le h hn hnat K hJbK) hy
  let ρ : ↥Y →* ↥K := (π.comp Y.subtype).codRestrict K (fun y => hYK y y.2)
  have hρval : ∀ z : ↥Y, ((ρ z : ↥K) : G ⧸ R) = π z := fun z => rfl
  let ι : ↥Y →* ↥K ⧸ Subgroup.center ↥K := (QuotientGroup.mk' (Subgroup.center ↥K)).comp ρ
  have hιker : pCore 2 ↥Y ≤ ι.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    have hyR : (y : G) ∈ R := hOY ⟨y, hy, rfl⟩
    have hπy : π y = 1 := (QuotientGroup.eq_one_iff (y : G)).mpr hyR
    have hρ1 : ρ y = 1 := Subtype.ext hπy
    show QuotientGroup.mk' (Subgroup.center ↥K) (ρ y) = 1
    rw [hρ1, map_one]
  let ι' : (↥Y ⧸ pCore 2 ↥Y) →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.lift (pCore 2 ↥Y) ι hιker
  have hι'mk : ∀ y : ↥Y, ι' (QuotientGroup.mk y) = QuotientGroup.mk' (Subgroup.center ↥K) (ρ y) :=
    fun y => rfl
  have hι'inj : Function.Injective ι' := by
    rw [injective_iff_map_eq_one]
    intro q hq1
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hzy : ρ y ∈ Subgroup.center ↥K := (QuotientGroup.eq_one_iff (ρ y)).mp hq1
    refine eq_one_of_central_SL2 φ (fun q' => ?_)
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective q'
    have hc : ρ y' * ρ y = ρ y * ρ y' := Subgroup.mem_center_iff.mp hzy (ρ y')
    have hπ : π (y' * y) = π (y * y') := by
      have := congrArg Subtype.val hc
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hρval, hρval] at this
      rw [map_mul, map_mul]
      exact this
    have hw : (y' * y)⁻¹ * (y * y') ∈ pCore 2 ↥Y :=
      h.mem_pCore_of_mem_R _ (QuotientGroup.eq.mp hπ)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact QuotientGroup.eq.mpr hw
  have hWCb : CFSG.CGT.Timmesfeld75.IsWC ((Jb.subgroupOf K).map
      (QuotientGroup.mk' (Subgroup.center ↥K))) :=
    hTK.map_quotient_central_odd (Subgroup.center ↥K) le_rfl hZodd
  exact ⟨hn2, hsimple, hlist, hstd, hcardTh, hperf, ρ, ι', hρval, hι'mk, hι'inj, hWCb, hZodd⟩

theorem eight_sl_card_dvd {Y R : Subgroup G} {T : Sylow 2 G} [R.Normal] (h : EightCtx Y T R) {n : ℕ}
    (hn : 1 ≤ n) (hnat : IsNaturalSLTwoModule ↥Y n)
    (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt) (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt)
    (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ∣
      Nat.card (↥(jBarClosure R T) ⧸ Subgroup.center ↥(jBarClosure R T)) := by
  obtain ⟨hn2, -, -, -, -, -, ρ, ι', -, -, hinj, -⟩ := eight_sl_ident h hn hnat hS h215 hL
  have hnat' := hnat
  obtain ⟨φ, -⟩ := hnat'
  have hcardQ : Nat.card (↥Y ⧸ pCore 2 ↥Y) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr φ.toEquiv, card_SL2_eq, GaloisField.card 2 n (by omega)]
  rw [← hcardQ]
  exact Subgroup.card_dvd_of_injective ι' hinj

theorem eight_sl_normal_of_psl2 {Y R : Subgroup G} {T : Sylow 2 G} [R.Normal] (h : EightCtx Y T R)
    {n : ℕ} (hn : 1 ≤ n) (hnat : IsNaturalSLTwoModule ↥Y n)
    (hS : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt) (h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt)
    (hL : CFSG.CGT.Timmesfeld75.ListWCIdentification) {f : ℕ}
    (hf : StatedClassicalModel
      (↥(jBarClosure R T) ⧸ Subgroup.center ↥(jBarClosure R T)) StatedLieTag.PSL 2 2 f) :
    Y.Normal := by
  classical
  obtain ⟨hn2, hsimple, hlist, hstd, hcardTh, hperf, ρ, ι', hρval, hι'mk, hι'inj, -⟩ :=
    eight_sl_ident h hn hnat hS h215 hL
  let π : G →* G ⧸ R := QuotientGroup.mk' R
  have hKn : (jBarClosure R T).Normal := Subgroup.normalClosure_normal
  generalize hK : jBarClosure R T = K at *
  have hTcard := (hstd.of_psl2 hf).1
  have hfn : f = n := by
    have : 2 ^ f = 2 ^ n := hTcard.symm.trans hcardTh
    exact Nat.pow_right_injective (le_refl 2) this
  obtain ⟨-, K', hK'f, hK'fin, hK'c, ⟨e⟩⟩ := hf
  have hcardΛ : Nat.card (↥K ⧸ Subgroup.center ↥K) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, card_psl2_two_pow (by omega) hK'c, hfn]
  have hnat' := hnat
  obtain ⟨φ, -⟩ := hnat'
  have hcardQ : Nat.card (↥Y ⧸ pCore 2 ↥Y) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr φ.toEquiv, card_SL2_eq, GaloisField.card 2 n (by omega)]
  have hι'bij : Function.Bijective ι' :=
    hι'inj.bijective_of_nat_card_le (hcardΛ.le.trans hcardQ.ge)
  have hdec : ∀ k : ↥K, ∃ y : ↥Y, ∃ z ∈ Subgroup.center ↥K, k = z * ρ y := by
    intro k
    obtain ⟨q, hq⟩ := hι'bij.2 (QuotientGroup.mk' (Subgroup.center ↥K) k)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hq' : QuotientGroup.mk' (Subgroup.center ↥K) (ρ y) =
        QuotientGroup.mk' (Subgroup.center ↥K) k := by rw [← hι'mk]; exact hq
    have hz : (ρ y)⁻¹ * k ∈ Subgroup.center ↥K := QuotientGroup.eq.mp hq'
    refine ⟨y, (ρ y)⁻¹ * k, hz, ?_⟩
    have hc := Subgroup.mem_center_iff.mp hz (ρ y)
    calc k = ρ y * ((ρ y)⁻¹ * k) := by group
      _ = ((ρ y)⁻¹ * k) * ρ y := hc
  have hρsurj : Function.Surjective ρ := by
    have hle : commutator ↥K ≤ ρ.range := by
      rw [commutator_def, Subgroup.commutator_le]
      intro k₁ _ k₂ _
      obtain ⟨y₁, z₁, hz₁, rfl⟩ := hdec k₁
      obtain ⟨y₂, z₂, hz₂, rfl⟩ := hdec k₂
      rw [commutatorElement_central_mul hz₁ hz₂, ← map_commutatorElement]
      exact ⟨_, rfl⟩
    rw [hperf] at hle
    intro k
    exact hle (Subgroup.mem_top k)
  refine ⟨fun y hy g => ?_⟩
  have hg : g ∈ Subgroup.normalizer (Y : Set G) := by
    refine mem_normalizer_of_conj_le_sup h.hNo h.hR2 h.R_le_normalizer_Y (fun y' hy' => ?_)
    have hYK : π y' ∈ K := by
      have h1 := (ρ ⟨y', hy'⟩).2
      rw [hρval ⟨y', hy'⟩] at h1
      exact h1
    have hk : π (g * y' * g⁻¹) ∈ K := by
      have := hKn.conj_mem (π y') hYK (π g)
      simpa [map_mul, map_inv] using this
    obtain ⟨y'', hy''⟩ := hρsurj ⟨π (g * y' * g⁻¹), hk⟩
    have hπeq : π (y'' : G) = π (g * y' * g⁻¹) := by
      rw [← hρval, hy'']
    have hr : (y'' : G)⁻¹ * (g * y' * g⁻¹) ∈ R := QuotientGroup.eq.mp hπeq
    have hdecomp : g * y' * g⁻¹ = (y'' : G) * ((y'' : G)⁻¹ * (g * y' * g⁻¹)) := by group
    rw [hdecomp]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left y''.2) (Subgroup.mem_sup_right hr)
  exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy

end CFSG.CGT.PushingUpLit.CGT6
