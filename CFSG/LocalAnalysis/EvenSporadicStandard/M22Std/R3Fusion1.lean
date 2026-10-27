module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3FusionC
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Theta
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutCensusA
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutCensusPinned
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutSituation
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.E3Lift
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.E3U0
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutCentOrder
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutWreathCase
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutXbarCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutXbarLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.KEngine2
public import CFSG.Sporadic.Schreier.MathieuOddCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddKernelInvolutionFusion
public import CFSG.Walter.J1

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Fin76b
  CFSG.EvenSporadicStandard.M23Std

theorem isoInv3_e32 :
    IsoInv3 (fun Y _ S F => ∃ J : Subgroup (MulAut Y), E32Facts Y S F J) := by
  intro X Y _ _ e S F ⟨J, hJ⟩
  exact ⟨J.map (MulAut.congr e).toMonoidHom, hJ.map' e (MulAut.congr e) (congr_conj e)⟩

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
  {T₁ : Subgroup (centralizer ({z} : Set G))} {F : Subgroup (L ⧸ center L)}
  {tb : L ⧸ center L} {Q : Sylow 2 G} {x : G} {L1 : Subgroup G}

set_option quotPrecheck false in
local notation "Hc" => centralizer ({z} : Set G)

theorem OutData.T_relIndex_odd (D : OutData L z t T₁ F tb) :
    ¬ 2 ∣ (T₁.map (Subgroup.subtype Hc) : Subgroup G).relIndex Hc := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTle := D.cfg.T_le
  have hTp := D.cfg.T_pgroup
  have hT'p : IsPGroup 2 ((T₁.map (Subgroup.subtype Hc)).subgroupOf Hc) := hTp.comap_subtype
  obtain ⟨P, hP⟩ := hT'p.exists_le_sylow
  have hPG : IsPGroup 2 ((P : Subgroup ↥Hc).map (Subgroup.subtype Hc)) := P.isPGroup'.map _
  have hTP : T₁.map (Subgroup.subtype Hc) ≤ (P : Subgroup ↥Hc).map (Subgroup.subtype Hc) :=
    fun k hk => ⟨⟨k, hTle hk⟩, hP (Subgroup.mem_subgroupOf.2 hk), rfl⟩
  have hPC : (P : Subgroup ↥Hc).map (Subgroup.subtype Hc) ≤ Hc := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have heq := D.cfg.T_max _ hPC hPG hTP
  have hT'eq : (T₁.map (Subgroup.subtype Hc)).subgroupOf Hc = (P : Subgroup ↥Hc) := by
    refine le_antisymm hP fun y hy => ?_
    have hym : (y : G) ∈ (P : Subgroup ↥Hc).map (Subgroup.subtype Hc) := ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (heq hym)
  unfold Subgroup.relIndex
  rw [hT'eq]
  exact P.not_dvd_index

omit [Finite G] in
theorem card_centralizer_b_of_census {A : Subgroup G} {F1 : Subgroup G}
    (hcens : DCensus L (normalizer (F1 : Set G) ⊓ A) F1) (hLA : L ≤ A) {b : G} (hbL : b ∈ L)
    (hb2 : b * b = 1) (hbN : b ∈ normalizer (F1 : Set G)) (hbF : b ∉ F1)
    (hb1 : b ≠ 1) :
    Nat.card ↥(centralizer ({b} : Set G) ⊓ (normalizer (F1 : Set G) ⊓ A)) = 64 ∧
      Nat.card {y : G // y ∈ F1 ∧ b * y = y * b} = 4 := by
  obtain ⟨-, -, -, -, -, h0, -, hF1, hb, hout, hcov⟩ := hcens
  have hbD : b ∈ normalizer (F1 : Set G) ⊓ A := Subgroup.mem_inf.2 ⟨hbN, hLA hbL⟩
  set μ : ↥(normalizer (F1 : Set G) ⊓ A) := ⟨b, hbD⟩ with hμ
  have h1 : μ * μ = 1 := Subtype.ext (by simpa using hb2)
  have h2 : μ ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have hcl : Nat.card (centralizer ({μ} : Set ↥(normalizer (F1 : Set G) ⊓ A))) = 64 ∧
      Nat.card {y : G // y ∈ F1 ∧ b * y = y * b} = 4 := by
    rcases hcov μ h1 h2 with h | h | h | h | h
    · exact absurd ((hF1 μ).1 h).1 hbF
    · exact absurd hbL (hout μ (Or.inl h))
    · exact absurd hbL (hout μ (Or.inr (Or.inl h)))
    · exact absurd hbL (hout μ (Or.inr (Or.inr h)))
    · exact ⟨h.2.2.1, h.2.2.2⟩
  have hsub : (centralizer ({b} : Set G) ⊓ (normalizer (F1 : Set G) ⊓ A)).subgroupOf
      (normalizer (F1 : Set G) ⊓ A) = centralizer ({μ} : Set ↥(normalizer (F1 : Set G) ⊓ A)) := by
    ext w
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_singleton_iff,
      mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h, -⟩
      exact Subtype.ext h
    · intro h
      exact ⟨congrArg Subtype.val h, w.2⟩
  refine ⟨?_, hcl.2⟩
  rw [← hcl.1, ← hsub]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm

theorem OuterSituation.exists_fusion_data
    (hEng : AutSylowEngine6 (Carrier .M22))
    (hCens : AutSylowWith (fun Y _ F => AutCensus Y F) (Carrier .M22))
    (hFacts : AutSylowWith3 (fun Y _ S F => ∃ J : Subgroup (MulAut Y), E32Facts Y S F J)
      (Carrier .M22))
    (hS : OuterSituation G L z t T₁ F tb Q x L1) :
    ∃ (A : Subgroup G) (b : G), L ≤ A ∧ A ≤ centralizer ({z} : Set G) ∧ z ∉ A ∧
      A ⊔ zpowers z = centralizer ({z} : Set G) ∧ (L.subgroupOf A).index = 2 ∧
      NormQuot (Equiv.Perm (Fin 6)) (normalizer (liftSub F : Set G) ⊓ A) (liftSub F) ∧
      DCensus L (normalizer (liftSub F : Set G) ⊓ A) (liftSub F) ∧
      b ∈ L ∧ b * b = 1 ∧ b ≠ 1 ∧ b ∉ liftSub F ∧ b ∈ normalizer (liftSub F : Set G) ∧
      Nat.card {y : G // y ∈ liftSub F ∧ b * y = y * b} = 4 ∧
      ∃ k ∈ normalizer (L1 : Set G), ∃ l ∈ L1, k * z * k⁻¹ = z * b * l := by
  classical
  obtain ⟨N, Sup⟩ := OutSetup.of_kStructure hS.one hS.transitive hS.K
  have D := hS.data
  obtain ⟨A, hLA, hAH, hzA, hAz, hidx⟩ := hS.complement
  have hq : IsSporadic (L ⧸ center L) .M22 :=
    isSporadic_quotient_of_center_eq_bot D.Zbot hS.sporadic
  have hcZ : center (L ⧸ center L) = ⊥ := center_eq_bot_of_isSporadic hq
  have hout := innAut_index_dvd_two hq
  obtain ⟨e⟩ := hq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2' : orderOf z = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact D.cfg.z_sq) D.cfg.z_ne
  have hθ := thetaH_surjective_of_rel hS.std hS.cyclic D.cfg.z_cent hz2' D.cfg.cent_le hout hS.rel
  have hE6 := D.engine6 hcZ (hEng.of_mulEquiv e.symm)
  have hC' : AutCensus (L ⧸ center L) F :=
    D.property (P := fun Y _ F => AutCensus Y F) hcZ
      (AutSylowWith.of_mulEquiv AutCensus.isoInv e.symm hCens)
  have hquot := D.normQuot_A hcZ hθ hLA hAH hzA hAz hE6.s6
  have hcens := D.dCensus hcZ hθ hLA hAH hzA hAz hC'
  have hF3 : AutSylowWith3
      (fun Y _ S F => ∃ J : Subgroup (MulAut Y), E32Facts Y S F J) (L ⧸ center L) :=
    AutSylowWith3.of_mulEquiv isoInv3_e32 e.symm hFacts
  obtain ⟨J, hJ⟩ := D.property3 hcZ hF3
  obtain ⟨E, b, hET, hEc, hEs, hEcard, hzE, hT1, hT2, hbL, hb2, hb1, hbF, hbE, -⟩ :=
    D.exists_E rfl hS.z_not_sq D.W.e16.card hJ
  have hbH : b ∈ Hc := D.l_mem_H hbL
  have hbT : (⟨b, hbH⟩ : ↥Hc) ∈ T₁ := (D.mem_T_iff hbH).1 (hET hbE)
  have hTN : ∀ (g : G) (hg : g ∈ Hc), (⟨g, hg⟩ : ↥Hc) ∈ T₁ →
      g ∈ normalizer (liftSub F : Set G) := by
    intro g hg hgT
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact D.T₁_normalizes_lift hgT ha
    · intro ha
      have := D.T₁_normalizes_lift (T₁.inv_mem hgT) ha
      have e1 : (↑(⟨g, hg⟩⁻¹ : ↥Hc) : G) * (g * a * g⁻¹) * (↑(⟨g, hg⟩⁻¹ : ↥Hc) : G)⁻¹ = a := by
        show g⁻¹ * (g * a * g⁻¹) * (g⁻¹)⁻¹ = a
        group
      rwa [e1] at this
  have hbN : b ∈ normalizer (liftSub F : Set G) := hTN b hbH hbT
  have hbD : b ∈ normalizer (liftSub F : Set G) ⊓ A := Subgroup.mem_inf.2 ⟨hbN, hLA hbL⟩
  obtain ⟨hCb64, hfix4⟩ := card_centralizer_b_of_census hcens hLA hbL hb2 hbN hbF hb1
  have hzc : ∀ g ∈ A, z * g = g * z := fun g hg =>
    (mem_centralizer_singleton_iff.1 (hAH hg)).symm
  have hbz : z * b = b * z := hzc b (hLA hbL)
  have hz2 : z * z = 1 := Sup.one.z_mul_self
  have hy2 : (z * b) * (z * b) = 1 := by
    calc z * b * (z * b) = z * (b * z) * b := by group
      _ = z * (z * b) * b := by rw [← hbz]
      _ = (z * z) * (b * b) := by group
      _ = 1 := by rw [hz2, hb2, one_mul]
  have hyz : (z * b) * z = z * (z * b) := by
    calc z * b * z = z * (b * z) := by group
      _ = z * (z * b) := by rw [← hbz]
  have hXE := Sup.inf_centralizer_eq hAH hAz
  have hyX : z * b ∈ normalizer (L1 : Set G) := by
    have : z * b ∈ zpowers z ⊔ (normalizer (liftSub F : Set G) ⊓ A) :=
      Subgroup.mul_mem_sup (Subgroup.mem_zpowers z) hbD
    rw [← hXE] at this
    exact (Subgroup.mem_inf.1 this).1
  have hyc : IsConj z (z * b) := hS.isConj_z_mul hbL hb2 hb1
  have hCG := hS.card_centralizer_z
  have hU16 := Sup.sixteen_le_card_centralizer_L1 hyX hy2
  have hzF : ∀ f ∈ liftSub F, z * f = f * z := fun f hf =>
    Sup.one.z_comm f (Sup.one.F_le hf)
  have hW : Nat.card ↥(centralizer ({z * b} : Set G) ⊓ liftSub F) = 4 := by
    rw [← hfix4]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
    rw [Subgroup.mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      have h3 : w * z = z * w := (hzF w h2).symm
      have h4 : z * (w * b) = z * (b * w) := by
        calc z * (w * b) = z * w * b := by group
          _ = w * z * b := by rw [← h3]
          _ = w * (z * b) := by group
          _ = (z * b) * w := h1
          _ = z * (b * w) := by group
      exact (mul_left_cancel h4).symm
    · rintro ⟨h2, h1⟩
      refine ⟨?_, h2⟩
      have h3 : w * z = z * w := (hzF w h2).symm
      calc w * (z * b) = (w * z) * b := by group
        _ = z * w * b := by rw [h3]
        _ = z * (w * b) := by group
        _ = z * (b * w) := by rw [← h1]
        _ = (z * b) * w := by group
  set Cb : Subgroup G := centralizer ({b} : Set G) ⊓ (normalizer (liftSub F : Set G) ⊓ A)
    with hCbdef
  have hCbA : ∀ g ∈ Cb, g ∈ A := fun g hg => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).2).2
  have hzCb : z ∉ Cb := fun h => hzA (hCbA z h)
  have hzNCb : ∀ a, a ∈ Cb ↔ z * a * z⁻¹ ∈ Cb :=
    normalizes_of_centralizes fun a ha => hzc a (hCbA a ha)
  have hQcard : Nat.card ↥(Cb ⊔ zpowers z) = 128 := by
    rw [card_sup_zpowers_invol hz2 hzNCb hzCb, hCb64]
  have hQp : IsPGroup 2 ↥(Cb ⊔ zpowers z) := IsPGroup.of_card (n := 7) (by rw [hQcard]; norm_num)
  have hzH : z ∈ Hc := mem_centralizer_singleton_iff.2 rfl
  have hQz : Cb ⊔ zpowers z ≤ Hc :=
    sup_le (fun g hg => hAH (hCbA g hg)) (Subgroup.zpowers_le.2 hzH)
  have hCbE : ∀ g ∈ Cb, g ∈ normalizer (L1 : Set G) := by
    intro g hg
    have : g ∈ zpowers z ⊔ (normalizer (liftSub F : Set G) ⊓ A) :=
      Subgroup.mem_sup_right (Subgroup.mem_inf.1 hg).2
    rw [← hXE] at this
    exact (Subgroup.mem_inf.1 this).1
  have hQN : Cb ⊔ zpowers z ≤ normalizer (L1 : Set G) :=
    sup_le hCbE (Subgroup.zpowers_le.2 Sup.zX.2)
  have hQy : Cb ⊔ zpowers z ≤ centralizer ({z * b} : Set G) := by
    refine sup_le (fun g hg => ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [mem_centralizer_singleton_iff]
      have hgb : g * b = b * g := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).1
      have hgz : g * z = z * g := (hzc g (hCbA g hg)).symm
      calc g * (z * b) = (g * z) * b := by group
        _ = z * g * b := by rw [hgz]
        _ = z * (g * b) := by group
        _ = z * (b * g) := by rw [hgb]
        _ = (z * b) * g := by group
    · rw [mem_centralizer_singleton_iff]
      exact hyz.symm
  have hzNF := normalizes_of_centralizes hzF
  have hzNFm : z ∈ normalizer (liftSub F : Set G) := Subgroup.mem_normalizer_iff.2 hzNF
  have hEQ : E ≤ Cb ⊔ zpowers z := by
    intro e he
    have heH : e ∈ Hc := D.cfg.T_le (hET he)
    have heT : (⟨e, heH⟩ : ↥Hc) ∈ T₁ := (D.mem_T_iff heH).1 (hET he)
    have heN : e ∈ normalizer (liftSub F : Set G) := hTN e heH heT
    have hzcA : zpowers z ≤ centralizer (A : Set G) :=
      Subgroup.zpowers_le.2 (mem_centralizer_iff.2 fun a ha => (hzc a ha).symm)
    have heA : e ∈ A ⊔ zpowers z := by rw [hAz]; exact heH
    obtain ⟨a, haA, w, hw, hae⟩ := exists_mul_of_mem_sup_of_le_centralizer hzcA heA
    have haeq : a = e * w⁻¹ := eq_mul_inv_of_mul_eq hae.symm
    have hwN : w ∈ normalizer (liftSub F : Set G) :=
      Subgroup.zpowers_le.2 hzNFm hw
    have haN : a ∈ normalizer (liftSub F : Set G) := by
      rw [haeq]
      exact Subgroup.mul_mem _ heN (Subgroup.inv_mem _ hwN)
    have hwb : w * b = b * w := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      exact ((Commute.zpow_left (show Commute z b from hbz) n)).eq
    have hab : a * b = b * a := by
      have heb : e * b = b * e := hEc e he b hbE
      rw [haeq]
      calc e * w⁻¹ * b = e * (w⁻¹ * b) := by group
        _ = e * (b * w⁻¹) := by
          rw [show w⁻¹ * b = b * w⁻¹ by
            calc w⁻¹ * b = w⁻¹ * (b * w) * w⁻¹ := by group
              _ = w⁻¹ * (w * b) * w⁻¹ := by rw [hwb]
              _ = b * w⁻¹ := by group]
        _ = (e * b) * w⁻¹ := by group
        _ = (b * e) * w⁻¹ := by rw [heb]
        _ = b * (e * w⁻¹) := by group
    have haCb : a ∈ Cb := Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 hab,
      Subgroup.mem_inf.2 ⟨haN, haA⟩⟩
    rw [hae]
    exact Subgroup.mul_mem_sup haCb hw
  have hKp : IsPGroup 2 ↥(L1 ⊔ zpowers z) := by
    have := hS.K.K_pgroup
    rwa [hS.K.K_eq] at this
  have hKs : ¬ 2 ∣ (L1 ⊔ zpowers z).relIndex (centralizer ((liftSub F : Subgroup G) : Set G)) := by
    have := hS.K.K_sylow
    rwa [hS.K.K_eq] at this
  obtain ⟨k, hk, l, hl, hkl⟩ := exists_normalizer_conj_of_fusion (T := T₁.map (Subgroup.subtype Hc))
    (E := E) (Q := Cb ⊔ zpowers z) (F := liftSub F) (L1 := L1) (z := z) (y := z * b)
    Sup.L1_comm Sup.L1_sq Sup.L1_card hz2 (Subgroup.mem_normalizer_iff.1 Sup.zX.2)
    hS.K.z_not_mem Sup.F_le Sup.one.F_card hzF Sup.L1_cz hKp hKs hS.K.not_conj Sup.one.fused
    hy2 hyz (Subgroup.mem_normalizer_iff.1 hyX) hyc hCG hU16 hW D.cfg.T_le D.cfg.T_pgroup
    D.T_relIndex_odd hEc hEs hEcard hzE (E.mul_mem hzE hbE) hT1 hT2 hQN hQy hQz hEQ hQp
    (by rw [hQcard])
  exact ⟨A, b, hLA, hAH, hzA, hAz, hidx, hquot, hcens, hbL, hb2, hb1, hbF, hbN, hfix4, k, hk, l, hl,
    hkl⟩

end CFSG.EvenSporadicStandard.M22Std
