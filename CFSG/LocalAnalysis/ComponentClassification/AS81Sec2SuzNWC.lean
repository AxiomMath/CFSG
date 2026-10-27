module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2End
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2LocalQ
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2P
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQO
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Cz

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.RankThree.OrthogonalInvolutions
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def SuzL34Data {G : Type} [Group G] (z : G) : Prop :=
  ∃ A R : Subgroup G, standardComponentIsStandard A ∧ TypeL34 (rankTwoQuot A) ∧
    Odd (Nat.card (center A)) ∧ IsSylowOf 2 R (centralizer (A : Set G)) ∧ IsElemAbelian 2 R ∧
    Nat.card R = 4 ∧ z ∈ A ∧
    ∀ r ∈ R, r ≠ 1 → centralizer ({r} : Set G) ≤ normalizer (A : Set G)

@[expose] def SuzRecognition' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : LargeExtraspecial.Setting G),
    S.width = 3 → (¬ ∃ U : Subgroup G, U ≤ S.QG ∧ IsElemAbelian 2 U ∧ Nat.card U = 16) →
    S.Mbar.map S.O.subtype = timmesfeldOmega S.q →
    (∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z) → SuzL34Data S.z →
    IsSporadic G .Suz

namespace Sec2Q

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F T₀ Q : Subgroup G}
  {u y z : G}

@[expose] def nwcSetting (h24 : Step24) (h26 : Step26) (h212 : Step212) (h216 : Step216)
    (hQ : Sec2Q G A R g E F T₀ Q u y z) (hO : AS76b.oddCoreIn (centralizer ({z} : Set G)) = ⊥)
    (hCN : centralizer ({z} : Set G) ≤ normalizer (Q : Set G)) : LargeExtraspecial.Setting G where
  z := z
  orderOf_z := hQ.order
  Q := Q.subgroupOf (centralizer ({z} : Set G))
  normal := (normal_subgroupOf_iff_le_normalizer hQ.Q_le_centralizer).mpr hCN
  extraspecial := CFSG.RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv
    (subgroupOfEquivOfLe hQ.Q_le_centralizer).symm hQ.q8.1
  centralizer_le := hQ.centralizer_subgroupOf_le h24 h26 h212 h216 hO hCN
  le_of_normal := fun P hPn hP2 x hx =>
    hQ.le_Q_of_isPGroup h24 h26 h212 h216 hO hCN (hP2.map _) (map_subtype_le P)
      (Sec2.le_normalizer_map_subtype hPn) ⟨x, hx, rfl⟩

theorem exists_conj_mem_Q_ne (h212 : Step212) (hQ : Sec2Q G A R g E F T₀ Q u y z) :
    ∃ n : G, n * z * n⁻¹ ∈ Q ∧ n * z * n⁻¹ ≠ z := by
  have hS := hQ.data.setting
  have hF := hS.frame
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hF.sylowR.isPGroup hS.odd
  have hEA16 : Nat.card (E ⊓ A : Subgroup G) = 16 := by
    have := card_eq_card_inf_mul hRA hF.R_le_E hF.E_le hRA1
    rw [hF.cardE, hF.cardR] at this
    omega
  have hzZ := hQ.z_mem_Z h212
  rw [hF.sec2Z_eq] at hzZ
  have hzEA : z ∈ E ⊓ A := ⟨hzZ.1.1, hzZ.2⟩
  have hz1 : z ≠ 1 := fun h => by
    have := hQ.order
    rw [h, orderOf_one] at this
    omega
  have h8 : Nat.card (E ⊓ A ⊓ Q : Subgroup G) = 8 := by
    have h := relIndex_mul_card (E ⊓ A ⊓ Q) (E ⊓ A)
    rw [hQ.index, show E ⊓ A ⊓ Q ⊓ (E ⊓ A) = E ⊓ A ⊓ Q from inf_eq_left.mpr inf_le_left,
      hEA16] at h
    omega
  have hnle : ¬ (E ⊓ A ⊓ Q ≤ zpowers z) := fun hle => by
    have h := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hQ.order, h8] at h
    omega
  obtain ⟨w, hw, hwz⟩ := Set.not_subset.mp hnle
  have hw1 : w ≠ 1 := fun h => hwz (h ▸ one_mem _)
  have hwne : w ≠ z := fun h => hwz (h ▸ mem_zpowers z)
  obtain ⟨n, -, hn⟩ := exists_conj_eq_of_card_sixteen hF.base.hyp.standard.1 hS.type hS.odd
    inf_le_right (AS76b.IsElemAbelian.mono hF.elemE inf_le_left) hEA16 hzEA
    (mem_inf.mp hw).1 hz1 hw1
  exact ⟨n, hn ▸ (mem_inf.mp hw).2, hn ▸ hwne⟩

theorem suzL34Data (h212 : Step212) (hQ : Sec2Q G A R g E F T₀ Q u y z) : SuzL34Data z := by
  have hS := hQ.data.setting
  have hF := hS.frame
  have hstd := hF.base.hyp.standard
  have hzZ := hQ.z_mem_Z h212
  rw [hF.sec2Z_eq] at hzZ
  refine ⟨A, R, hstd, hS.type, hS.odd, hF.sylowR, hF.elemR, hF.cardR, hzZ.2,
    fun r hr hr1 c hc => ?_⟩
  rw [← AS76b.normalizer_centralizer_eq hstd]
  exact RankTwoSporadic.mem_normalizer_of_commute_of_tightlyEmbedded
    (AS76b.tightlyEmbedded_centralizer hstd) (hF.sylowR.le hr) hr1 (hF.elemR.2 r hr)
    (mem_centralizer_singleton_iff.mp hc)

theorem isSporadic_suz' [IsSimpleGroup G] (h24 : Step24) (h26 : Step26) (h212 : Step212)
    (h216 : Step216) (hSuz : SuzRecognition') (hQ : Sec2Q G A R g E F T₀ Q u y z)
    (hO : AS76b.oddCoreIn (centralizer ({z} : Set G)) = ⊥)
    (hCN : centralizer ({z} : Set G) ≤ normalizer (Q : Set G)) : IsSporadic G .Suz := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQC := hQ.Q_le_centralizer
  let S := hQ.nwcSetting h24 h26 h212 h216 hO hCN
  have hQS : Nat.card S.Q = Nat.card Q := Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv
  have hw3 : S.width = 3 := S.width_eq (by rw [hQS, hQ.q8.2.1])
  have hQG : S.QG = Q := by
    change (Q.subgroupOf (centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype = Q
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hQC]
  have hnoE : ¬ ∃ U : Subgroup G, U ≤ S.QG ∧ IsElemAbelian 2 U ∧ Nat.card U = 16 := by
    rw [hQG]
    exact hQ.q8.2.2
  obtain ⟨ψ, ρ, -, -, -, -, -, hrange, hρker⟩ := h216 G A R g E F T₀ Q u y z hQ
  rw [hQ.oddCoreIn_M_inf_centralizer_eq_bot hO hCN, sup_bot_eq] at hρker
  have hQM : Q ≤ sec2M Q (sec2T E T₀) := hQ.le.trans (Sec2.le_sec2M Q _)
  have hMC : sec2M Q (sec2T E T₀) ≤ centralizer ({z} : Set G) :=
    hQ.M_le_normalizer.trans hQ.normalizer_le_centralizer
  have h1 : Nat.card (sec2M Q (sec2T E T₀)) =
      Nat.card Q * Nat.card (timmesfeldOmega qMinus) := by
    have h := Sec2.card_eq_card_inf_ker_mul_card_map' ρ ⊤
    rw [top_inf_eq, ← MonoidHom.range_eq_map, hrange, hρker, Subgroup.card_top,
      Nat.card_congr (subgroupOfEquivOfLe hQM).toEquiv] at h
    exact h
  have h2 : Nat.card (sec2M Q (sec2T E T₀)) =
      Nat.card Q * Nat.card (((sec2M Q (sec2T E T₀)).subgroupOf S.M).map S.ρ) := by
    have h := Sec2.card_eq_card_inf_ker_mul_card_map' S.ρ
      ((sec2M Q (sec2T E T₀)).subgroupOf S.M)
    have e : (sec2M Q (sec2T E T₀)).subgroupOf S.M ⊓ S.ρ.ker = S.Q := by
      rw [S.ker_ρ]
      exact inf_eq_right.mpr fun x hx => hQM hx
    have hMS : Nat.card ((sec2M Q (sec2T E T₀)).subgroupOf S.M) =
        Nat.card (sec2M Q (sec2T E T₀)) := Nat.card_congr (subgroupOfEquivOfLe hMC).toEquiv
    rw [e, hQS, hMS] at h
    exact h
  have h3 : Nat.card (timmesfeldOmega qMinus) ∣ Nat.card S.Mbar := by
    have h4 : Nat.card (((sec2M Q (sec2T E T₀)).subgroupOf S.M).map S.ρ) =
        Nat.card (timmesfeldOmega qMinus) :=
      Nat.eq_of_mul_eq_mul_left Nat.card_pos (h2.symm.trans h1)
    rw [← h4]
    exact Subgroup.card_dvd_of_le (Subgroup.map_le_range _ _)
  have hMbar : S.Mbar.map S.O.subtype = timmesfeldOmega S.q := by
    have hnd := Sec2Omega.qMinusForm_nondegenerate
    have e := LargeExtraspecial.s12_timmesfeldOmega_eq Sec2Omega.qMinusForm hnd
    rw [Sec2Omega.coe_qMinusForm] at e
    refine Sec2.Mbar_map_eq_of_dvd S (by omega) hnd (by rw [Sec2Omega.finrank_fin_six, hw3]) ?_
    rw [← e]
    exact h3
  obtain ⟨n, hnQ, hnz⟩ := hQ.exists_conj_mem_Q_ne h212
  exact hSuz G S hw3 hnoE hMbar ⟨n, by rw [hQG]; exact hnQ, hnz⟩ (hQ.suzL34Data h212)

end Sec2Q

theorem sec2SuzXR_of_steps''
    (h18 : Step18) (h110 : Step110) (h21 : Step21) (h24 : Step24) (h25 : Step25) (h26 : Step26)
    (h27 : Step27) (h212 : Step212) (h216 : Step216) (h218 : Step218) (h219 : Step219)
    (hGold : GoldschmidtQO) (hSuz : SuzRecognition') : Sec2SuzXR := by
  have hLQ := sec2LocalQ_of h21 h24 h25 h26 h212
  intro G _ _ A R g E F hF hL ho hb htop
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : Sec2Setting G A R g E F := ⟨hF, hL, ho, hb⟩
  obtain ⟨⟨u, y, huy⟩, -⟩ := h27 G A R g E F hS
  obtain ⟨⟨T₀, hT₀, hT₀syl⟩, -⟩ := h212 G A R g E F hS
  have hD : Sec2Data G A R g E F T₀ u y := ⟨hS, hT₀, hT₀syl, huy⟩
  obtain ⟨Q, hq8, hQT, hyQ, huniq, hQHT, hHTQ, hidx⟩ := hLQ G A R g E F T₀ u y hD
  obtain ⟨z, hz, hcen⟩ := hD.exists_centerIn_eq h24 h212
  have hQ : Sec2Q G A R g E F T₀ Q u y z :=
    ⟨hD, hz, hcen, hq8, hQT, hyQ, huniq, hQHT, hHTQ, hidx⟩
  have hXtop := hD.rankTwoX_eq_top h212 htop
  obtain ⟨hXF, hXsimple⟩ := AS76b.asc08Lemma34 G A hF.base.hyp31
  have hXs : IsSimpleGroup ↥(rankTwoX A) := by
    show IsSimpleGroup ↥(normalClosure (A : Set G))
    rw [hXF]
    exact hXsimple
  let e : ↥(rankTwoX A) ≃* G := (MulEquiv.subgroupCongr hXtop).trans Subgroup.topEquiv
  have : IsSimpleGroup G := e.isSimpleGroup_congr.mp hXs
  have h2c : ∃ S : Sylow 2 G, z ∈ (S : Subgroup G) ∧
      (S : Subgroup G) ≤ centralizer ({z} : Set G) := by
    have hc := (hQ.sylow_T₀ h212).card_eq
    rw [Subgroup.card_top] at hc
    refine ⟨Sylow.ofCard T₀ hc, ?_, ?_⟩
    · rw [Sylow.coe_ofCard]
      exact hQ.T_le_T₀ hQ.z_mem_T
    · rw [Sylow.coe_ofCard]
      exact hQ.T₀_le_centralizer h212
  have hzE : z ∈ E := by
    have h : z ∈ centerIn (E ⊔ F) := (hQ.z_mem_Z h212).2
    rw [← hF.inf_eq_center] at h
    exact h.1
  have hO := h18 G A R g E F hF hL hb z hzE hz h2c (hQ.not_mem_rightConjugate h21 h212)
  have hQT₀ : Q ≤ T₀ := hQ.le.trans hQ.T_le_T₀
  have hT₀N := hQ.T₀_le_normalizer_Q h26 h212
  have hHyp : Hyp19 G z Q T₀ :=
    ⟨hz, h2c, hQ.Q_le_centralizer, hq8.1, Or.inl hq8.2.1,
      hQ.sylow_zpowers_centralizer h24 h26 h212 h216, hQ.sylow_T₀_centralizer h212, hQT₀,
      fun c hc hcT => h219 G A R g E F T₀ Q u y z hQ c hc (hcT.trans hT₀N),
      (h218 G A R g E F T₀ Q u y z hQ)⟩
  have hstrong := h110 G z Q T₀ hHyp
  have hCN := hGold G z Q T₀ (sec2M Q (sec2T E T₀)) hz (hQ.sylow_T₀_centralizer h212) hQT₀
    hQ.z_mem_Q (Or.inl hq8.2.1)
    (fun a ha b hb => commutator_mem_of_extraspecial hq8.1 hQ.centerIn_Q ha hb) hstrong
    (hQ.M_le_normalizer.trans hQ.normalizer_le_centralizer) hQ.M_le_normalizer
    (hQ.derived_acts_nontrivially h216)
  rw [hO, sup_bot_eq] at hCN
  obtain ⟨f⟩ := hQ.isSporadic_suz' h24 h26 h212 h216 hSuz hO hCN
  exact ⟨e.trans f⟩

end CFSG.ComponentClassification.AS81
