module

public import CFSG.ClassicalInvolution.RouteD.TWT9Case
public import CFSG.ClassicalInvolution.RouteD.TWU3Group
public import CFSG.ClassicalInvolution.RouteD.TWU4Twin
public import CFSG.ClassicalInvolution.RouteD.TWU4Z
public import CFSG.ClassicalInvolution.RouteD.TWU5Class
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
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.RouteD.TWU

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Asc77
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.RouteD.TWT9
open QuadraticMap

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

section Main

variable {p f : ℕ} [Fact p.Prime]



theorem twinYPatternAtL_td4_one_proved (h1 : p ^ f % 4 = 1) :
    TwinYPatternAtL p f .POmegaMinus 4
      (fun Ω K β t => PartnerPatternMinus p f 4 Ω K β t) := by
  intro G _ _ _ hnab K z S hshape T e J J' w e' β s hcfg hP1 hP1' hty hty'
  classical
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simpa using S.five
    · exact h
  have hcen : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f S.odd
  have hadm : StatedLieAdmissible .POmegaMinus 4 p f := ⟨Fact.out, hf, by show 4 ≤ 4; omega⟩
  obtain ⟨c⟩ := TCtx.nonempty_minus (by norm_num : 4 ≤ 4) S.odd S.five S.inClass S.exact hKΩ
    S.cls S.p1 hshape
  have cq := Exotic.centralQuot_minus c.hp2 c.hq hadm
  have hKJ : Commutes K J := hcfg.twin.comm_K J hcfg.mem_J hcfg.J_ne_K
  have hKJ' : Commutes K J' := hcfg.twin.comm_K J' hcfg.mem_J' hcfg.J'_ne_K
  have hKu : K ∈ centralizingMembers (𝒞 K) {e'.u} := e'.mem_centralizingMembers_u hKΩ hKJ hKJ'
  have hTJ : Commutes T J := hcfg.twin.comm_T J hcfg.mem_J hcfg.J_ne_T
  have hTJ' : Commutes T J' := hcfg.twin.comm_T J' hcfg.mem_J' hcfg.J'_ne_T
  have hTu : T ∈ centralizingMembers (𝒞 K) {e'.u} :=
    e'.mem_centralizingMembers_u hcfg.twin.mem.1 hTJ hTJ'
  obtain ⟨W₀, hW₀⟩ := id hcfg.linear
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW₀
  have hKβne : K ≠ β := ne_of_linearBlockStandardPair hW₀
  have hTQ : locImg (𝒞 K) z T ≤ c.d.Q₁ :=
    locImg_twin_le_Q₁ c hcfg.twin.mem hcfg.clsT hcfg.twin.ne
  have hlayer : ∀ L : Subgroup G, L ∈ centralizingMembers (𝒞 K) {z} → L ≠ K → Commutes β L →
      IsLayerMember c L := by
    intro L hLz hLK hβL
    refine ⟨hLz, hLK, fun hle => ?_⟩
    have hLT : L = T := c.eq_of_locImg_le_Q₁ hLz hcfg.twin.mem hle hTQ
    have hzL : z ∈ L := hLT ▸ hcfg.clsT.mem
    have hβz : β ∈ centralizingMembers (𝒞 K) {z} :=
      mem_centralizingMembers_of_commutes hcfg.memβ.1 hzL hβL
    rcases S.cp_at_member hcen hKΩ S.cls hβz with h | h
    · exact hnKβ h
    · exact hKβne h.symm
  have hJL : IsLayerMember c J := hlayer J hcfg.mem_J hcfg.J_ne_K hcfg.comm_J
  have hJ'L : IsLayerMember c J' := hlayer J' hcfg.mem_J' hcfg.J'_ne_K hcfg.comm_J'
  obtain ⟨RJ, hRJ, hJR⟩ := hJL.exists_fund
  obtain ⟨RJ', hRJ', hJ'R⟩ := hJ'L.exists_fund
  obtain ⟨FM, -, hFM, -⟩ := twin_datum_td4 c hcfg.mem_J hcfg.mem_J' hcfg.clsJ hcfg.clsJ' e'
    hcfg.twinJ.ne.symm hRJ hJR hRJ' hJ'R
  have htz : s * z * s⁻¹ = z := partner_involution_commutes c.hp2 c.hz hcfg.clsβ hcfg.linear
  obtain ⟨J₁, J₂, w₁, AK, AT, AJ, AJ', hJ₁, hJ₂, hKJ₁, hKJ₂, hTJ₁, hTJ₂, hJJ, hJne, hβJ₁, hzJ₁,
    hzJ₂, hw₁, hw₁', hAK, hAT, hAJ, hAJ', hAKsq, hATsq, hAJsq, hAJ'sq, hsP⟩ :=
    leaf_twin_group c.hp2 c.hq S.inClass S.exact hP1' h1 hty' hKu hTu hcfg.memβ c.hz hcfg.clsT
      hcfg.clsβ hcfg.linear hcfg.twin.ne
      (commutes_symm (hcfg.twin.comm_T K c.hKz hcfg.twin.ne.symm))
  have hJ₁z : J₁ ∈ centralizingMembers (𝒞 K) {z} :=
    mem_centralizingMembers_of_commutes hJ₁.1 c.hz.mem (commutes_symm hKJ₁)
  have hJ₂z : J₂ ∈ centralizingMembers (𝒞 K) {z} :=
    mem_centralizingMembers_of_commutes hJ₂.1 c.hz.mem (commutes_symm hKJ₂)
  have hnK : ∀ {L : Subgroup G}, Commutes K L → L ≠ K := fun hc h =>
    not_commutes_self_of_mem S.inClass hKΩ (by rw [h] at hc; exact hc)
  have hlayerz : ∀ {L : Subgroup G}, L ∈ centralizingMembers (𝒞 K) {z} → L ≠ K → z ∉ L →
      IsLayerMember c L := fun hLz hLK hzL =>
    ⟨hLz, hLK, fun hle => hzL (by
      rw [c.eq_of_locImg_le_Q₁ hLz hcfg.twin.mem hle hTQ]
      exact hcfg.clsT.mem)⟩
  obtain ⟨RJ₁, hRJ₁, hJ₁R⟩ := (hlayerz hJ₁z (hnK hKJ₁) hzJ₁).exists_fund
  obtain ⟨RJ₂, hRJ₂, hJ₂R⟩ := (hlayerz hJ₂z (hnK hKJ₂) hzJ₂).exists_fund
  obtain ⟨ĉ, hĉψ, hρO, hρ2, hρdim, hρcomm⟩ := twin_lift_td4 c hJ₁z hJ₂z hw₁ hw₁'
    (⟨AJ, AJ', hAJ, hAJ', hAJsq, hAJ'sq⟩ : TwinElt J₁ J₂ w₁) hJne hRJ₁ hJ₁R hRJ₂ hJ₂R
  have hxY : AJ * AJ' ∈ locLayer (𝒞 K) z :=
    (locLayer (𝒞 K) z).mul_mem (le_centralizingLayer hJ₁z hAJ) (le_centralizingLayer hJ₂z hAJ')
  have hu₂x : Commute (AK * AT) (AJ * AJ') :=
    ((commute_of_commutes hKJ₁ hAK hAJ).mul_right (commute_of_commutes hKJ₂ hAK hAJ')).mul_left
      ((commute_of_commutes hTJ₁ hAT hAJ).mul_right (commute_of_commutes hTJ₂ hAT hAJ'))
  have hconjL : ∀ L ∈ centralizingMembers (𝒞 K) {z}, L ≠ K → ¬ locImg (𝒞 K) z L ≤ c.d.Q₁ →
      ∀ l ∈ L, s * l * s⁻¹ = (AJ * AJ') * l * (AJ * AJ')⁻¹ := by
    intro L hL hLK hLQ l hl
    have hLT : L ≠ T := fun h => hLQ (h ▸ hTQ)
    have hKl : Commute AK l := commute_of_commutes (c.commutes_K_of_ne hL hLK) hAK hl
    have hTl : Commute AT l := commute_of_commutes (hcfg.twin.comm_T L hL hLT) hAT hl
    exact conj_eq_of_split hsP hu₂x.eq (hKl.mul_left hTl).eq
  have hαθ : ∀ y, c.d.ψ ((MulAut.conj ĉ) y) =
      locAut c.hΩ.conjInvariant htz (c.d.ψ y) :=
    locAut_eq_conj_td4 c htz hxY (hĉψ hxY) hconjL
  have hJc : ∀ n ∈ J, n * (AJ * AJ') = (AJ * AJ') * n := by
    intro n hn
    have hu : AJ * AJ' = (AK * AT)⁻¹ * s := by rw [hsP]; group
    have hnu : Commute n (AK * AT) :=
      (commute_of_commutes hKJ hAK hn).symm.mul_right (commute_of_commutes hTJ hAT hn).symm
    have hns : Commute n s := (commute_of_commutes hcfg.comm_J hcfg.clsβ.mem hn).symm
    rw [hu]
    exact (hnu.inv_right.mul_right hns).eq
  have hfixM := hρcomm (N := J) (RN := RJ) hJc hJR (c.hY.perfR _ hRJ)
  obtain ⟨W₁, hW₁⟩ := id hβJ₁
  have hW₁' := linearBlockStandardPair_symm hW₁
  have hJ₁t : conjSub s J₁ = J₁ :=
    conjSub_eq_of_standardPair h2 hW₁' hcfg.clsβ.mem hcfg.clsβ.orderOf_eq_two
  obtain ⟨x₁, hx₁J, hx₁1, hx₁p, hx₁inv⟩ :=
    TWS7.exists_inverted_unipotent (p := p) h2 hW₁' hcfg.clsβ.mem hcfg.clsβ.orderOf_eq_two
  obtain ⟨hαJ, x₀, hx₀J, hx₀1, hx₀p, hx₀α⟩ :=
    unip_data_td4 c htz hJ₁z hRJ₁ hJ₁R hJ₁t hx₁J hx₁1 hx₁p hx₁inv hαθ
  have hconj : ∀ y v, spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) ((MulAut.conj ĉ) y) (spinAction (quadMinus 4 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2) ĉ v) = spinAction (quadMinus 4 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2) ĉ (spinAction (quadMinus 4 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2) y v) := fun y v => spinAction_conj_apply ĉ y v
  set ρ := spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) ĉ
    with hρ
  have hnormJ : ∀ l ∈ RJ₁.map (spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)), ρ * l * ρ ∈ RJ₁.map (spinAction (quadMinus 4 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2)) := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨(MulAut.conj ĉ) y, hαJ y hy, ?_⟩
    refine LinearEquiv.ext fun v => ?_
    have e1 : ρ (ρ v) = v := by simpa using LinearEquiv.congr_fun hρ2 v
    have := hconj y (ρ v)
    rw [e1] at this
    exact this
  have hx₀inv : ∀ v, ρ (spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) x₀ v) = (spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) x₀).symm (ρ v) := by
    intro v
    have h1 := hconj x₀ v
    rw [hx₀α, map_inv] at h1
    exact h1.symm
  obtain ⟨x', hRJ₁eq, hscal⟩ := class_spin_td4c c.hp2 c.hq cq hρO hρ2 hRJ₁ FM hFM hfixM hnormJ
    hx₀J hx₀1 hx₀p hx₀inv hρdim
  have hn2 : locImg (𝒞 K) z J₁ =
      ((rootSL2 (minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame 0 1
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x').toMonoidHom).map
        c.d.ψ := by
    rw [hJ₁R, hRJ₁eq]
  exact pattern_td4 c htz hJ₁.1 hKJ₁ hβJ₁ hn2 hαθ hρO hconj (ε := 1) (by norm_num)
    (fun y h₁ h₂ => by simpa using hscal y h₁ h₂)

theorem twinYPatternAtL_td4_proved (hcls : TwinInvolution p f) :
    TwinYPatternAtL p f .POmegaMinus 4
      (fun Ω K β t => PartnerPatternMinus p f 4 Ω K β t) := by
  intro G _ _ _ hnab K z S hshape T e J J' w e' β s hcfg hP1 hP1' hty hty'
  have hodd : p ^ f % 2 = 1 := Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two Fact.out S.odd).pow
  have h4 : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by omega
  rcases h4 with h1 | h3
  · exact twinYPatternAtL_td4_one_proved h1 G hnab K z S hshape T e J J' w e' β s hcfg hP1 hP1'
      hty hty'
  · exact twinYPatternAtL_td4_three hcls h3 G hnab K z S hshape T e J J' w e' β s hcfg hP1 hP1'
      hty hty'

end Main

end CFSG.ClassicalInvolution.RouteD.TWU
