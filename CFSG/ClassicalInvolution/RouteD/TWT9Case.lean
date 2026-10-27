module

public import CFSG.ClassicalInvolution.RouteD.TWT9Fix
public import CFSG.ClassicalInvolution.RouteD.TWT9Class
public import CFSG.ClassicalInvolution.RouteD.TWT9Model
public import CFSG.ClassicalInvolution.RouteD.TWT9Typed
public import CFSG.ClassicalInvolution.RouteD.TWT9Lift
public import CFSG.ClassicalInvolution.RouteD.TWT9Spin
public import CFSG.ClassicalInvolution.RouteD.TWEB3LCfg
public import CFSG.ClassicalInvolution.RouteD.TWS7Grp
public import CFSG.ClassicalInvolution.RouteD.TWEB4V
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

namespace CFSG.ClassicalInvolution.RouteD.TWT9

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Asc77
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
open QuadraticMap

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

section Main

variable {p f : ℕ} [Fact p.Prime]

theorem not_isSquare_neg_one_of_mod_three (hf : f ≠ 0) (h3 : p ^ f % 4 = 3) :
    ¬ IsSquare (-1 : GaloisField p f) := by
  classical
  have : Fintype (GaloisField p f) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p f) = p ^ f := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p f hf
  rw [FiniteField.isSquare_neg_one_iff, hcard]
  omega



theorem twinYPatternAtL_td4_three (hcls : TwinInvolution p f) (h3 : p ^ f % 4 = 3) :
    TwinYPatternAtL p f .POmegaMinus 4
      (fun Ω K β t => PartnerPatternMinus p f 4 Ω K β t) := by
  intro G _ _ _ hnab K z S hshape T e J J' w e' β s hcfg hP1 hP1' hty hty'
  classical
  have hrow : TwinRow .POmegaMinus 4 :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by norm_num⟩))))
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
  have hodd : Odd (Nat.card (GaloisField p f)) := c.hodd
  have cq := Exotic.centralQuot_minus c.hp2 c.hq hadm
  have hKJ : Commutes K J := hcfg.twin.comm_K J hcfg.mem_J hcfg.J_ne_K
  have hKJ' : Commutes K J' := hcfg.twin.comm_K J' hcfg.mem_J' hcfg.J'_ne_K
  have hKu : K ∈ centralizingMembers (𝒞 K) {e'.u} :=
    e'.mem_centralizingMembers_u hKΩ hKJ hKJ'
  obtain ⟨W₀, hW₀⟩ := id hcfg.linear
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW₀
  have hKβne : K ≠ β := ne_of_linearBlockStandardPair hW₀
  obtain ⟨T₀, hT₀z, hT₀Q⟩ := c.exists_twin
  have hT₀ : IsTwinAt (𝒞 K) K T₀ z := isTwinAt_of_ctx c hT₀z hT₀Q.le
  have clsT₀ : IsClassicalMember p f T₀ z := hcls G hnab K z S .POmegaMinus 4 hrow hshape T₀ hT₀
  have hlayer : ∀ L : Subgroup G, L ∈ centralizingMembers (𝒞 K) {z} → L ≠ K → Commutes β L →
      IsLayerMember c L := by
    intro L hLz hLK hβL
    refine ⟨hLz, hLK, fun hle => ?_⟩
    have hLT₀ : L = T₀ := c.eq_of_locImg_le_Q₁ hLz hT₀z hle hT₀Q.le
    have hzL : z ∈ L := hLT₀ ▸ clsT₀.mem
    have hβz : β ∈ centralizingMembers (𝒞 K) {z} :=
      mem_centralizingMembers_of_commutes hcfg.memβ.1 hzL hβL
    rcases S.cp_at_member hcen hKΩ S.cls hβz with h | h
    · exact hnKβ h
    · exact hKβne h.symm
  have hJL : IsLayerMember c J := hlayer J hcfg.mem_J hcfg.J_ne_K hcfg.comm_J
  have hJ'L : IsLayerMember c J' := hlayer J' hcfg.mem_J' hcfg.J'_ne_K hcfg.comm_J'
  obtain ⟨RJ, hRJ, hJR⟩ := hJL.exists_fund
  obtain ⟨RJ', hRJ', hJ'R⟩ := hJ'L.exists_fund
  have hne : RJ' ≠ RJ := fun h => hcfg.twinJ.ne
    (c.eq_of_locImg_eq hcfg.mem_J' hcfg.mem_J (by rw [hJ'R, hJR, h]))
  obtain ⟨FM, g', hFM, hFM', hg'O, hg'2, hg'fix, hg'dim, hg'le, hg'an, hg'comm⟩ :=
    twin_datum_td4 c hcfg.mem_J hcfg.mem_J' hcfg.clsJ hcfg.clsJ' e' hcfg.twinJ.ne.symm hRJ hJR
      hRJ' hJ'R
  have htwin : ∀ i j, IsFundamental (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) (RJ.map (spinAction (quadMinus 4 (GaloisField p f)
        (minusCoeffs p f).1 (minusCoeffs p f).2))) i →
      IsFundamental (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)
        (RJ'.map (spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2))) j → i = j := by
    intro i j hi hj
    rw [hFM] at hi
    rw [hFM'] at hj
    rw [IsFundamental.involution_unique hodd hi (IsFundamental.of_frame FM),
      IsFundamental.involution_unique hodd hj (IsFundamental.of_frame_swap FM)]
  have htz : s * z * s⁻¹ = z := partner_involution_commutes c.hp2 c.hz hcfg.clsβ hcfg.linear
  have h2t : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hcfg.clsβ.orderOf_eq_two, pow_two] at this
  have hKt : conjSub s K = K :=
    conjSub_eq_of_standardPair h2 hW₀ hcfg.clsβ.mem hcfg.clsβ.orderOf_eq_two
  let θ : spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) →*
    locQuot (𝒞 K) z := c.d.ψ
  let σ := locAut c.hΩ.conjInvariant htz
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut c.hΩ.conjInvariant htz h2t
  have hσr : ∀ k', σ (θ k') ∈ θ.range := fun k' =>
    locAut_mem_range c htz h2t hKt
      (Exotic.range_le_iSup_fund_minus (by omega) hadm c.hY.std c.d.ψ) k'
  have hfixσ : ∀ {L : Subgroup G} {R : Subgroup (spinGroup (quadMinus 4 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2))},
      L ∈ centralizingMembers (𝒞 K) {z} → locImg (𝒞 K) z L = R.map θ → Commutes β L →
      ∀ r ∈ R, σ (θ r) = θ r := fun hL hLR hβL r hr =>
    (locAut_fixed_iff c.hΩ c.hP1 htz hL).mp (fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hβL s hcfg.clsβ.mem n hn).symm) _
      (by rw [hLR]; exact ⟨r, hr, rfl⟩)
  obtain ⟨x, α, g₀, -, -, hαθ, hg₀O, hg₀2, hconj, -⟩ := lift_td4 c.hp2 c.hq θ c.d.ker_le σ hσ2 hσr
    hRJ hRJ' hne htwin (hfixσ hcfg.mem_J hJR hcfg.comm_J)
    (hfixσ hcfg.mem_J' hJ'R hcfg.comm_J')
  have hcommg : ∀ {R : Subgroup (spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2))},
      R ∈ fundamentalSubgroups .POmegaMinus (minusDatum 4 (minusCoeffs_irr p f)) →
      (∀ r ∈ R, σ (θ r) = θ r) →
      ∀ l ∈ R.map (spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2)), g₀ * l = l * g₀ :=
    fun hR hfix => TWE.B6.commute_of_fixed θ c.d.ker_le σ α hαθ (cq.perf _ hR) hfix hconj
  have hperfN : ∀ {R : Subgroup (spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2))},
      R ∈ fundamentalSubgroups .POmegaMinus (minusDatum 4 (minusCoeffs_irr p f)) → R ≤ ⁅R, R⁆ :=
    fun hR => c.hY.perfR _ hR
  obtain ⟨J₁, hJ₁, N, hN, hKJ₁, hβJ₁, hKN, hβN, hJ₁N⟩ := exists_chain_members_td4 S.odd S.five
    S.inClass S.exact hP1' h3 hty' hKu hcfg.memβ S.cls hcfg.clsβ hcfg.linear
  have hJ₁z : J₁ ∈ centralizingMembers (𝒞 K) {z} :=
    mem_centralizingMembers_of_commutes hJ₁.1 c.hz.mem (commutes_symm hKJ₁)
  have hNz : N ∈ centralizingMembers (𝒞 K) {z} :=
    mem_centralizingMembers_of_commutes hN.1 c.hz.mem (commutes_symm hKN)
  obtain ⟨W₂, hW₂⟩ := id hJ₁N
  have hJ₁Nne : J₁ ≠ N := ne_of_linearBlockStandardPair hW₂
  have hJ₁Nnc : ¬ Commutes J₁ N := not_commutes_of_linearBlockStandardPair hW₂
  have hJ₁L : IsLayerMember c J₁ := IsLayerMember.of_not_commutes c hJ₁z hNz hJ₁Nne hJ₁Nnc
  have hNL : IsLayerMember c N :=
    IsLayerMember.of_not_commutes c hNz hJ₁z hJ₁Nne.symm (fun h => hJ₁Nnc (commutes_symm h))
  obtain ⟨RJ₁, hRJ₁, hJ₁R⟩ := hJ₁L.exists_fund
  obtain ⟨RN, hRN, hNR⟩ := hNL.exists_fund
  obtain ⟨W₁, hW₁⟩ := id hβJ₁
  have hW₁' := linearBlockStandardPair_symm hW₁
  have hJ₁t : conjSub s J₁ = J₁ :=
    conjSub_eq_of_standardPair h2 hW₁' hcfg.clsβ.mem hcfg.clsβ.orderOf_eq_two
  obtain ⟨x₁, hx₁J, hx₁1, hx₁p, hx₁inv⟩ :=
    TWS7.exists_inverted_unipotent (p := p) h2 hW₁' hcfg.clsβ.mem hcfg.clsβ.orderOf_eq_two
  obtain ⟨hαJ, x₀, hx₀J, hx₀1, hx₀p, hx₀α⟩ :=
    unip_data_td4 c htz hJ₁z hRJ₁ hJ₁R hJ₁t hx₁J hx₁1 hx₁p hx₁inv hαθ
  have hnormJ : ∀ l ∈ RJ₁.map (spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)), g₀ * l * g₀ ∈ RJ₁.map (spinAction (quadMinus 4 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2)) := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨α y, hαJ y hy, ?_⟩
    refine LinearEquiv.ext fun v => ?_
    have e1 : g₀ (g₀ v) = v := by simpa using LinearEquiv.congr_fun hg₀2 v
    have := hconj y (g₀ v)
    rw [e1] at this
    exact this
  have hx₀inv : ∀ v, g₀ (spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) x₀ v) = (spinAction (quadMinus 4 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2) x₀).symm (g₀ v) := by
    intro v
    have h1 := hconj x₀ v
    rw [hx₀α, map_inv] at h1
    exact h1.symm
  have hnsq : ¬ IsSquare (-1 : GaloisField p f) := not_isSquare_neg_one_of_mod_three c.hf h3
  obtain ⟨x', ε, hε, hRJ₁eq, hscal⟩ := class_spin_td4a c.hp2 c.hq cq hg₀O hg₀2 hg'O hg'2 hRJ₁ hRN
    FM hFM (hcommg hRJ (hfixσ hcfg.mem_J hJR hcfg.comm_J))
    (hcommg hRN (hfixσ hNz hNR hβN)) hnormJ hx₀J hx₀1 hx₀p hx₀inv hg'le hg'dim
    (hg'comm (fun n hn => Subgroup.mem_centralizer_singleton_iff.mp (hJ₁.2 hn)) hJ₁R
      (hperfN hRJ₁))
    (hg'comm (fun n hn => Subgroup.mem_centralizer_singleton_iff.mp (hN.2 hn)) hNR (hperfN hRN))
    (hg'an hnsq)
  have hn2 : locImg (𝒞 K) z J₁ =
      ((rootSL2 (minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame 0 1
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x').toMonoidHom).map
        c.d.ψ := by
    rw [hJ₁R, hRJ₁eq]
  exact pattern_td4 c htz hJ₁.1 hKJ₁ hβJ₁ hn2 hαθ hg₀O hconj
    (by rcases hε with rfl | rfl <;> norm_num) hscal

end Main

end CFSG.ClassicalInvolution.RouteD.TWT9
