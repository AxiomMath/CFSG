module

public import CFSG.ClassicalInvolution.RouteD.TWEClose
public import CFSG.ClassicalInvolution.RouteD.TWDConfig
public import CFSG.ClassicalInvolution.RouteD.TWEB6Fix
public import CFSG.ClassicalInvolution.RouteD.TWEB6YBridge
public import CFSG.ClassicalInvolution.RouteD.TWEB6Fixed
public import CFSG.ClassicalInvolution.RouteD.TwinSmallCases
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

namespace CFSG.ClassicalInvolution.RouteD.TWE.B6

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Asc77
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

section Main

variable {p f : ℕ} [Fact p.Prime]

theorem twinBCase_six (hΩall : HypOmegaModAll p f) (hP4 : Ih8G2D4 p f)
    (hH : TwinFrameHyp51 p f) (hcls : TwinInvolution p f) : TwinBCase p f 6 := by
  intro G _ _ _ hnab K z S hshape β hβ t ht hKβ hfix
  classical
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simpa using S.five
    · exact h
  have hcen : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  have hΩ : InClass p f (𝒞 K) := S.inClass
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f S.odd
  have hrow : TwinRow .POmegaOdd 6 := Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by norm_num⟩))
  have hlarge : TwinRow.large .POmegaOdd 6 := Or.inr (Or.inr ⟨rfl, by norm_num⟩)
  obtain ⟨c⟩ := TCtx.nonempty_odd (by norm_num : 3 ≤ 6) S.odd S.five S.inClass S.exact hKΩ S.cls
    S.p1 hshape
  have hsingle : ∀ L ∈ 𝒞 K, ∃ g : G, L = conjSub g K := single_class K
  obtain ⟨T, hTz, hTQ⟩ := c.exists_twin
  have hT : IsTwinAt (𝒞 K) K T z := isTwinAt_of_ctx c hTz hTQ.le
  have clsT : IsClassicalMember p f T z := hcls G hnab K z S .POmegaOdd 6 hrow hshape T hT
  have hTΩ : T ∈ 𝒞 K := hTz.1
  obtain ⟨M, hMΩ, hKM, hβM, hMnon⟩ := hfix
  obtain ⟨W₀, hW₀⟩ := id hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW₀
  have hMz : M ∈ centralizingMembers (𝒞 K) {z} :=
    mem_centralizingMembers_of_commutes hMΩ S.cls.mem (commutes_symm hKM)
  have hMK : M ≠ K := fun h => not_commutes_self_of_mem hΩ hKΩ (by rw [h] at hKM; exact hKM)
  have hMT : M ≠ T := fun h => hMnon (fun N hN hNM => by
    rw [h]; exact hT.comm_T N hN (by rw [← h]; exact hNM))
  have hMN : ∃ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ M ∧ ¬ Commutes M N := by
    by_contra h
    exact hMnon fun N hN hNM => by_contra fun hc => h ⟨N, hN, hNM, hc⟩
  obtain ⟨w, hw⟩ := hΩ.classical M hMΩ
  have hwz : w ≠ z := by
    intro hwz
    apply hMnon
    intro N hN hNM
    have hN' : N ∈ centralizingMembers (𝒞 K) {w} := by rw [hwz]; exact hN
    exact (S.cp_at_member hcen hMΩ hw hN').resolve_right hNM
  obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape hMΩ hw
  obtain ⟨J', hJ'⟩ := exists_isTwinAt_of_ctx cx
  have hSM : RouteDSetup p f M w := S.of_mem_conjClass hMΩ hw
  have hclsM : 𝒞 M = 𝒞 K := conjClass_eq_of_mem hMΩ
  have hshapeM : LocalShapeT p f 2 .POmegaOdd 6 (𝒞 M) w := by
    rw [hclsM]; exact localShapeT_at_member S hMΩ hw hshape
  have hJ'M : IsTwinAt (𝒞 M) M J' w := by rw [hclsM]; exact hJ'
  have clsJ' : IsClassicalMember p f J' w := hcls G hnab M w hSM .POmegaOdd 6 hrow hshapeM J' hJ'M
  have hJ'Ω : J' ∈ 𝒞 K := hJ'.mem.1
  have hKw : K ∈ centralizingMembers (𝒞 K) {w} :=
    mem_centralizingMembers_of_commutes hKΩ hw.mem hKM
  have hJ'K : J' ≠ K := fun h => hwz (Gaps.unique_involution_of_isClassicalMember h2
    (S.exact K hKΩ) (h ▸ clsJ') S.cls)
  have hJ'T : J' ≠ T := fun h => hwz (Gaps.unique_involution_of_isClassicalMember h2
    (S.exact T hTΩ) (h ▸ clsJ') clsT)
  have hJ'Kc : Commutes J' K := hJ'.comm_T K hKw hJ'K.symm
  have hJ'z : J' ∈ centralizingMembers (𝒞 K) {z} :=
    mem_centralizingMembers_of_commutes hJ'Ω S.cls.mem hJ'Kc
  have hJ'L : IsLayerMember c J' := ⟨hJ'z, hJ'K, fun hle =>
    hJ'T (c.eq_of_locImg_le_Q₁ hJ'z hTz hle hTQ.le)⟩
  obtain ⟨e'⟩ := exists_twinElt hw clsJ' (S.exact M hMΩ) (S.exact J' hJ'Ω)
    (odd_natCard_galoisField S.odd S.five)
  obtain ⟨nd, h0, h1⟩ := exists_dnodes_of_pair_odd (by norm_num : 5 ≤ 6) c hsingle hshape hβ ht
    hKβ hMΩ hKM hβM
  have hnodeW : ∀ a : Fin 6, nd.J a ∈ centralizingMembers (𝒞 K) {w} := fun a =>
    mem_centralizingMembers_of_commutes (nd.mem a) hw.mem (commutes_symm (nd.commK a))
  have hneJ' : ∀ a : Fin 6, nd.J a ≠ J' := by
    intro a h
    obtain ⟨b, hab⟩ : ∃ b : Fin 6, DNodes.Adj a b := by
      by_cases h4 : a.val ≤ 3
      · exact ⟨⟨a.val + 1, by omega⟩, by simp [DNodes.adj_def]; omega⟩
      · exact ⟨⟨3, by norm_num⟩, by simp [DNodes.adj_def]; omega⟩
    have hbJ' : nd.J b ≠ J' := fun hb => nd.ne_J hΩ hab.ne (h.trans hb.symm)
    have := hJ'.comm_T (nd.J b) (hnodeW b) hbJ'
    rw [← h] at this
    exact nd.not_commutes_of_adj hab this
  have hnodeu : ∀ a : Fin 6, nd.J a ∈ centralizingMembers (𝒞 K) {e'.u} := fun a =>
    e'.mem_centralizingMembers_u (nd.mem a) (commutes_symm (nd.commK a))
      (commutes_symm (hJ'.comm_T (nd.J a) (hnodeW a) (hneJ' a)))
  have hY1 := twinYP1On_large_proved (p := p) (f := f) S.odd S.five hΩall hP4 hH hcls
  have hY2 := twinYTypeOn_large_proved (p := p) (f := f) S.odd S.five hΩall hP4 hH hcls
  have hP1' := hY1 G hnab M w hSM .POmegaOdd 6 hrow hlarge hshapeM J' hJ'M clsJ' e'
  have hty' := hY2 G hnab M w hSM .POmegaOdd 6 hrow hlarge hshapeM J' hJ'M clsJ' e' hP1'
  rw [hclsM] at hP1' hty'
  obtain ⟨N₁, hN₁, N₂, hN₂, hNc, hN₁4, hN₁5, hN₂4, hN₂5, hN₁₂, hne₁₂⟩ := exists_bridges_group S.odd
    S.five hΩ S.exact hP1' hty' nd hnodeu
  have htz : t * z * t⁻¹ = z := partner_involution_commutes c.hp2 c.hz ht hKβ
  obtain ⟨Rz, RzM, x, tM, α, g₀, hRz, hRzM, hxR, hxM, hαθ, hg₀O, hg₀2, hconj⟩ :=
    recognition_six c ht htz hKβ hMΩ hMN nd h0 h1 hN₁.1 (fun a ha => (hNc a ha).1) hN₁4 hN₁5
  obtain ⟨ε, hε, hscal⟩ := scalar_six c ht htz hMz nd h0 h1 hRz hRzM hxR hxM hαθ hg₀O hg₀2 hconj
    hN₁.1 hN₂.1 (fun a ha => (hNc a ha).1) (fun a ha => (hNc a ha).2) hN₁4 hN₂4 hN₁₂ hne₁₂ e' hw
    clsJ' hJ'z hJ'L hJ'M.ne.symm
    (fun n hn => Subgroup.mem_centralizer_singleton_iff.mp (hN₁.2 hn))
    (fun n hn => Subgroup.mem_centralizer_singleton_iff.mp (hN₂.2 hn))
  have hn2 : locImg (𝒞 K) z (nd.J ⟨2, by omega⟩) =
      ((rootSL2 (oddFrame 6 (GaloisField p f)).toHypFrame 0 1 (by omega) (by omega) (by omega)
        true false).map (MulAut.conj x).toMonoidHom).map c.d.ψ := by
    rw [(hRz 2 (by omega) (by omega)).2]
    exact congrArg (fun S => S.map c.d.ψ) (hxR 0 (by norm_num))
  exact pattern_six c htz nd h0 h1 hn2 hαθ hg₀O hconj (by rcases hε with rfl | rfl <;> norm_num)
    hscal

theorem twinBExistsCase_six (hΩall : HypOmegaModAll p f) (hP4 : Ih8G2D4 p f)
    (hH : TwinFrameHyp51 p f) (hcls : TwinInvolution p f) : TwinBExistsCase p f 6 := by
  intro G _ _ _ hnab K z S m hm hshape
  subst hm
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simpa using S.five
    · exact h
  have hadm : StatedLieAdmissible .POmegaOdd 6 p f := ⟨Fact.out, hf, by norm_num, S.odd⟩
  obtain ⟨c⟩ := TCtx.nonempty_odd (by norm_num : 3 ≤ 6) S.odd S.five S.inClass S.exact
    (mem_conjClass_self K) S.cls S.p1 hshape
  obtain ⟨β, hβ, ⟨t, ht⟩, hKβ, hfix⟩ := c.exists_partner_odd (by norm_num) hadm (single_class K)
    hshape
  exact ⟨β, hβ, t, ht, hKβ, twinBCase_six hΩall hP4 hH hcls G hnab K z S hshape β hβ t ht hKβ hfix⟩

theorem twinBExistsSmallRest_of_three_four (hΩall : HypOmegaModAll p f) (hP4 : Ih8G2D4 p f)
    (hH : TwinFrameHyp51 p f) (hcls : TwinInvolution p f) (h3 : TwinBExistsCase p f 3)
    (h4 : TwinBExistsCase p f 4) : TwinBExistsSmallRest p f := by
  intro G _ _ _ hnab K z S m hm hshape
  rcases hm with rfl | rfl | rfl
  · exact h3 G hnab K z S 3 rfl hshape
  · exact h4 G hnab K z S 4 rfl hshape
  · exact twinBExistsCase_six hΩall hP4 hH hcls G hnab K z S 6 rfl hshape

end Main

end CFSG.ClassicalInvolution.RouteD.TWE.B6
