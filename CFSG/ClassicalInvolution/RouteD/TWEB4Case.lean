module

public import CFSG.ClassicalInvolution.RouteD.TWEClose
public import CFSG.ClassicalInvolution.RouteD.TWDConfig
public import CFSG.ClassicalInvolution.RouteD.TWEB4Nodes
public import CFSG.ClassicalInvolution.RouteD.TWEB4Grp
public import CFSG.ClassicalInvolution.RouteD.TWEB4Bridge
public import CFSG.ClassicalInvolution.RouteD.TWEB4Fix
public import CFSG.ClassicalInvolution.RouteD.TWS7Grp
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

namespace CFSG.ClassicalInvolution.RouteD.TWE.B4

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Asc77
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.RouteD.TWE.B6
open QuadraticMap

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

section Main

variable {p f : ℕ} [Fact p.Prime]


theorem twinBCase_four (hΩall : HypOmegaModAll p f) (hP4 : Ih8G2D4 p f)
    (hH : TwinFrameHyp51 p f) (hcls : TwinInvolution p f) : TwinBCase p f 4 := by
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
  have hrow : TwinRow .POmegaOdd 4 := Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by norm_num⟩))
  have hlarge : TwinRow.large .POmegaOdd 4 := Or.inr (Or.inr ⟨rfl, by norm_num⟩)
  obtain ⟨c⟩ := TCtx.nonempty_odd (by norm_num : 3 ≤ 4) S.odd S.five S.inClass S.exact hKΩ S.cls
    S.p1 hshape
  have hsingle : ∀ L ∈ 𝒞 K, ∃ g : G, L = conjSub g K := single_class K
  obtain ⟨T, hTz, hTQ⟩ := c.exists_twin
  have hT : IsTwinAt (𝒞 K) K T z := isTwinAt_of_ctx c hTz hTQ.le
  have clsT : IsClassicalMember p f T z := hcls G hnab K z S .POmegaOdd 4 hrow hshape T hT
  have hTΩ : T ∈ 𝒞 K := hTz.1
  obtain ⟨M, hMΩ, hKM, hβM, hMnon⟩ := hfix
  obtain ⟨W₀, hW₀⟩ := id hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW₀
  have hMz : M ∈ centralizingMembers (𝒞 K) {z} :=
    mem_centralizingMembers_of_commutes hMΩ S.cls.mem (commutes_symm hKM)
  have hMK : M ≠ K := fun h => not_commutes_self_of_mem hΩ hKΩ (by rw [h] at hKM; exact hKM)
  have hMN : ∃ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ M ∧ ¬ Commutes M N := by
    by_contra h
    exact hMnon fun N hN hNM => by_contra fun hc => h ⟨N, hN, hNM, hc⟩
  obtain ⟨w, hw⟩ := hΩ.classical M hMΩ
  obtain ⟨cx⟩ := exists_ctx_member c hsingle hshape hMΩ hw
  obtain ⟨J', hJ'⟩ := exists_isTwinAt_of_ctx cx
  have hSM : RouteDSetup p f M w := S.of_mem_conjClass hMΩ hw
  have hclsM : 𝒞 M = 𝒞 K := conjClass_eq_of_mem hMΩ
  have hshapeM : LocalShapeT p f 2 .POmegaOdd 4 (𝒞 M) w := by
    rw [hclsM]; exact localShapeT_at_member S hMΩ hw hshape
  have hJ'M : IsTwinAt (𝒞 M) M J' w := by rw [hclsM]; exact hJ'
  have clsJ' : IsClassicalMember p f J' w := hcls G hnab M w hSM .POmegaOdd 4 hrow hshapeM J' hJ'M
  have hJ'Ω : J' ∈ 𝒞 K := hJ'.mem.1
  have hwz : w ≠ z := by
    intro hwz
    apply hMnon
    intro N hN hNM
    have hN' : N ∈ centralizingMembers (𝒞 K) {w} := by rw [hwz]; exact hN
    exact (S.cp_at_member hcen hMΩ hw hN').resolve_right hNM
  have hKw : K ∈ centralizingMembers (𝒞 K) {w} :=
    mem_centralizingMembers_of_commutes hKΩ hw.mem hKM
  have hβw : β ∈ centralizingMembers (𝒞 K) {w} :=
    mem_centralizingMembers_of_commutes hβ hw.mem hβM
  have hJ'K : J' ≠ K := fun h => hwz (Gaps.unique_involution_of_isClassicalMember h2
    (S.exact K hKΩ) (h ▸ clsJ') S.cls)
  have hJ'T : J' ≠ T := fun h => hwz (Gaps.unique_involution_of_isClassicalMember h2
    (S.exact T hTΩ) (h ▸ clsJ') clsT)
  have hJ'Kc : Commutes J' K := hJ'.comm_T K hKw hJ'K.symm
  have hJ'z : J' ∈ centralizingMembers (𝒞 K) {z} :=
    mem_centralizingMembers_of_commutes hJ'Ω S.cls.mem hJ'Kc
  have hJ'L : IsLayerMember c J' := ⟨hJ'z, hJ'K, fun hle =>
    hJ'T (c.eq_of_locImg_le_Q₁ hJ'z hTz hle hTQ.le)⟩
  have hβJ' : β ≠ J' := fun h => hnKβ (commutes_symm (h ▸ hJ'Kc))
  have hJ'β : Commutes J' β := hJ'.comm_T β hβw hβJ'
  obtain ⟨e'⟩ := exists_twinElt hw clsJ' (S.exact M hMΩ) (S.exact J' hJ'Ω)
    (odd_natCard_galoisField S.odd S.five)
  obtain ⟨nd, h0, h1⟩ := exists_dnodes_of_pair_odd_ge4 (le_refl 4) c hsingle hshape hβ ht
    hKβ hMΩ hKM hβM
  have hnodeW : ∀ a : Fin 4, nd.J a ∈ centralizingMembers (𝒞 K) {w} := fun a =>
    mem_centralizingMembers_of_commutes (nd.mem a) hw.mem (commutes_symm (nd.commK a))
  have hneJ' : ∀ a : Fin 4, nd.J a ≠ J' := by
    intro a h
    obtain ⟨b, hab⟩ : ∃ b : Fin 4, DNodes.Adj a b := by
      by_cases h1 : a.val = 1
      · exact ⟨⟨0, by norm_num⟩, by simp [DNodes.adj_def]; omega⟩
      · exact ⟨⟨1, by norm_num⟩, by simp [DNodes.adj_def]; omega⟩
    have hbJ' : nd.J b ≠ J' := fun hb => nd.ne_J hΩ hab.ne (h.trans hb.symm)
    have := hJ'.comm_T (nd.J b) (hnodeW b) hbJ'
    rw [← h] at this
    exact nd.not_commutes_of_adj hab this
  have hnodeu : ∀ a : Fin 4, nd.J a ∈ centralizingMembers (𝒞 K) {e'.u} := fun a =>
    e'.mem_centralizingMembers_u (nd.mem a) (commutes_symm (nd.commK a))
      (commutes_symm (hJ'.comm_T (nd.J a) (hnodeW a) (hneJ' a)))
  have hKu : K ∈ centralizingMembers (𝒞 K) {e'.u} := by
    have := hnodeu ⟨0, by omega⟩
    rwa [h0] at this
  have hβu : β ∈ centralizingMembers (𝒞 K) {e'.u} := by
    have := hnodeu ⟨1, by omega⟩
    rwa [h1] at this
  have hY1 := twinYP1On_large_proved (p := p) (f := f) S.odd S.five hΩall hP4 hH hcls
  have hY2 := twinYTypeOn_large_proved (p := p) (f := f) S.odd S.five hΩall hP4 hH hcls
  have hP1' := hY1 G hnab M w hSM .POmegaOdd 4 hrow hlarge hshapeM J' hJ'M clsJ' e'
  have hty' := hY2 G hnab M w hSM .POmegaOdd 4 hrow hlarge hshapeM J' hJ'M clsJ' e' hP1'
  rw [hclsM] at hP1' hty'
  obtain ⟨N₁, hN₁, N₂, hN₂, hKN₁, hβN₁, hKN₂, hβN₂, hnc, hne₁₂⟩ := exists_noncommuting_members
    S.odd S.five hΩ S.exact hP1' hty' hKu hβu c.hz ht hKβ
  have htz : t * z * t⁻¹ = z := partner_involution_commutes c.hp2 c.hz ht hKβ
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW₀ ht.mem ht.orderOf_eq_two
  have hadm : StatedLieAdmissible .POmegaOdd 4 p f := ⟨Fact.out, hf, by norm_num, c.hp2⟩
  have hodd : Odd (Nat.card (GaloisField p f)) := c.hodd
  have cq := centralQuot_odd (m := 4) c.hp2 (by norm_num : 3 ≤ 4) c.hq
  obtain ⟨N₀, hN₀z, hN₀M, hN₀c⟩ := hMN
  have hMlayer : IsLayerMember c M :=
    IsLayerMember.of_not_commutes c hMz hN₀z (fun h => hN₀M h.symm) hN₀c
  obtain ⟨RzM, hRzM, hMR⟩ := hMlayer.exists_fund
  obtain ⟨RJ', hRJ', hJ'R⟩ := hJ'L.exists_fund
  have hN₁z : N₁ ∈ centralizingMembers (𝒞 K) {z} :=
    mem_centralizingMembers_of_commutes hN₁.1 c.hz.mem (commutes_symm hKN₁)
  have hN₂z : N₂ ∈ centralizingMembers (𝒞 K) {z} :=
    mem_centralizingMembers_of_commutes hN₂.1 c.hz.mem (commutes_symm hKN₂)
  obtain ⟨RN₁, hRN₁, hN₁R⟩ :=
    (IsLayerMember.of_not_commutes c hN₁z hN₂z hne₁₂ hnc).exists_fund
  obtain ⟨RN₂, hRN₂, hN₂R⟩ :=
    (IsLayerMember.of_not_commutes c hN₂z hN₁z (fun h => hne₁₂ h.symm)
      (fun h => hnc (commutes_symm h))).exists_fund
  obtain ⟨b, hb2, hJz, hJK, hJQ⟩ := exists_layer_leaf c nd h0
  have hJL : IsLayerMember c (nd.J b) := ⟨hJz, hJK, hJQ⟩
  obtain ⟨RJ, hRJ, hJR⟩ := hJL.exists_fund
  obtain ⟨FM, g', hFM, hFM', hg'O, hg'2, hg'fix, hg'dim, hg'le, hg'comm⟩ :=
    twin_datum_b4 c hMz hJ'z hw clsJ' e' hJ'M.ne.symm hRzM hMR hRJ' hJ'R
  have htwin : ∀ i j, IsFundamental (quadOdd 4 (GaloisField p f))
      (RzM.map (spinAction (quadOdd 4 (GaloisField p f)))) i →
      IsFundamental (quadOdd 4 (GaloisField p f))
        (RJ'.map (spinAction (quadOdd 4 (GaloisField p f)))) j → i = j := by
    intro i j hi hj
    rw [hFM] at hi
    rw [hFM'] at hj
    rw [IsFundamental.involution_unique hodd hi (IsFundamental.of_frame FM),
      IsFundamental.involution_unique hodd hj (IsFundamental.of_frame_swap FM)]
  have hne : RJ' ≠ RzM := fun h =>
    hJ'M.ne (c.eq_of_locImg_eq hJ'z hMz (by rw [hJ'R, hMR, h]))
  let θ : spinGroup (quadOdd 4 (GaloisField p f)) →* locQuot (𝒞 K) z := c.d.ψ
  let σ := locAut hΩ.conjInvariant htz
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hΩ.conjInvariant htz h2t
  have hσr : ∀ k', σ (θ k') ∈ θ.range := fun k' =>
    locAut_mem_range c htz h2t hKt (range_le_iSup_fund_odd (by omega) hadm c.hY.std c.d.ψ) k'
  have hfixσ : ∀ {L : Subgroup G} {R : Subgroup (spinGroup (quadOdd 4 (GaloisField p f)))},
      L ∈ centralizingMembers (𝒞 K) {z} → locImg (𝒞 K) z L = R.map θ → Commutes β L →
      ∀ r ∈ R, σ (θ r) = θ r := fun hL hLR hβL r hr =>
    (locAut_fixed_iff hΩ c.hP1 htz hL).mp (fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hβL t ht.mem n hn).symm) _
      (by rw [hLR]; exact ⟨r, hr, rfl⟩)
  obtain ⟨x, α, g₀, -, -, hαθ, hg₀O, hg₀2, hconj, -⟩ := lift_b4 c.hp2 c.hq θ c.d.ker_le σ hσ2 hσr
    hRzM hRJ' hne htwin (hfixσ hMz hMR hβM) (hfixσ hJ'z hJ'R (commutes_symm hJ'β))
  have hcommg : ∀ {R : Subgroup (spinGroup (quadOdd 4 (GaloisField p f)))},
      R ∈ fundamentalSubgroups .POmegaOdd (oddDatum 4 (GaloisField p f)) →
      (∀ r ∈ R, σ (θ r) = θ r) →
      ∀ l ∈ R.map (spinAction (quadOdd 4 (GaloisField p f))), g₀ * l = l * g₀ :=
    fun hR hfix => commute_of_fixed θ c.d.ker_le σ α hαθ (cq.perf _ hR) hfix hconj
  have hadjb : DNodes.Adj b (⟨1, by omega⟩ : Fin 4) := by
    have := b.isLt
    simp [DNodes.adj_def]
    omega
  obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj hadjb
  rw [h1] at hW₁
  have hJt : conjSub t (nd.J b) = nd.J b :=
    conjSub_eq_of_standardPair h2 hW₁ ht.mem ht.orderOf_eq_two
  obtain ⟨x₁, hx₁J, hx₁1, hx₁p, hx₁inv⟩ :=
    TWS7.exists_inverted_unipotent (p := p) h2 hW₁ ht.mem ht.orderOf_eq_two
  obtain ⟨hαJ, x₀, hx₀J, hx₀1, hx₀p, hx₀α⟩ :=
    unip_data_b4 c htz hJz hRJ hJR hJt hx₁J hx₁1 hx₁p hx₁inv hαθ
  have hnormJ : ∀ l ∈ RJ.map (spinAction (quadOdd 4 (GaloisField p f))),
      g₀ * l * g₀ ∈ RJ.map (spinAction (quadOdd 4 (GaloisField p f))) := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨α y, hαJ y hy, ?_⟩
    refine LinearEquiv.ext fun v => ?_
    have e1 : g₀ (g₀ v) = v := by simpa using LinearEquiv.congr_fun hg₀2 v
    have := hconj y (g₀ v)
    rw [e1] at this
    exact this
  have hx₀inv : ∀ v, g₀ (spinAction (quadOdd 4 (GaloisField p f)) x₀ v) =
      (spinAction (quadOdd 4 (GaloisField p f)) x₀).symm (g₀ v) := by
    intro v
    have h1 := hconj x₀ v
    rw [hx₀α, map_inv] at h1
    exact h1.symm
  have hJM : nd.J b ≠ M := fun h => not_commutes_self_of_mem hΩ hMΩ (by
    have := nd.commK b
    rw [h] at this
    exact this)
  have hRJM : RJ ≠ RzM := fun h => hJM (c.eq_of_locImg_eq hJz hMz (by rw [hJR, hMR, h]))
  have hRJM' : RJ ≠ RJ' := fun h =>
    hneJ' b (c.eq_of_locImg_eq hJz hJ'z (by rw [hJR, hJ'R, h]))
  have hcomm : Commutes (RzM.map (spinAction (quadOdd 4 (GaloisField p f))))
      (RJ.map (spinAction (quadOdd 4 (GaloisField p f)))) :=
    (cq.commutes_iff hRzM).mpr ((c.commutes_iff_fund hMz hJz hRzM hMR hJR).mp (nd.commK b))
  have hSne : RN₁.map (spinAction (quadOdd 4 (GaloisField p f))) ≠
      RN₂.map (spinAction (quadOdd 4 (GaloisField p f))) := fun e =>
    hne₁₂ (c.eq_of_locImg_eq hN₁z hN₂z (by rw [hN₁R, hN₂R, cq.map_inj hRN₁ hRN₂ e]))
  have hSnc : ¬ Commutes (RN₁.map (spinAction (quadOdd 4 (GaloisField p f))))
      (RN₂.map (spinAction (quadOdd 4 (GaloisField p f)))) := fun h =>
    hnc ((c.commutes_iff_fund hN₁z hN₂z hRN₁ hN₁R hN₂R).mpr ((cq.commutes_iff hRN₁).mp h))
  have hperfN : ∀ {R : Subgroup (spinGroup (quadOdd 4 (GaloisField p f)))},
      R ∈ fundamentalSubgroups .POmegaOdd (oddDatum 4 (GaloisField p f)) → R ≤ ⁅R, R⁆ :=
    fun hR => c.hY.perfR _ hR
  obtain ⟨x', ε, hε, hRJeq, hscal⟩ := class_spin_b4 c.hp2 c.hq cq hg₀O hg₀2 hg'O hg'2 hRzM hRJ'
    hRJ hRN₁ hRN₂ FM hFM hFM' hRJM hRJM' hcomm (hcommg hRzM (hfixσ hMz hMR hβM))
    (hcommg hRN₁ (hfixσ hN₁z hN₁R hβN₁)) (hcommg hRN₂ (hfixσ hN₂z hN₂R hβN₂)) hnormJ hx₀J hx₀1
    hx₀p hx₀inv hg'le hg'dim hg'fix
    (hg'comm (fun n hn => Subgroup.mem_centralizer_singleton_iff.mp (hN₁.2 hn)) hN₁R
      (hperfN hRN₁))
    (hg'comm (fun n hn => Subgroup.mem_centralizer_singleton_iff.mp (hN₂.2 hn)) hN₂R
      (hperfN hRN₂)) hSnc hSne
  have hn2 : locImg (𝒞 K) z (nd.J b) =
      ((rootSL2 (oddFrame 4 (GaloisField p f)).toHypFrame 0 1 (by omega) (by omega) (by omega)
        true false).map (MulAut.conj x').toMonoidHom).map c.d.ψ := by
    rw [hJR, hRJeq]
  exact pattern_b4 c htz nd h0 h1 hb2 hn2 hαθ hg₀O hconj
    (by rcases hε with rfl | rfl <;> norm_num) hscal

end Main

end CFSG.ClassicalInvolution.RouteD.TWE.B4
