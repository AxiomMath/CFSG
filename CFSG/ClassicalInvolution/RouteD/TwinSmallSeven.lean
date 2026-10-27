module

public import CFSG.ClassicalInvolution.RouteD.TwinSmallFix
public import CFSG.ClassicalInvolution.RouteD.TwinSmallLeaf
public import CFSG.ClassicalInvolution.RouteD.TwinSmallLift
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusSmallPattern
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralBridge
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

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinSmall

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution.Models.OrthogonalPairs

local macro "fr_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes.adj_def]; done)
    | (simp [DNodes.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

theorem minus_fixed_of_nodes_seven (c : TCtx p f .POmegaMinus 7 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaMinus 7 Ω z) {β : Subgroup G} {t : G}
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hMN : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N)
    (nd : DNodes p f (7 - 1) Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β) :
    ∃ x : spinGroup (quadMinus 7 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2),
      locImg Ω z (nd.J ⟨2, by omega⟩) =
        ((rankOne (minusDatum 7 (minusCoeffs_irr p f)).rootGroup
          (⟨0, by omega⟩ : Fin (7 - 1))).map (MulAut.conj x).toMonoidHom).map c.d.ψ ∧
      ∀ k : Fin (7 - 1), 1 ≤ k.val →
        ∀ r ∈ (rankOne (minusDatum 7 (minusCoeffs_irr p f)).rootGroup k).map
          (MulAut.conj x).toMonoidHom,
        locAut c.hΩ.conjInvariant (partner_involution_commutes c.hp2 c.hz ht hKβ) (c.d.ψ r) =
          c.d.ψ r := by
  classical
  have hMFZ : FundNoncentral p := CFSG.ClassicalInvolution.RouteD.Gaps.fundNoncentral p
  have hirr := minusCoeffs_irr p f
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have htz := partner_involution_commutes c.hp2 c.hz ht hKβ
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  obtain ⟨W, hW⟩ := hKβ
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr c.hf
  have hadm : StatedLieAdmissible .POmegaMinus 7 p f := ⟨Fact.out, hf1, by norm_num⟩
  have hF := orthFacts_minus c.hp2 (by norm_num : 5 ≤ 7) c.hq
  have cq := ctx_centralQuot c (by norm_num : 4 ≤ 7)
  have hKJ : ∀ a (h : a < 7 - 1), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by simp; omega)) (by fr_idx)
  have hmemz : ∀ a (h : a < 7 - 1), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hnb : ∀ a (h : a < 7 - 1), 2 ≤ a →
      ∃ b, ∃ hb : b < 7 - 1, 2 ≤ b ∧ DNodes.Adj (⟨a, h⟩ : Fin (7 - 1)) ⟨b, hb⟩ := by
    intro a h ha
    have : a < 6 := h
    interval_cases a
    · exact ⟨3, by omega, by omega, by fr_idx⟩
    · exact ⟨2, by omega, by omega, by fr_idx⟩
    · exact ⟨3, by omega, by omega, by fr_idx⟩
    · exact ⟨3, by omega, by omega, by fr_idx⟩
  have hlayer : ∀ a (h : a < 7 - 1), 2 ≤ a → IsLayerMember c (nd.J ⟨a, h⟩) := by
    intro a h ha
    obtain ⟨b, hb, hb2, hab⟩ := hnb a h ha
    exact IsLayerMember.of_not_commutes c (hmemz a h ha) (hmemz b hb hb2)
      (nd.ne_J hΩ hab.ne) (nd.not_commutes_of_adj hab)
  have hexRz : ∀ a : ℕ, ∃ R : Subgroup (SpinM p f 7),
      ∀ (h : a < 7 - 1), 2 ≤ a →
        R ∈ fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr p f)) ∧
          locImg Ω z (nd.J ⟨a, h⟩) = R.map c.d.ψ := by
    intro a
    by_cases hv : a < 7 - 1 ∧ 2 ≤ a
    · obtain ⟨R, hR, hLR⟩ := (hlayer a hv.1 hv.2).exists_fund
      exact ⟨R, fun _ _ => ⟨hR, hLR⟩⟩
    · exact ⟨⊥, fun h ha => absurd ⟨h, ha⟩ hv⟩
  choose Rz hRz using hexRz
  have hMK : Commutes M K := by
    rw [← h0]
    exact nd.commK _
  have hMz : M ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hMΩ c.hz.mem hMK
  obtain ⟨N, hNz, hNM, hNc⟩ := hMN
  have hMlayer : IsLayerMember c M :=
    IsLayerMember.of_not_commutes c hMz hNz (fun h => hNM h.symm) hNc
  obtain ⟨RzM, hRzM, hMR⟩ := hMlayer.exists_fund
  have hcommz : ∀ a (ha : a < 7 - 1) b (hb : b < 7 - 1) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      Commutes (nd.J ⟨a, ha⟩) (nd.J ⟨b, hb⟩) → Commutes (Rz a) (Rz b) :=
    fun a ha b hb ha2 hb2 h => (c.commutes_iff_fund (hmemz a ha ha2) (hmemz b hb hb2)
      (hRz a ha ha2).1 (hRz a ha ha2).2 (hRz b hb hb2).2).mp h
  have hMcomm : ∀ a (ha : a < 7 - 1) (ha2 : 2 ≤ a), Commutes RzM (Rz a) :=
    fun a ha ha2 => (c.commutes_iff_fund hMz (hmemz a ha ha2) hRzM hMR (hRz a ha ha2).2).mp
      (nd.commK _)
  have hadjz : ∀ a (ha : a < 7 - 1) b (hb : b < 7 - 1) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes.Adj (⟨a, ha⟩ : Fin (7 - 1)) ⟨b, hb⟩ →
        ModelAdj (Subgroup.center (SpinM p f 7)) (Rz a) (Rz b) := fun a ha b hb ha2 hb2 hab =>
    modelAdj_of_adj c (hmemz a ha ha2) (hmemz b hb hb2) (hRz a ha ha2).1 (hRz b hb hb2).1
      (hRz a ha ha2).2 (hRz b hb hb2).2 (nd.cl _) (nd.cl _) (nd.ne_J hΩ hab.ne)
      (nd.not_commutes_of_adj hab) (nd.commute_w h2 _ _) (nd.conjSub_w h2 hab)
  have hlinz : ∀ a (ha : a < 7 - 1) b (hb : b < 7 - 1) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes.Adj (⟨a, ha⟩ : Fin (7 - 1)) ⟨b, hb⟩ →
        ∃ W₁, LinearBlockStandardPair (GaloisField p f) W₁ (Rz a) (Rz b) := by
    intro a ha b hb ha2 hb2 hab
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj hab
    obtain ⟨W₂, hW₂⟩ := linearBlockStandardPair_locImg_of_members c.hP1 (hmemz a ha ha2)
      (hmemz b hb hb2) hW₁
    rw [(hRz a ha ha2).2, (hRz b hb hb2).2] at hW₂
    exact hF.lift c.d.ψ c.d.ker_le _ (hRz a ha ha2).1 _ (hRz b hb hb2).1 ⟨W₂, hW₂⟩
  have hfixnode : ∀ a (h : a < 7 - 1), 2 ≤ a → Commutes β (nd.J ⟨a, h⟩) →
      ∀ x ∈ locImg Ω z (nd.J ⟨a, h⟩), locAut hΩ.conjInvariant htz x = x := fun a h ha hc =>
    (locAut_fixed_iff hΩ c.hP1 htz (hmemz a h ha)).mp fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hc t ht.mem n hn).symm
  have hβJ : ∀ a (h : a < 7 - 1), 3 ≤ a → Commutes β (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h1]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by simp; omega)) (by fr_idx)
  have hMβ : Commutes β M := by
    rw [← h1]
    exact commutes_symm (nd.commK _)
  have hstab2 : (locImg Ω z (nd.J ⟨2, by omega⟩)).map
      (locAut hΩ.conjInvariant htz).toMonoidHom = locImg Ω z (nd.J ⟨2, by omega⟩) := by
    rw [locAut_locImg hΩ.conjInvariant htz]
    congr 1
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj (a := ⟨2, by omega⟩) (b := ⟨1, by omega⟩) (by fr_idx)
    rw [h1] at hW₁
    exact conjSub_eq_of_standardPair h2 hW₁ ht.mem ht.orderOf_eq_two
  let θ : spinGroup (quadMinus 7 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) →* locQuot Ω z := c.d.ψ
  let σ := locAut hΩ.conjInvariant htz
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hΩ.conjInvariant htz h2t
  have hσr : ∀ k', σ (θ k') ∈ θ.range := fun k' =>
    locAut_mem_range c htz h2t hKt
      (Exotic.range_le_iSup_fund_minus (by omega) hadm c.hY.std c.d.ψ) k'
  let R : ℕ → Subgroup (SpinM p f 7) := fun a => Rz (a + 2)
  let Rtw : Subgroup (SpinM p f 7) := Rz 5
  let RM : Subgroup (SpinM p f 7) := RzM
  have hRf : ∀ a ≤ 2, R a ∈ fundamentalSubgroups .POmegaMinus
      (minusDatum 7 (minusCoeffs_irr p f)) := fun a ha =>
    (hRz (a + 2) (by omega) (by omega)).1
  have hRtwf : Rtw ∈ fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr p f)) :=
    (hRz 5 (by omega) (by omega)).1
  have hRMf : RM ∈ fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr p f)) :=
    hRzM
  have hadj : ∀ a < 2, ModelAdj (Subgroup.center _) (R a) (R (a + 1)) := fun a ha =>
    hadjz (a + 2) (by omega) (a + 3) (by omega) (by omega) (by omega) (by fr_idx)
  have hlin : ∀ a < 2, ∃ W, LinearBlockStandardPair (GaloisField p f) W (R a) (R (a + 1)) :=
    fun a ha => hlinz (a + 2) (by omega) (a + 3) (by omega) (by omega) (by omega) (by fr_idx)
  have hcomm : ∀ a b, a + 1 < b → b ≤ 2 → Commutes (R a) (R b) := fun a b hab hb =>
    hcommz (a + 2) (by omega) (b + 2) (by omega) (by omega) (by omega)
      (nd.commutes_of_not_adj (fin_ne_of_val_ne (by fr_idx)) (by fr_idx))
  have hM : ∀ a ≤ 2, Commutes RM (R a) := fun a ha =>
    hMcomm (a + 2) (by omega) (by omega)
  have hne : Rtw ≠ R 2 := by
    intro h
    have h' : Rz 5 = Rz (2 + 2) := h
    have h2' : nd.J ⟨5, by omega⟩ = nd.J ⟨2 + 2, by omega⟩ :=
      c.eq_of_locImg_eq (hmemz _ _ (by omega)) (hmemz _ _ (by omega))
        (by rw [(hRz 5 (by omega) (by omega)).2, (hRz (2 + 2) (by omega) (by omega)).2, h'])
    exact nd.ne_J hΩ (fin_ne_of_val_ne (by simp)) h2'
  obtain ⟨hdist2, htwin2⟩ := chain_twin_data_seven c hsingle hshape hMΩ nd h0
    (hRz 2 (by omega) (by omega)).1 (hRz 3 (by omega) (by omega)).1 (hRz 4 (by omega) (by omega)).1
    (hRz 5 (by omega) (by omega)).1 (hRz 2 (by omega) (by omega)).2 (hRz 3 (by omega) (by omega)).2
    (hRz 4 (by omega) (by omega)).2 (hRz 5 (by omega) (by omega)).2
  have hdist : ∀ a b, a + 1 < b → b ≤ 2 → ∀ i j,
      IsFundamental (QM p f 7) ((R a).map (spinAction (QM p f 7))) i →
      IsFundamental (QM p f 7) ((R b).map (spinAction (QM p f 7))) j → i ≠ j := by
    intro a b hab hb
    obtain rfl : a = 0 := by omega
    obtain rfl : b = 2 := by omega
    exact hdist2
  have htwin : ∀ i j, IsFundamental (QM p f 7) ((R 2).map (spinAction (QM p f 7))) i →
      IsFundamental (QM p f 7) (Rtw.map (spinAction (QM p f 7))) j → i = j := htwin2
  have hfix : ∀ a, 1 ≤ a → a ≤ 2 → ∀ y ∈ R a, σ (θ y) = θ y := fun a ha1 ha2 y hy =>
    hfixnode (a + 2) (by omega) (by omega) (hβJ (a + 2) (by omega) (by omega)) _
      (by rw [(hRz (a + 2) (by omega) (by omega)).2]; exact ⟨y, hy, rfl⟩)
  have hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y := fun y hy =>
    hfixnode 5 (by omega) (by omega) (hβJ 5 (by omega) (by omega)) _
      (by rw [(hRz 5 (by omega) (by omega)).2]; exact ⟨y, hy, rfl⟩)
  have hfixM : ∀ y ∈ RM, σ (θ y) = θ y := fun y hy =>
    (locAut_fixed_iff hΩ c.hP1 htz hMz).mp (fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hMβ t ht.mem n hn).symm) _
      (by rw [hMR]; exact ⟨y, hy, rfl⟩)
  have hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ := by
    intro y hy
    have hL : locImg Ω z (nd.J ⟨2, by omega⟩) = (R 0).map θ :=
      (hRz (0 + 2) (by omega) (by omega)).2
    rw [← hL, ← hstab2]
    refine ⟨θ y, ?_, rfl⟩
    rw [hL]
    exact ⟨y, hy, rfl⟩
  obtain ⟨x, tM, hxR, hxtw, hxM, α, g₀, hαθ, hg₀O, hg₀2, hconj⟩ := minusLift_of_chain_frame
    (s := 2) c.hp2 c.hq (by omega) θ c.d.ker_le σ hσ2 hσr hRf hRtwf hRMf hadj hlin hcomm hM hdist
    hne htwin hfix hfixtw hfixM hnorm0
  have hnode : ∀ a (ha : a ≤ 2), locImg Ω z (nd.J ⟨a + 2, by omega⟩) =
      ((rootSL2 (minusHyp 7 (minusCoeffs p f).1 (minusCoeffs p f).2) a (a + 1)
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom).map
          c.d.ψ := by
    intro a ha
    rw [(hRz (a + 2) (by omega) (by omega)).2]
    have h := hxR a ha
    change Rz (a + 2) = _ at h
    rw [h]
  have hMimg : locImg Ω z M =
      ((rootSL2 (minusHyp 7 (minusCoeffs p f).1 (minusCoeffs p f).2) 4 5
        (by omega) (by omega) (by omega) true tM).map (MulAut.conj x).toMonoidHom).map c.d.ψ := by
    rw [hMR]
    have h : RM = _ := hxM
    change RzM = _ at h
    rw [h]
  have hconj' : ∀ y, spinAction (QM p f 7) (α y) * g₀ = g₀ * spinAction (QM p f 7) y :=
    fun y => LinearEquiv.ext fun v => hconj y v
  obtain ⟨R₁, hR₁, ⟨F₁, hR₁m, hv₁, hα₁⟩, hR₁f⟩ := leaf_fixed_cluster c hsingle hshape ht htz hMΩ nd
    h0 h1 x tM hnode hMimg
  obtain ⟨R₂, hR₂, ⟨F₂, hR₂m, hv₂, hα₂⟩, hR₂f⟩ := leaf_fixed_M c hsingle hshape ht htz hMΩ nd
    h0 h1 x tM hnode hMimg
  have hmov0 : ∃ y ∈ (rootSL2 (minusHyp 7 (minusCoeffs p f).1 (minusCoeffs p f).2) 0 1
      (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom,
      σ (θ y) ≠ θ y := by
    by_contra hcon
    push Not at hcon
    have hJ2 := hmemz 2 (by omega) (by omega)
    have hNt : nd.J ⟨2, by omega⟩ ≤ Subgroup.centralizer ({t} : Set G) := by
      rw [locAut_fixed_iff hΩ c.hP1 htz hJ2]
      intro a ha
      rw [hnode 0 (by omega)] at ha
      obtain ⟨y, hy, rfl⟩ := ha
      exact hcon y hy
    have hβJ2 : Commutes β (nd.J ⟨2, by omega⟩) :=
      commutes_partner_of_centralizes_gen hMFZ c hsingle hshape (h1 ▸ nd.mem _) ht ⟨W, hW⟩ hJ2
        hNt (hKJ 2 (by omega) le_rfl)
    exact nd.not_commutes_of_adj (a := ⟨1, by omega⟩) (b := ⟨2, by omega⟩) (by fr_idx)
      (h1 ▸ hβJ2)
  refine ⟨x, ?_, ?_⟩
  · rw [rankOne_minusDatum_of_lt hirr (by show 0 + 1 < 7 - 1; omega)]
    exact hnode 0 (by omega)
  · refine minus_nodes_fixed_seven hirr h2 c.h4 cq.ker_le θ c.d.ker_le σ α hαθ hg₀O hg₀2 hconj'
      x tM ?_ ?_ ⟨R₁, F₁, cq.perf R₁ hR₁, hR₁m, hv₁, hα₁, hR₁f⟩
      ⟨R₂, F₂, cq.perf R₂ hR₂, hR₂m, hv₂, hα₂, hR₂f⟩ ?_ hmov0
    · intro a h1' ha y hy
      exact hfix a h1' ha y (by rw [hxR a ha]; exact hy)
    · intro y hy
      exact hfixM y (by rw [hxM]; exact hy)
    · intro y hy
      have h := hnorm0 y (by rw [hxR 0 (by omega)]; exact hy)
      rwa [hxR 0 (by omega)] at h

theorem PartnerPatternMinus.of_fixed_member_seven (c : TCtx p f .POmegaMinus 7 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaMinus 7 Ω z) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hfix : HasFixedMember Ω K β z) : PartnerPatternMinus p f 7 Ω K β t := by
  classical
  have hΩ := c.hΩ
  have htz := partner_involution_commutes c.hp2 c.hz ht hKβ
  obtain ⟨M, hMΩ, hKM, hβM, hMnot⟩ := hfix
  have hMN : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N := by
    by_contra hcon
    push Not at hcon
    exact hMnot hcon
  obtain ⟨nd, h0, h1⟩ := exists_dnodes_of_pair_minus (by omega) c hsingle hshape hβ ht hKβ hMΩ hKM
    hβM
  obtain ⟨x, hx2, hxfix⟩ := minus_fixed_of_nodes_seven c hsingle hshape ht hKβ hMΩ hMN nd h0 h1
  obtain ⟨j, hjK, hjperf, hjY, hjΩ, hjc, hjp, hjtw, hjimg⟩ :=
    exists_nodes_typeTwistedD_img (m := 7) (by omega) (spinMinus6Generated_galois c.hp2)
      (spinMinus6_noCover_galois c.hp2 c.hq) c
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk_surjective (c.d.ψ x)
  have hy : (y₀ : G) ∈ locLayer Ω z := y₀.2
  have hyz : (y₀ : G) * z * (y₀ : G)⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {z} hy)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have himg : ∀ a : Fin (7 - 1), locImg Ω z (conjSub (y₀ : G) (j a)) =
      ((rankOne (minusDatum 7 (minusCoeffs_irr p f)).rootGroup a).map
        (MulAut.conj x).toMonoidHom).map c.d.ψ := by
    intro a
    rw [locImg_conjSub_layer, hjimg a, show locMk Ω z y₀ = c.d.ψ x from hy₀]
    exact map_conj_map_hom c.d.ψ x _
  refine PartnerPatternMinus.of_locAut c hjK hjperf hjY hjΩ hjc hjp hjtw hy htz
    (fun a ha w hw => ?_) (fun a ha => ?_)
  · rw [himg a] at hw
    obtain ⟨r, hr, rfl⟩ := hw
    exact hxfix a ha r hr
  ·
    obtain ⟨a', ha'⟩ := a
    have ha0 : a' = 0 := ha
    subst ha0
    have hmemy : conjSub (y₀ : G) (j ⟨0, by omega⟩) ∈ centralizingMembers Ω {z} := by
      have := centralizingMembers_conj hΩ.conjInvariant (y₀ : G) z
      rw [hyz] at this
      rw [this]
      exact ⟨j ⟨0, by omega⟩, mem_centralizingMembers_of_commutes (hjΩ _ (by simp))
        c.hz.mem (commutes_symm (hjK _)), rfl⟩
    have hK2 : Commutes K (nd.J ⟨2, by omega⟩) := by
      rw [← h0]
      exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by simp)) (by fr_idx)
    have hJ2 : nd.J ⟨2, by omega⟩ ∈ centralizingMembers Ω {z} :=
      mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem (commutes_symm hK2)
    have heq : conjSub (y₀ : G) (j ⟨0, by omega⟩) = nd.J ⟨2, by omega⟩ :=
      c.eq_of_locImg_eq hmemy hJ2 (by rw [himg, hx2])
    rw [heq]
    obtain ⟨W, hW⟩ := nd.pair_of_adj (a := ⟨1, by omega⟩) (b := ⟨2, by omega⟩) (by fr_idx)
    rw [h1] at hW
    exact ⟨W, hW⟩

end Main

end CFSG.ClassicalInvolution.RouteD.TwinSmall

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT

variable {p f : ℕ} [Fact p.Prime]

theorem twinTDCase_seven : TwinTDCase p f 7 := by
  intro G _ _ _ hnab K z S m hm hshape β hβ t ht hKβ hfix
  subst hm
  obtain ⟨c⟩ := TCtx.nonempty_minus (by omega) S.odd S.five S.inClass S.exact
    (mem_conjClass_self K) S.cls S.p1 hshape
  exact TwinSmall.PartnerPatternMinus.of_fixed_member_seven c (single_class K) hshape hβ ht hKβ hfix

end CFSG.ClassicalInvolution.RouteD
