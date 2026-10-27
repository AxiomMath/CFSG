module

public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusZ
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusSmallLeaf
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusSmallFix
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

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.RootSystem
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.CurtisTits CFSG.Timmesfeld QuadraticMap

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

theorem minus_fixed_of_nodes_ge3 (hMFZ : FundNoncentral p) {u : ℕ}
    (c : TCtx p f .POmegaMinus (u + 3 + 5) Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hshape : LocalShapeT p f 2 .POmegaMinus (u + 3 + 5) Ω z) {β : Subgroup G} {t : G}
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hMN : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N)
    (nd : DNodes p f (u + 3 + 5 - 1) Ω M) (h0 : nd.J ⟨0, by omega⟩ = K)
    (h1 : nd.J ⟨1, by omega⟩ = β) :
    ∃ x : spinGroup (quadMinus (u + 3 + 5) (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2),
      locImg Ω z (nd.J ⟨2, by omega⟩) =
        ((rankOne (minusDatum (u + 3 + 5) (minusCoeffs_irr p f)).rootGroup
          (⟨0, by omega⟩ : Fin (u + 3 + 5 - 1))).map (MulAut.conj x).toMonoidHom).map c.d.ψ ∧
      ∀ k : Fin (u + 3 + 5 - 1), 1 ≤ k.val →
        ∀ r ∈ (rankOne (minusDatum (u + 3 + 5) (minusCoeffs_irr p f)).rootGroup k).map
          (MulAut.conj x).toMonoidHom,
        locAut c.hΩ.conjInvariant (partner_involution_commutes c.hp2 c.hz ht hKβ) (c.d.ψ r) =
          c.d.ψ r := by
  classical
  have hirr := minusCoeffs_irr p f
  have hm3 : 3 ≤ u + 3 + 5 - 1 := by omega
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
  have hadm : StatedLieAdmissible .POmegaMinus (u + 3 + 5) p f :=
    ⟨Fact.out, hf1, by show 4 ≤ u + 3 + 5; omega⟩
  have hF := orthFacts_minus c.hp2 (by omega : 5 ≤ u + 3 + 5) c.hq
  have hKJ : ∀ a (h : a < u + 3 + 5 - 1), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by simp; omega)) (by fr_idx)
  have hmemz : ∀ a (h : a < u + 3 + 5 - 1), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hnb : ∀ a (h : a < u + 3 + 5 - 1), 2 ≤ a →
      ∃ b, ∃ hb : b < u + 3 + 5 - 1, 2 ≤ b ∧ DNodes.Adj (⟨a, h⟩ : Fin (u + 3 + 5 - 1)) ⟨b, hb⟩ := by
    intro a h ha
    by_cases h1 : a ≤ u + 4
    · exact ⟨a + 1, by omega, by omega, by fr_idx⟩
    · exact ⟨u + 4, by omega, by omega, by fr_idx⟩
  have hlayer : ∀ a (h : a < u + 3 + 5 - 1), 2 ≤ a → IsLayerMember c (nd.J ⟨a, h⟩) := by
    intro a h ha
    obtain ⟨b, hb, hb2, hab⟩ := hnb a h ha
    exact IsLayerMember.of_not_commutes c (hmemz a h ha) (hmemz b hb hb2)
      (nd.ne_J hΩ hab.ne) (nd.not_commutes_of_adj hab)
  have hexRz : ∀ a : ℕ, ∃ R : Subgroup (modelUniv .POmegaMinus (u + 3 + 5) p f Fact.out).K,
      ∀ (h : a < u + 3 + 5 - 1), 2 ≤ a →
        R ∈ fundamentalSubgroups .POmegaMinus
            (modelUniv .POmegaMinus (u + 3 + 5) p f Fact.out).D ∧
          locImg Ω z (nd.J ⟨a, h⟩) = R.map c.d.ψ := by
    intro a
    by_cases hv : a < u + 3 + 5 - 1 ∧ 2 ≤ a
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
  have hcommz : ∀ a (ha : a < u + 3 + 5 - 1) b (hb : b < u + 3 + 5 - 1) (ha2 : 2 ≤ a)
      (hb2 : 2 ≤ b), Commutes (nd.J ⟨a, ha⟩) (nd.J ⟨b, hb⟩) → Commutes (Rz a) (Rz b) :=
    fun a ha b hb ha2 hb2 h => (c.commutes_iff_fund (hmemz a ha ha2) (hmemz b hb hb2)
      (hRz a ha ha2).1 (hRz a ha ha2).2 (hRz b hb hb2).2).mp h
  have hMcomm : ∀ a (ha : a < u + 3 + 5 - 1) (ha2 : 2 ≤ a), Commutes RzM (Rz a) :=
    fun a ha ha2 => (c.commutes_iff_fund hMz (hmemz a ha ha2) hRzM hMR (hRz a ha ha2).2).mp
      (nd.commK _)
  have hadjz : ∀ a (ha : a < u + 3 + 5 - 1) b (hb : b < u + 3 + 5 - 1) (ha2 : 2 ≤ a)
      (hb2 : 2 ≤ b), DNodes.Adj (⟨a, ha⟩ : Fin (u + 3 + 5 - 1)) ⟨b, hb⟩ →
        ModelAdj (Subgroup.center (modelUniv .POmegaMinus (u + 3 + 5) p f Fact.out).K)
          (Rz a) (Rz b) := fun a ha b hb ha2 hb2 hab =>
    modelAdj_of_adj c (hmemz a ha ha2) (hmemz b hb hb2) (hRz a ha ha2).1 (hRz b hb hb2).1
      (hRz a ha ha2).2 (hRz b hb hb2).2 (nd.cl _) (nd.cl _) (nd.ne_J hΩ hab.ne)
      (nd.not_commutes_of_adj hab) (nd.commute_w h2 _ _) (nd.conjSub_w h2 hab)
  have hlinz : ∀ a (ha : a < u + 3 + 5 - 1) b (hb : b < u + 3 + 5 - 1) (ha2 : 2 ≤ a)
      (hb2 : 2 ≤ b), DNodes.Adj (⟨a, ha⟩ : Fin (u + 3 + 5 - 1)) ⟨b, hb⟩ →
        ∃ W₁, LinearBlockStandardPair (GaloisField p f) W₁ (Rz a) (Rz b) := by
    intro a ha b hb ha2 hb2 hab
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj hab
    obtain ⟨W₂, hW₂⟩ := linearBlockStandardPair_locImg_of_members c.hP1 (hmemz a ha ha2)
      (hmemz b hb hb2) hW₁
    rw [(hRz a ha ha2).2, (hRz b hb hb2).2] at hW₂
    exact hF.lift c.d.ψ c.d.ker_le _ (hRz a ha ha2).1 _ (hRz b hb hb2).1 ⟨W₂, hW₂⟩
  have hfixnode : ∀ a (h : a < u + 3 + 5 - 1), 2 ≤ a → Commutes β (nd.J ⟨a, h⟩) →
      ∀ x ∈ locImg Ω z (nd.J ⟨a, h⟩), locAut hΩ.conjInvariant htz x = x := fun a h ha hc =>
    (locAut_fixed_iff hΩ c.hP1 htz (hmemz a h ha)).mp fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hc t ht.mem n hn).symm
  have hβJ : ∀ a (h : a < u + 3 + 5 - 1), 3 ≤ a → Commutes β (nd.J ⟨a, h⟩) := by
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
  let θ : spinGroup (quadMinus (u + 3 + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) →* locQuot Ω z := c.d.ψ
  let σ := locAut hΩ.conjInvariant htz
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hΩ.conjInvariant htz h2t
  have hσr : ∀ k', σ (θ k') ∈ θ.range := fun k' =>
    locAut_mem_range c htz h2t hKt
      (Exotic.range_le_iSup_fund_minus (by omega) hadm c.hY.std c.d.ψ) k'
  let R : ℕ → Subgroup (spinGroup (quadMinus (u + 3 + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) := fun a => Rz (a + 2)
  let Rtw : Subgroup (spinGroup (quadMinus (u + 3 + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) := Rz (u + 6)
  let RM : Subgroup (spinGroup (quadMinus (u + 3 + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) := RzM
  have hRf : ∀ a ≤ u + 3, R a ∈ fundamentalSubgroups .POmegaMinus
      (minusDatum (u + 3 + 5) (minusCoeffs_irr p f)) := fun a ha =>
    (hRz (a + 2) (by omega) (by omega)).1
  have hRtwf : Rtw ∈ fundamentalSubgroups .POmegaMinus
      (minusDatum (u + 3 + 5) (minusCoeffs_irr p f)) :=
    (hRz (u + 6) (by omega) (by omega)).1
  have hRMf : RM ∈ fundamentalSubgroups .POmegaMinus
      (minusDatum (u + 3 + 5) (minusCoeffs_irr p f)) := hRzM
  have hadj : ∀ a < u + 3, ModelAdj (Subgroup.center _) (R a) (R (a + 1)) := fun a ha =>
    hadjz (a + 2) (by omega) (a + 3) (by omega) (by omega) (by omega) (by fr_idx)
  have hlin : ∀ a < u + 3, ∃ W, LinearBlockStandardPair (GaloisField p f) W (R a) (R (a + 1)) :=
    fun a ha => hlinz (a + 2) (by omega) (a + 3) (by omega) (by omega) (by omega) (by fr_idx)
  have hcomm : ∀ a b, a + 1 < b → b ≤ u + 3 → Commutes (R a) (R b) := fun a b hab hb =>
    hcommz (a + 2) (by omega) (b + 2) (by omega) (by omega) (by omega)
      (nd.commutes_of_not_adj (fin_ne_of_val_ne (by fr_idx)) (by fr_idx))
  have hM : ∀ a ≤ u + 3, Commutes RM (R a) := fun a ha =>
    hMcomm (a + 2) (by omega) (by omega)
  have hadjtw : ModelAdj (Subgroup.center _) (R (u + 2)) Rtw :=
    hadjz (u + 2 + 2) (by omega) (u + 6) (by omega) (by omega) (by omega) (by fr_idx)
  have hcommtw : ∀ a, a ≤ u + 1 → Commutes (R a) Rtw := fun a ha =>
    hcommz (a + 2) (by omega) (u + 6) (by omega) (by omega) (by omega)
      (nd.commutes_of_not_adj (fin_ne_of_val_ne (by fr_idx)) (by fr_idx))
  have hcommtw' : Commutes (R (u + 3)) Rtw :=
    hcommz (u + 3 + 2) (by omega) (u + 6) (by omega) (by omega) (by omega)
      (nd.commutes_of_not_adj (fin_ne_of_val_ne (by fr_idx)) (by fr_idx))
  have hne : Rtw ≠ R (u + 3) := by
    intro h
    have h' : Rz (u + 6) = Rz (u + 3 + 2) := h
    have h2' : nd.J ⟨u + 6, by omega⟩ = nd.J ⟨u + 3 + 2, by omega⟩ :=
      c.eq_of_locImg_eq (hmemz _ _ (by omega)) (hmemz _ _ (by omega))
        (by rw [(hRz (u + 6) (by omega) (by omega)).2, (hRz (u + 3 + 2) (by omega) (by omega)).2,
          h'])
    exact nd.ne_J hΩ (fin_ne_of_val_ne (by simp)) h2'
  have hfix : ∀ a, 1 ≤ a → a ≤ u + 3 → ∀ y ∈ R a, σ (θ y) = θ y := fun a ha1 ha2 y hy =>
    hfixnode (a + 2) (by omega) (by omega) (hβJ (a + 2) (by omega) (by omega)) _
      (by rw [(hRz (a + 2) (by omega) (by omega)).2]; exact ⟨y, hy, rfl⟩)
  have hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y := fun y hy =>
    hfixnode (u + 6) (by omega) (by omega) (hβJ (u + 6) (by omega) (by omega)) _
      (by rw [(hRz (u + 6) (by omega) (by omega)).2]; exact ⟨y, hy, rfl⟩)
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
  obtain ⟨x, tM, hxR, hxtw, hxM, α, g₀, hαθ, hg₀O, hg₀2, hconj⟩ := minusLift_of_chain_long c.hp2
    c.hq θ c.d.ker_le σ hσ2 hσr hRf hRtwf hRMf hadj hlin hcomm hM hadjtw hcommtw hcommtw' hne hfix
    hfixtw hfixM hnorm0
  have cq := Exotic.centralQuot_minus c.hp2 c.hq hadm
  have hnode : ∀ a (ha : a ≤ u + 3), locImg Ω z (nd.J ⟨a + 2, by omega⟩) =
      ((rootSL2 (minusHyp (u + 3 + 5) (minusCoeffs p f).1 (minusCoeffs p f).2) a (a + 1)
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom).map
          c.d.ψ := by
    intro a ha
    rw [(hRz (a + 2) (by omega) (by omega)).2]
    have h := hxR a ha
    change Rz (a + 2) = _ at h
    rw [h]
  have hMimg : locImg Ω z M =
      ((rootSL2 (minusHyp (u + 3 + 5) (minusCoeffs p f).1 (minusCoeffs p f).2) (u + 3 + 2)
        (u + 3 + 3) (by omega) (by omega) (by omega) true tM).map
          (MulAut.conj x).toMonoidHom).map c.d.ψ := by
    rw [hMR]
    have h : RM = _ := hxM
    change RzM = _ at h
    rw [h]
  have hconj' : ∀ y, spinAction (quadMinus (u + 3 + 5) (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2) (α y) * g₀ = g₀ * spinAction _ y :=
    fun y => LinearEquiv.ext fun v => hconj y v
  have hMβ' : Commutes β M := hMβ
  refine ⟨x, ?_, ?_⟩
  · rw [rankOne_minusDatum_of_lt hirr (by show 0 + 1 < u + 3 + 5 - 1; omega)]
    exact hnode 0 (by omega)
  · refine minus_nodes_fixed_bridge hirr h2 c.h4 (s := u + 3) (by omega) cq.ker_le θ c.d.ker_le σ
      α hαθ hg₀O hg₀2 hconj' x tM ?_ ?_ ?_ ?_ ?_ ?_
    · intro a h1' ha y hy
      exact hfix a h1' ha y (by rw [hxR a ha]; exact hy)
    · exact leafBridge_fixed (s := u + 3) (by omega) c.hp2 c.hq c hsingle hshape ht htz hMΩ hMz nd
        h0 h1 x tM hnode hMimg
    · intro y hy
      exact hfixM y (by rw [hxM]; exact hy)
    · intro w y hy
      exact leafW_fixed_ge3 (s := u + 3) (by omega) c.hp2 c.hq c hsingle hshape ht htz hMΩ hMz nd
        h0 h1 x tM hnode hMimg (Pi.single w 1) y hy
    · intro y hy
      have h := hnorm0 y (by rw [hxR 0 (by omega)]; exact hy)
      rwa [hxR 0 (by omega)] at h
    · by_contra hcon
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


end Main

end CFSG.ClassicalInvolution.RouteD.Gaps
