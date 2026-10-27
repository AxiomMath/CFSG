module

public import CFSG.ClassicalInvolution.RouteD.SmallBFive
public import CFSG.ClassicalInvolution.RouteD.GapsFrBLast
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

variable {p f : ℕ} [Fact p.Prime]

section Chain

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups IsClassicalMember
  centralizingMembers modelUniv)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.RouteD CFSG.Timmesfeld

theorem toralNormal_odd_of_chain_five_lift (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type} [Group X]
    (θ : spinGroup (quadOdd 5 (GaloisField p f)) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadOdd 5 (GaloisField p f))))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {R : ℕ → Subgroup (spinGroup (quadOdd 5 (GaloisField p f)))}
    {Rtw RM : Subgroup (spinGroup (quadOdd 5 (GaloisField p f)))}
    (hRf : ∀ a ≤ 1, R a ∈ fundamentalSubgroups .POmegaOdd (oddDatum 5 (GaloisField p f)))
    (hRtwf : Rtw ∈ fundamentalSubgroups .POmegaOdd (oddDatum 5 (GaloisField p f)))
    (hRMf : RM ∈ fundamentalSubgroups .POmegaOdd (oddDatum 5 (GaloisField p f)))
    (hadj : ModelAdj (Subgroup.center _) (R 0) (R 1))
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField p f) W (R 0) (R 1))
    (hM : ∀ a ≤ 1, Commutes RM (R a))
    (hadjtw : ModelAdj (Subgroup.center _) (R 0) Rtw) (hcommtw : Commutes (R 1) Rtw)
    (hMtw : Commutes RM Rtw) (hne : Rtw ≠ R 1)
    (hfix : ∀ y ∈ R 1, σ (θ y) = θ y) (hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y)
    (hfixM : ∀ y ∈ RM, σ (θ y) = θ y) (hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ) :
    ∃ (α : spinGroup (quadOdd 5 (GaloisField p f)) ≃* spinGroup (quadOdd 5 (GaloisField p f)))
      (k₀ : spinGroup (quadOdd 5 (GaloisField p f))) (v : Fin 5 → ZMod 2),
      (∀ x, θ (α x) = σ (θ x)) ∧ OddToralProp θ σ k₀ v ∧ OddLift α v := by
  have hm3 : 3 ≤ 5 := by omega
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have cq := centralQuot_odd (m := 5) hp2 hm3 hq
  have hdim : 9 ≤ Module.finrank (GaloisField p f)
      (Fin 5 ⊕ Fin 5 ⊕ Unit → GaloisField p f) := by
    rw [finrank_odd]
    omega
  have hQ : (quadOdd 5 (GaloisField p f)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadOdd 5 (GaloisField p f) h2)
  have htwin := chain_twin_five_odd hp2 hq (hRf 0 (by omega)) (hRf 1 le_rfl) hRtwf hRMf hadj hadjtw
    hcommtw (hM 0 (by omega)) (hM 1 le_rfl) hMtw
  obtain ⟨x, hxR, hxtw, t, hxM⟩ := spin_chain_recognition_gen hp2 hq hQ (s := 1) (by omega)
    (oddFrame (1 + 4) (GaloisField p f)).toHypFrame hdim cq hRf hRtwf hRMf
    (fun a ha => by
      obtain rfl : a = 0 := by omega
      exact hadj)
    (fun a ha => by
      obtain rfl : a = 0 := by omega
      exact hlin)
    (fun a b hab hb => absurd hb (by omega)) hM
    (fun a b hab hb => absurd hb (by omega)) hne htwin
  exact toralNormal_odd_of_frame_chain_lift hp2 hq (s := 1) (by omega) θ hker σ hσ2 hσr x t hxR
    hxtw hxM (fun a ha1 ha2 => by
      obtain rfl : a = 1 := by omega
      exact hfix) hfixtw hfixM hnorm0

end Chain

section Nodes

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld

local macro "sbl_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes.adj_def]; done)
    | (simp [DNodes.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem toralNormalB_lift_of_nodes_five (c : TCtx p f .POmegaOdd 5 Ω K z) {β : Subgroup G}
    {t : G} (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hMN : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N)
    (nd : DNodes p f 5 Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β) :
    ∃ (α : spinGroup (quadOdd 5 (GaloisField p f)) ≃* spinGroup (quadOdd 5 (GaloisField p f)))
      (k₀ : spinGroup (quadOdd 5 (GaloisField p f))) (v : Fin 5 → ZMod 2),
      (∀ x, c.d.ψ (α x) = locAut c.hΩ.conjInvariant
        (partner_involution_commutes c.hp2 c.hz ht hKβ) (c.d.ψ x)) ∧
      ToralPropB c (partner_involution_commutes c.hp2 c.hz ht hKβ) k₀ v ∧ OddLift α v := by
  classical
  have hm3 : 3 ≤ 5 := by omega
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have htz := partner_involution_commutes c.hp2 c.hz ht hKβ
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  obtain ⟨W, hW⟩ := hKβ
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hF := orthFacts_odd c.hp2 (by norm_num : 4 ≤ 5) c.hq
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr c.hf
  have hadm : StatedLieAdmissible .POmegaOdd 5 p f := ⟨Fact.out, hf1, by omega, c.hp2⟩
  have hKJ : ∀ a (h : a < 5), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by sbl_idx)) (by sbl_idx)
  have hmemz : ∀ a (h : a < 5), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hnb : ∀ a (h : a < 5), 2 ≤ a →
      ∃ b, ∃ hb : b < 5, 2 ≤ b ∧ DNodes.Adj (⟨a, h⟩ : Fin 5) ⟨b, hb⟩ := by
    intro a h ha
    by_cases h1 : a = 2
    · exact ⟨3, by omega, by omega, by sbl_idx⟩
    · exact ⟨2, by omega, by omega, by sbl_idx⟩
  have hlayer : ∀ a (h : a < 5), 2 ≤ a → IsLayerMember c (nd.J ⟨a, h⟩) := by
    intro a h ha
    obtain ⟨b, hb, hb2, hab⟩ := hnb a h ha
    exact IsLayerMember.of_not_commutes c (hmemz a h ha) (hmemz b hb hb2)
      (nd.ne_J hΩ hab.ne) (nd.not_commutes_of_adj hab)
  have hexRz : ∀ a : ℕ, ∃ R : Subgroup (modelUniv .POmegaOdd 5 p f Fact.out).K,
      ∀ (h : a < 5), 2 ≤ a →
        R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 5 p f Fact.out).D ∧
          locImg Ω z (nd.J ⟨a, h⟩) = R.map c.d.ψ := by
    intro a
    by_cases hv : a < 5 ∧ 2 ≤ a
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
  have hcommz : ∀ a (ha : a < 5) b (hb : b < 5) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      Commutes (nd.J ⟨a, ha⟩) (nd.J ⟨b, hb⟩) → Commutes (Rz a) (Rz b) :=
    fun a ha b hb ha2 hb2 h => (c.commutes_iff_fund (hmemz a ha ha2) (hmemz b hb hb2)
      (hRz a ha ha2).1 (hRz a ha ha2).2 (hRz b hb hb2).2).mp h
  have hMcomm : ∀ a (ha : a < 5) (ha2 : 2 ≤ a), Commutes RzM (Rz a) :=
    fun a ha ha2 => (c.commutes_iff_fund hMz (hmemz a ha ha2) hRzM hMR (hRz a ha ha2).2).mp
      (nd.commK _)
  have hadjz : ∀ a (ha : a < 5) b (hb : b < 5) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes.Adj (⟨a, ha⟩ : Fin 5) ⟨b, hb⟩ →
        ModelAdj (Subgroup.center (modelUniv .POmegaOdd 5 p f Fact.out).K)
          (Rz a) (Rz b) := fun a ha b hb ha2 hb2 hab =>
    modelAdj_of_adj c (hmemz a ha ha2) (hmemz b hb hb2) (hRz a ha ha2).1 (hRz b hb hb2).1
      (hRz a ha ha2).2 (hRz b hb hb2).2 (nd.cl _) (nd.cl _) (nd.ne_J hΩ hab.ne)
      (nd.not_commutes_of_adj hab) (nd.commute_w h2 _ _) (nd.conjSub_w h2 hab)
  have hlinz : ∀ a (ha : a < 5) b (hb : b < 5) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes.Adj (⟨a, ha⟩ : Fin 5) ⟨b, hb⟩ →
        ∃ W₁, LinearBlockStandardPair (GaloisField p f) W₁ (Rz a) (Rz b) := by
    intro a ha b hb ha2 hb2 hab
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj hab
    obtain ⟨W₂, hW₂⟩ := linearBlockStandardPair_locImg_of_members c.hP1 (hmemz a ha ha2)
      (hmemz b hb hb2) hW₁
    rw [(hRz a ha ha2).2, (hRz b hb hb2).2] at hW₂
    exact hF.lift c.d.ψ c.d.ker_le _ (hRz a ha ha2).1 _ (hRz b hb hb2).1 ⟨W₂, hW₂⟩
  have hfixnode : ∀ a (h : a < 5), 2 ≤ a → Commutes β (nd.J ⟨a, h⟩) →
      ∀ x ∈ locImg Ω z (nd.J ⟨a, h⟩), locAut hΩ.conjInvariant htz x = x := fun a h ha hc =>
    (locAut_fixed_iff hΩ c.hP1 htz (hmemz a h ha)).mp fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hc t ht.mem n hn).symm
  have hβJ : ∀ a (h : a < 5), 3 ≤ a → Commutes β (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h1]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by sbl_idx)) (by sbl_idx)
  have hMβ : Commutes β M := by
    rw [← h1]
    exact commutes_symm (nd.commK _)
  have hstab2 : (locImg Ω z (nd.J ⟨2, by omega⟩)).map (locAut hΩ.conjInvariant htz).toMonoidHom =
      locImg Ω z (nd.J ⟨2, by omega⟩) := by
    rw [locAut_locImg hΩ.conjInvariant htz]
    congr 1
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj (a := ⟨2, by omega⟩) (b := ⟨1, by omega⟩) (by sbl_idx)
    rw [h1] at hW₁
    exact conjSub_eq_of_standardPair h2 hW₁ ht.mem ht.orderOf_eq_two
  let θ : spinGroup (quadOdd 5 (GaloisField p f)) →* locQuot Ω z := c.d.ψ
  let σ := locAut hΩ.conjInvariant htz
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hΩ.conjInvariant htz h2t
  have hσr : ∀ k', σ (θ k') ∈ θ.range := fun k' =>
    locAut_mem_range c htz h2t hKt (range_le_iSup_fund_odd (by omega) hadm c.hY.std c.d.ψ) k'
  let R : ℕ → Subgroup (spinGroup (quadOdd 5 (GaloisField p f))) := fun a => Rz (a + 2)
  let Rtw : Subgroup (spinGroup (quadOdd 5 (GaloisField p f))) := Rz 4
  let RM : Subgroup (spinGroup (quadOdd 5 (GaloisField p f))) := RzM
  have hRf : ∀ a ≤ 1, R a ∈ fundamentalSubgroups .POmegaOdd (oddDatum 5 (GaloisField p f)) :=
    fun a ha => (hRz (a + 2) (by omega) (by omega)).1
  have hRtwf : Rtw ∈ fundamentalSubgroups .POmegaOdd (oddDatum 5 (GaloisField p f)) :=
    (hRz 4 (by omega) (by omega)).1
  have hRMf : RM ∈ fundamentalSubgroups .POmegaOdd (oddDatum 5 (GaloisField p f)) := hRzM
  have hadj : ModelAdj (Subgroup.center _) (R 0) (R 1) :=
    hadjz 2 (by omega) 3 (by omega) (by omega) (by omega) (by sbl_idx)
  have hlin : ∃ W, LinearBlockStandardPair (GaloisField p f) W (R 0) (R 1) :=
    hlinz 2 (by omega) 3 (by omega) (by omega) (by omega) (by sbl_idx)
  have hM : ∀ a ≤ 1, Commutes RM (R a) := fun a ha =>
    hMcomm (a + 2) (by omega) (by omega)
  have hadjtw : ModelAdj (Subgroup.center _) (R 0) Rtw :=
    hadjz 2 (by omega) 4 (by omega) (by omega) (by omega) (by sbl_idx)
  have hcommtw : Commutes (R 1) Rtw :=
    hcommz 3 (by omega) 4 (by omega) (by omega) (by omega)
      (nd.commutes_of_not_adj (fin_ne_of_val_ne (by sbl_idx)) (by sbl_idx))
  have hMtw : Commutes RM Rtw := hMcomm 4 (by omega) (by omega)
  have hne : Rtw ≠ R 1 := by
    intro h
    have h' : Rz 4 = Rz (1 + 2) := h
    have h2' : nd.J ⟨4, by omega⟩ = nd.J ⟨1 + 2, by omega⟩ :=
      c.eq_of_locImg_eq (hmemz _ _ (by omega)) (hmemz _ _ (by omega))
        (by rw [(hRz 4 (by omega) (by omega)).2, (hRz (1 + 2) (by omega) (by omega)).2, h'])
    exact nd.ne_J hΩ (fin_ne_of_val_ne (by sbl_idx)) h2'
  have hfix : ∀ y ∈ R 1, σ (θ y) = θ y := fun y hy =>
    hfixnode (1 + 2) (by omega) (by omega) (hβJ (1 + 2) (by omega) (by omega)) _
      (by rw [(hRz (1 + 2) (by omega) (by omega)).2]; exact ⟨y, hy, rfl⟩)
  have hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y := fun y hy =>
    hfixnode 4 (by omega) (by omega) (hβJ 4 (by omega) (by omega)) _
      (by rw [(hRz 4 (by omega) (by omega)).2]; exact ⟨y, hy, rfl⟩)
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
  obtain ⟨α, k₀, v, hαθ, hk₀, hl⟩ := toralNormal_odd_of_chain_five_lift c.hp2 c.hq θ c.d.ker_le σ
    hσ2 hσr hRf hRtwf hRMf hadj hlin hM hadjtw hcommtw hMtw hne hfix hfixtw hfixM hnorm0
  exact ⟨α, k₀, v, hαθ, hk₀, hl⟩

end Nodes

end CFSG.ClassicalInvolution.RouteD.Gaps
